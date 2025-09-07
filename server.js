// server.js — Acurly (Provider Cache + Cooldown + SMTP + Fail-soft writeback)
require('dotenv').config();

const express = require('express');
const axios = require('axios');
const crypto = require('crypto');
const dns = require('dns').promises;
const net = require('net');
const tls = require('tls');

// ========== ENV ==========
const {
    // HubSpot
    HUBSPOT_TOKEN,                 // Private App Access Token (Bearer)
    HUBSPOT_APP_SECRET,            // Private App Client Secret (for v3 webhook signatures)
    // Providers
    PROVIDER_PDL_API_KEY,          // People Data Labs (person + company)
    PROVIDER_APOLLO_API_KEY,       // Apollo (optional; may be blocked on free tier)
    ENABLE_PDL = 'true',           // "true"/"false" — feature flag
    ENABLE_APOLLO = 'true',        // "true"/"false" — feature flag
    // Behavior
    WRITEBACK_MIN_CONFIDENCE = '0.80',
    FLAG_MIN_CONFIDENCE = '0.60',
    COOLDOWN_MS = String(10 * 60 * 1000),            // default 10 minutes
    PROVIDER_CACHE_TTL_MS = String(7 * 24 * 60 * 60 * 1000), // default 7 days
    PROVIDER_CACHE_MAX = '1000',
    // SMTP verify
    SMTP_VERIFY = 'false',         // "true" to enable SMTP email verification
    SMTP_HELO_DOMAIN = 'acurly.com',
    SMTP_TIMEOUT_MS = '8000',
    // Debugging / Security
    DISABLE_SIGNATURE_VERIFY,      // "true" only while wiring
    DEBUG_SIGNATURE,               // "true" to log base string
    DEBUG_SMTP                     // "true" to see SMTP commands
} = process.env;

if (!HUBSPOT_TOKEN) console.warn('⚠️  HUBSPOT_TOKEN not set');
if (!HUBSPOT_APP_SECRET && DISABLE_SIGNATURE_VERIFY !== 'true') {
    console.warn('⚠️  HUBSPOT_APP_SECRET not set; set DISABLE_SIGNATURE_VERIFY="true" only temporarily while wiring');
}

const WRITEBACK_THRESHOLD = parseFloat(WRITEBACK_MIN_CONFIDENCE);
const CONTACT_COOLDOWN_MS = parseInt(COOLDOWN_MS, 10) || (10 * 60 * 1000);
const CACHE_TTL = parseInt(PROVIDER_CACHE_TTL_MS, 10) || (7 * 24 * 60 * 60 * 1000);
const CACHE_MAX = parseInt(PROVIDER_CACHE_MAX, 10) || 1000;
const SMTP_TIMEOUT = parseInt(SMTP_TIMEOUT_MS, 10) || 8000;

// ========== APP ==========
const app = express();
app.set('trust proxy', true); // make signature URL match tunnel host/proto
app.use(express.json({
    limit: '1mb',
    verify: (req, _res, buf) => { req.rawBody = buf ? buf.toString('utf8') : ''; }
}));

// ========== HS CLIENT ==========
const hs = axios.create({
    baseURL: 'https://api.hubapi.com',
    headers: { Authorization: `Bearer ${HUBSPOT_TOKEN}` },
    timeout: 7000
});

// ========== UTILS ==========
const clamp = (n, min, max) => Math.max(min, Math.min(max, n));

// score (providers + recency proxy)
function scoreField(sources = []) {
    const weight = { pdl: 0.35, apollo: 0.30 };
    const uniqProviders = Array.from(new Set(sources.map(s => s.provider)));
    let s = clamp(uniqProviders.length * 0.15, 0, 0.45);
    const recencyDays = Math.min(...sources.map(x => x.recency_days ?? 365));
    s += clamp(1 - (recencyDays / 365), 0, 1) * 0.20;
    s += Math.max(...sources.map(x => weight[x.provider] || 0), 0);
    return clamp(s, 0, 1);
}

function mergeCandidates(cands = []) {
    const byKey = {};
    for (const c of cands) {
        if (!c || !c.key || !c.value) continue;
        (byKey[c.key] ||= []).push(c);
    }
    const fields = [];
    for (const [key, arr] of Object.entries(byKey)) {
        // prefer PDL over Apollo when tied (simpler & safer comparator)
        arr.sort((a, b) => {
            const order = { pdl: 2, apollo: 1 };
            const rb = order[b.provider] || 0;
            const ra = order[a.provider] || 0;
            return rb - ra;
        });

        const best = arr[0];
        const sources = arr.map(a => ({ provider: a.provider, recency_days: a.recency_days ?? 365, value: a.value }));
        fields.push({ key, value: best.value, confidence: scoreField(sources), sources });
    }
    return fields;
}

function toHubSpotProps(fields, extras = {}) {
    const props = {};
    for (const f of fields) {
        if (f.confidence < WRITEBACK_THRESHOLD) continue;
        if (f.key === 'work_email') props['acurly_work_email'] = f.value;
        if (f.key === 'direct_phone') props['acurly_direct_phone'] = f.value;
        if (f.key === 'job_title') props['acurly_job_title'] = f.value;
        if (f.key === 'first_name') props['acurly_first_name'] = f.value;
        if (f.key === 'last_name') props['acurly_last_name'] = f.value;

    }
    const avg = fields.length ? fields.reduce((a, b) => a + b.confidence, 0) / fields.length : 0;
    props['acurly_confidence_overall'] = Math.round(avg * 100) / 100;
    props['acurly_enriched_at'] = new Date().toISOString();
    props['acurly_sources_json'] = JSON.stringify(fields.flatMap(f => f.sources));
    Object.assign(props, extras);
    return props;
}

// ========== SIMPLE METRICS ==========
const metrics = {
    pdl_fetch: 0,
    pdl_cache_hit: 0,
    apollo_fetch: 0,
    apollo_cache_hit: 0,
    cooldown_skips: 0,
    webhook_processed: 0,
    webhook_skipped: 0
};

// ========== CACHE & COOLDOWN ==========
const providerCache = new Map();   // key -> { data, expiresAt }
const contactCooldown = new Map(); // contactId -> { lastAt, lastKey }

function cacheGet(key) {
    const e = providerCache.get(key);
    if (!e) return null;
    if (Date.now() > e.expiresAt) { providerCache.delete(key); return null; }
    return e.data;
}
function cacheSet(key, data, ttl = CACHE_TTL) {
    if (providerCache.size >= CACHE_MAX) {
        const firstKey = providerCache.keys().next().value;
        providerCache.delete(firstKey);
    }
    providerCache.set(key, { data, expiresAt: Date.now() + ttl });
}

// ========== HUBSPOT HELPERS ==========
async function hsGetContact(contactId) {
    const props = ['email', 'firstname', 'lastname', 'company', 'website'].join(',');
    const r = await hs.get(`/crm/v3/objects/contacts/${contactId}`, { params: { properties: props } });
    return r.data?.properties || {};
}

// Fail-soft writeback: drop unknown props, skip 404, retry once.
async function hsUpdateContact(contactId, props) {
    if (!Object.keys(props).length) return;
    console.log('[writeback] contact', contactId, 'props:', JSON.stringify(props));
    try {
        await hs.patch(`/crm/v3/objects/contacts/${contactId}`, { properties: props });
    } catch (e) {
        const st = e?.response?.status;
        const url = e?.response?.config?.url || e?.config?.url;
        const data = e?.response?.data;
        console.warn('[hs] error', st, url, typeof data === 'string' ? data.slice(0, 200) + '...' : data);

        const errors = data?.errors || [];
        const missing = new Set();
        for (const err of errors) {
            if (err.code === 'PROPERTY_DOESNT_EXIST' && err.context?.name) missing.add(err.context.name);
        }
        if (missing.size) {
            for (const key of missing) delete props[key];
            console.warn('[writeback] retrying without unknown props:', Array.from(missing).join(', '));
            await hs.patch(`/crm/v3/objects/contacts/${contactId}`, { properties: props });
            return;
        }
        if (st === 404) { console.warn('[writeback] contact not found, skipping'); return; }
        throw e;
    }
}

// ========== PROVIDERS (with Patch B cache) ==========

// PDL person enrichment
async function enrichWithPDL({ email, firstName, lastName, company, domain }) {
    if (ENABLE_PDL !== 'true' || !PROVIDER_PDL_API_KEY) return null;

    const key = `pdl:${(email || '').toLowerCase()}|${(firstName || '').toLowerCase()}|${(lastName || '').toLowerCase()}|${(company || '').toLowerCase()}|${(domain || '').toLowerCase()}`;
    const hit = cacheGet(key);
    if (hit !== null) { metrics.pdl_cache_hit++; console.log('[pdl] cache_hit', key); return hit; }

    const url = 'https://api.peopledatalabs.com/v5/person/enrich';
    const params = { api_key: PROVIDER_PDL_API_KEY };
    if (email) params.email = email;
    if (firstName) params.first_name = firstName;
    if (lastName) params.last_name = lastName;
    if (company) params.company = company;
    if (domain) params.company_website = domain;

    metrics.pdl_fetch++; console.log('[pdl] fetch', key);
    try {
        const { data } = await axios.get(url, { params, timeout: 4500 });
        if (!data || data.status !== 200 || !data.data) { cacheSet(key, null, 60 * 60 * 1000); return null; }

        const out = [];
        if (data.data.email) out.push({ key: 'work_email', value: data.data.email, provider: 'pdl', recency_days: 30 });
        if (data.data.job_title) out.push({ key: 'job_title', value: data.data.job_title, provider: 'pdl', recency_days: 30 });
        if (data.data.first_name) out.push({ key: 'first_name', value: data.data.first_name, provider: 'pdl', recency_days: 30 });
        if (data.data.last_name) out.push({ key: 'last_name', value: data.data.last_name, provider: 'pdl', recency_days: 30 });
        const phones = data.data.phone_numbers || [];
        if (phones.length) out.push({ key: 'direct_phone', value: phones[0], provider: 'pdl', recency_days: 30 });

        cacheSet(key, out);
        return out;
    } catch (e) {
        const status = e?.response?.status;
        if (status === 429) cacheSet(key, null, 15 * 60 * 1000); // 15m backoff
        else cacheSet(key, null, 5 * 60 * 1000); // 5m backoff
        console.log('PDL err', e?.response?.data || e.message);
        return null;
    }
}

// Apollo people match (optional; cache-wrapped)
async function enrichWithApollo({ email }) {
    if (ENABLE_APOLLO !== 'true' || !PROVIDER_APOLLO_API_KEY || !email) return null;

    const key = `apollo:${email.toLowerCase()}`;
    const hit = cacheGet(key);
    if (hit !== null) { metrics.apollo_cache_hit++; console.log('[apollo] cache_hit', key); return hit; }

    const url = 'https://api.apollo.io/api/v1/people/match';
    const body = { email, reveal_phone_number: true };

    metrics.apollo_fetch++; console.log('[apollo] fetch', key);
    try {
        const { data } = await axios.post(url, body, {
            headers: { 'X-Api-Key': PROVIDER_APOLLO_API_KEY, 'Content-Type': 'application/json' },
            timeout: 4500
        });
        const person = data?.person || data;
        if (!person) { cacheSet(key, null); return null; }

        const out = [];
        if (person.title) out.push({ key: 'job_title', value: person.title, provider: 'apollo', recency_days: 60 });

        const emails = (person.emails || []).map(e => e.value || e).filter(Boolean);
        const work = emails.find(e => !/@gmail\.|@yahoo\.|@outlook\./i.test(e));
        if (work) out.push({ key: 'work_email', value: work, provider: 'apollo', recency_days: 60 });

        const phones = (person.phone_numbers || person.phones || []).map(p => p.number || p).filter(Boolean);
        if (phones.length) out.push({ key: 'direct_phone', value: phones[0], provider: 'apollo', recency_days: 60 });

        cacheSet(key, out);
        return out;
    } catch (e) {
        cacheSet(key, null, 60 * 60 * 1000); // 1h negative cache to avoid log spam on free tier
        console.log('Apollo err', e?.response?.data || e.message);
        return null;
    }
}

// ========== SMTP VERIFY ==========
async function smtpVerifyEmail(email) {
    if (SMTP_VERIFY !== 'true') return { status: 'unknown', reason: 'disabled' };
    const m = /^[^@]+@([^@]+\.[^@]+)$/.exec(email || '');
    if (!m) return { status: 'undeliverable', reason: 'invalid_format' };
    const domain = m[1].toLowerCase();

    let mx;
    try {
        const records = await dns.resolveMx(domain);
        if (!records?.length) return { status: 'unknown', reason: 'no_mx' };
        mx = records.sort((a, b) => a.priority - b.priority).slice(0, 3);
    } catch {
        return { status: 'unknown', reason: 'mx_lookup_failed' };
    }

    for (const rec of mx) {
        const host = rec.exchange;
        try {
            const result = await attemptSmtp(host, email);
            if (result.status !== 'unknown') return result;
        } catch { /* try next MX */ }
    }
    return { status: 'unknown', reason: 'all_mx_failed_or_indeterminate' };
}

function readLine(socket) {
    return new Promise((resolve, reject) => {
        let buf = '';
        const onData = (chunk) => {
            buf += chunk.toString('utf8');
            const lines = buf.split('\r\n');
            if (lines.length > 1) {
                const last = lines[lines.length - 2];
                if (/^\d{3}[\s-]/.test(last)) {
                    socket.off('data', onData);
                    resolve(buf);
                }
            }
        };
        const onErr = (e) => { socket.off('data', onData); reject(e); };
        socket.once('error', onErr);
        socket.on('data', onData);
    });
}

function writeLine(socket, line) {
    if (DEBUG_SMTP === 'true') console.log('> ', line);
    socket.write(line + '\r\n');
}

async function upgradeStartTLS(socket, host) {
    writeLine(socket, 'STARTTLS');
    const resp = await readLine(socket);
    if (!/^220/.test(resp)) return socket; // no TLS
    return new Promise((resolve, reject) => {
        const secure = tls.connect({ socket, servername: host }, () => resolve(secure));
        secure.setTimeout(SMTP_TIMEOUT, () => { secure.destroy(new Error('tls_timeout')); });
        secure.once('error', reject);
    });
}
async function attemptSmtp(host, email) {
    const helo = SMTP_HELO_DOMAIN || 'acurly.com';
    const from = `verify@${helo}`;
    return new Promise((resolve) => {
        const socket = net.createConnection(25, host);
        let finished = false;
        const done = (res) => { if (!finished) { finished = true; try { socket.destroy(); } catch { } resolve(res); } };
        socket.setTimeout(SMTP_TIMEOUT, () => done({ status: 'unknown', reason: 'timeout' }));
        socket.once('error', () => done({ status: 'unknown', reason: 'connect_error' }));

        (async () => {
            try {
                let resp = await readLine(socket);
                if (!/^220/.test(resp)) return done({ status: 'unknown', reason: 'no_banner' });

                writeLine(socket, `EHLO ${helo}`);
                resp = await readLine(socket);

                if (/^530[ -]/m.test(resp) || /STARTTLS/m.test(resp)) {
                    try {
                        const sec = await upgradeStartTLS(socket, host);
                        writeLine(sec, `EHLO ${helo}`);
                        resp = await readLine(sec);
                        socket.write = sec.write.bind(sec);
                        socket.once = sec.once.bind(sec);
                        socket.on = sec.on.bind(sec);
                    } catch { return done({ status: 'unknown', reason: 'starttls_failed' }); }
                }

                writeLine(socket, `MAIL FROM:<${from}>`);
                resp = await readLine(socket);
                if (!/^250/.test(resp)) return done({ status: 'unknown', reason: 'mail_from_rejected' });

                writeLine(socket, `RCPT TO:<${email}>`);
                resp = await readLine(socket);
                if (/^250|^251/.test(resp)) return done({ status: 'deliverable', reason: 'accepted' });
                if (/^252/.test(resp)) return done({ status: 'unknown', reason: 'accepts_all_or_cannot_verify' });
                if (/^421|^450|^451|^452/.test(resp)) return done({ status: 'unknown', reason: 'temp_fail_or_greylist' });
                if (/^550|^551|^552|^553|^554/.test(resp)) return done({ status: 'undeliverable', reason: 'rejected' });
                return done({ status: 'unknown', reason: 'other' });
            } catch {
                return done({ status: 'unknown', reason: 'exception' });
            }
        })();
    });
}

// Email verify cache
const emailCache = new Map();
async function verifyEmailWithCache(email) {
    const key = `smtp:${(email || '').toLowerCase()}`;
    if (emailCache.has(key)) return emailCache.get(key);
    const res = await smtpVerifyEmail(email);
    emailCache.set(key, res);
    return res;
}

// ========== SIGNATURE VERIFY (v3) ==========
function verifyHubSpotSignature(req) {
    if (DISABLE_SIGNATURE_VERIFY === 'true') return true;
    const sig = req.headers['x-hubspot-signature-v3'];
    const ts = req.headers['x-hubspot-request-timestamp'];
    if (!sig || !ts || !HUBSPOT_APP_SECRET) return false;
    if (Math.abs(Date.now() - Number(ts)) > 5 * 60 * 1000) return false;

    const method = req.method.toUpperCase();
    const url = `${req.protocol}://${req.get('host')}${req.originalUrl}`;
    const base = `${method}${url}${req.rawBody || ''}${ts}`;
    const hmac = crypto.createHmac('sha256', HUBSPOT_APP_SECRET).update(base).digest('base64');
    if (DEBUG_SIGNATURE === 'true') { console.log('sig-debug', { url, ts, computed: hmac, received: sig }); }
    try { return crypto.timingSafeEqual(Buffer.from(hmac), Buffer.from(sig)); }
    catch { return false; }
}

// ========== ROUTES ==========
app.get('/health', (_, res) => res.send('ok'));

app.get('/admin/stats', (_req, res) => {
    res.json({
        metrics,
        providerCacheSize: providerCache.size,
        emailCacheSize: emailCache.size,
        cooldownSize: contactCooldown.size,
        config: {
            ENABLE_PDL, ENABLE_APOLLO,
            WRITEBACK_MIN_CONFIDENCE, COOLDOWN_MS, CACHE_TTL
        }
    });
});

// quick local test (no HubSpot)
app.get('/test/verify-email', async (req, res) => {
    try {
        const email = String(req.query.email || '');
        const r = await verifyEmailWithCache(email);
        res.json({ email, ...r });
    } catch (e) { res.status(500).json({ error: e.message }); }
});

app.post('/test/enrich', async (req, res) => {
    try {
        const input = req.body || {};
        const cands = [];
        try { const a = await enrichWithPDL(input); if (a) cands.push(...a); } catch { }
        try { const b = await enrichWithApollo(input); if (b) cands.push(...b); } catch { }

        let emailStatus = 'unknown';
        const work = cands.find(x => x.key === 'work_email');
        if (work && SMTP_VERIFY === 'true') {
            const r = await verifyEmailWithCache(work.value);
            emailStatus = r.status;
            if (r.status === 'undeliverable') {
                for (let i = cands.length - 1; i >= 0; i--) if (cands[i].key === 'work_email') cands.splice(i, 1);
            }
        }
        const merged = mergeCandidates(cands);
        return res.json({ fields: merged, props: toHubSpotProps(merged, { acurly_email_status: emailStatus }) });
    } catch (e) { res.status(500).json({ error: e.message }); }
});

// main webhook (create + propertyChange; dedup; cooldown; cache-wrapped providers)
app.post('/webhooks/hubspot', async (req, res) => {
    try {
        if (!verifyHubSpotSignature(req)) return res.status(401).send('invalid signature');

        const events = Array.isArray(req.body) ? req.body : [req.body];
        const allowedProps = new Set(['email', 'firstname', 'lastname', 'company', 'website']);

        // keep only create + propertyChange of allowed props
        const valid = events.filter(evt => {
            const isCreate = evt.subscriptionType === 'contact.creation';
            const isPropChange = evt.subscriptionType === 'contact.propertyChange'
                ? allowedProps.has(evt.propertyName || '') // some HS payloads include propertyName
                : false;
            return isCreate || isPropChange;
        });

        // dedup by contact id for this delivery
        const uniqueIds = Array.from(new Set(valid.map(e => String(e.objectId))));
        for (const contactId of uniqueIds) {
            metrics.webhook_processed++;
            console.log('[webhook] process contact id=', contactId);

            // pull latest
            const p = await hsGetContact(contactId);
            const input = {
                email: p.email,
                firstName: p.firstname,
                lastName: p.lastname,
                company: p.company,
                domain: (p.website || '').replace(/^https?:\/\//, '')
            };
            const inputKey = `${(input.email || '').toLowerCase()}|${(input.firstName || '').toLowerCase()}|${(input.lastName || '').toLowerCase()}|${(input.company || '').toLowerCase()}|${(input.domain || '').toLowerCase()}`;

            // cooldown skip
            const prev = contactCooldown.get(contactId);
            if (prev && prev.lastKey === inputKey && (Date.now() - prev.lastAt) < CONTACT_COOLDOWN_MS) {
                metrics.webhook_skipped++; console.log('[skip] cooldown same-input (contact', contactId + ')');
                continue;
            }
            contactCooldown.set(contactId, { lastAt: Date.now(), lastKey: inputKey });

            // Enrich via cache-wrapped providers
            const cands = [];
            try { const a = await enrichWithPDL(input); if (a) cands.push(...a); } catch (e) { console.log('PDL err', e?.response?.data || e.message); }

            const need = (k) => !cands.find(x => x.key === k);
            if (need('work_email') || need('direct_phone') || need('job_title')) {
                try { const b = await enrichWithApollo({ email: input.email }); if (b) cands.push(...b); } catch (e) { console.log('Apollo err', e?.response?.data || e.message); }
            }

            // SMTP gate
            let emailStatus = 'unknown';
            const work = cands.find(x => x.key === 'work_email');
            if (work && SMTP_VERIFY === 'true') {
                const r = await verifyEmailWithCache(work.value);
                emailStatus = r.status;
                console.log('[smtp]', work.value, '->', r.status, r.reason || '');
                if (r.status === 'undeliverable') {
                    for (let i = cands.length - 1; i >= 0; i--) if (cands[i].key === 'work_email') cands.splice(i, 1);
                }
            }

            const merged = mergeCandidates(cands);
            console.log('[enrich] merged fields:', merged.map(f => `${f.key}=${f.value}`).join(', ') || '(none)');
            const props = toHubSpotProps(merged, { acurly_email_status: emailStatus });
            // Optionally copy high-confidence names into core fields if currently blank
            if (process.env.FILL_CORE_NAME_FIELDS === 'true') {
                const nameThresh = parseFloat(process.env.NAME_FILL_THRESHOLD || '0.80');
                const first = merged.find(x => x.key === 'first_name' && x.confidence >= nameThresh);
                const last = merged.find(x => x.key === 'last_name' && x.confidence >= nameThresh);

                // Fetch current names once (we already have p = hsGetContact(contactId) above)
                const coreFirstEmpty = !p.firstname || !p.firstname.trim();
                const coreLastEmpty = !p.lastname || !p.lastname.trim();

                if (coreFirstEmpty && first) props['firstname'] = first.value;
                if (coreLastEmpty && last) props['lastname'] = last.value;
            }

            await hsUpdateContact(contactId, props);
        }

        return res.status(200).send('ok');
    } catch (err) {
        console.error('Webhook error:', err?.response?.data || err.message);
        return res.status(500).send('error');
    }
});

// ---------- ADMIN: bootstrap all Acurly properties ----------
app.post('/admin/bootstrap', async (_req, res) => {
  try {
    // ensure group
    const groupName = 'acurly_enrichment';
    const group = { name: groupName, label: 'Acurly Enrichment', displayOrder: -1 };
    try { await hs.post('/crm/v3/properties/contacts/groups', group); } catch {}

    const defs = [
      { name:'acurly_work_email',         label:'Acurly Work Email',         type:'string', fieldType:'text' },
      { name:'acurly_direct_phone',       label:'Acurly Direct Phone',       type:'string', fieldType:'text' },
      { name:'acurly_job_title',          label:'Acurly Job Title',          type:'string', fieldType:'text' },
      { name:'acurly_confidence_overall', label:'Acurly Confidence Overall', type:'number', fieldType:'number' },
      { name:'acurly_enriched_at',        label:'Acurly Enriched At',        type:'datetime', fieldType:'date' },
      { name:'acurly_sources_json',       label:'Acurly Sources JSON',       type:'string', fieldType:'text' },
      { name:'acurly_email_status',       label:'Acurly Email Status',       type:'string', fieldType:'text' },
        // nice add-ons so "something" always shows
      { name: 'acurly_first_name', label: 'Acurly First Name', type: 'string', fieldType: 'text' },
      { name: 'acurly_last_name', label: 'Acurly Last Name', type: 'string', fieldType: 'text' },
      { name:'acurly_company_industry',   label:'Acurly Company Industry',   type:'string', fieldType:'text' },
      { name:'acurly_company_size',       label:'Acurly Company Size',       type:'number', fieldType:'number' }

    ];

    const exists = new Set();
    try {
      const r = await hs.get('/crm/v3/properties/contacts');
      for (const p of (r.data?.results||[])) exists.add(p.name);
    } catch {}

    const created = [];
    for (const d of defs) {
      if (exists.has(d.name)) continue;
      await hs.post('/crm/v3/properties/contacts', { groupName, ...d });
      created.push(d.name);
    }
    res.json({ ok: true, created });
  } catch (e) {
    res.status(500).json({ ok: false, error: e?.response?.data || e.message });
  }
});

// ---------- ADMIN AUTH + ROUTES (paste above // ========== START ==========) ----------
function adminAuth(req, res, next) {
    const hdr = req.headers.authorization || '';
    if (!hdr.startsWith('Basic ')) {
        return res.set('WWW-Authenticate', 'Basic realm="Acurly Admin"').status(401).send('auth required');
    }
    const [u, p] = Buffer.from(hdr.slice(6), 'base64').toString('utf8').split(':');
    if (u === process.env.ADMIN_USER && p === process.env.ADMIN_PASS) return next();
    return res.status(403).send('forbidden');
}

// Simple admin landing (read-only)
app.get('/admin', adminAuth, (req, res) => {
    res.set('Content-Type', 'text/html');
    const cfg = {
        ENABLE_PDL: process.env.ENABLE_PDL,
        ENABLE_APOLLO: process.env.ENABLE_APOLLO,
        WRITEBACK_MIN_CONFIDENCE: process.env.WRITEBACK_MIN_CONFIDENCE,
        COOLDOWN_MS: process.env.COOLDOWN_MS,
        PROVIDER_CACHE_TTL_MS: process.env.PROVIDER_CACHE_TTL_MS,
        SMTP_VERIFY: process.env.SMTP_VERIFY,
        SMTP_HELO_DOMAIN: process.env.SMTP_HELO_DOMAIN
    };
    res.end(`<!doctype html>
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <style>body{font-family:system-ui,Arial;margin:24px;max-width:880px}code{background:#f5f5f5;padding:2px 6px;border-radius:4px}
  .kv{display:grid;grid-template-columns:260px 1fr;gap:8px 16px;margin:12px 0}.card{border:1px solid #eee;padding:16px;border-radius:12px;margin:16px 0}</style>
  <h1>Acurly Admin</h1>
  <div class="card">
    <h2>Guardrails</h2>
    <div class="kv">
      <div>Confidence threshold</div><div><code>${cfg.WRITEBACK_MIN_CONFIDENCE || ''}</code></div>
      <div>Cooldown (ms)</div><div><code>${cfg.COOLDOWN_MS || ''}</code></div>
      <div>Provider cache TTL (ms)</div><div><code>${cfg.PROVIDER_CACHE_TTL_MS || ''}</code></div>
      <div>SMTP verify</div><div><code>${cfg.SMTP_VERIFY || ''}</code> (HELO: <code>${cfg.SMTP_HELO_DOMAIN || ''}</code>)</div>
      <div>PDL enabled</div><div><code>${cfg.ENABLE_PDL || ''}</code></div>
      <div>Apollo enabled</div><div><code>${cfg.ENABLE_APOLLO || ''}</code></div>
    </div>
    <p>Update these in Render → Environment and redeploy.</p>
  </div>
  <div class="card">
    <h2>Endpoints</h2>
    <p><code>GET /admin</code> (this page)</p>
    <p><code>POST /admin/preview/:id</code> (dry-run; no writeback)</p>
    <p><a href="/admin/stats">/admin/stats</a> (JSON metrics; not auth-protected in some builds)</p>
  </div>`);
});

// PREVIEW: show what we WOULD write (no writeback)
app.post('/admin/preview/:id', adminAuth, async (req, res) => {
    try {
        const contactId = String(req.params.id);
        const p = await hsGetContact(contactId);
        const input = {
            email: p.email,
            firstName: p.firstname,
            lastName: p.lastname,
            company: p.company,
            domain: (p.website || '').replace(/^https?:\/\//, '')
        };

        const cands = [];
        try { const a = await enrichWithPDL(input); if (a) cands.push(...a); } catch { }
        const need = (k) => !cands.find(x => x.key === k);
        if (need('work_email') || need('direct_phone') || need('job_title')) {
            try { const b = await enrichWithApollo({ email: input.email }); if (b) cands.push(...b); } catch { }
        }

        let emailStatus = 'unknown';
        const work = cands.find(x => x.key === 'work_email');
        if (work && process.env.SMTP_VERIFY === 'true') {
            const r = await verifyEmailWithCache(work.value);
            emailStatus = r.status;
            if (r.status === 'undeliverable') {
                for (let i = cands.length - 1; i >= 0; i--) if (cands[i].key === 'work_email') cands.splice(i, 1);
            }
        }

        const merged = mergeCandidates(cands);
        const props = toHubSpotProps(merged, { acurly_email_status: emailStatus });
        res.json({ input, merged, would_write: props });
    } catch (e) {
        res.status(500).json({ ok: false, error: e?.response?.data || e.message });
    }
});


// ========== START ==========
const PORT = process.env.PORT || 3000;
app.listen(PORT, () => console.log(`Acurly listening on :${PORT}`));
