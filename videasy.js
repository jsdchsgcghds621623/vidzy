// ═══════════════════════════════════════════════════════════════
//  vidzee.wtf stream proxy — production grade
//  Playwright + pure network interception (NO clicking)
//  Aiven PostgreSQL persistence — DB first, Playwright fallback
//  Hard 15s cap per capture
//  TV    → https://player.vidzee.wtf/embed/tv/{tmdb}/{s}/{e}
//  MOVIE → https://player.vidzee.wtf/embed/movie/{tmdb}
//  Uses chromium-headless-shell — truly windowless binary, no flash
// ═══════════════════════════════════════════════════════════════
require('dotenv').config();

const express       = require('express');
const cors          = require('cors');
const compression   = require('compression');
const helmet        = require('helmet');
const rateLimit     = require('express-rate-limit');
const { chromium }  = require('playwright');
const { Pool }      = require('pg');
const crypto        = require('crypto');

const app  = express();
const PORT = Number(process.env.PORT) || 3000;

// ─── Tunables ─────────────────────────────────────────────
const HEADLESS             = process.env.HEADLESS !== 'false';
const CAPTURE_TIMEOUT      = Number(process.env.CAPTURE_TIMEOUT)   || 15_000;
const CONTEXT_MAX_AGE      = Number(process.env.CONTEXT_MAX_AGE)   || 15 * 60_000;
const CAPTURE_CONCURRENCY  = Number(process.env.CAPTURE_CONCURRENCY) || 6;
const QUEUE_TIMEOUT        = Number(process.env.QUEUE_TIMEOUT)     || 30_000;
const MEM_CACHE_MAX        = Number(process.env.MEM_CACHE_MAX)     || 2000;
const CACHE_TTL            = Number(process.env.CACHE_TTL)         || 30 * 60_000;
const NEGATIVE_CACHE_TTL   = Number(process.env.NEGATIVE_CACHE_TTL)|| 60_000;
const DB_POOL_MAX          = Number(process.env.DB_POOL_MAX)       || 10;
const RATE_LIMIT_MAX       = Number(process.env.RATE_LIMIT_MAX)    || 120;
const LOG_LEVEL            = (process.env.LOG_LEVEL  || 'info').toLowerCase();
const LOG_JSON             = process.env.LOG_JSON === 'true';
const LOG_COLOR            = process.env.LOG_COLOR !== 'false' && process.stdout.isTTY;

// ─── CORS allow-list ──────────────────────────────────────
// Comma-separated. Hostnames are matched exactly (scheme ignored).
const ALLOWED_ORIGINS = (
  process.env.ALLOWED_ORIGINS ||
  [
    'https://moonflix.website',
    'https://www.moonflix.website',
    'https://player.moonflix.website',
    // add dev origins here if needed:
    // 'http://localhost:3000',
    // 'http://localhost:5173',
  ].join(',')
)
  .split(',')
  .map(s => s.trim().toLowerCase())
  .filter(Boolean);

const ALLOWED_HOSTS = new Set(
  ALLOWED_ORIGINS.map(o => {
    try { return new URL(o).hostname.toLowerCase(); }
    catch { return o.replace(/^https?:\/\//, '').split('/')[0].toLowerCase(); }
  })
);

function hostOf(value) {
  if (!value || value === 'null') return null;
  try { return new URL(value).hostname.toLowerCase(); }
  catch { return null; }
}

function isAllowedOrigin(origin) {
  const h = hostOf(origin);
  return !!h && ALLOWED_HOSTS.has(h);
}

function isAllowedReferer(referer) {
  const h = hostOf(referer);
  return !!h && ALLOWED_HOSTS.has(h);
}

// ─── VidZee API matcher ───────────────────────────────────
// Capture any response whose URL contains one of these fragments.
// Tune via env: VIDZEE_API_MATCH="/api/sources,/api/stream"
const VIDZEE_API_MATCH = (process.env.VIDZEE_API_MATCH || '/api/sources')
  .split(',')
  .map(s => s.trim())
  .filter(Boolean);

// ═══════════════════════════════════════════════════════════════
//  BEAUTIFUL TERMINAL LOGGER
// ═══════════════════════════════════════════════════════════════
const C = LOG_COLOR ? {
  reset: '\x1b[0m', bold: '\x1b[1m', dim: '\x1b[2m', italic: '\x1b[3m',
  red: '\x1b[31m', green: '\x1b[32m', yellow: '\x1b[33m', blue: '\x1b[34m',
  magenta: '\x1b[35m', cyan: '\x1b[36m', white: '\x1b[37m', gray: '\x1b[90m',
  bgRed: '\x1b[41m', bgGreen: '\x1b[42m', bgYellow: '\x1b[43m',
  bgBlue: '\x1b[44m', bgMagenta: '\x1b[45m', bgCyan: '\x1b[46m',
} : new Proxy({}, { get: () => '' });

const LEVELS = { debug: 10, info: 20, warn: 30, error: 40 };
const LEVEL_MIN = LEVELS[LOG_LEVEL] || 20;

const LEVEL_META = {
  debug: { icon: '🔍', color: C.gray,    label: 'DEBUG' },
  info:  { icon: 'ℹ️ ', color: C.cyan,    label: 'INFO ' },
  ok:    { icon: '✅', color: C.green,   label: 'OK   ' },
  warn:  { icon: '⚠️ ', color: C.yellow,  label: 'WARN ' },
  error: { icon: '❌', color: C.red,     label: 'ERROR' },
};

const TAG_STYLE = {
  db:        { icon: '💾', color: C.magenta },
  browser:   { icon: '🌐', color: C.blue },
  context:   { icon: '🧩', color: C.blue },
  cache:     { icon: '⚡', color: C.yellow },
  capture:   { icon: '🎯', color: C.cyan },
  server:    { icon: '🚀', color: C.green },
  http:      { icon: '🌐', color: C.white },
  proxy:     { icon: '🎬', color: C.magenta },
  queue:     { icon: '⏳', color: C.yellow },
  shutdown:  { icon: '🛑', color: C.red },
  ready:     { icon: '✨', color: C.green },
};

function ts() {
  const d = new Date();
  const p = n => String(n).padStart(2, '0');
  return `${p(d.getHours())}:${p(d.getMinutes())}:${p(d.getSeconds())}`;
}

function fmtVal(v) {
  if (v === null || v === undefined) return '';
  if (typeof v === 'object') return JSON.stringify(v);
  return String(v);
}

function log(level, tag, msg, extra) {
  if (LOG_JSON) {
    const line = JSON.stringify({
      t: new Date().toISOString(), level,
      tag: tag || 'app', msg, ...(extra || {}),
    });
    (level === 'error' || level === 'warn' ? process.stderr : process.stdout).write(line + '\n');
    return;
  }

  const lvl = LEVELS[level] ?? 20;
  if (lvl < LEVEL_MIN) return;

  const meta = LEVEL_META[level] || LEVEL_META.info;
  const tstyle = TAG_STYLE[tag] || { icon: '·', color: C.gray };

  let extras = '';
  if (extra && typeof extra === 'object') {
    const parts = [];
    for (const [k, v] of Object.entries(extra)) {
      const val = fmtVal(v);
      if (val === '') continue;
      parts.push(`${C.gray}${k}${C.reset}${C.dim}=${C.reset}${C.white}${val}${C.reset}`);
    }
    if (parts.length) extras = '  ' + parts.join(' ');
  }

  const line =
    `${C.gray}${ts()}${C.reset}  ` +
    `${meta.color}${meta.icon}${C.reset}  ` +
    `${tstyle.color}${String(tag || 'app').padEnd(8)}${C.reset}` +
    `${C.white}${msg}${C.reset}` +
    extras;

  (level === 'error' || level === 'warn' ? process.stderr : process.stdout).write(line + '\n');
}

function banner() {
  if (LOG_JSON) return;
  const lines = [
    '',
    `${C.cyan}  ╭─────────────────────────────────────────────────────────────╮${C.reset}`,
    `${C.cyan}  │${C.reset}  ${C.bold}🎬  vidzee.wtf stream proxy${C.reset}                              ${C.cyan}│${C.reset}`,
    `${C.cyan}  │${C.reset}  ${C.gray}v2.2 · production grade · playwright + postgres${C.reset}             ${C.cyan}│${C.reset}`,
    `${C.cyan}  │${C.reset}  ${C.gray}headless-shell · windowless · DB-first · no-click${C.reset}        ${C.cyan}│${C.reset}`,
    `${C.cyan}  ╰─────────────────────────────────────────────────────────────╯${C.reset}`,
    '',
  ];
  process.stdout.write(lines.join('\n') + '\n');
}

function divider(label) {
  if (LOG_JSON) return;
  const w = 62;
  const mid = ` ${label} `;
  const left = Math.floor((w - mid.length) / 2);
  const right = w - mid.length - left;
  process.stdout.write(
    `\n${C.gray}  ${'─'.repeat(left)}${C.reset}${C.bold}${mid}${C.reset}${C.gray}${'─'.repeat(right)}${C.reset}\n`
  );
}

// ═══════════════════════════════════════════════════════════════
//  EXPRESS
// ═══════════════════════════════════════════════════════════════
app.disable('x-powered-by');
app.use(helmet({ contentSecurityPolicy: false, crossOriginEmbedderPolicy: false }));
app.use(compression());

// ─── CORS (strict allow-list) ─────────────────────────────
// NOTE: app.use(cors(...)) already answers all OPTIONS preflights.
// We intentionally do NOT call app.options('*', ...) — that syntax
// breaks on Express 5 (path-to-regexp v8) and is redundant anyway.
const corsOptions = {
  origin(origin, cb) {
    if (!origin) return cb(null, false);           // no Origin → emit no CORS headers
    if (isAllowedOrigin(origin)) return cb(null, true);
    log('warn', 'http', 'cors origin rejected', { origin });
    return cb(null, false);
  },
  credentials: true,
  methods: ['GET', 'HEAD', 'OPTIONS'],
  allowedHeaders: ['Content-Type', 'Accept', 'Origin', 'X-Requested-With'],
  exposedHeaders: ['x-cache-source', 'Retry-After'],
  maxAge: 86_400,
  optionsSuccessStatus: 204,
};

app.use(cors(corsOptions));

app.use(express.json({ limit: '64kb' }));

// Pretty request logger
app.use((req, res, next) => {
  req.id = crypto.randomBytes(4).toString('hex');
  req._t0 = process.hrtime.bigint();

  const q = { ...req.query };
  delete q.type;

  const queryStr = Object.entries(q)
    .map(([k, v]) => `${C.gray}${k}${C.reset}${C.dim}=${C.reset}${C.white}${v}${C.reset}`)
    .join('  ');

  log('info', 'http', `${C.cyan}→${C.reset}  ${C.bold}${req.method}${C.reset}  ${req.path}${queryStr ? '  ' + queryStr : ''}`, { id: req.id });

  res.on('finish', () => {
    const ms = Number(process.hrtime.bigint() - req._t0) / 1e6;
    const statusColor =
      res.statusCode >= 500 ? C.red :
      res.statusCode >= 400 ? C.yellow :
      res.statusCode >= 300 ? C.cyan :
      C.green;
    const msColor = ms < 100 ? C.green : ms < 1000 ? C.cyan : ms < 3000 ? C.yellow : C.red;
    const tag = res.getHeader('x-cache-source') || '';

    log('info', 'http',
      `${statusColor}← ${res.statusCode}${C.reset}  ${C.bold}${req.path}${C.reset}  ` +
      `${msColor}${ms.toFixed(0)}ms${C.reset}` +
      (tag ? `  ${C.gray}via ${C.reset}${C.magenta}${tag}${C.reset}` : '')
    , { id: req.id });
  });

  next();
});

app.use('/api', rateLimit({
  windowMs: 60_000,
  max: RATE_LIMIT_MAX,
  standardHeaders: true,
  legacyHeaders: false,
}));

// ─── API guard ────────────────────────────────────────────
// Blocks the API from ever being readable in a normal browser tab.
function deny(res, req, reason) {
  log('warn', 'http', 'access denied', {
    id: req.id,
    reason,
    origin: req.get('origin') || '-',
    referer: (req.get('referer') || '-').slice(0, 60),
  });
  res.status(403);
  res.setHeader('Cache-Control', 'no-store');
  res.setHeader('Vary', 'Origin');
  res.type('text/plain; charset=utf-8');
  return res.send('403 Forbidden');
}

function apiGuard(req, res, next) {
  // Let CORS preflight reach cors()
  if (req.method === 'OPTIONS') return next();

  const mode = (req.get('sec-fetch-mode') || '').toLowerCase();
  const dest = (req.get('sec-fetch-dest') || '').toLowerCase();
  const site = (req.get('sec-fetch-site') || '').toLowerCase();

  // 1) Direct browser navigation: address bar, bookmark, link, <a target=_blank>
  if (mode === 'navigate' || dest === 'document') {
    return deny(res, req, 'direct_navigation');
  }

  // 2) Cross-site no-cors subresource: <img>, <script>, <iframe>, <video>…
  if (site === 'cross-site' && mode === 'no-cors') {
    return deny(res, req, 'cross_site_no_cors');
  }

  const origin  = req.get('origin');
  const referer = req.get('referer');

  // 3) Browser request → Origin (or Referer) must be one of your domains
  if (origin) {
    if (!isAllowedOrigin(origin)) return deny(res, req, 'origin_not_allowed');
    return next();
  }
  if (referer) {
    if (!isAllowedReferer(referer)) return deny(res, req, 'referer_not_allowed');
    return next();
  }

  // 4) No Origin + no Referer → non-browser client (curl, SSR fetch, uptime probe)
  return next();
}

app.use('/api', apiGuard);

// ═══════════════════════════════════════════════════════════════
//  DATABASE  (default database: vid)
// ═══════════════════════════════════════════════════════════════
function buildPoolConfig() {
  const ssl = { rejectUnauthorized: false };

  if (process.env.DATABASE_URL) {
    const cleanUrl = process.env.DATABASE_URL
      .replace(/([?&])sslmode=[^&]*&?/g, '$1')
      .replace(/[?&]$/, '');
    return {
      connectionString: cleanUrl,
      ssl,
      max: DB_POOL_MAX,
      min: 2,
      idleTimeoutMillis: 30_000,
      connectionTimeoutMillis: 10_000,
      statement_timeout: 5_000,
      query_timeout: 5_000,
      application_name: 'vidzee-proxy',
    };
  }

  return {
    host: process.env.PGHOST,
    port: Number(process.env.PGPORT) || 5432,
    user: process.env.PGUSER,
    password: process.env.PGPASSWORD,
    database: process.env.PGDATABASE || 'vid',   // ← new database name
    ssl,
    max: DB_POOL_MAX,
    min: 2,
    idleTimeoutMillis: 30_000,
    connectionTimeoutMillis: 10_000,
    statement_timeout: 5_000,
    query_timeout: 5_000,
    application_name: 'vidzee-proxy',
  };
}

const pool = new Pool(buildPoolConfig());
pool.on('error', (err) => log('error', 'db', 'idle client error', { err: err.message }));
pool.on('connect', () => log('debug', 'db', 'new client connected'));
pool.on('acquire', () => log('debug', 'db', 'client acquired'));
pool.on('remove', () => log('debug', 'db', 'client removed'));

let dbReady = false;

async function initDb() {
  await pool.query(`
    CREATE TABLE IF NOT EXISTS stream_cache (
      id          SERIAL PRIMARY KEY,
      media_type  TEXT        NOT NULL DEFAULT 'tv',
      tmdb        TEXT        NOT NULL,
      season      INTEGER     NOT NULL,
      episode     INTEGER     NOT NULL,
      payload     JSONB       NOT NULL,
      created_at  TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      updated_at  TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );
    ALTER TABLE stream_cache
      ADD COLUMN IF NOT EXISTS media_type TEXT NOT NULL DEFAULT 'tv';
    ALTER TABLE stream_cache
      DROP CONSTRAINT IF EXISTS stream_cache_unique;
    CREATE UNIQUE INDEX IF NOT EXISTS stream_cache_unique
      ON stream_cache (media_type, tmdb, season, episode);
    CREATE INDEX IF NOT EXISTS idx_stream_cache_lookup
      ON stream_cache (tmdb, season, episode);
  `);
  dbReady = true;
  log('ok', 'db', 'stream_cache table ready');
  log('ok', 'db', 'pool ready', { pool: DB_POOL_MAX, min: 2, database: pool.options.database });
}

async function getFromDb(mediaType, tmdb, season, episode) {
  if (!dbReady) return null;
  try {
    const { rows } = await pool.query(
      `SELECT payload FROM stream_cache
       WHERE media_type = $1 AND tmdb = $2 AND season = $3 AND episode = $4
       LIMIT 1`,
      [mediaType, String(tmdb), Number(season), Number(episode)]
    );
    if (!rows.length) return null;
    log('debug', 'db', 'hit', { key: `${mediaType} ${tmdb}|${season}|${episode}` });
    return rows[0].payload;
  } catch (err) {
    log('error', 'db', 'query failed', { err: err.message });
    return null;
  }
}

async function saveToDb(mediaType, tmdb, season, episode, payload) {
  if (!dbReady) return;
  try {
    await pool.query(
      `INSERT INTO stream_cache (media_type, tmdb, season, episode, payload, updated_at)
       VALUES ($1, $2, $3, $4, $5::jsonb, NOW())
       ON CONFLICT (media_type, tmdb, season, episode)
       DO UPDATE SET payload = EXCLUDED.payload, updated_at = NOW()`,
      [mediaType, String(tmdb), Number(season), Number(episode), JSON.stringify(payload)]
    );
    log('ok', 'db', 'saved', { key: `${mediaType} ${tmdb}|${season}|${episode}` });
  } catch (err) {
    log('error', 'db', 'save failed', { err: err.message });
  }
}

// ═══════════════════════════════════════════════════════════════
//  LRU CACHE
// ═══════════════════════════════════════════════════════════════
class LRUCache {
  constructor(maxSize) {
    this.max = maxSize;
    this.map = new Map();
  }
  get(key) {
    const v = this.map.get(key);
    if (!v) return null;
    if (Date.now() > v.expires) { this.map.delete(key); return null; }
    this.map.delete(key);
    this.map.set(key, v);
    return v.data;
  }
  set(key, data, ttlMs) {
    if (this.map.has(key)) this.map.delete(key);
    this.map.set(key, { data, expires: Date.now() + ttlMs });
    if (this.map.size > this.max) {
      const first = this.map.keys().next().value;
      this.map.delete(first);
    }
  }
  get size() { return this.map.size; }
}

const cache = new LRUCache(MEM_CACHE_MAX);

// ═══════════════════════════════════════════════════════════════
//  SEMAPHORE
// ═══════════════════════════════════════════════════════════════
class Semaphore {
  constructor(max, timeoutMs) {
    this.max = max;
    this.timeoutMs = timeoutMs;
    this.current = 0;
    this.queue = [];
  }
  _makeReleaser() {
    let done = false;
    return () => {
      if (done) return;
      done = true;
      this.current--;
      const next = this.queue.shift();
      if (next) {
        clearTimeout(next.timer);
        this.current++;
        next.resolve(this._makeReleaser());
      }
    };
  }
  acquire() {
    if (this.current < this.max) {
      this.current++;
      return Promise.resolve(this._makeReleaser());
    }
    return new Promise((resolve, reject) => {
      const entry = { resolve, reject, timer: null };
      entry.timer = setTimeout(() => {
        const i = this.queue.indexOf(entry);
        if (i >= 0) this.queue.splice(i, 1);
        reject(new Error('queue_timeout'));
      }, this.timeoutMs);
      this.queue.push(entry);
    });
  }
  async run(fn) {
    const release = await this.acquire();
    try { return await fn(); }
    finally { release(); }
  }
  stats() { return { current: this.current, queued: this.queue.length, max: this.max }; }
}

const captureSem = new Semaphore(CAPTURE_CONCURRENCY, QUEUE_TIMEOUT);

// ═══════════════════════════════════════════════════════════════
//  SINGLE-FLIGHT
// ═══════════════════════════════════════════════════════════════
const inflight = new Map();
function singleFlight(key, fn) {
  const existing = inflight.get(key);
  if (existing) {
    log('debug', 'cache', 'single-flight join', { key });
    return existing;
  }
  const p = (async () => fn())().finally(() => inflight.delete(key));
  inflight.set(key, p);
  return p;
}

// ═══════════════════════════════════════════════════════════════
//  BROWSER — truly windowless via chromium-headless-shell
// ═══════════════════════════════════════════════════════════════
let browser = null, context = null, initPromise = null;
let contextCreatedAt = 0;
let browserBinary = 'unknown';

const USER_AGENT =
  'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36';

const LAUNCH_ARGS = [
  '--headless=new',
  '--disable-blink-features=AutomationControlled',
  '--no-sandbox',
  '--disable-dev-shm-usage',
  '--disable-gpu',
  '--disable-software-rasterizer',
  '--disable-extensions',
  '--disable-default-apps',
  '--no-first-run',
  '--no-default-browser-check',
  '--disable-background-networking',
  '--disable-background-timer-throttling',
  '--disable-backgrounding-occluded-windows',
  '--disable-renderer-backgrounding',
  '--disable-features=IsolateOrigins,site-per-process,Translate,BackForwardCache',
  '--autoplay-policy=no-user-gesture-required',
  '--mute-audio',
  '--hide-scrollbars',
  '--noerrdialogs',
  '--disable-crash-reporter',
  '--disable-breakpad',
];

async function launchBrowser() {
  if (browser && browser.isConnected()) return;
  if (browser) { try { await browser.close(); } catch {} }

  if (!HEADLESS) {
    log('warn', 'browser', 'launching HEADED (HEADLESS=false) — window will be visible');
    browser = await chromium.launch({ headless: false, args: LAUNCH_ARGS });
    browserBinary = 'chromium (headed)';
    log('ok', 'browser', 'chromium ready (headed)');
    browser.on('disconnected', () => {
      log('warn', 'browser', 'disconnected');
      browser = null; context = null;
    });
    return;
  }

  try {
    log('info', 'browser', 'launching', { channel: 'chromium-headless-shell' });
    browser = await chromium.launch({
      headless: true,
      channel: 'chromium-headless-shell',
      args: LAUNCH_ARGS,
    });
    browserBinary = 'chromium-headless-shell';
    log('ok', 'browser', 'ready — windowless (no flash possible)');
  } catch (err) {
    log('warn', 'browser', 'headless-shell unavailable, falling back', {
      err: err.message,
      hint: 'run: npx playwright install chromium-headless-shell',
    });
    browser = await chromium.launch({
      headless: true,
      args: LAUNCH_ARGS,
    });
    browserBinary = 'chromium (--headless=new)';
    log('ok', 'browser', 'ready (new headless mode)');
  }

  browser.on('disconnected', () => {
    log('warn', 'browser', 'disconnected');
    browser = null;
    context = null;
  });
}

async function createContext() {
  const ctx = await browser.newContext({
    userAgent: USER_AGENT,
    viewport: { width: 1920, height: 1080 },
    locale: 'en-US',
    timezoneId: 'Asia/Kolkata',
    extraHTTPHeaders: {
      'Accept-Language': 'en-US,en;q=0.9',
      'sec-ch-ua': '"Chromium";v="131", "Not_A Brand";v="24"',
      'sec-ch-ua-mobile': '?0',
      'sec-ch-ua-platform': '"Windows"',
    },
  });
  await ctx.addInitScript(() => {
    Object.defineProperty(navigator, 'webdriver', { get: () => undefined });
    window.chrome = window.chrome || { runtime: {} };
  });
  contextCreatedAt = Date.now();
  log('ok', 'context', 'created');
  return ctx;
}

async function ensureBrowser() {
  if (initPromise) return initPromise;
  initPromise = (async () => {
    if (!browser || !browser.isConnected()) await launchBrowser();
    if (!context || Date.now() - contextCreatedAt > CONTEXT_MAX_AGE) {
      if (context) { try { await context.close(); } catch {} }
      context = await createContext();
    }
  })().finally(() => { initPromise = null; });
  return initPromise;
}

async function acquirePage() {
  try {
    return await context.newPage();
  } catch (err) {
    log('warn', 'context', 'dead — recreating', { err: err.message });
    contextCreatedAt = 0;
    try { await context.close(); } catch {}
    context = null;
    await ensureBrowser();
    return await context.newPage();
  }
}

// ═══════════════════════════════════════════════════════════════
//  CAPTURE  — pure network interception, NO clicking
// ═══════════════════════════════════════════════════════════════
const BLOCKED_TYPES = new Set(['image', 'font', 'media', 'manifest']);
const BLOCKED_HOSTS = [
  'google-analytics.com', 'googletagmanager.com', 'googleadservices.com',
  'doubleclick.net', 'facebook.net', 'connect.facebook.net',
  'hotjar.com', 'clarity.ms', 'sentry.io', 'newrelic.com',
  'cloudflareinsights.com', 'static.cloudflareinsights.com',
];

function buildEmbedUrl(mediaType, tmdb, s, e) {
  return mediaType === 'movie'
    ? `https://player.vidzee.wtf/embed/movie/${tmdb}`
    : `https://player.vidzee.wtf/embed/tv/${tmdb}/${s}/${e}`;
}

const sleep = (ms) => new Promise(r => setTimeout(r, Math.max(0, ms)));

/**
 * Try to extract an m3u8 / stream URL from a JSON payload.
 * Handles the most common shapes returned by streaming players.
 */
function extractStreamFromJson(json) {
  if (!json || typeof json !== 'object') return null;

  // Direct m3u8 string fields
  for (const k of ['m3u8', 'm3u8_path', 'm3u8_url', 'hls', 'hls_url', 'file', 'src', 'url', 'stream_url']) {
    if (typeof json[k] === 'string' && json[k].includes('.m3u8')) return json[k];
  }

  // Nested sources / streams arrays
  for (const arrKey of ['sources', 'streams', 'source', 'links', 'servers', 'data']) {
    const arr = json[arrKey];
    if (Array.isArray(arr)) {
      for (const item of arr) {
        if (typeof item === 'string' && item.includes('.m3u8')) return item;
        if (item && typeof item === 'object') {
          for (const k of ['file', 'url', 'src', 'm3u8', 'link', 'stream_url', 'source']) {
            if (typeof item[k] === 'string' && item[k].includes('.m3u8')) return item[k];
          }
        }
      }
    }
  }

  // Deep scan — any string value containing .m3u8
  const stack = [json];
  while (stack.length) {
    const cur = stack.pop();
    if (!cur || typeof cur !== 'object') continue;
    for (const v of Object.values(cur)) {
      if (typeof v === 'string' && v.includes('.m3u8')) return v;
      if (typeof v === 'object') stack.push(v);
    }
  }

  return null;
}

async function captureStream(mediaType, tmdb, s, e) {
  const deadline  = Date.now() + CAPTURE_TIMEOUT;
  const remaining = () => deadline - Date.now();
  const notAvailable = (reason, extra = {}) => ({
    available: false,
    reason,
    message: 'This movie / episode is not available on this server.',
    ...extra,
  });

  const embedUrl = buildEmbedUrl(mediaType, tmdb, s, e);
  const page = await acquirePage();
  const startedAt = Date.now();

  page.setDefaultTimeout(3000);
  page.setDefaultNavigationTimeout(5000);

  let captured = null;          // full JSON payload if available
  let capturedUrl = '';         // URL of the API response
  let m3u8Url = null;           // extracted m3u8 URL (from JSON or direct request)
  let apiResponded = false;
  let apiReturnedEmpty = false;

  let resolveCapture;
  const captureSignal = new Promise(r => { resolveCapture = r; });

  // ── block junk ──────────────────────────────────────────
  await page.route('**/*', (route) => {
    const req = route.request();
    if (BLOCKED_TYPES.has(req.resourceType())) return route.abort();
    const u = req.url();
    if (BLOCKED_HOSTS.some(h => u.includes(h))) return route.abort();
    return route.continue();
  });

  // ── intercept API responses (JSON with sources / m3u8) ──
  page.on('response', async (res) => {
    const url = res.url();
    if (!VIDZEE_API_MATCH.some(fragment => url.includes(fragment))) return;

    apiResponded = true;
    if (captured || m3u8Url) return;

    try {
      const text = await res.text();
      if (res.status() === 200 && text.trim().startsWith('{')) {
        const json = JSON.parse(text);

        // Try to extract m3u8 directly from JSON
        const extracted = extractStreamFromJson(json);
        if (extracted) {
          m3u8Url = extracted;
          captured = json;
          capturedUrl = url;
          log('ok', 'capture', 'm3u8 extracted from JSON', {
            url: url.slice(0, 100),
            m3u8: extracted.slice(0, 120),
          });
          resolveCapture(json);
          return;
        }

        // If JSON has sources but no m3u8 string yet, keep the JSON
        if (json.sources || json.streams || json.data) {
          captured = json;
          capturedUrl = url;
          log('ok', 'capture', 'JSON hit (no m3u8 yet)', { url: url.slice(0, 100) });
          // don't resolve yet — a later response may carry the m3u8
        } else {
          apiReturnedEmpty = true;
        }
      }
    } catch {}
  });

  // ── intercept direct .m3u8 requests ─────────────────────
  page.on('response', (res) => {
    const url = res.url();
    if (url.includes('.m3u8') && !m3u8Url) {
      m3u8Url = url;
      capturedUrl = url;
      log('ok', 'capture', 'direct m3u8 intercepted', { url: url.slice(0, 160) });
      resolveCapture({ m3u8: url });
    }
  });

  const raceSleep = async (ms) => {
    if (remaining() <= 0) return;
    await Promise.race([sleep(ms), captureSignal]);
  };

  try {
    log('info', 'capture', 'start', {
      type: mediaType,
      key: `${tmdb}|${s}|${e}`,
      budget: `${CAPTURE_TIMEOUT}ms`,
      url: embedUrl,
    });

    const gotoTimeout = Math.min(5000, Math.max(1000, remaining()));
    try {
      await page.goto(embedUrl, { waitUntil: 'domcontentloaded', timeout: gotoTimeout });
    } catch (err) {
      log('warn', 'capture', 'goto failed', { err: err.message });
      return notAvailable('timeout');
    }

    if (remaining() <= 0) return notAvailable('timeout');

    // Wait for the app to mount and fire its API request
    await Promise.race([
      page.waitForSelector('#root > *', { timeout: Math.min(2500, remaining()) }).catch(() => {}),
      captureSignal,
    ]);

    // Give the network a moment to settle — no clicking needed
    await raceSleep(400);

    // Poll until capture or deadline — just wait, never click
    while (!captured && !m3u8Url && remaining() > 0) {
      await raceSleep(300);
    }

  } finally {
    await page.close().catch(() => {});
  }

  const took = Date.now() - startedAt;

  // ── build result ────────────────────────────────────────
  if (m3u8Url) {
    log('ok', 'capture', 'done (m3u8)', { took: `${took}ms`, m3u8: m3u8Url.slice(0, 120) });
    return {
      available: true,
      data: captured || { m3u8: m3u8Url },
      m3u8: m3u8Url,
      from: capturedUrl,
    };
  }

  if (captured) {
    log('ok', 'capture', 'done (json)', { took: `${took}ms` });
    return { available: true, data: captured, m3u8: null, from: capturedUrl };
  }

  if (apiReturnedEmpty) {
    log('warn', 'capture', 'empty response', { took: `${took}ms` });
    return notAvailable('empty_response');
  }
  if (!apiResponded) {
    log('warn', 'capture', 'no API response', { took: `${took}ms` });
    return notAvailable('no_response');
  }
  log('warn', 'capture', 'timeout', { took: `${took}ms` });
  return notAvailable('timeout');
}

// ═══════════════════════════════════════════════════════════════
//  ROUTES
// ═══════════════════════════════════════════════════════════════
async function resolveStream(mediaType, tmdb, s, e, key) {
  const m2 = cache.get(key);
  if (m2) return { payload: m2, source: 'memory', negative: m2.available === false };

  const dbHit = await getFromDb(mediaType, tmdb, s, e);
  if (dbHit) {
    log('ok', 'cache', 'db hit', { key });
    cache.set(key, dbHit, CACHE_TTL);
    return { payload: dbHit, source: 'database', negative: dbHit.available === false };
  }

  log('info', 'cache', 'miss — capturing', { key });

  const cap = await captureSem.run(() => captureStream(mediaType, tmdb, s, e));

  if (!cap.available) {
    const body = {
      available: false,
      error: 'Not available',
      message: cap.message || 'This movie / episode is not available on this server.',
      reason: cap.reason,
      type: mediaType, tmdb, season: s, episode: e,
    };
    cache.set(key, body, NEGATIVE_CACHE_TTL);
    return { payload: body, source: 'capture', negative: true };
  }

  const payload = {
    available: true,
    type: mediaType,
    m3u8: cap.m3u8 || null,          // ← top-level m3u8 for easy consumption
    ...cap.data,
  };
  cache.set(key, payload, CACHE_TTL);
  saveToDb(mediaType, tmdb, s, e, payload).catch(() => {});

  return { payload, source: 'capture', negative: false };
}

async function streamHandler(req, res) {
  const { tmdb } = req.query;
  const rawType  = String(req.query.type || '').toLowerCase();
  const mediaType =
    rawType === 'movie' ? 'movie'
    : rawType === 'tv'  ? 'tv'
    : req.path.startsWith('/api/movie') ? 'movie'
    : 'tv';

  if (!tmdb) return res.status(400).json({ error: 'Missing tmdb' });

  const isMovie = mediaType === 'movie';
  const s = isMovie ? 0 : Number(req.query.s ?? 1);
  const e = isMovie ? 0 : Number(req.query.e ?? 1);

  const key = `${mediaType}|${tmdb}|${s}|${e}`;

  // Fast memory path
  const memHit = cache.get(key);
  if (memHit) {
    res.setHeader('x-cache-source', 'memory');
    return res.json({ ...memHit, _cached: 'memory' });
  }

  try {
    const result = await singleFlight(key, () =>
      resolveStream(mediaType, tmdb, s, e, key));

    res.setHeader('x-cache-source', result.source);

    if (result.negative) return res.status(404).json(result.payload);

    return res.json({
      ...result.payload,
      _cached: result.source === 'capture' ? false : result.source,
    });
  } catch (err) {
    if (err.message === 'queue_timeout') {
      res.set('Retry-After', '5');
      log('warn', 'queue', 'full — rejecting', { key, ...captureSem.stats() });
      return res.status(503).json({
        available: false,
        error: 'Server busy',
        reason: 'queue_timeout',
        retryAfter: 5,
      });
    }
    log('error', 'proxy', 'stream error', { err: err.message, key });
    return res.status(502).json({
      available: false,
      error: 'Capture failed',
      message: err.message,
    });
  }
}

app.get('/api/stream', streamHandler);
app.get('/api/movie',  streamHandler);

app.get('/health', async (_req, res) => {
  let dbOk = false;
  try {
    if (dbReady) { await pool.query('SELECT 1'); dbOk = true; }
  } catch {}
  res.json({
    ok: true,
    uptime: Math.round(process.uptime()),
    browser: !!(browser && browser.isConnected()),
    browserBinary,
    contextAge: contextCreatedAt ? Date.now() - contextCreatedAt : null,
    memoryCache: cache.size,
    memoryCacheMax: MEM_CACHE_MAX,
    capture: captureSem.stats(),
    inflight: inflight.size,
    db: dbOk,
    dbName: pool.options.database,
    apiMatch: VIDZEE_API_MATCH,
    mem: process.memoryUsage().rss,
  });
});

// ═══════════════════════════════════════════════════════════════
//  BOOT + SHUTDOWN
// ═══════════════════════════════════════════════════════════════
let shuttingDown = false;

(async () => {
  banner();

  try { await initDb(); }
  catch (err) {
    log('error', 'db', 'init failed — running WITHOUT database', { err: err.message });
    dbReady = false;
  }

  try { await ensureBrowser(); }
  catch (err) { log('error', 'browser', 'init failed', { err: err.message }); }

  if (browser) {
    try {
      const v = browser.version();
      log('info', 'browser', 'version', { v, binary: browserBinary });
    } catch {}
  }

  const server = app.listen(PORT, () => {
    log('ok', 'server', `listening on ${C.bold}http://localhost:${PORT}${C.reset}`);
    log('info', 'server', 'config', {
      concurrency: CAPTURE_CONCURRENCY,
      queueTimeout: `${QUEUE_TIMEOUT / 1000}s`,
      captureTimeout: `${CAPTURE_TIMEOUT / 1000}s`,
      memCache: MEM_CACHE_MAX,
      dbPool: DB_POOL_MAX,
      dbName: pool.options.database,
      logLevel: LOG_LEVEL,
      headless: HEADLESS,
      binary: browserBinary,
      apiMatch: VIDZEE_API_MATCH.join(' | '),
    });
    log('info', 'server', 'cors allow-list', { hosts: [...ALLOWED_HOSTS].join(', ') });
    log('ready', 'proxy', 'ready — waiting for requests');
    process.stdout.write('\n');
  });

  server.keepAliveTimeout = 65_000;
  server.headersTimeout   = 66_000;
  server.requestTimeout   = 120_000;

  async function shutdown(sig) {
    if (shuttingDown) return;
    shuttingDown = true;
    divider(`shutting down (${sig})`);
    log('info', 'shutdown', 'closing HTTP server');
    server.close(() => log('ok', 'shutdown', 'HTTP closed'));

    const force = setTimeout(() => {
      log('warn', 'shutdown', 'forcing exit after 10s');
      process.exit(1);
    }, 10_000);
    force.unref();

    try { await context?.close(); log('ok', 'shutdown', 'context closed'); } catch {}
    try { await browser?.close(); log('ok', 'shutdown', 'browser closed'); } catch {}
    try { await pool.end();       log('ok', 'shutdown', 'db pool drained'); } catch {}

    clearTimeout(force);
    log('ok', 'shutdown', 'done');
    process.exit(0);
  }

  process.on('SIGINT',  () => shutdown('SIGINT'));
  process.on('SIGTERM', () => shutdown('SIGTERM'));

  process.on('unhandledRejection', e => log('error', 'proxy', 'unhandledRejection', { err: String(e) }));
  process.on('uncaughtException',  e => log('error', 'proxy', 'uncaughtException',  { err: String(e) }));
})();