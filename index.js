/**
 * +---------------------------------------------------+
 * |   CANTOR8 ROUND-TRIP BOT v2.0  (CC <-> USDCx)     |
 * |   Optimized for 1tx/hour rate limit               |
 * |   Wall-clock anchored, persistent state           |
 * +---------------------------------------------------+
 *
 * Usage: node index.js
 * Files:
 *   config.json     - settings
 *   accounts.json   - one mnemonic per line
 *   proxy.txt       - one proxy per line (optional)
 *   state/*.json    - per-account persistent state (auto)
 */

import { readFileSync, writeFileSync, existsSync, mkdirSync } from 'fs';
import { randomBytes, randomInt } from 'crypto';
import http from 'http';
import https from 'https';
import path from 'path';
import { mnemonicToSeedSync } from '@scure/bip39';
import { HDKey } from '@scure/bip32';
import * as ed from '@noble/ed25519';
import { sha512 } from '@noble/hashes/sha512';
import axios from 'axios';
import chalk from 'chalk';
import stringWidth from 'string-width';
import { HttpsProxyAgent } from 'https-proxy-agent';
import { HttpProxyAgent } from 'http-proxy-agent';

// ---------- Setup ---------------------------------------------------------
ed.etc.sha512Sync = (...m) => sha512(ed.etc.concatBytes(...m));

// Default config (inline). Override by creating ./config.json.
const DEFAULT_CONFIG = {
    api: {
        backend_url: 'https://wallet.cantor8.tech/api',
        swap_url: 'https://swap.cantor8.tech/api',
        exchange_url: 'https://exchange.cantor8.tech',
    },
    derivation: {
        path_prefix: "m/44'/60'",
        path_suffix: "0/0",
        key_count: 5,
    },
    swap: {
        enabled: true,
        amount_min: 26.5,
        amount_max: 32,
        interval_minutes: 60,
        interval_jitter_seconds: 300,
        interval_buffer_seconds: 30,
        max_swaps: 100,
        reward_landed_threshold: 100,
        usdcx_dust_reserve: 0.0001,
        min_usdcx_for_swap: 1,
        min_ceth_for_recovery: 0.0005,
    },
    retry: {
        rate_limit_initial_delay_minutes: 61,
        rate_limit_delays: [900, 1800, 3600],
        server_rejected_delays: [15, 30, 60],
        max_422_retries: 3,
        max_eligibility_attempts: 20,
        max_resume_poll_minutes: 30,
    },
    background_refresh: {
        enabled: true,
        interval_seconds: 300,
    },
    stagger_min_seconds: 5,
    stagger_max_seconds: 60,
    state_dir: './state',
};

let config = DEFAULT_CONFIG;
try {
    const userCfg = JSON.parse(readFileSync(new URL('./config.json', import.meta.url), 'utf-8'));
    // Shallow merge top-level keys; deep-merge nested objects
    config = { ...DEFAULT_CONFIG, ...userCfg };
    for (const k of ['api', 'derivation', 'swap', 'retry', 'background_refresh']) {
        if (userCfg[k]) config[k] = { ...DEFAULT_CONFIG[k], ...userCfg[k] };
    }
} catch { /* use defaults */ }

const accountLines = readFileSync(new URL('./accounts.json', import.meta.url), 'utf-8')
    .split('\n').map(l => l.trim()).filter(l => l.length > 0);
let proxyLines = [];
try {
    proxyLines = readFileSync(new URL('./proxy.txt', import.meta.url), 'utf-8')
        .split('\n').map(l => l.trim()).filter(l => l.length > 0);
} catch { /* optional */ }

config.accounts = accountLines.map((mnemonic, i) => ({
    name: `Acc ${i + 1}`,
    mnemonic,
    proxy: proxyLines[i] || '',
}));

const BACKEND = config.api.backend_url;
const SWAP_API = config.api.swap_url;
const EXCHANGE = config.api.exchange_url;

const STATE_DIR = config.state_dir || './state';
if (!existsSync(STATE_DIR)) mkdirSync(STATE_DIR, { recursive: true });

const ASSET_TO_INSTRUMENT = { '0x0': 'Amulet', 'USDCX': 'USDCx', 'CETH': 'cETH' };

const PAIR_CC = { chain: 'CC', asset: '0x0', label: 'CC' };
const PAIR_USDCX = { chain: 'CC', asset: 'USDCX', label: 'USDCx' };

const BASE_HEADERS = {
    'Accept': 'application/json',
    'Content-Type': 'application/json',
    'Origin': 'https://wallet.cantor8.tech',
    'Referer': 'https://wallet.cantor8.tech/',
    'User-Agent': 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/145.0.0.0 Safari/537.36',
};

const TOKEN_MAX_AGE_MS = 45 * 60 * 1000;

// ---------- State Persistence --------------------------------------------

function shortPartyId(pid) {
    return pid ? pid.slice(0, 16).replace(/[^a-zA-Z0-9_-]/g, '_') : 'unknown';
}

function stateFilePath(partyId) {
    return path.join(STATE_DIR, `state-${shortPartyId(partyId)}.json`);
}

function loadState(partyId) {
    const fp = stateFilePath(partyId);
    if (!existsSync(fp)) {
        return {
            lastSwapTimestamp: 0,
            lastDirection: null,        // 'CC_TO_USDCX' | 'USDCX_TO_CC' | null
            totalTxCount: 0,
            rewardBaseline: { txns: null, reward: null },
        };
    }
    try {
        return JSON.parse(readFileSync(fp, 'utf-8'));
    } catch {
        return { lastSwapTimestamp: 0, lastDirection: null, totalTxCount: 0, rewardBaseline: { txns: null, reward: null } };
    }
}

function saveState(partyId, state) {
    const fp = stateFilePath(partyId);
    try {
        writeFileSync(fp, JSON.stringify(state, null, 2), 'utf-8');
    } catch { /* non-critical */ }
}

// ---------- Crypto -------------------------------------------------------

function generateKeyPairs(mnemonic) {
    const { path_prefix, path_suffix, key_count } = config.derivation;
    const seed = mnemonicToSeedSync(mnemonic, '');
    const hdkey = HDKey.fromMasterSeed(seed);
    const keyPairs = [];
    for (let i = 0; i < key_count; i++) {
        const p = `${path_prefix}/${i}'/${path_suffix}`;
        const child = hdkey.derive(p);
        const privateKey = child.privateKey;
        if (!privateKey || privateKey.length !== 32) throw new Error(`Key derivation failed at ${p}`);
        const publicKey = ed.getPublicKey(privateKey);
        keyPairs.push({ index: i, path: p, privateKey, publicKey, publicKeyHex: Buffer.from(publicKey).toString('hex') });
    }
    return keyPairs;
}

function signMessage(privateKey, message) {
    const msg = typeof message === 'string' ? new TextEncoder().encode(message) : message;
    return ed.sign(msg, privateKey);
}

function toHex(bytes) { return Buffer.from(bytes).toString('hex'); }
function toBase64(bytes) { return Buffer.from(bytes).toString('base64'); }

function generateOrderId() {
    const chars = 'abcdefghijklmnopqrstuvwxyz0123456789';
    let id = 'ord_';
    for (let i = 0; i < 20; i++) id += chars[randomInt(0, chars.length)];
    return id;
}

// ---------- Helpers ------------------------------------------------------

const sleep = (sec) => new Promise(r => setTimeout(r, sec * 1000));
const shortId = (id) => !id ? '?' : (id.length > 20 ? `${id.slice(0, 12)}...${id.slice(-8)}` : id);

function randomFloat(min, max, decimals = 2) {
    const v = Math.random() * (max - min) + min;
    return Math.round(v * Math.pow(10, decimals)) / Math.pow(10, decimals);
}

function randomDelaySec(minSec, maxSec) {
    return Math.floor(Math.random() * (maxSec - minSec + 1)) + minSec;
}

function formatDuration(seconds) {
    if (seconds < 0) return '0s';
    const h = Math.floor(seconds / 3600);
    const m = Math.floor((seconds % 3600) / 60);
    const s = Math.floor(seconds % 60);
    if (h > 0) return `${h}h${String(m).padStart(2, '0')}m`;
    if (m > 0) return `${m}m${String(s).padStart(2, '0')}s`;
    return `${s}s`;
}

function formatUptime(startMs) {
    return formatDuration(Math.floor((Date.now() - startMs) / 1000));
}

function formatError(err) {
    if (err.response) {
        const code = err.response.status;
        const msg = err.response.data?.detail || err.response.data?.message || '';
        if (code >= 500) return `[${code}] Server error`;
        if (code === 401) return `[401] Auth expired`;
        if (code === 400) return `[400] ${msg || 'Bad request'}`;
        if (code === 409) return `[409] Active order exists`;
        if (code === 422) return `[422] ${msg || 'Rejected'}`;
        if (code === 429) return `[429] Rate limited`;
        return `[${code}] ${msg || 'Error'}`;
    }
    if (err.code) return `[${err.code}]`;
    return err.message?.slice(0, 50) || 'Unknown error';
}

function ts() {
    return new Date().toLocaleTimeString('en-GB', { hour12: false }).replace(/:/g, '.');
}

// ---------- Retry --------------------------------------------------------

const RETRYABLE_CODES = [
    'ECONNRESET', 'ECONNREFUSED', 'ETIMEDOUT', 'ENOTFOUND',
    'EPIPE', 'EAI_AGAIN', 'ENETUNREACH', 'EHOSTUNREACH',
    'ERR_SOCKET_CONNECTION_TIMEOUT', 'ECONNABORTED',
    'ERR_NETWORK', 'EHOSTDOWN', 'ESOCKETTIMEDOUT', 'EADDRINFO',
];

function isRetryableError(err) {
    if (err.code === 'ERR_BAD_RESPONSE') return false;
    if (RETRYABLE_CODES.includes(err.code)) return true;
    if (err.response?.status === 400) {
        const detail = String(err.response?.data?.detail || err.response?.data?.message || '');
        if (detail.toLowerCase().includes('challenge')) return true;
    }
    if (err.message?.includes('socket hang up')) return true;
    if (err.message?.includes('ECONNRESET')) return true;
    if (err.message?.includes('timeout')) return true;
    if (err.message?.includes('tunneling socket')) return true;
    if (err.message?.includes('Proxy')) return true;
    return false;
}

function getEscalatingDelay(attempt, delays) {
    if (attempt < delays.length) return delays[attempt];
    return delays[delays.length - 1];
}

async function retryOnNetwork(fn, { baseDelay = 3, label = '', log = null, throwOnRateLimit = false } = {}) {
    let rateLimitAttempt = 0;
    const rateLimitInitialDelayMin = config.retry?.rate_limit_initial_delay_minutes ?? 61;
    const rateLimitDelays = config.retry?.rate_limit_delays || [900, 1800, 3600];
    let consecutiveTimeouts = 0;
    const MAX_CONSECUTIVE_TIMEOUTS = 3;

    for (let attempt = 0; ; attempt++) {
        try {
            const r = await fn();
            consecutiveTimeouts = 0;
            return r;
        } catch (err) {
            if (err.response?.status >= 500) throw err;

            if (err.response?.status === 429) {
                if (throwOnRateLimit) throw err;
                let delay;
                if (rateLimitAttempt === 0) {
                    delay = rateLimitInitialDelayMin * 60; // FIXED: was * 31
                    if (log) log(`[wait] 429 first hit, ${rateLimitInitialDelayMin}m`);
                } else {
                    delay = getEscalatingDelay(rateLimitAttempt - 1, rateLimitDelays);
                    if (log) log(`[wait] 429 #${rateLimitAttempt}, ${formatDuration(delay)}`);
                }
                rateLimitAttempt++;
                await sleep(delay);
                continue;
            }

            if (err.response?.status === 422) throw err;
            if (!isRetryableError(err)) throw err;

            const isFatalConn = err.code === 'ETIMEDOUT' || err.code === 'ECONNABORTED'
                || err.code === 'ERR_SOCKET_CONNECTION_TIMEOUT'
                || (err.message && err.message.includes('timeout'));
            if (isFatalConn) {
                consecutiveTimeouts++;
                if (consecutiveTimeouts >= MAX_CONSECUTIVE_TIMEOUTS) {
                    if (log) log(`[fail] ${MAX_CONSECUTIVE_TIMEOUTS}x conn fail, soft restart`);
                    throw err;
                }
            } else {
                consecutiveTimeouts = 0;
            }

            const rawDelay = Math.min(baseDelay * Math.pow(2, attempt), 30);
            const jitter = rawDelay * (0.7 + Math.random() * 0.6);
            const delay = Math.round(jitter * 10) / 10;
            if (log) log(`[retry] ${formatError(err)} ${delay}s (#${attempt + 1})`);
            await sleep(delay);
        }
    }
}

// ---------- Axios Factory ------------------------------------------------

const keepAliveHttpAgent = new http.Agent({ keepAlive: true, maxSockets: 10 });
const keepAliveHttpsAgent = new https.Agent({ keepAlive: true, maxSockets: 10 });

function createAxiosInstance(proxyUrl) {
    const opts = { timeout: 90000, maxRedirects: 5, decompress: true };
    if (proxyUrl) {
        const agentOpts = { keepAlive: true, maxSockets: 10, timeout: 90000 };
        opts.httpsAgent = new HttpsProxyAgent(proxyUrl, agentOpts);
        opts.httpAgent = new HttpProxyAgent(proxyUrl, agentOpts);
        opts.proxy = false;
    } else {
        opts.httpAgent = keepAliveHttpAgent;
        opts.httpsAgent = keepAliveHttpsAgent;
    }
    return axios.create(opts);
}

// ---------- API ----------------------------------------------------------

function createWalletApi(ax) {
    const h = BASE_HEADERS;
    const auth = (token) => ({ ...h, Authorization: `Bearer ${token}` });
    return {
        recoverAccount: (keys) =>
            ax.post(`${BACKEND}/accounts/recovery_v3`, { public_keys: keys }, { headers: h }).then(r => r.data),
        getChallenge: (pid) =>
            ax.post(`${BACKEND}/auth/challenge`, { party_id: pid }, { headers: h }).then(r => r.data),
        login: (pid, ch, sig) =>
            ax.post(`${BACKEND}/auth/login`, { party_id: pid, challenge: ch, signature: sig }, { headers: h }).then(r => r.data),
        getBalance: (token) =>
            ax.get(`${BACKEND}/balance`, { headers: auth(token) }).then(r => r.data),
        getMyTag: (token) =>
            ax.get(`${BACKEND}/tags/my`, { headers: auth(token) }).then(r => r.data),
        prepareTransfer: (token, body) =>
            ax.post(`${BACKEND}/transfer/prepare`, {
                instrument_admin_id: body.instrumentAdminId,
                instrument_id: body.instrumentId,
                receiver_party_id: body.receiverPartyId,
                amount: body.amount,
                reason: body.reason || '',
                app_name: body.appName || 'swap-v1',
                metadata: body.metadata || {},
            }, { headers: auth(token) }).then(r => r.data),
        executeTransaction: (token, body) =>
            ax.post(`${BACKEND}/transaction/execute`, {
                command_id: body.commandId,
                prepared_tx_b64: body.preparedTxB64,
                hashing_scheme_version: body.hashingSchemeVersion,
                signature_b64: body.signatureB64,
            }, { headers: auth(token) }).then(r => r.data),
        getTransferStatus: (token, commandId) =>
            ax.get(`${BACKEND}/transfer/status`, { params: { command_id: commandId }, headers: auth(token) }).then(r => r.data),
        getOffers: (token) =>
            ax.get(`${BACKEND}/offers`, { headers: auth(token) }).then(r => r.data),
        getRegisterStatus: (token) =>
            ax.get(`${BACKEND}/register/status_v2`, { headers: auth(token) }).then(r => r.data),
        postConfirmV2: (token) =>
            ax.post(`${BACKEND}/register/post_confirm_v2`, {}, { headers: auth(token) }).then(r => r.data),
        getOutgoingExpired: (token) =>
            ax.get(`${BACKEND}/offers/outgoing_expired`, { headers: auth(token) }).then(r => r.data),
    };
}

function createSwapApi(ax) {
    const h = BASE_HEADERS;
    const auth = (token) => ({ ...h, Authorization: `Bearer ${token}` });
    return {
        getNonce: () =>
            ax.get(`${SWAP_API}/auth/nonce`, { headers: h }).then(r => r.data),
        bindSignature: (nonce, cantonAddress) =>
            ax.post(`${SWAP_API}/auth/signature`, { nonce, cantonAddress, signature: null }, { headers: h }).then(r => r.data),
        getQuote: (fromChain, fromAsset, toChain, toAsset, sendAmount) =>
            ax.post(`${SWAP_API}/quotes`, {
                fromChain, fromAsset, toChain, toAsset, sendAmount: String(sendAmount),
            }, { headers: h }).then(r => r.data),
        createOrder: (swapToken, orderId, quoteId, toAddress, slippageBps = 200) =>
            ax.post(`${SWAP_API}/orders`, { orderId, quoteId, toAddress, slippageBps }, { headers: auth(swapToken) }).then(r => r.data),
        getOrderStatus: (swapToken, orderId) =>
            ax.get(`${SWAP_API}/orders/${encodeURIComponent(orderId)}`, { headers: auth(swapToken) }).then(r => r.data),
        getActiveOrder: (swapToken, filters = {}) =>
            ax.get(`${SWAP_API}/orders/active`, { params: filters, headers: auth(swapToken) }).then(r => r.data),
        cancelOrder: (swapToken, orderId) =>
            ax.post(`${SWAP_API}/orders/${encodeURIComponent(orderId)}/cancel`, {}, { headers: auth(swapToken) }).then(r => r.data),
        checkExchange: async () => {
            for (let i = 0; i < 3; i++) {
                try {
                    await ax.head(EXCHANGE, { headers: h, timeout: 10000 });
                    return true;
                } catch (err) {
                    if (err.response?.status >= 500) return false;
                    if (err.response?.status >= 400) return true;
                    if (i < 2) await sleep(2);
                }
            }
            return true;
        },
        getLeaderboard: (address = null) =>
            ax.get(`${SWAP_API}/leaderboard`, {
                params: { limit: 50, includeRewards: true, includeAll: true, ...(address ? { address } : {}) },
                headers: h,
            }).then(r => r.data),
        checkEligibility: (partyId) =>
            ax.get(`${SWAP_API}/party/check-eligibility`, { params: { partyId }, headers: h }).then(r => r.data),
    };
}

// ---------- Dashboard ----------------------------------------------------

const MAX_ACC_LOGS = 1;

const dashboard = {
    accounts: [],
    _timer: null,
    _renderPending: false,

    init(accountConfigs) {
        this.accounts = accountConfigs.map((acc, i) => ({
            name: acc.name || `Acc ${i + 1}`,
            startTime: Date.now(),
            cc: 0, usdcx: 0, ceth: 0,
            totalSwaps: 0,
            lastDirection: '',
            nextSwapAt: 0,
            monthReward: 0, monthVolume: 0, monthTxns: 0,
            diffTxns: 0, diffReward: 0,
            rank: 0,
            proxy: !!acc.proxy,
            proxyHost: '',
            proxyIp: '',
            status: 'init',
            logs: [],
            isSwapping: false,
            modalCC: 0, nowCC: 0, modalLocked: false,
        }));
    },

    update(index, data) {
        Object.assign(this.accounts[index], data);
        this._scheduleRender();
    },

    log(index, msg) {
        const a = this.accounts[index];
        a.logs.push(`${ts()} ${msg}`);
        while (a.logs.length > MAX_ACC_LOGS) a.logs.shift();
        this._scheduleRender();
    },

    _scheduleRender() {
        if (this._renderPending) return;
        this._renderPending = true;
        setTimeout(() => {
            this._renderPending = false;
            this._render();
        }, 200);
    },

    _render() {
        const out = process.stdout;
        out.write('\x1B[H\x1B[2J');

        const total = this.accounts.length;
        const sumSwaps = this.accounts.reduce((s, a) => s + a.totalSwaps, 0);
        const active = this.accounts.filter(a => a.isSwapping || /swap|wait|prepare|exec/i.test(a.status)).length;
        const now = new Date().toLocaleTimeString('en-GB', { hour12: false });

        const padR = (s, w) => {
            const vl = stringWidth(String(s));
            if (vl >= w) return String(s).substring(0, w);
            return String(s) + ' '.repeat(w - vl);
        };
        const trunc = (s, w) => {
            if (stringWidth(String(s)) <= w) return padR(s, w);
            const stripped = String(s).replace(/\x1B\[[0-9;]*m/g, '');
            let result = '', len = 0;
            for (const ch of stripped) {
                if (len + stringWidth(ch) > w - 2) break;
                result += ch;
                len += stringWidth(ch);
            }
            return padR(result + '..', w);
        };

        const C = { acc: 7, status: 26, cc: 9, usdcx: 9, ceth: 9, swaps: 6, next: 8, reward: 8, up: 7 };
        const widths = [C.acc, C.status, C.cc, C.usdcx, C.ceth, C.swaps, C.next, C.reward, C.up];

        const sep = (w, ch, l, m, r) => {
            let line = l;
            for (let i = 0; i < w.length; i++) {
                line += ch.repeat(w[i] + 2);
                line += (i < w.length - 1) ? m : r;
            }
            return chalk.gray(' ' + line);
        };
        const row = (cells, colors) => {
            let r = chalk.gray(' |');
            for (let i = 0; i < cells.length; i++) r += ' ' + colors[i](cells[i]) + ' ' + chalk.gray('|');
            return r;
        };
        const calcSpan = (w) => w.reduce((s, x) => s + x + 3, 0) - 1;
        const fullSpan = (content, w) => {
            const span = calcSpan(w);
            const vis = stringWidth(content.replace(/\x1B\[[0-9;]*m/g, ''));
            const pad = Math.max(0, span - vis);
            return chalk.gray(' |') + content + ' '.repeat(pad) + chalk.gray('|');
        };
        const gray = s => chalk.gray(s);

        out.write(sep(widths, '-', '+', '-', '+') + '\n');
        const hdr = ' ' + chalk.cyan.bold('CANTOR8 ROUND-TRIP') + chalk.gray('  |  ') +
            chalk.gray('Acc:') + chalk.white(`${total}`) +
            chalk.gray('  Sw:') + chalk.white(`${sumSwaps}`) +
            chalk.gray('  Act:') + chalk.white(`${active}`) +
            chalk.gray('  Time:') + chalk.white(now);
        out.write(fullSpan(hdr, widths) + '\n');
        out.write(sep(widths, '-', '+', '+', '+') + '\n');

        out.write(row(
            [padR('Akun', C.acc), padR('Status', C.status), padR('CC', C.cc), padR('USDCx', C.usdcx),
             padR('cETH', C.ceth), padR('Swap', C.swaps), padR('Next', C.next), padR('Reward', C.reward), padR('Up', C.up)],
            Array(9).fill(gray)
        ) + '\n');
        out.write(sep(widths, '-', '+', '+', '+') + '\n');

        for (let i = 0; i < total; i++) {
            const a = this.accounts[i];
            const up = formatUptime(a.startTime);
            const dirCh = a.lastDirection === 'CC_TO_USDCX' ? '>' :
                          a.lastDirection === 'USDCX_TO_CC' ? '<' :
                          a.lastDirection === 'CETH_TO_USDCX' ? 'r' : '-';
            const swapStr = `${a.totalSwaps}${dirCh}`;
            const rwd = a.diffReward || 0;
            const rwdStr = rwd > 0 ? `+${rwd.toFixed(2)}` : rwd < 0 ? rwd.toFixed(2) : '-';

            let nextStr = '-';
            if (a.nextSwapAt > 0) {
                const remSec = Math.max(0, Math.floor((a.nextSwapAt - Date.now()) / 1000));
                nextStr = remSec > 0 ? formatDuration(remSec) : 'now';
            }

            const rwdColor = rwd > 0 ? chalk.yellow : rwd < 0 ? chalk.red : chalk.gray;
            const cethStr = (a.ceth || 0) > 0 ? (a.ceth).toFixed(6) : '-';
            const cethColor = (a.ceth || 0) > 0 ? chalk.hex('#627EEA') : chalk.gray;

            out.write(row(
                [padR(a.name, C.acc), trunc(a.status, C.status), padR(a.cc.toFixed(2), C.cc),
                 padR(a.usdcx.toFixed(4), C.usdcx), padR(cethStr, C.ceth),
                 padR(swapStr, C.swaps), padR(nextStr, C.next),
                 padR(rwdStr, C.reward), padR(up, C.up)],
                [chalk.cyan, chalk.white, chalk.green.bold, chalk.yellow, cethColor,
                 chalk.white.bold, chalk.magenta, rwdColor, chalk.gray]
            ) + '\n');
        }

        out.write(sep(widths, '-', '+', '+', '+') + '\n');
        const sumReward = this.accounts.reduce((s, a) => s + (a.diffReward || 0), 0);
        const sumTxns = this.accounts.reduce((s, a) => s + (a.diffTxns || 0), 0);
        const sumVol = this.accounts.reduce((s, a) => s + (a.monthVolume || 0), 0);
        const sesText = ' ' + chalk.white.bold('Session') + '  ' +
            chalk.gray('Swaps:') + chalk.green(`${sumSwaps}`) + '  ' +
            chalk.gray('Reward:') + chalk.yellow(`${sumReward >= 0 ? '+' : ''}${sumReward.toFixed(2)}CC`) + '  ' +
            chalk.gray('Tx:') + chalk.cyan(`${sumTxns >= 0 ? '+' : ''}${sumTxns}`) + '  ' +
            chalk.gray('Vol:') + chalk.magenta(`$${sumVol.toFixed(0)}`);
        out.write(fullSpan(sesText, widths) + '\n');
        out.write(sep(widths, '-', '+', '-', '+') + '\n');

        // ===== REKAP =====
        const hasRekap = this.accounts.some(a => a.modalCC > 0);
        if (hasRekap) {
            const RK = { name: 7, modal: 9, now: 9, loss: 9, rwd: 8, net: 9, mRwd: 9 };
            const rkWidths = [RK.name, RK.modal, RK.now, RK.loss, RK.rwd, RK.net, RK.mRwd];

            out.write('\n');
            out.write(sep(rkWidths, '-', '+', '-', '+') + '\n');
            out.write(fullSpan(' ' + chalk.white.bold('REKAP') + chalk.gray('  (CC value: real CC + USDCx via quote)'), rkWidths) + '\n');
            out.write(sep(rkWidths, '-', '+', '+', '+') + '\n');

            out.write(row(
                [padR('Akun', RK.name), padR('Modal', RK.modal), padR('Now', RK.now),
                 padR('Loss', RK.loss), padR('Rwd', RK.rwd), padR('Net', RK.net), padR('Monthly', RK.mRwd)],
                Array(7).fill(gray)
            ) + '\n');
            out.write(sep(rkWidths, '-', '+', '+', '+') + '\n');

            let tModal = 0, tNow = 0, tLoss = 0, tRwd = 0, tNet = 0, tMRwd = 0;
            for (const a of this.accounts) {
                if (!(a.modalCC > 0)) continue;
                const modal = a.modalCC;
                const nowCC = a.nowCC || 0;
                const loss = modal - nowCC;
                const rwdVal = a.diffReward || 0;
                const mRwd = a.monthReward || 0;
                const net = rwdVal - loss;

                tModal += modal; tNow += nowCC; tLoss += loss;
                tRwd += rwdVal; tNet += net; tMRwd += mRwd;

                const lossStr = `${loss >= 0 ? '-' : '+'}${Math.abs(loss).toFixed(2)}`;
                const rwdStr = `+${rwdVal.toFixed(2)}`;
                const mRwdStr = `+${mRwd.toFixed(2)}`;
                const netStr = net >= 0 ? `+${net.toFixed(2)}` : `${net.toFixed(2)}`;

                out.write(row(
                    [padR(a.name, RK.name), padR(modal.toFixed(2), RK.modal), padR(nowCC.toFixed(2), RK.now),
                     padR(lossStr, RK.loss), padR(rwdStr, RK.rwd), padR(netStr, RK.net), padR(mRwdStr, RK.mRwd)],
                    [chalk.cyan, chalk.white, chalk.white, chalk.red, chalk.yellow,
                     net >= 0 ? chalk.green : chalk.red, chalk.magenta]
                ) + '\n');
            }

            out.write(sep(rkWidths, '-', '+', '+', '+') + '\n');
            const tLossStr = `${tLoss >= 0 ? '-' : '+'}${Math.abs(tLoss).toFixed(2)}`;
            const tRwdStr = `+${tRwd.toFixed(2)}`;
            const tMRwdStr = `+${tMRwd.toFixed(2)}`;
            const tNetStr = tNet >= 0 ? `+${tNet.toFixed(2)}` : `${tNet.toFixed(2)}`;
            out.write(row(
                [padR('TOTAL', RK.name), padR(tModal.toFixed(2), RK.modal), padR(tNow.toFixed(2), RK.now),
                 padR(tLossStr, RK.loss), padR(tRwdStr, RK.rwd), padR(tNetStr, RK.net), padR(tMRwdStr, RK.mRwd)],
                [chalk.white.bold, chalk.white.bold, chalk.white.bold, chalk.red, chalk.yellow,
                 tNet >= 0 ? chalk.green.bold : chalk.red.bold, chalk.magenta.bold]
            ) + '\n');
            out.write(sep(rkWidths, '-', '+', '-', '+') + '\n');
        }
    },

    startAutoRefresh() {
        if (this._timer) return;
        this._timer = setInterval(() => this._scheduleRender(), 5000);
    },

    stop() {
        if (this._timer) { clearInterval(this._timer); this._timer = null; }
    },
};

// ---------- Session ------------------------------------------------------

function createSession() {
    return {
        walletToken: null,
        swapToken: null,
        partyId: null,
        keyPair: null,
        keyPairs: null,
        matchIdx: 0,
        walletLoginTime: 0,
        swapLoginTime: 0,

        async refreshWalletToken(walletApi, log) {
            log('[auth] refreshing wallet token');
            await retryOnNetwork(async () => {
                const { challenge } = await walletApi.getChallenge(this.partyId);
                const sig = toHex(signMessage(this.keyPair.privateKey, challenge));
                const { access_token } = await walletApi.login(this.partyId, challenge, sig);
                this.walletToken = access_token;
                this.walletLoginTime = Date.now();
            }, { baseDelay: 3, label: 'refreshWallet', log });
        },

        async refreshSwapToken(swapApi, log) {
            log('[auth] refreshing swap token');
            await retryOnNetwork(async () => {
                const { nonce } = await swapApi.getNonce();
                const swapAuth = await swapApi.bindSignature(nonce, this.partyId);
                this.swapToken = swapAuth.accessToken;
                this.swapLoginTime = Date.now();
            }, { baseDelay: 3, label: 'refreshSwap', log });
        },

        async ensureFreshTokens(walletApi, swapApi, log) {
            const now = Date.now();
            if (this.walletLoginTime && (now - this.walletLoginTime) > TOKEN_MAX_AGE_MS) {
                try { await this.refreshWalletToken(walletApi, log); } catch (e) { log(`[warn] wallet refresh: ${formatError(e)}`); }
            }
            if (this.swapLoginTime && (now - this.swapLoginTime) > TOKEN_MAX_AGE_MS) {
                try { await this.refreshSwapToken(swapApi, log); } catch (e) { log(`[warn] swap refresh: ${formatError(e)}`); }
            }
        },

        async withRetry(fn, tokenType, walletApi, swapApi, log, opts = {}) {
            return await retryOnNetwork(async () => {
                try {
                    return await fn();
                } catch (err) {
                    if (err.response?.status === 401) {
                        if (tokenType === 'swap') await this.refreshSwapToken(swapApi, log);
                        else await this.refreshWalletToken(walletApi, log);
                        return await fn();
                    }
                    throw err;
                }
            }, { baseDelay: 3, label: 'apiCall', log, throwOnRateLimit: opts.throwOnRateLimit || false });
        },
    };
}

// ---------- Resolve Active Order ----------------------------------------

async function resolveActiveOrder(ctx) {
    const { session, swapApi, walletApi, log } = ctx;
    const TERMINAL = ['COMPLETED', 'CANCELLED', 'REFUNDED', 'FAILED'];
    try {
        const active = await swapApi.getActiveOrder(session.swapToken, {});
        if (!active?.orderId || TERMINAL.includes(active.status)) return false;
        log(`[recover] active order ${shortId(active.orderId)} (${active.status})`);
        const maxPolls = Math.ceil((config.retry?.max_resume_poll_minutes ?? 30) * 60 / 5);
        for (let p = 0; p < maxPolls; p++) {
            await sleep(5);
            if (p % 12 === 0 && p > 0) await session.ensureFreshTokens(walletApi, swapApi, log);
            try {
                const st = await swapApi.getOrderStatus(session.swapToken, active.orderId);
                if (TERMINAL.includes(st.status)) {
                    log(`[recover] order ${shortId(active.orderId)} = ${st.status}`);
                    return true;
                }
            } catch (pe) {
                if (pe.response?.status === 401) { await session.refreshSwapToken(swapApi, log); continue; }
                break;
            }
        }
        log('[recover] resume timeout, will try cancel');
        try { await swapApi.cancelOrder(session.swapToken, active.orderId); } catch { /* ignore */ }
        return true;
    } catch { return false; }
}

// ---------- Validate Offer ----------------------------------------------

function isOfferSafe(offer, partyId) {
    // Receiver must be self
    const receiver = offer.receiver_party_id || offer.receiverPartyId;
    if (receiver && receiver !== partyId) return false;
    // Amount must be positive
    const amount = parseFloat(offer.amount || 0);
    if (!isFinite(amount) || amount <= 0) return false;
    // Instrument must be in our known list
    const inst = offer.instrument_id || offer.instrumentId || '';
    const knownInstruments = ['Amulet', 'CC (Amulet)', 'CC', 'USDCx', 'USDCX'];
    if (inst && !knownInstruments.includes(inst)) return false;
    return true;
}

// ---------- Accept Pending Offers ---------------------------------------

async function acceptPendingOffers(ctx) {
    const { session, walletApi, swapApi, log, ax } = ctx;
    let offers = [];
    try {
        const r = await session.withRetry(
            () => walletApi.getOffers(session.walletToken), 'wallet', walletApi, swapApi, log
        );
        offers = r.offers || [];
    } catch { return; }

    if (!offers.length) return;
    log(`[offers] ${offers.length} pending`);

    for (const offer of offers) {
        // SAFETY: validate offer before signing
        if (!isOfferSafe(offer, session.partyId)) {
            log(`[offers] skip suspicious: rcv=${offer.receiver_party_id || offer.receiverPartyId} amt=${offer.amount} inst=${offer.instrument_id || offer.instrumentId}`);
            continue;
        }

        const contractId = offer.contract_id || offer.contractId;
        const commandId = offer.command_id || offer.commandId;
        const instrumentId = offer.instrument_id || offer.instrumentId || 'USDCx';
        const amount = offer.amount || '?';

        try {
            const preparedTxB64 = offer.prepared_tx_b64 || offer.preparedTxB64;
            const hashB64 = offer.hash_b64 || offer.hashB64;

            if (preparedTxB64 && hashB64) {
                const signature = signMessage(session.keyPair.privateKey, Buffer.from(hashB64, 'base64'));
                await session.withRetry(() => walletApi.executeTransaction(session.walletToken, {
                    commandId, preparedTxB64,
                    signatureB64: toBase64(signature),
                    hashingSchemeVersion: offer.hashing_scheme_version || 'HASHING_SCHEME_VERSION_V2',
                }), 'wallet', walletApi, swapApi, log);
                log(`[offers] accepted ${amount} ${instrumentId}`);
            } else if (contractId) {
                let rawPrepare = null;
                for (const ep of ['/offer/accept/prepare', '/offers/accept/prepare', '/offers/accept']) {
                    try {
                        const authH = { ...BASE_HEADERS, Authorization: `Bearer ${session.walletToken}` };
                        rawPrepare = (await ax.post(`${BACKEND}${ep}`, {
                            contract_id: contractId, party_id: session.partyId,
                        }, { headers: authH })).data;
                        break;
                    } catch (e) {
                        if (e.response?.status !== 404) continue;
                    }
                }
                if (rawPrepare) {
                    const pTx = rawPrepare.prepared_tx_b64 || rawPrepare.preparedTxB64;
                    const pH = rawPrepare.hash_b64 || rawPrepare.hashB64;
                    if (pTx && pH) {
                        const signature = signMessage(session.keyPair.privateKey, Buffer.from(pH, 'base64'));
                        await session.withRetry(() => walletApi.executeTransaction(session.walletToken, {
                            commandId: rawPrepare.command_id || rawPrepare.commandId,
                            preparedTxB64: pTx,
                            signatureB64: toBase64(signature),
                            hashingSchemeVersion: rawPrepare.hashing_scheme_version || rawPrepare.hashingSchemeVersion || 'HASHING_SCHEME_VERSION_V2',
                        }), 'wallet', walletApi, swapApi, log);
                        log(`[offers] accepted ${amount} ${instrumentId}`);
                    }
                }
            }
        } catch (err) {
            log(`[offers] err: ${formatError(err)}`);
        }
    }
}

// ---------- Refresh Account Data ----------------------------------------

function parseHoldings(holdings) {
    let cc = 0, usdcx = 0, ceth = 0;
    for (const [tok, info] of Object.entries(holdings || {})) {
        if (tok === 'Amulet' || tok === 'CC (Amulet)' || tok === 'CC') cc = info.balance || 0;
        if (tok === 'USDCx' || tok === 'USDCX') usdcx = info.balance || 0;
        if (tok === 'CETH' || tok === 'cETH') ceth = info.balance || 0;
    }
    return { cc, usdcx, ceth };
}

function getInstrumentAdminId(holdings, assetKey) {
    const nameMap = {
        '0x0': ['Amulet', 'CC (Amulet)', 'CC'],
        'USDCX': ['USDCx', 'USDCX'],
        'CETH': ['cETH', 'CETH'],
    };
    const names = nameMap[assetKey] || [assetKey];
    for (const n of names) {
        if (holdings?.[n]?.instrument_admin_id) return holdings[n].instrument_admin_id;
    }
    return '';
}

// Cache: asset -> CC rate (how many CC per 1 unit of asset)
const _rateCache = {};

async function estimateTotalCCValue(swapApi, cc, usdcx, ceth = 0) {
    let total = cc;
    // USDCx -> CC
    if (usdcx > 0.01) {
        if (_rateCache['USDCX']) {
            total += usdcx * _rateCache['USDCX'];
        } else {
            try {
                const q = await swapApi.getQuote('CC', 'USDCX', 'CC', '0x0', usdcx);
                if (q?.receiveAmount) {
                    const recv = parseFloat(q.receiveAmount);
                    _rateCache['USDCX'] = recv / usdcx;
                    total += recv;
                }
            } catch { /* skip */ }
        }
    }
    // cETH -> CC (via cached rate or quote)
    if (ceth > 0.00001) {
        if (_rateCache['CETH']) {
            total += ceth * _rateCache['CETH'];
        } else {
            try {
                const q = await swapApi.getQuote('CC', 'CETH', 'CC', '0x0', ceth);
                if (q?.receiveAmount) {
                    const recv = parseFloat(q.receiveAmount);
                    _rateCache['CETH'] = recv / ceth;
                    total += recv;
                }
            } catch { /* skip */ }
        }
    }
    return total;
}

async function refreshAccountData(ctx, persistedState) {
    const { session, walletApi, swapApi, log, index } = ctx;
    const { holdings = {} } = await session.withRetry(
        () => walletApi.getBalance(session.walletToken), 'wallet', walletApi, swapApi, log
    );
    const { cc, usdcx, ceth } = parseHoldings(holdings);

    let rewardUpdate = {};
    try {
        const lb = await swapApi.getLeaderboard(session.partyId);
        const me = lb.requestedAddress || null;
        if (me) {
            const monthReward = parseFloat(me.rewardAccruedCc ?? 0);
            const monthVolume = parseFloat(me.rewardVolumeUsd ?? me.volumeUsd ?? 0);
            const monthTxns = parseInt(me.rewardSwapCount ?? me.swapCount ?? 0);
            const rank = parseInt(me.rank ?? me.position ?? 0);

            // Reward baseline from persistent state
            let diffTxns = 0, diffReward = 0;
            if (persistedState?.rewardBaseline?.txns != null) {
                diffTxns = monthTxns - persistedState.rewardBaseline.txns;
                diffReward = monthReward - persistedState.rewardBaseline.reward;
            }
            rewardUpdate = { monthReward, monthVolume, monthTxns, rank, diffTxns, diffReward };
        }
    } catch { /* skip */ }

    dashboard.update(index, { cc, usdcx, ceth, ...rewardUpdate });

    // Estimate total CC value (real CC + USDCx + cETH via quote/cache)
    try {
        const a = dashboard.accounts[index];
        if (!a.isSwapping) {
            const nowCC = await estimateTotalCCValue(swapApi, cc, usdcx, ceth);
            if (nowCC > 0) {
                if (!a.modalLocked) {
                    // Modal not locked yet -> sync both
                    dashboard.update(index, { modalCC: nowCC, nowCC });
                } else {
                    dashboard.update(index, { nowCC });
                }
            }
        }
    } catch { /* skip */ }

    return { holdings, cc, usdcx, ceth, ...rewardUpdate };
}

// ---------- Background Refresh ------------------------------------------

function startBackgroundRefresh(ctx, persistedStateRef) {
    const bg = config.background_refresh || {};
    if (bg.enabled === false) return null;
    const intervalSec = bg.interval_seconds || 300;

    const id = setInterval(async () => {
        const a = dashboard.accounts[ctx.index];
        if (a.isSwapping) return;
        try {
            await ctx.session.ensureFreshTokens(ctx.walletApi, ctx.swapApi, () => {});
            await refreshAccountData(ctx, persistedStateRef.value);
        } catch { /* silent */ }
    }, intervalSec * 1000);
    return id;
}

function stopBackgroundRefresh(id) {
    if (id) clearInterval(id);
}

// ---------- Execute Single Swap -----------------------------------------

async function executeSwap(ctx, { fromAsset, toAsset, amount, fromLabel, toLabel, instrumentAdminId }) {
    const { session, walletApi, swapApi, log } = ctx;

    try {
        log(`[quote] ${parseFloat(amount).toFixed(4)} ${fromLabel} -> ${toLabel}`);
        const quote = await swapApi.getQuote('CC', fromAsset, 'CC', toAsset, amount);
        log(`[quote] send=${parseFloat(quote.sendAmount).toFixed(2)} recv=${parseFloat(quote.receiveAmount).toFixed(4)} rate=${parseFloat(quote.rate).toFixed(4)}`);

        // Cache rate from real quote (more accurate than periodic test quotes)
        try {
            const send = parseFloat(quote.sendAmount), recv = parseFloat(quote.receiveAmount);
            if (send > 0 && recv > 0) {
                if (toAsset === '0x0') {
                    // X -> CC: rate = how many CC per 1 X
                    _rateCache[fromAsset] = recv / send;
                } else if (fromAsset === '0x0') {
                    // CC -> X: inverse = how many CC per 1 X
                    _rateCache[toAsset] = send / recv;
                }
            }
        } catch { /* skip */ }

        let orderId = generateOrderId();
        let order;
        try {
            order = await session.withRetry(
                () => swapApi.createOrder(session.swapToken, orderId, quote.quoteId, session.partyId),
                'swap', walletApi, swapApi, log, { throwOnRateLimit: true }
            );
        } catch (createErr) {
            const status = createErr.response?.status;
            const detail = String(createErr.response?.data?.detail || '');

            if (status === 429) return { error: true, code: 'RATE_LIMITED', message: '[429] Rate limited' };

            if (status === 422) {
                log(`[err] 422 ${detail || 'rejected'}`);
                const delays = config.retry?.server_rejected_delays || [15, 30, 60];
                const maxRetry = config.retry?.max_422_retries ?? 3;
                let recovered = false;
                for (let r = 0; r < maxRetry; r++) {
                    const d = getEscalatingDelay(r, delays);
                    log(`[wait] 422 retry ${formatDuration(d)} (#${r + 1}/${maxRetry})`);
                    await sleep(d);
                    try {
                        await session.ensureFreshTokens(walletApi, swapApi, log);
                        const newQuote = await swapApi.getQuote('CC', fromAsset, 'CC', toAsset, amount);
                        Object.assign(quote, newQuote);
                        const newOrderId = generateOrderId();
                        order = await swapApi.createOrder(session.swapToken, newOrderId, newQuote.quoteId, session.partyId);
                        orderId = newOrderId;
                        recovered = true;
                        break;
                    } catch (re) {
                        if (re.response?.status === 422) continue;
                        throw re;
                    }
                }
                if (!recovered) return { error: true, code: '422_EXHAUSTED', message: '[422] retries exhausted' };
            } else if (status === 409) {
                log('[recover] 409 active order, resolving');
                let staleId = createErr.response?.data?.message?.match(/ord_\w+/)?.[0]
                    || JSON.stringify(createErr.response?.data || {}).match(/ord_\w+/)?.[0]
                    || null;
                if (!staleId) {
                    try { staleId = (await swapApi.getActiveOrder(session.swapToken, {}))?.orderId; } catch { /* ignore */ }
                }
                if (staleId) {
                    try { await swapApi.cancelOrder(session.swapToken, staleId); log(`[recover] cancelled ${shortId(staleId)}`); } catch { /* ignore */ }
                }
                await acceptPendingOffers(ctx);
                await sleep(2);
                const newQuote = await swapApi.getQuote('CC', fromAsset, 'CC', toAsset, amount);
                Object.assign(quote, newQuote);
                order = await swapApi.createOrder(session.swapToken, orderId, newQuote.quoteId, session.partyId);
            } else {
                throw createErr;
            }
        }

        log(`[order] created ${shortId(orderId)}`);

        const instrumentId = ASSET_TO_INSTRUMENT[fromAsset] || fromAsset;
        log(`[transfer] ${order.requiredAmount} ${instrumentId}`);
        let rawPrepare = null;
        for (let r = 0; r < 3; r++) {
            try {
                rawPrepare = await session.withRetry(() => walletApi.prepareTransfer(session.walletToken, {
                    instrumentAdminId: instrumentAdminId || '',
                    instrumentId,
                    receiverPartyId: order.deposit.address,
                    amount: order.requiredAmount,
                    reason: orderId,
                    appName: 'swap-v1',
                    metadata: {},
                }), 'wallet', walletApi, swapApi, log, { throwOnRateLimit: true });
                break;
            } catch (pe) {
                const m = pe.response?.data?.detail || pe.response?.data?.message || pe.message;
                if (String(m).includes('No holdings') && r < 2) { await sleep(15); continue; }
                throw pe;
            }
        }

        const commandId = rawPrepare.command_id || rawPrepare.commandId;
        const preparedTxB64 = rawPrepare.prepared_tx_b64 || rawPrepare.preparedTxB64;
        const hashB64 = rawPrepare.hash_b64 || rawPrepare.hashB64;
        const hashingSchemeVersion = rawPrepare.hashing_scheme_version || rawPrepare.hashingSchemeVersion || 'HASHING_SCHEME_VERSION_V2';
        if (!preparedTxB64 || !hashB64) {
            log('[err] missing prepared_tx_b64 / hash_b64');
            return { error: true, code: 'NO_PREPARE', message: 'missing prepare data' };
        }

        const signature = signMessage(session.keyPair.privateKey, Buffer.from(hashB64, 'base64'));
        await session.withRetry(() => walletApi.executeTransaction(session.walletToken, {
            commandId, preparedTxB64,
            signatureB64: toBase64(signature),
            hashingSchemeVersion,
        }), 'wallet', walletApi, swapApi, log, { throwOnRateLimit: true });

        log('[transfer] executed, waiting confirm');
        for (let p = 0; p < 20; p++) {
            await sleep(3);
            try {
                const st = await walletApi.getTransferStatus(session.walletToken, commandId);
                if (st.status === 'success') { log('[transfer] confirmed'); break; }
            } catch { /* continue */ }
        }

        await sleep(3);
        const finalStatus = await pollOrderStatus(ctx, orderId, 10, toAsset);

        if (finalStatus === 'COMPLETED' || finalStatus === 'WALLET_CONFIRMED') {
            log(`[order] ${finalStatus}`);
            await acceptPendingOffers(ctx);
            return { receiveAmount: quote.receiveAmount, orderId };
        } else if (finalStatus === 'TIMEOUT') {
            log('[order] timeout, cancel');
            try { await swapApi.cancelOrder(session.swapToken, orderId); } catch { /* ignore */ }
            return { error: true, code: 'TIMEOUT', message: 'order timeout' };
        } else {
            log(`[order] ${finalStatus}`);
            return { error: true, code: finalStatus, message: `order ${finalStatus}` };
        }
    } catch (err) {
        if (err.response?.status === 429) return { error: true, code: 'RATE_LIMITED', message: '[429] Rate limited' };
        log(`[err] swap: ${formatError(err)}`);
        return { error: true, code: err.response?.status || err.code, message: err.response?.data?.detail || err.message };
    }
}

// ---------- Poll Order Status -------------------------------------------

async function pollOrderStatus(ctx, orderId, maxMinutes = 10, toAsset = null) {
    const { session, walletApi, swapApi, log } = ctx;
    const TERMINAL = ['COMPLETED', 'CANCELLED', 'REFUNDED', 'FAILED'];
    const ICONS = { COMPLETED: '+', FAILED: '!', CANCELLED: 'x', FUNDED: '$', EXECUTING: '~', PROCESSING: '~', WITHDRAWING: '>', AWAITING_DEPOSIT: '.' };
    const maxPolls = Math.ceil(maxMinutes * 60 / 5); // FIXED: was * 31

    let lastStatus = '', stuckSince = 0, pollCount = 0;
    let preBalance = null;
    if (toAsset) {
        try {
            const { holdings = {} } = await session.withRetry(
                () => walletApi.getBalance(session.walletToken), 'wallet', walletApi, swapApi, log
            );
            const { cc, usdcx } = parseHoldings(holdings);
            preBalance = toAsset === '0x0' ? cc : usdcx;
        } catch { preBalance = 0; }
    }

    async function walletSideCheck() {
        if (!toAsset) return false;
        try {
            const r = await session.withRetry(
                () => walletApi.getOffers(session.walletToken), 'wallet', walletApi, swapApi, log
            );
            if ((r.offers?.length || 0) > 0) {
                try { await acceptPendingOffers(ctx); } catch { /* ignore */ }
                return true;
            }
            const { holdings = {} } = await session.withRetry(
                () => walletApi.getBalance(session.walletToken), 'wallet', walletApi, swapApi, log
            );
            const { cc, usdcx } = parseHoldings(holdings);
            const cur = toAsset === '0x0' ? cc : usdcx;
            if (preBalance != null && cur > preBalance + 0.01) return true;
        } catch { /* ignore */ }
        return false;
    }

    let netErrors = 0;
    while (pollCount < maxPolls) {
        try {
            const { status } = await retryOnNetwork(
                () => swapApi.getOrderStatus(session.swapToken, orderId),
                { baseDelay: 3, label: 'pollStatus', log }
            );
            netErrors = 0;
            if (status !== lastStatus) {
                log(`[order] ${ICONS[status] || '.'} ${status} (${pollCount * 5}s)`);
                lastStatus = status;
                stuckSince = pollCount;
            }
            if (status === 'CANCELLED' || status === 'FAILED') {
                if (await walletSideCheck()) return 'WALLET_CONFIRMED';
                return status;
            }
            if (TERMINAL.includes(status)) return status;

            const stuck = pollCount - stuckSince;
            if (toAsset && stuck >= 3 && stuck % 2 === 0) {
                if (await walletSideCheck()) return 'WALLET_CONFIRMED';
            }
        } catch (err) {
            if (err.response?.status === 401) { await session.refreshSwapToken(swapApi, log); continue; }
            netErrors++;
            log(`[poll] err ${netErrors}/10 ${formatError(err)}`);
            if (netErrors >= 3 && netErrors % 2 === 1) {
                if (await walletSideCheck()) return 'WALLET_CONFIRMED';
            }
            if (netErrors >= 10) {
                if (await walletSideCheck()) return 'WALLET_CONFIRMED';
                throw err;
            }
            await sleep(10);
        }
        pollCount++;
        await sleep(5);
    }
    return 'TIMEOUT';
}

// ---------- Round-Trip Engine -------------------------------------------

async function runRoundTrip(ctx, persistedStateRef) {
    const { session, walletApi, swapApi, log, index } = ctx;
    const sw = config.swap;
    const intervalMs = sw.interval_minutes * 60 * 1000;
    const jitterMs = (sw.interval_jitter_seconds || 0) * 1000;
    const bufferMs = (sw.interval_buffer_seconds || 30) * 1000;
    const dustReserve = sw.usdcx_dust_reserve ?? 0.0001;
    const minUsdcx = sw.min_usdcx_for_swap ?? 1;
    const rewardThreshold = sw.reward_landed_threshold ?? 100;
    const maxSwaps = sw.max_swaps || 100;

    log(`[plan] interval=${sw.interval_minutes}m+/-${Math.round(jitterMs / 60000)}m buffer=${sw.interval_buffer_seconds}s amt=${sw.amount_min}-${sw.amount_max}CC`);

    let state = persistedStateRef.value;
    let consecutiveFailures = 0;
    const MAX_CONSECUTIVE_FAILURES = 5;

    // Lock modal CC value at start (so REKAP shows real loss/profit)
    {
        const a = dashboard.accounts[index];
        if (a.modalCC > 0 && !a.modalLocked) {
            dashboard.update(index, { modalLocked: true });
            log(`[rekap] modal locked at ${a.modalCC.toFixed(2)} CC`);
        }
    }

    // ===== RECOVERY: cETH leftover (from old triangular bot) =====
    // If account has cETH balance, swap cETH -> USDCx first (NOT cETH -> CC).
    // This counts as 1 TX in the rate-limit window. Next swap will be USDCx -> CC.
    const minCethRecovery = sw.min_ceth_for_recovery ?? 0.0005;
    try {
        const refreshedInit = await refreshAccountData(ctx, state).catch(() => null);
        const cethInit = refreshedInit?.ceth ?? 0;
        const holdingsInit = refreshedInit?.holdings || {};

        if (cethInit >= minCethRecovery) {
            // Respect rate-limit: only do recovery if it's been long enough since last swap
            const sinceLast = state.lastSwapTimestamp === 0
                ? Infinity
                : Date.now() - state.lastSwapTimestamp;
            const requiredWait = intervalMs + bufferMs;

            if (sinceLast >= requiredWait) {
                log(`[recovery] cETH=${cethInit.toFixed(8)} -> USDCx (leftover from old bot)`);
                dashboard.update(index, { status: 'cETH->USDCx (recovery)', isSwapping: true });
                await resolveActiveOrder(ctx);

                const recResult = await executeSwap(ctx, {
                    fromAsset: 'CETH', toAsset: 'USDCX',
                    amount: cethInit,
                    fromLabel: 'cETH', toLabel: 'USDCx',
                    instrumentAdminId: getInstrumentAdminId(holdingsInit, 'CETH'),
                });

                dashboard.update(index, { isSwapping: false });

                if (recResult && !recResult.error) {
                    state.lastSwapTimestamp = Date.now();
                    state.lastDirection = 'CETH_TO_USDCX'; // Next will be USDCX_TO_CC (alternation logic)
                    state.totalTxCount += 1;

                    if (state.rewardBaseline.txns == null) {
                        const a = dashboard.accounts[index];
                        state.rewardBaseline = { txns: a.monthTxns, reward: a.monthReward };
                    }
                    saveState(session.partyId, state);
                    persistedStateRef.value = state;

                    dashboard.update(index, {
                        totalSwaps: state.totalTxCount,
                        lastDirection: 'CETH_TO_USDCX',
                    });
                    log(`[recovery] cETH->USDCx OK, recv=${parseFloat(recResult.receiveAmount).toFixed(4)} USDCx`);

                    // Refresh after recovery
                    await sleep(3);
                    try { await acceptPendingOffers(ctx); } catch { /* ignore */ }
                    await refreshAccountData(ctx, state).catch(() => null);
                } else {
                    log(`[recovery] cETH->USDCx failed: ${recResult?.message || 'unknown'} (will retry next interval)`);
                    // Don't update timestamp, will try again on next loop iteration
                }
            } else {
                const remaining = Math.ceil((requiredWait - sinceLast) / 1000);
                log(`[recovery] cETH detected (${cethInit.toFixed(8)}) but waiting rate-limit window (${formatDuration(remaining)})`);
            }
        }
    } catch (e) {
        log(`[recovery] cETH check error: ${formatError(e)}`);
    }
    // ===== END RECOVERY =====

    while (state.totalTxCount < maxSwaps) {
        // 1) Calculate next swap time (wall-clock anchored)
        let nextSwapAt;
        if (state.lastSwapTimestamp === 0) {
            // First TX ever for this account: go now
            nextSwapAt = Date.now();
        } else {
            // Subsequent TX: anchor to last successful swap time
            const jitter = jitterMs > 0 ? (Math.random() * 2 - 1) * jitterMs : 0;
            nextSwapAt = state.lastSwapTimestamp + intervalMs + bufferMs + jitter;
        }

        const waitMs = nextSwapAt - Date.now();
        dashboard.update(index, { nextSwapAt });

        if (waitMs > 0) {
            const waitSec = Math.ceil(waitMs / 1000);
            log(`[wait] next swap in ${formatDuration(waitSec)}`);
            dashboard.update(index, { status: `wait ${formatDuration(waitSec)}` });
            // Sleep in chunks so dashboard nextSwapAt updates smoothly
            const chunkSec = 30;
            let remaining = waitSec;
            while (remaining > 0) {
                const chunk = Math.min(chunkSec, remaining);
                await sleep(chunk);
                remaining -= chunk;
                // Refresh tokens periodically while waiting
                if (remaining > 0 && remaining % (10 * 60) === 0) {
                    try { await session.ensureFreshTokens(walletApi, swapApi, log); } catch { /* skip */ }
                }
            }
        }

        // 2) Refresh tokens, balance, offers
        try { await session.ensureFreshTokens(walletApi, swapApi, log); } catch { /* skip */ }
        try { await acceptPendingOffers(ctx); } catch { /* skip */ }

        const refreshed = await refreshAccountData(ctx, state).catch(() => null);
        const cc = refreshed?.cc ?? 0;
        const usdcx = refreshed?.usdcx ?? 0;
        const holdings = refreshed?.holdings || {};

        // 3) Reward landed -> stop
        if (cc >= rewardThreshold) {
            log(`[done] reward landed CC=${cc.toFixed(2)} >= ${rewardThreshold}`);
            dashboard.update(index, { status: 'reward-landed' });
            return;
        }

        // 4) Determine direction (alternate)
        let direction;
        if (state.lastDirection === 'CC_TO_USDCX' && usdcx >= minUsdcx) {
            direction = 'USDCX_TO_CC';
        } else if (state.lastDirection === 'USDCX_TO_CC') {
            direction = 'CC_TO_USDCX';
        } else if (usdcx >= minUsdcx) {
            // Recovery / first-run: if we have USDCx, swap that back first
            direction = 'USDCX_TO_CC';
        } else {
            direction = 'CC_TO_USDCX';
        }

        // 5) Determine amount
        let amount, fromAsset, toAsset, fromLabel, toLabel;
        if (direction === 'CC_TO_USDCX') {
            amount = randomFloat(sw.amount_min, sw.amount_max, 2);
            fromAsset = '0x0'; toAsset = 'USDCX';
            fromLabel = 'CC'; toLabel = 'USDCx';

            if (cc < amount) {
                log(`[skip] CC=${cc.toFixed(2)} < required ${amount.toFixed(2)}, fallback USDCX_TO_CC if possible`);
                if (usdcx >= minUsdcx) {
                    direction = 'USDCX_TO_CC';
                    amount = Math.max(0, usdcx - dustReserve);
                    fromAsset = 'USDCX'; toAsset = '0x0';
                    fromLabel = 'USDCx'; toLabel = 'CC';
                } else {
                    log(`[skip] insufficient balances, wait next interval`);
                    dashboard.update(index, { status: 'insufficient' });
                    state.lastSwapTimestamp = Date.now(); // pretend swap happened, wait full window
                    saveState(session.partyId, state);
                    persistedStateRef.value = state;
                    consecutiveFailures++;
                    if (consecutiveFailures >= MAX_CONSECUTIVE_FAILURES) {
                        log(`[fail] ${MAX_CONSECUTIVE_FAILURES}x consecutive insufficient, exiting`);
                        return;
                    }
                    continue;
                }
            }
        } else {
            // USDCX_TO_CC
            amount = Math.max(0, usdcx - dustReserve);
            fromAsset = 'USDCX'; toAsset = '0x0';
            fromLabel = 'USDCx'; toLabel = 'CC';
            if (amount < minUsdcx) {
                log(`[skip] USDCx=${usdcx.toFixed(4)} < min ${minUsdcx}, fallback CC_TO_USDCX`);
                direction = 'CC_TO_USDCX';
                amount = randomFloat(sw.amount_min, sw.amount_max, 2);
                fromAsset = '0x0'; toAsset = 'USDCX';
                fromLabel = 'CC'; toLabel = 'USDCx';
                if (cc < amount) {
                    log(`[skip] both balances low, wait next interval`);
                    dashboard.update(index, { status: 'insufficient' });
                    state.lastSwapTimestamp = Date.now();
                    saveState(session.partyId, state);
                    persistedStateRef.value = state;
                    consecutiveFailures++;
                    if (consecutiveFailures >= MAX_CONSECUTIVE_FAILURES) return;
                    continue;
                }
            }
        }

        // 6) Execute swap
        dashboard.update(index, { status: `${fromLabel}->${toLabel}`, isSwapping: true });
        await resolveActiveOrder(ctx);

        const result = await executeSwap(ctx, {
            fromAsset, toAsset, amount, fromLabel, toLabel,
            instrumentAdminId: getInstrumentAdminId(holdings, fromAsset),
        });

        dashboard.update(index, { isSwapping: false });

        if (!result || result.error) {
            consecutiveFailures++;
            log(`[fail] swap failed: ${result?.message || 'unknown'} (${consecutiveFailures}/${MAX_CONSECUTIVE_FAILURES})`);

            if (result?.code === 'RATE_LIMITED') {
                // Already rate-limited: anchor reset to now+61min so next attempt aligns
                state.lastSwapTimestamp = Date.now();
                saveState(session.partyId, state);
                persistedStateRef.value = state;
                log(`[wait] anchor reset for next 60m window`);
            } else {
                // Other failures: short retry without resetting anchor
                log(`[wait] retry in 60s (anchor preserved)`);
                dashboard.update(index, { status: 'retry-60s' });
                await sleep(60);
            }

            if (consecutiveFailures >= MAX_CONSECUTIVE_FAILURES) {
                log(`[fail] ${MAX_CONSECUTIVE_FAILURES}x failures, soft restart`);
                const e = new Error('TOO_MANY_FAILURES');
                e.response = { status: 500 };
                throw e;
            }
            continue;
        }

        // 7) SUCCESS: update state and anchor
        consecutiveFailures = 0;
        state.lastSwapTimestamp = Date.now();
        state.lastDirection = direction;
        state.totalTxCount += 1;

        // Set baseline on first successful swap
        if (state.rewardBaseline.txns == null) {
            const a = dashboard.accounts[index];
            state.rewardBaseline = {
                txns: a.monthTxns,
                reward: a.monthReward,
            };
        }
        saveState(session.partyId, state);
        persistedStateRef.value = state;

        dashboard.update(index, {
            totalSwaps: state.totalTxCount,
            lastDirection: direction,
        });
        log(`[ok] swap #${state.totalTxCount} ${direction} amt=${amount.toFixed(2)} recv=${parseFloat(result.receiveAmount).toFixed(4)}`);

        // 8) Refresh balance after swap
        await sleep(3);
        try { await acceptPendingOffers(ctx); } catch { /* skip */ }
        await refreshAccountData(ctx, state).catch(() => null);
    }

    log(`[done] reached max_swaps=${maxSwaps}`);
    dashboard.update(index, { status: 'done' });
}

// ---------- Per-Account Runner ------------------------------------------

const ACCOUNT_RETRY_BASE_DELAY = 15;

async function runAccount(accConfig, index) {
    const log = (msg) => dashboard.log(index, msg);
    for (let attempt = 1; ; attempt++) {
        try {
            await runAccountOnce(accConfig, index, log);
            return;
        } catch (err) {
            if (err.response?.status >= 500 || err.code === 'ERR_BAD_RESPONSE') {
                log(`[restart] soft 5s (${formatError(err)})`);
                dashboard.update(index, { status: 'soft-restart' });
                await sleep(5);
                attempt = Math.max(1, attempt - 1);
                continue;
            }
            log(`[err] ${formatError(err)}`);
            const delay = Math.min(ACCOUNT_RETRY_BASE_DELAY * Math.pow(1.5, attempt - 1), 120);
            log(`[restart] in ${Math.round(delay)}s (#${attempt})`);
            dashboard.update(index, { status: `restart #${attempt}` });
            await sleep(delay);
        }
    }
}

async function runAccountOnce(accConfig, index, log) {
    const ax = createAxiosInstance(accConfig.proxy || '');
    const walletApi = createWalletApi(ax);
    const swapApi = createSwapApi(ax);
    const session = createSession();

    if (accConfig.proxy) {
        log(`[proxy] ${accConfig.proxy.replace(/\/\/.*@/, '//***@')}`);
        const proxyHost = (accConfig.proxy.match(/@([^:/]+)/) || [])[1] || 'proxy';
        dashboard.update(index, { proxyHost });
    }

    // Step 1: derive keys
    dashboard.update(index, { status: 'deriving' });
    const keyPairs = generateKeyPairs(accConfig.mnemonic);

    // Step 2: recover account
    dashboard.update(index, { status: 'recover' });
    const recovery = await retryOnNetwork(
        () => walletApi.recoverAccount(keyPairs.map(k => k.publicKeyHex)),
        { baseDelay: 3, label: 'recover', log }
    );
    const matchIdx = (recovery.results || []).findIndex(r => r !== null);
    if (matchIdx === -1) throw new Error('No account found for mnemonic');
    const acct = recovery.results[matchIdx];
    log(`[party] ${shortId(acct.party_id)}`);

    // Step 3: login
    dashboard.update(index, { status: 'auth' });
    session.partyId = acct.party_id;
    session.keyPairs = keyPairs;
    session.matchIdx = matchIdx;
    session.keyPair = keyPairs[matchIdx];

    for (let a = 1; ; a++) {
        try {
            const { challenge } = await walletApi.getChallenge(acct.party_id);
            const sig = toHex(signMessage(keyPairs[matchIdx].privateKey, challenge));
            const { access_token } = await walletApi.login(acct.party_id, challenge, sig);
            session.walletToken = access_token;
            session.walletLoginTime = Date.now();
            break;
        } catch (err) {
            const is400Challenge = err.response?.status === 400 &&
                String(err.response?.data?.detail || err.response?.data?.message || '')
                    .toLowerCase().includes('challenge');
            if (is400Challenge) continue;
            if (!isRetryableError(err)) throw err;
            const d = Math.min(3 * Math.pow(2, a - 1), 30);
            log(`[login] ${formatError(err)} retry ${d}s (#${a})`);
            await sleep(d);
        }
    }
    log('[auth] ok');

    try {
        await walletApi.getRegisterStatus(session.walletToken);
        await walletApi.postConfirmV2(session.walletToken);
        await walletApi.getOutgoingExpired(session.walletToken);
    } catch { /* non-critical */ }

    // Step 4: swap auth
    dashboard.update(index, { status: 'swap-auth' });
    await retryOnNetwork(async () => {
        const { nonce } = await swapApi.getNonce();
        const swapAuth = await swapApi.bindSignature(nonce, session.partyId);
        session.swapToken = swapAuth.accessToken;
        session.swapLoginTime = Date.now();
    }, { baseDelay: 5, label: 'swapAuth', log });
    log('[swap-auth] ok');

    // Step 5: eligibility check (with bound)
    const maxElig = config.retry?.max_eligibility_attempts ?? 20;
    let eligOk = false;
    for (let e = 1; e <= maxElig; e++) {
        try {
            const r = await swapApi.checkEligibility(session.partyId);
            if (r.eligible) { eligOk = true; log('[eligible]'); break; }
            log(`[ineligible] retry 30s (#${e}/${maxElig})`);
            dashboard.update(index, { status: `ineligible #${e}` });
            await sleep(30);
            await session.ensureFreshTokens(walletApi, swapApi, log);
        } catch {
            // API error -> assume eligible
            eligOk = true;
            break;
        }
    }
    if (!eligOk) {
        log('[ineligible] exhausted, proceeding anyway');
    }

    // Step 6: load persistent state
    const persistedStateRef = { value: loadState(session.partyId) };
    log(`[state] loaded txCount=${persistedStateRef.value.totalTxCount} lastDir=${persistedStateRef.value.lastDirection || 'none'} lastSwap=${persistedStateRef.value.lastSwapTimestamp ? new Date(persistedStateRef.value.lastSwapTimestamp).toISOString() : 'never'}`);

    // Step 7: initial data + recovery
    const ctx = { session, walletApi, swapApi, log, name: accConfig.name, index, ax };
    await refreshAccountData(ctx, persistedStateRef.value);
    await resolveActiveOrder(ctx);

    // Step 8: background refresh
    const bgId = startBackgroundRefresh(ctx, persistedStateRef);

    // Step 9: round-trip engine
    try {
        if (config.swap.enabled) {
            await runRoundTrip(ctx, persistedStateRef);
        } else {
            log('[swap] disabled');
            dashboard.update(index, { status: 'idle' });
        }
    } finally {
        stopBackgroundRefresh(bgId);
    }

    log('[done]');
    dashboard.update(index, { status: 'done' });
}

// ---------- Proxy IP Logger ---------------------------------------------

async function fetchAndLogProxyIps(accounts) {
    const proxied = accounts.filter(a => a.proxy);
    if (!proxied.length) return;
    console.log(chalk.gray('  fetching proxy IPs...'));
    const endpoints = [
        { url: 'https://api.ipify.org?format=json', extract: r => r.data?.ip },
        { url: 'https://api4.my-ip.io/ip.json', extract: r => r.data?.ip },
        { url: 'https://ipinfo.io/json', extract: r => r.data?.ip },
        { url: 'https://api.ipify.org', extract: r => String(r.data).trim() },
    ];
    async function getIp(proxyUrl) {
        const ax = axios.create({
            httpAgent: new HttpProxyAgent(proxyUrl, { keepAlive: true, timeout: 20000 }),
            httpsAgent: new HttpsProxyAgent(proxyUrl, { keepAlive: true, timeout: 20000 }),
            proxy: false, timeout: 20000,
        });
        for (const ep of endpoints) {
            try {
                const r = await ax.get(ep.url);
                const ip = ep.extract(r);
                if (ip && ip.includes('.')) return ip;
            } catch { /* try next */ }
        }
        return 'FAILED';
    }
    const lines = [];
    for (const acc of accounts) {
        if (acc.proxy) {
            const ip = await getIp(acc.proxy);
            lines.push(ip);
            console.log(chalk.gray(`    ${acc.name}: ${chalk.cyan(ip)}`));
        } else {
            lines.push('no-proxy');
        }
    }
    const ts = new Date().toISOString().replace('T', ' ').slice(0, 19);
    writeFileSync(new URL('./proxy_ips.txt', import.meta.url), `# ${ts}\n` + lines.join('\n') + '\n', 'utf-8');
    console.log('');
}

// ---------- Main --------------------------------------------------------

async function main() {
    const accounts = config.accounts || [];
    if (!accounts.length) {
        console.error(chalk.red('No accounts configured'));
        process.exit(1);
    }

    process.stdout.write('\x1B[H\x1B[2J');
    console.log(chalk.cyan.bold(`  CANTOR8 ROUND-TRIP BOT v2.0 - ${accounts.length} account(s)\n`));

    await fetchAndLogProxyIps(accounts);

    dashboard.init(accounts);
    dashboard.startAutoRefresh();

    // Graceful shutdown
    const shutdown = (sig) => {
        console.log(chalk.yellow(`\n  received ${sig}, shutting down...`));
        dashboard.stop();
        // Give running ops a moment to finalize
        setTimeout(() => process.exit(0), 2000);
    };
    process.on('SIGINT', () => shutdown('SIGINT'));
    process.on('SIGTERM', () => shutdown('SIGTERM'));

    const staggerMin = config.stagger_min_seconds ?? 5;
    const staggerMax = config.stagger_max_seconds ?? 60;
    const delays = accounts.map((_, i) => i === 0 ? 0 : randomDelaySec(staggerMin, staggerMax));
    let cum = 0;
    console.log(chalk.gray('  stagger plan:'));
    for (let i = 0; i < accounts.length; i++) {
        cum += delays[i];
        console.log(chalk.gray(`    ${accounts[i].name}: t+${formatDuration(cum)}`));
    }
    console.log('');

    const results = await Promise.allSettled(
        accounts.map((acc, i) => {
            const total = delays.slice(0, i + 1).reduce((a, b) => a + b, 0);
            return new Promise(resolve => {
                setTimeout(async () => {
                    try { resolve(await runAccount(acc, i)); }
                    catch (err) { resolve(Promise.reject(err)); }
                }, total * 1000);
            });
        })
    );

    dashboard.stop();
    const ok = results.filter(r => r.status === 'fulfilled').length;
    const fail = results.filter(r => r.status === 'rejected').length;
    console.log(chalk.bold.green(`\n  done: ${ok} ok, ${fail} fail\n`));
}

main().catch(err => {
    console.error(chalk.red('fatal:'), err);
    process.exit(1);
});
