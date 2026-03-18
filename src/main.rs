use std::collections::{HashMap, HashSet, VecDeque};
use std::net::{Ipv4Addr, SocketAddr};
use std::sync::Arc;
use std::time::{Duration, Instant};

use base64::Engine;
use clap::Parser;
use once_cell::sync::Lazy;
use rand::RngCore;
use tokio::io::{AsyncReadExt, AsyncWriteExt, ReadHalf, WriteHalf};
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::Mutex;
use tokio::time::timeout;
use tracing::{debug, error, info, warn};

use aes::Aes256;
use ctr::cipher::{KeyIvInit, StreamCipher};
use ctr::Ctr128BE;

const DEFAULT_PORT: u16 = 1080;
const DC_FAIL_COOLDOWN: f64 = 60.0;
const WS_POOL_SIZE: usize = 4;
const WS_POOL_MAX_AGE: Duration = Duration::from_secs(120);

// ─── Telegram IP ranges ──────────────────────────────────────────────────────

static TG_RANGES: Lazy<Vec<(u32, u32)>> = Lazy::new(|| {
    vec![
        (ip_to_u32("185.76.151.0"),  ip_to_u32("185.76.151.255")),
        (ip_to_u32("149.154.160.0"), ip_to_u32("149.154.175.255")),
        (ip_to_u32("91.105.192.0"),  ip_to_u32("91.105.193.255")),
        (ip_to_u32("91.108.0.0"),    ip_to_u32("91.108.255.255")),
    ]
});

/// IP -> (dc_id, is_media)
static IP_TO_DC: Lazy<HashMap<&'static str, (u32, bool)>> = Lazy::new(|| {
    let mut m = HashMap::new();
    // DC1
    m.insert("149.154.175.50",  (1u32, false));
    m.insert("149.154.175.51",  (1, false));
    m.insert("149.154.175.53",  (1, false));
    m.insert("149.154.175.54",  (1, false));
    m.insert("149.154.175.52",  (1, true));
    // DC2
    m.insert("149.154.167.41",  (2, false));
    m.insert("149.154.167.50",  (2, false));
    m.insert("149.154.167.51",  (2, false));
    m.insert("149.154.167.220", (2, false));
    m.insert("95.161.76.100",   (2, false));
    m.insert("149.154.167.151", (2, true));
    m.insert("149.154.167.222", (2, true));
    m.insert("149.154.167.223", (2, true));
    m.insert("149.154.162.123", (2, true));
    // DC3
    m.insert("149.154.175.100", (3, false));
    m.insert("149.154.175.101", (3, false));
    m.insert("149.154.175.102", (3, true));
    // DC4
    m.insert("149.154.167.91",  (4, false));
    m.insert("149.154.167.92",  (4, false));
    m.insert("149.154.164.250", (4, true));
    m.insert("149.154.166.120", (4, true));
    m.insert("149.154.166.121", (4, true));
    m.insert("149.154.167.118", (4, true));
    m.insert("149.154.165.111", (4, true));
    // DC5
    m.insert("91.108.56.100",   (5, false));
    m.insert("91.108.56.101",   (5, false));
    m.insert("91.108.56.116",   (5, false));
    m.insert("91.108.56.126",   (5, false));
    m.insert("149.154.171.5",   (5, false));
    m.insert("91.108.56.102",   (5, true));
    m.insert("91.108.56.128",   (5, true));
    m.insert("91.108.56.151",   (5, true));
    m
});

// ─── Helpers ─────────────────────────────────────────────────────────────────

fn ip_to_u32(ip: &str) -> u32 {
    let p: Vec<u32> = ip.split('.').map(|x| x.parse().unwrap()).collect();
    (p[0] << 24) | (p[1] << 16) | (p[2] << 8) | p[3]
}

fn is_telegram_ip(ip: &str) -> bool {
    if ip.contains(':') { return false; } // IPv6 not supported
    let p: Vec<u32> = match ip.split('.').map(|x| x.parse::<u32>()).collect::<Result<Vec<_>, _>>() {
        Ok(v) if v.len() == 4 => v,
        _ => return false,
    };
    let n = (p[0] << 24) | (p[1] << 16) | (p[2] << 8) | p[3];
    TG_RANGES.iter().any(|&(lo, hi)| lo <= n && n <= hi)
}

fn human_bytes(mut n: f64) -> String {
    for unit in &["B", "KB", "MB", "GB"] {
        if n.abs() < 1024.0 { return format!("{:.1}{}", n, unit); }
        n /= 1024.0;
    }
    format!("{:.1}TB", n)
}

fn is_http_transport(data: &[u8]) -> bool {
    data.starts_with(b"POST ") || data.starts_with(b"GET ") ||
    data.starts_with(b"HEAD ") || data.starts_with(b"OPTIONS ")
}

fn xor_mask(data: &mut [u8], mask: &[u8; 4]) {
    for (i, b) in data.iter_mut().enumerate() { *b ^= mask[i & 3]; }
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{:02x}", x)).collect::<Vec<_>>().join("")
}

// ─── MTProto DC extraction ────────────────────────────────────────────────────

fn dc_from_init(data: &[u8]) -> (Option<u32>, bool) {
    if data.len() < 64 { return (None, false); }
    let key: [u8; 32] = data[8..40].try_into().unwrap();
    let iv:  [u8; 16] = data[40..56].try_into().unwrap();
    let mut cipher = Ctr128BE::<Aes256>::new(&key.into(), &iv.into());
    let mut ks = [0u8; 64];
    cipher.apply_keystream(&mut ks);
    let mut plain = [0u8; 8];
    for i in 0..8 { plain[i] = data[56 + i] ^ ks[56 + i]; }
    let proto  = u32::from_le_bytes(plain[0..4].try_into().unwrap());
    let dc_raw = i16::from_le_bytes(plain[4..6].try_into().unwrap());
    debug!("dc_from_init: proto=0x{:08X} dc_raw={} plain={}", proto, dc_raw, hex(&plain));
    if matches!(proto, 0xEFEFEFEF | 0xEEEEEEEE | 0xDDDDDDDD) {
        let dc = dc_raw.unsigned_abs() as u32;
        if (1..=5).contains(&dc) { return (Some(dc), dc_raw < 0); }
    }
    (None, false)
}

/// Patch dc_id bytes (60-61) inside the 64-byte encrypted init packet.
/// Android with useSecret=0 leaves those bytes random; the WS relay
/// needs a valid dc_id to route the connection correctly.
fn patch_init_dc(data: &mut [u8; 64], dc: u32, is_media: bool) {
    let dc_raw: i16 = if is_media { -(dc as i16) } else { dc as i16 };
    let new_dc = dc_raw.to_le_bytes();
    let key: [u8; 32] = data[8..40].try_into().unwrap();
    let iv:  [u8; 16] = data[40..56].try_into().unwrap();
    let mut cipher = Ctr128BE::<Aes256>::new(&key.into(), &iv.into());
    let mut ks = [0u8; 64];
    cipher.apply_keystream(&mut ks);
    data[60] = ks[60] ^ new_dc[0];
    data[61] = ks[61] ^ new_dc[1];
    debug!("init patched: dc_id -> {} (is_media={})", dc, is_media);
}

fn ws_domains(dc: u32, is_media: bool) -> Vec<String> {
    if is_media {
        vec![format!("kws{}-1.web.telegram.org", dc), format!("kws{}.web.telegram.org", dc)]
    } else {
        vec![format!("kws{}.web.telegram.org", dc), format!("kws{}-1.web.telegram.org", dc)]
    }
}

// ─── MTProto message splitter ─────────────────────────────────────────────────
//
// The Telegram WS relay processes one MTProto message per WS frame.
// Mobile clients batch multiple messages in one TCP write (msgs_ack +
// req_DH_params).  Sent as one WS frame, the relay only handles the
// first message and the DH handshake never completes.
//
// This splitter maintains a shadow AES-CTR decryptor to find abridged-
// protocol message boundaries in the ciphertext stream, then splits
// each chunk at those boundaries before wrapping into WS frames.

struct MsgSplitter {
    /// Shadow decryptor — we decrypt only to find boundaries, never use the plaintext
    cipher: Ctr128BE<Aes256>,
    /// Decrypted bytes not yet forming a complete MTProto message
    plain_pending: Vec<u8>,
    /// How many bytes of *ciphertext* correspond to plain_pending
    pending_cipher_len: usize,
}

impl MsgSplitter {
    fn new(init_data: &[u8; 64]) -> Self {
        let key: [u8; 32] = init_data[8..40].try_into().unwrap();
        let iv:  [u8; 16] = init_data[40..56].try_into().unwrap();
        let mut cipher = Ctr128BE::<Aes256>::new(&key.into(), &iv.into());
        // Advance keystream past the 64-byte init packet
        let mut skip = [0u8; 64];
        cipher.apply_keystream(&mut skip);
        MsgSplitter { cipher, plain_pending: Vec::new(), pending_cipher_len: 0 }
    }

    /// Decrypt `chunk`, find MTProto abridged boundaries, return ciphertext parts.
    fn split(&mut self, chunk: &[u8]) -> Vec<Vec<u8>> {
        // Decrypt the new chunk and append to pending plaintext
        let mut dec = chunk.to_vec();
        self.cipher.apply_keystream(&mut dec);
        self.plain_pending.extend_from_slice(&dec);
        self.pending_cipher_len += chunk.len();

        // Find complete MTProto abridged messages in plain_pending
        let mut boundaries: Vec<usize> = Vec::new(); // byte offsets in plain_pending
        let mut pos = 0usize;
        let pb = &self.plain_pending;
        while pos < pb.len() {
            let first = pb[pos];
            let (hdr_len, msg_len) = if first == 0x7f {
                if pos + 4 > pb.len() { break; }
                let n = (u32::from_le_bytes([pb[pos+1], pb[pos+2], pb[pos+3], 0]) & 0xFF_FFFF) as usize * 4;
                (4, n)
            } else {
                (1, first as usize * 4)
            };
            if msg_len == 0 || pos + hdr_len + msg_len > pb.len() { break; }
            pos += hdr_len + msg_len;
            boundaries.push(pos);
        }

        if boundaries.len() <= 1 {
            // One (possibly incomplete) message — send as-is, keep pending bytes
            // that were already consumed (pos) cleared
            let consumed_plain = pos.min(self.plain_pending.len());
            self.plain_pending.drain(..consumed_plain);
            self.pending_cipher_len -= consumed_plain.min(self.pending_cipher_len);
            return vec![chunk.to_vec()];
        }

        // Map plain boundaries to cipher boundaries.
        // Because AES-CTR is a byte-for-byte stream cipher, the byte offsets
        // in the plaintext correspond 1:1 to the same offsets in the ciphertext.
        // plain_pending holds bytes from cipher offset (total_processed - pending_cipher_len).
        let _plain_base = self.pending_cipher_len.saturating_sub(chunk.len());
        // chunk starts at (plain_pending.len() - dec.len()) within plain_pending
        let chunk_start_in_pending = self.plain_pending.len() - dec.len();

        let mut result: Vec<Vec<u8>> = Vec::new();
        let mut prev_in_chunk = 0usize;

        for boundary in &boundaries {
            // boundary is offset within plain_pending
            if *boundary <= chunk_start_in_pending { continue; }
            let end_in_chunk = boundary - chunk_start_in_pending;
            let end_in_chunk = end_in_chunk.min(chunk.len());
            if end_in_chunk > prev_in_chunk {
                result.push(chunk[prev_in_chunk..end_in_chunk].to_vec());
                prev_in_chunk = end_in_chunk;
            }
        }
        if prev_in_chunk < chunk.len() {
            result.push(chunk[prev_in_chunk..].to_vec());
        }
        if result.is_empty() { return vec![chunk.to_vec()]; }

        let consumed_plain = boundaries.last().copied().unwrap_or(pos);
        self.plain_pending.drain(..consumed_plain);
        self.pending_cipher_len = self.plain_pending.len();

        result
    }
}

// ─── Stats ────────────────────────────────────────────────────────────────────

#[derive(Default)]
pub struct Stats {
    pub connections_total:         u64,
    pub connections_ws:            u64,
    pub connections_tcp_fallback:  u64,
    pub connections_http_rejected: u64,
    pub connections_passthrough:   u64,
    pub ws_errors:                 u64,
    pub bytes_up:                  u64,
    pub bytes_down:                u64,
    pub pool_hits:                 u64,
    pub pool_misses:               u64,
}
impl Stats {
    pub fn summary(&self) -> String {
        let pool_total = self.pool_hits + self.pool_misses;
        format!(
            "total={} ws={} tcp_fb={} http_skip={} pass={} err={} pool={}/{} up={} down={}",
            self.connections_total, self.connections_ws, self.connections_tcp_fallback,
            self.connections_http_rejected, self.connections_passthrough, self.ws_errors,
            self.pool_hits, pool_total,
            human_bytes(self.bytes_up as f64), human_bytes(self.bytes_down as f64))
    }
}

// ─── WebSocket ────────────────────────────────────────────────────────────────

type TlsStream = tokio_native_tls::TlsStream<TcpStream>;

const OP_BINARY: u8 = 0x2;
const OP_CLOSE:  u8 = 0x8;
const OP_PING:   u8 = 0x9;
const OP_PONG:   u8 = 0xA;
const OP_TEXT:   u8 = 0x1;

#[derive(Debug)]
struct WsHandshakeError {
    status_code: u16,
    status_line: String,
    location:    Option<String>,
}
impl WsHandshakeError {
    fn is_redirect(&self) -> bool { matches!(self.status_code, 301|302|303|307|308) }
}
impl std::fmt::Display for WsHandshakeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "HTTP {}: {}", self.status_code, self.status_line)
    }
}
impl std::error::Error for WsHandshakeError {}

async fn ws_connect(
    ip: &str, domain: &str, path: &str, conn_timeout: Duration,
) -> Result<(ReadHalf<TlsStream>, WriteHalf<TlsStream>), Box<dyn std::error::Error + Send + Sync>> {
    let connector = native_tls::TlsConnector::builder()
        .danger_accept_invalid_certs(true)
        .danger_accept_invalid_hostnames(true)
        .build()?;
    let connector = tokio_native_tls::TlsConnector::from(connector);

    let tcp = timeout(conn_timeout, TcpStream::connect(format!("{}:443", ip))).await??;
    tcp.set_nodelay(true)?;
    let stream = timeout(conn_timeout, connector.connect(domain, tcp)).await??;

    let (mut rd, mut wr) = tokio::io::split(stream);

    let mut kb = [0u8; 16];
    rand::thread_rng().fill_bytes(&mut kb);
    let ws_key = base64::engine::general_purpose::STANDARD.encode(kb);
    let req = format!(
        "GET {} HTTP/1.1\r\nHost: {}\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n\
         Sec-WebSocket-Key: {}\r\nSec-WebSocket-Version: 13\r\nSec-WebSocket-Protocol: binary\r\n\
         Origin: https://web.telegram.org\r\n\
         User-Agent: Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 \
         (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36\r\n\r\n",
        path, domain, ws_key
    );
    timeout(conn_timeout, wr.write_all(req.as_bytes())).await??;

    let mut buf = Vec::with_capacity(512);
    let mut b = [0u8; 1];
    loop {
        timeout(conn_timeout, rd.read_exact(&mut b)).await??;
        buf.push(b[0]);
        if buf.ends_with(b"\r\n\r\n") { break; }
        if buf.len() > 16384 { return Err("Response headers too large".into()); }
    }

    let s = String::from_utf8_lossy(&buf);
    let mut lines = s.lines();
    let first = lines.next().unwrap_or("").to_string();
    let parts: Vec<&str> = first.splitn(3, ' ').collect();
    let code: u16 = parts.get(1).and_then(|x| x.parse().ok()).unwrap_or(0);
    debug!("WS handshake response: {}", first.trim());

    if code == 101 { return Ok((rd, wr)); }

    let mut headers = HashMap::new();
    for line in lines {
        if let Some((k, v)) = line.split_once(':') {
            headers.insert(k.trim().to_lowercase(), v.trim().to_string());
        }
    }
    Err(Box::new(WsHandshakeError {
        status_code: code,
        status_line: first,
        location: headers.get("location").cloned(),
    }))
}

fn ws_frame(opcode: u8, data: &[u8]) -> Vec<u8> {
    let mut frame = Vec::with_capacity(10 + data.len());
    frame.push(0x80 | opcode);
    let len = data.len();
    if      len < 126   { frame.push(0x80 | len as u8); }
    else if len < 65536 { frame.push(0x80 | 126); frame.extend_from_slice(&(len as u16).to_be_bytes()); }
    else                { frame.push(0x80 | 127); frame.extend_from_slice(&(len as u64).to_be_bytes()); }
    let mut mk = [0u8; 4];
    rand::thread_rng().fill_bytes(&mut mk);
    frame.extend_from_slice(&mk);
    let mut d = data.to_vec();
    xor_mask(&mut d, &mk);
    frame.extend_from_slice(&d);
    frame
}

async fn ws_read_frame(rd: &mut ReadHalf<TlsStream>) -> std::io::Result<(u8, Vec<u8>)> {
    let mut hdr = [0u8; 2];
    rd.read_exact(&mut hdr).await?;
    let opcode    = hdr[0] & 0x0F;
    let is_masked = hdr[1] & 0x80 != 0;
    let mut length = (hdr[1] & 0x7F) as u64;
    if length == 126 {
        let mut b = [0u8; 2]; rd.read_exact(&mut b).await?;
        length = u16::from_be_bytes(b) as u64;
    } else if length == 127 {
        let mut b = [0u8; 8]; rd.read_exact(&mut b).await?;
        length = u64::from_be_bytes(b);
    }
    let mask_key = if is_masked {
        let mut m = [0u8; 4]; rd.read_exact(&mut m).await?; Some(m)
    } else { None };
    let mut payload = vec![0u8; length as usize];
    rd.read_exact(&mut payload).await?;
    if let Some(mk) = mask_key { xor_mask(&mut payload, &mk); }
    Ok((opcode, payload))
}

// ─── WebSocket connection pool ────────────────────────────────────────────────

struct PoolEntry {
    rd:      ReadHalf<TlsStream>,
    wr:      WriteHalf<TlsStream>,
    created: Instant,
}

#[derive(Clone)]
pub struct WsPool {
    idle:      Arc<Mutex<HashMap<(u32, bool), VecDeque<PoolEntry>>>>,
    refilling: Arc<Mutex<HashSet<(u32, bool)>>>,
}

impl WsPool {
    fn new() -> Self {
        WsPool {
            idle:      Arc::new(Mutex::new(HashMap::new())),
            refilling: Arc::new(Mutex::new(HashSet::new())),
        }
    }

    async fn get(
        &self,
        dc: u32, is_media: bool,
        target_ip: String, domains: Vec<String>,
        stats: Arc<Mutex<Stats>>,
    ) -> Option<(ReadHalf<TlsStream>, WriteHalf<TlsStream>)> {
        let key = (dc, is_media);
        {
            let mut idle = self.idle.lock().await;
            let bucket = idle.entry(key).or_default();
            while let Some(entry) = bucket.pop_front() {
                if entry.created.elapsed() > WS_POOL_MAX_AGE { continue; }
                let left = bucket.len();
                debug!("WS pool hit for DC{}{} (age={:.1}s, left={})",
                    dc, if is_media {"m"} else {""}, entry.created.elapsed().as_secs_f64(), left);
                stats.lock().await.pool_hits += 1;
                self.schedule_refill(key, target_ip, domains);
                return Some((entry.rd, entry.wr));
            }
        }
        stats.lock().await.pool_misses += 1;
        self.schedule_refill(key, target_ip, domains);
        None
    }

    fn schedule_refill(&self, key: (u32, bool), target_ip: String, domains: Vec<String>) {
        let idle      = self.idle.clone();
        let refilling = self.refilling.clone();
        tokio::spawn(async move {
            {
                let mut r = refilling.lock().await;
                if r.contains(&key) { return; }
                r.insert(key);
            }
            let (dc, is_media) = key;
            let current_len = idle.lock().await.get(&key).map(|b| b.len()).unwrap_or(0);
            let needed = WS_POOL_SIZE.saturating_sub(current_len);
            if needed == 0 { refilling.lock().await.remove(&key); return; }

            let mut tasks = Vec::new();
            for _ in 0..needed {
                let ip   = target_ip.clone();
                let doms = domains.clone();
                tasks.push(tokio::spawn(async move {
                    for domain in &doms {
                        match ws_connect(&ip, domain, "/apiws", Duration::from_secs(8)).await {
                            Ok(halves) => return Some(halves),
                            Err(e) => {
                                if e.downcast_ref::<WsHandshakeError>()
                                    .map(|w| w.is_redirect()).unwrap_or(false) { continue; }
                                return None;
                            }
                        }
                    }
                    None
                }));
            }
            let mut added = 0usize;
            for t in tasks {
                if let Ok(Some((rd, wr))) = t.await {
                    idle.lock().await.entry(key).or_default()
                        .push_back(PoolEntry { rd, wr, created: Instant::now() });
                    added += 1;
                }
            }
            debug!("WS pool refilled DC{}{}: {} ready",
                dc, if is_media {"m"} else {""}, current_len + added);
            refilling.lock().await.remove(&key);
        });
    }

    pub async fn warmup(&self, dc_opt: &HashMap<u32, String>) {
        let count = dc_opt.len();
        for (dc, target_ip) in dc_opt {
            for is_media in [false, true] {
                let domains = ws_domains(*dc, is_media);
                self.schedule_refill((*dc, is_media), target_ip.clone(), domains);
            }
        }
        info!("WS pool warmup started for {} DC(s)", count);
    }
}

// ─── Shared state ─────────────────────────────────────────────────────────────

#[derive(Clone)]
pub struct ProxyState {
    pub dc_opt:        Arc<HashMap<u32, String>>,
    pub ws_blacklist:  Arc<Mutex<HashSet<(u32, bool)>>>,
    pub dc_fail_until: Arc<Mutex<HashMap<(u32, bool), Instant>>>,
    pub stats:         Arc<Mutex<Stats>>,
    pub ws_pool:       WsPool,
}

// ─── Bridge: TCP <-> WebSocket ────────────────────────────────────────────────

async fn bridge_ws(
    mut tcp_rd: tokio::net::tcp::OwnedReadHalf,
    mut tcp_wr: tokio::net::tcp::OwnedWriteHalf,
    mut ws_rd:  ReadHalf<TlsStream>,
    mut ws_wr:  WriteHalf<TlsStream>,
    label: String,
    dc: Option<u32>, dst: String, port: u16, is_media: bool,
    stats: Arc<Mutex<Stats>>,
    mut splitter: Option<MsgSplitter>,
) {
    let dc_tag  = dc.map(|d| format!("DC{}{}", d, if is_media {"m"} else {""})).unwrap_or_else(|| "DC?".to_string());
    let dst_tag = format!("{}:{}", dst, port);
    let sup  = stats.clone();
    let sdn  = stats.clone();
    let lu   = label.clone();
    let ld   = label.clone();
    let bytes_up   = Arc::new(std::sync::atomic::AtomicU64::new(0));
    let bytes_down = Arc::new(std::sync::atomic::AtomicU64::new(0));
    let bu2  = bytes_up.clone();
    let bd2  = bytes_down.clone();
    let start = Instant::now();

    // TCP → WS
    let t_up = tokio::spawn(async move {
        let mut buf = vec![0u8; 32768];
        loop {
            let n = match tcp_rd.read(&mut buf).await {
                Ok(0) | Err(_) => break,
                Ok(n) => n,
            };
            sup.lock().await.bytes_up += n as u64;
            bu2.fetch_add(n as u64, std::sync::atomic::Ordering::Relaxed);

            let parts: Vec<Vec<u8>> = if let Some(ref mut sp) = splitter {
                sp.split(&buf[..n])
            } else {
                vec![buf[..n].to_vec()]
            };

            for part in parts {
                let frame = ws_frame(OP_BINARY, &part);
                if ws_wr.write_all(&frame).await.is_err() { break; }
            }
        }
        debug!("[{}] tcp->ws ended", lu);
        let _ = ws_wr.write_all(&ws_frame(OP_CLOSE, b"")).await;
        let _ = ws_wr.shutdown().await;
    });

    // WS → TCP
    let t_dn = tokio::spawn(async move {
        loop {
            let (opcode, payload) = match ws_read_frame(&mut ws_rd).await {
                Ok(f) => f,
                Err(e) => { debug!("[{}] ws read error: {}", ld, e); break; }
            };
            match opcode {
                OP_CLOSE => { debug!("[{}] WS close received", ld); break; }
                OP_PING | OP_PONG => continue,
                OP_TEXT | OP_BINARY => {
                    sdn.lock().await.bytes_down += payload.len() as u64;
                    bd2.fetch_add(payload.len() as u64, std::sync::atomic::Ordering::Relaxed);
                    if tcp_wr.write_all(&payload).await.is_err() { break; }
                }
                _ => continue,
            }
        }
        debug!("[{}] ws->tcp ended", ld);
    });

    tokio::select! { _ = t_up => {}, _ = t_dn => {} }

    let elapsed = start.elapsed().as_secs_f64();
    info!("[{}] {} ({}) WS closed: ^{} v{} in {:.1}s",
        label, dc_tag, dst_tag,
        human_bytes(bytes_up.load(std::sync::atomic::Ordering::Relaxed) as f64),
        human_bytes(bytes_down.load(std::sync::atomic::Ordering::Relaxed) as f64),
        elapsed);
}

// ─── Bridge: TCP <-> TCP (fallback) ──────────────────────────────────────────

async fn pipe(mut r: tokio::net::tcp::OwnedReadHalf, mut w: tokio::net::tcp::OwnedWriteHalf,
              stats: Arc<Mutex<Stats>>, is_up: bool) {
    let mut buf = vec![0u8; 65536];
    loop {
        match r.read(&mut buf).await {
            Ok(0) | Err(_) => break,
            Ok(n) => {
                { let mut s = stats.lock().await;
                  if is_up { s.bytes_up += n as u64; } else { s.bytes_down += n as u64; } }
                if w.write_all(&buf[..n]).await.is_err() { break; }
            }
        }
    }
}

async fn pipe_plain(mut r: tokio::net::tcp::OwnedReadHalf, mut w: tokio::net::tcp::OwnedWriteHalf) {
    let mut buf = vec![0u8; 65536];
    loop {
        match r.read(&mut buf).await {
            Ok(0) | Err(_) => break,
            Ok(n) => { if w.write_all(&buf[..n]).await.is_err() { break; } }
        }
    }
}

async fn tcp_fallback(
    tcp_rd: tokio::net::tcp::OwnedReadHalf,
    tcp_wr: tokio::net::tcp::OwnedWriteHalf,
    dst: &str, port: u16, init: &[u8], label: &str,
    stats: Arc<Mutex<Stats>>,
) -> bool {
    let remote = match timeout(Duration::from_secs(10),
        TcpStream::connect(format!("{}:{}", dst, port))).await
    {
        Ok(Ok(s)) => s,
        _ => { warn!("[{}] TCP fallback to {}:{} failed", label, dst, port); return false; }
    };
    let _ = remote.set_nodelay(true);
    stats.lock().await.connections_tcp_fallback += 1;
    let (rr, mut rw) = remote.into_split();
    if rw.write_all(init).await.is_err() { return false; }
    let su = stats.clone(); let sd = stats.clone();
    let t1 = tokio::spawn(pipe(tcp_rd, rw, su, true));
    let t2 = tokio::spawn(pipe(rr, tcp_wr, sd, false));
    tokio::select! { _ = t1 => {}, _ = t2 => {} }
    true
}

// ─── SOCKS5 ───────────────────────────────────────────────────────────────────

fn socks5_reply(status: u8) -> [u8; 10] {
    let mut r = [0u8; 10];
    r[0] = 5; r[1] = status; r[2] = 0; r[3] = 1;
    r
}

// ─── Client handler ───────────────────────────────────────────────────────────

pub async fn handle_client(stream: TcpStream, state: ProxyState, peer: SocketAddr) {
    let label = format!("{}:{}", peer.ip(), peer.port());
    state.stats.lock().await.connections_total += 1;
    if let Err(e) = handle_inner(stream, state, &label).await {
        debug!("[{}] error: {}", label, e);
    }
}

async fn handle_inner(
    mut stream: TcpStream, state: ProxyState, label: &str,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let _ = stream.set_nodelay(true);

    // ── SOCKS5 greeting ───────────────────────────────────────────────────────
    let mut hdr = [0u8; 2];
    timeout(Duration::from_secs(10), stream.read_exact(&mut hdr)).await??;
    if hdr[0] != 5 {
        debug!("[{}] not SOCKS5 (ver={})", label, hdr[0]);
        return Ok(());
    }
    let mut methods = vec![0u8; hdr[1] as usize];
    timeout(Duration::from_secs(10), stream.read_exact(&mut methods)).await??;
    stream.write_all(&[0x05, 0x00]).await?;

    // ── SOCKS5 CONNECT ────────────────────────────────────────────────────────
    let mut req = [0u8; 4];
    timeout(Duration::from_secs(10), stream.read_exact(&mut req)).await??;
    if req[1] != 1 {
        stream.write_all(&socks5_reply(0x07)).await?;
        return Ok(());
    }

    let dst = match req[3] {
        1 => { let mut r = [0u8; 4]; stream.read_exact(&mut r).await?; Ipv4Addr::from(r).to_string() }
        3 => {
            let mut d = [0u8; 1]; stream.read_exact(&mut d).await?;
            let mut dom = vec![0u8; d[0] as usize]; stream.read_exact(&mut dom).await?;
            String::from_utf8_lossy(&dom).to_string()
        }
        4 => {
            // IPv6 not supported — read and reject with a clear error message
            let mut r = [0u8; 16]; stream.read_exact(&mut r).await?;
            let addr = std::net::Ipv6Addr::from(r);
            let mut pb = [0u8; 2]; stream.read_exact(&mut pb).await?;
            let port = u16::from_be_bytes(pb);
            error!(
                "[{}] IPv6 address detected: [{}]:{} — \
                 IPv6 addresses are not supported; disable IPv6 to continue using the proxy.",
                label, addr, port);
            stream.write_all(&socks5_reply(0x05)).await?;
            return Ok(());
        }
        _ => { stream.write_all(&socks5_reply(0x08)).await?; return Ok(()); }
    };
    let mut pb = [0u8; 2]; stream.read_exact(&mut pb).await?;
    let port = u16::from_be_bytes(pb);

    debug!("[{}] CONNECT {}:{}", label, dst, port);

    // ── Non-Telegram: passthrough ─────────────────────────────────────────────
    if !is_telegram_ip(&dst) {
        state.stats.lock().await.connections_passthrough += 1;
        debug!("[{}] passthrough -> {}:{}", label, dst, port);
        match timeout(Duration::from_secs(10), TcpStream::connect(format!("{}:{}", dst, port))).await {
            Ok(Ok(remote)) => {
                let _ = remote.set_nodelay(true);
                stream.write_all(&socks5_reply(0x00)).await?;
                let (cr, cw) = stream.into_split();
                let (rr, rw) = remote.into_split();
                tokio::select! {
                    _ = tokio::spawn(pipe_plain(cr, rw)) => {}
                    _ = tokio::spawn(pipe_plain(rr, cw)) => {}
                }
            }
            _ => {
                warn!("[{}] passthrough failed {}:{}", label, dst, port);
                stream.write_all(&socks5_reply(0x05)).await?;
            }
        }
        return Ok(());
    }

    // ── Telegram: accept SOCKS, read MTProto init ─────────────────────────────
    stream.write_all(&socks5_reply(0x00)).await?;

    let mut init = [0u8; 64];
    match timeout(Duration::from_secs(15), stream.read_exact(&mut init)).await {
        Ok(Ok(_)) => {}
        _ => { debug!("[{}] client disconnected before init", label); return Ok(()); }
    }

    debug!("[{}] init[0..8] = {}", label, hex(&init[..8]));

    if is_http_transport(&init) {
        state.stats.lock().await.connections_http_rejected += 1;
        debug!("[{}] HTTP transport rejected", label);
        return Ok(());
    }

    // ── Extract DC ────────────────────────────────────────────────────────────
    let (dc_opt_val, mut is_media) = dc_from_init(&init);
    let mut init_patched = false;

    let dc_id = if let Some(dc) = dc_opt_val {
        Some(dc)
    } else {
        // Android with useSecret=0 — look up by destination IP and patch init
        if let Some(&(dc, media)) = IP_TO_DC.get(dst.as_str()) {
            if state.dc_opt.contains_key(&dc) {
                is_media = media;
                patch_init_dc(&mut init, dc, is_media);
                init_patched = true;
            }
            Some(dc)
        } else {
            None
        }
    };

    info!("[{}] {}:{} DC={:?} media={}", label, dst, port, dc_id, is_media);

    let dc = match dc_id {
        Some(d) if state.dc_opt.contains_key(&d) => d,
        other => {
            warn!("[{}] unknown DC{:?} for {}:{} -> TCP fallback", label, other, dst, port);
            let (cr, cw) = stream.into_split();
            tcp_fallback(cr, cw, &dst, port, &init, label, state.stats).await;
            return Ok(());
        }
    };

    let dc_key = (dc, is_media);
    let now    = Instant::now();
    let mt     = if is_media { " media" } else { "" };

    // ── WS blacklist ──────────────────────────────────────────────────────────
    if state.ws_blacklist.lock().await.contains(&dc_key) {
        debug!("[{}] DC{}{} blacklisted -> TCP", label, dc, mt);
        let (cr, cw) = stream.into_split();
        tcp_fallback(cr, cw, &dst, port, &init, label, state.stats).await;
        return Ok(());
    }

    // ── Cooldown ──────────────────────────────────────────────────────────────
    {
        let m = state.dc_fail_until.lock().await;
        if let Some(&until) = m.get(&dc_key) {
            if now < until {
                let secs = until.duration_since(now).as_secs();
                debug!("[{}] DC{}{} cooldown ({}s) -> TCP", label, dc, mt, secs);
                drop(m);
                let (cr, cw) = stream.into_split();
                tcp_fallback(cr, cw, &dst, port, &init, label, state.stats).await;
                return Ok(());
            }
        }
    }

    // ── Try WebSocket (pool first, then direct) ───────────────────────────────
    let domains = ws_domains(dc, is_media);
    let target  = state.dc_opt[&dc].clone();
    let mut ws_halves: Option<(ReadHalf<TlsStream>, WriteHalf<TlsStream>)> = None;
    let mut ws_failed_redirect = false;
    let mut all_redirects      = true;

    ws_halves = state.ws_pool.get(dc, is_media, target.clone(), domains.clone(), state.stats.clone()).await;
    if ws_halves.is_some() {
        info!("[{}] DC{}{} ({}:{}) -> pool hit via {}", label, dc, mt, dst, port, target);
    } else {
        for domain in &domains {
            info!("[{}] DC{}{} ({}:{}) -> wss://{}/apiws via {}", label, dc, mt, dst, port, domain, target);
            match ws_connect(&target, domain, "/apiws", Duration::from_secs(10)).await {
                Ok(halves) => {
                    info!("[{}] DC{}{} WS connected OK via {}", label, dc, mt, domain);
                    all_redirects = false;
                    ws_halves = Some(halves);
                    break;
                }
                Err(e) => {
                    state.stats.lock().await.ws_errors += 1;
                    if let Some(we) = e.downcast_ref::<WsHandshakeError>() {
                        if we.is_redirect() {
                            ws_failed_redirect = true;
                            warn!("[{}] DC{}{} got {} from {} -> {:?}", label, dc, mt, we.status_code, domain, we.location);
                            continue;
                        }
                        all_redirects = false;
                        warn!("[{}] DC{}{} WS handshake error: {}", label, dc, mt, we.status_line);
                    } else {
                        all_redirects = false;
                        warn!("[{}] DC{}{} WS connect failed: {}", label, dc, mt, e);
                    }
                }
            }
        }
    }

    // ── WS failed: fallback ───────────────────────────────────────────────────
    if ws_halves.is_none() {
        if ws_failed_redirect && all_redirects {
            state.ws_blacklist.lock().await.insert(dc_key);
            warn!("[{}] DC{}{} blacklisted (all 302)", label, dc, mt);
        } else {
            let until = now + Duration::from_secs_f64(DC_FAIL_COOLDOWN);
            state.dc_fail_until.lock().await.insert(dc_key, until);
            info!("[{}] DC{}{} WS cooldown {}s", label, dc, mt, DC_FAIL_COOLDOWN as u64);
        }
        info!("[{}] DC{}{} -> TCP fallback {}:{}", label, dc, mt, dst, port);
        let (cr, cw) = stream.into_split();
        tcp_fallback(cr, cw, &dst, port, &init, label, state.stats).await;
        return Ok(());
    }

    // ── WS success: send init, start bridging ─────────────────────────────────
    state.dc_fail_until.lock().await.remove(&dc_key);
    state.stats.lock().await.connections_ws += 1;

    let (ws_rd, mut ws_wr) = ws_halves.unwrap();

    // Splitter only needed when init was patched (Android useSecret=0)
    let splitter = if init_patched { Some(MsgSplitter::new(&init)) } else { None };

    ws_wr.write_all(&ws_frame(OP_BINARY, &init)).await?;
    debug!("[{}] sent init frame ({} bytes)", label, init.len());

    let (tcp_rd, tcp_wr) = stream.into_split();
    bridge_ws(tcp_rd, tcp_wr, ws_rd, ws_wr, label.to_string(),
              Some(dc), dst, port, is_media, state.stats, splitter).await;
    Ok(())
}

// ─── Stats logger ─────────────────────────────────────────────────────────────

pub async fn log_stats_task(state: ProxyState) {
    loop {
        tokio::time::sleep(Duration::from_secs(60)).await;
        let stats  = state.stats.lock().await;
        let bl     = state.ws_blacklist.lock().await;
        let bl_str = if bl.is_empty() { "none".to_string() } else {
            let mut v: Vec<String> = bl.iter()
                .map(|(d,m)| format!("DC{}{}", d, if *m {"m"} else {""})).collect();
            v.sort(); v.join(", ")
        };
        info!("stats: {} | ws_bl: {}", stats.summary(), bl_str);
    }
}

// ─── CLI / main ───────────────────────────────────────────────────────────────

#[derive(Parser, Debug)]
#[command(name = "tg-ws-proxy", about = "Telegram Desktop WebSocket Bridge Proxy (Rust)")]
struct Args {
    #[arg(long, default_value_t = DEFAULT_PORT)]
    port: u16,
    #[arg(long, default_value = "127.0.0.1")]
    host: String,
    #[arg(long = "dc-ip", value_name = "DC:IP")]
    dc_ip: Vec<String>,
    #[arg(short, long)]
    verbose: bool,
}

pub fn parse_dc_ip_list(list: &[String]) -> Result<HashMap<u32, String>, String> {
    let mut map = HashMap::new();
    for entry in list {
        match entry.split_once(':') {
            Some((dc_s, ip_s)) => {
                let dc: u32 = dc_s.parse().map_err(|_| format!("Invalid DC in {:?}", entry))?;
                ip_s.parse::<Ipv4Addr>().map_err(|_| format!("Invalid IP in {:?}", entry))?;
                map.insert(dc, ip_s.to_string());
            }
            None => return Err(format!("Invalid --dc-ip {:?}, expected DC:IP", entry)),
        }
    }
    Ok(map)
}

#[tokio::main]
async fn main() {
    let mut args = Args::parse();
    if args.dc_ip.is_empty() {
        args.dc_ip = vec![
            "2:149.154.167.220".to_string(),
            "4:149.154.167.220".to_string(),
        ];
    }

    let level = if args.verbose { "debug" } else { "info" };
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::try_from_default_env()
            .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new(level)))
        .with_target(false)
        .init();

    let dc_opt = match parse_dc_ip_list(&args.dc_ip) {
        Ok(m) => m,
        Err(e) => { error!("{}", e); std::process::exit(1); }
    };

    let state = ProxyState {
        dc_opt:        Arc::new(dc_opt),
        ws_blacklist:  Arc::new(Mutex::new(HashSet::new())),
        dc_fail_until: Arc::new(Mutex::new(HashMap::new())),
        stats:         Arc::new(Mutex::new(Stats::default())),
        ws_pool:       WsPool::new(),
    };

    let addr      = format!("{}:{}", args.host, args.port);
    let addr_ip   = args.host.clone();
    let addr_port = args.port;
    let listener  = match TcpListener::bind(&addr).await {
        Ok(l) => l,
        Err(e) => { error!("Failed to bind {}: {}", addr, e); std::process::exit(1); }
    };

    info!("{}", "=".repeat(60));
    info!("  Telegram WS Bridge Proxy (Rust)");
    info!("  Listening on   {}", addr);
    info!("  Target DC IPs:");
    let mut dcs: Vec<_> = state.dc_opt.iter().collect();
    dcs.sort_by_key(|(k, _)| **k);
    for (dc, ip) in &dcs { info!("    DC{}: {}", dc, ip); }
    info!("{}", "=".repeat(60));
    info!("  Configure Telegram Desktop:");
    info!("    SOCKS5 proxy -> {}:{}  (no user/pass)", addr_ip, addr_port);
    info!("{}", "=".repeat(60));

    tokio::spawn(log_stats_task(state.clone()));
    state.ws_pool.warmup(&state.dc_opt).await;

    loop {
        match listener.accept().await {
            Ok((stream, peer)) => {
                let s = state.clone();
                tokio::spawn(async move { handle_client(stream, s, peer).await; });
            }
            Err(e) => error!("Accept error: {}", e),
        }
    }
}
