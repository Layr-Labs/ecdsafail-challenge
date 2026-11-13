//! frogdrop point addition: (x, y) += (ox, oy) on secp256k1, affine, in place, with the 3-of-4 Euclid traversal
//! (frogdrop_col) as the inversion core. Same outer structure as froghop-double's point addition (two divisions,
//! measurement-based erasure of dy and lambda after Luo et al. / gnuchev):
//!
//!   dx = x - ox, dy = y - oy
//!   division 1:  forward traversal on dx (passenger dy) -> inv = 1/dx;  lambda = inv * dy;  measure dy away;
//!                inverse traversal -> dx;  recompute dy = lambda * dx, fix its phase, uncompute
//!   x:  dx' = lambda^2 - dx - 3 ox;   y:  ndy = -lambda * dx';  measure lambda away
//!   division 2:  forward traversal on dx' -> inv';  recompute lambda = -ndy * inv', fix its phase, uncompute;
//!                inverse traversal -> dx'
//!   x3 = dx' + ox,  y3 = ndy - oy

use super::builder::{B, G};
use super::frogdrop_col::{column, pool_size, traversal_end, ColPar, ColScr, Fd};
use super::frogdrop_sched::{from_text, Sched, L0};
use super::modp_frogdrop::{ctrl_neg, ctrl_neg_nm, load_bits, mac, modadd, modsub, product, product_nf, Ms};
use super::field_consume_fifth::product_consume_five_high_clean;
use crate::circuit::{BitId, QubitId};

pub const SCHED_FROGDROP: &str = include_str!("sched_frogdrop.txt");
/// q765-MAP: drop the last TRIM columns of the schedule. A walk needing more than 203 - TRIM columns fails; in
/// 4,000,000 sample() walks the longest needs 197 (P(len >= 197) = 2.5e-7). FD: 16,000,000 walks: 15 need >= 197
/// (lambda 0.017 at TRIM 7), 4 need >= 199 (TRIM 5: lambda about 0.0045). Env override FD_TRIM.
pub const TRIM: usize = 5;
pub fn trim() -> usize {
    static P: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_TRIM").ok().and_then(|v| v.trim().parse::<usize>().ok()).unwrap_or(TRIM))
}
pub fn sched() -> super::frogdrop_sched::Sched {
    let mut s = from_text(&sched_text());
    let n = s.cols.len() - trim();
    s.cols.truncate(n);
    s
}
/// LAM: count-build overrides of the schedule text (LAM_SCHED = path) and the switch threshold (LAM_L0).
fn sched_text() -> String {
    std::env::var("LAM_SCHED").map(|p| std::fs::read_to_string(p).unwrap()).unwrap_or_else(|_| SCHED_FROGDROP.to_string())
}
fn lam_l0() -> usize { std::env::var("LAM_L0").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(L0) }

/// Machine constants.
pub const N: usize = 288;
pub const NQ: usize = 138;
pub const K: usize = 29;
pub const KP: usize = 25;
/// q765-C: count-build override of KP (FD_KP); inert in an empty environment.
pub fn kp() -> usize {
    static P: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_KP").ok().and_then(|v| v.trim().parse::<usize>().ok()).unwrap_or(KP))
}
/// FD (from pane C): deferred header erasure on every column, on by default with the HT fusion off
/// (C measured -129k); C_HDR_ALL=0 restores the parent (columns < 121 and 203 only).
pub fn hdr_all() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| !fuse_on() && std::env::var("C_HDR_ALL").map(|v| v.trim() != "0").unwrap_or(true))
}
pub const QB: usize = 24;
pub const TOT: usize = 83;
pub const TAIL: usize = 40;
pub const EMAX: usize = 28;
/// idle counter bits (max idle columns C - min(N - 1) ~ 103 < 2^7)
pub const CNTB: usize = 7;
/// size registers sy, sx (pair values have <= NQ < 2^8 bits)
pub const SW: usize = 8;
/// Extra column-pool lanes (lane CURVE): appended at the pool's end, they join the map's AND-carry bank (`andc`).
/// Peak = 770 + POOLX. Count-build override: FD_POOLX.
pub const POOLX: usize = 0;
/// How pinned signed-batch frames treat the POOLX lanes: 1 = not at all, 2 = in their rows' carry banks.
pub const POOLX_MODE: usize = 2;
/// Count-build switches (lane CURVE experiments): FD_NOFUSE (no fused HT pairs), FD_NOBATCH (no signed batches).
/// lane CURVE: fused HT column pairs (bulengerk R12; their layout is pinned to KP 30 and a 64-lane pool).
pub const FUSE: bool = false;
pub fn fuse_on() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| if std::env::var("FD_NOFUSE").is_ok() { false } else { FUSE || fuse765() })
}
/// q765-MAP: fused HT pairs on the 59-lane pool (KP < 30). The pair's kernel borrows Q[116..121) as the five
/// missing pool lanes, so only pairs whose columns all have m <= 116 fuse. Env FD_FUSE765=1.
pub const FUSE765: bool = true;
pub fn fuse765() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| FUSE765 || std::env::var("FD_FUSE765").is_ok())
}
/// Q window of a fused pair's kernel: 121 on the 64-lane pool, 116 when five lanes are borrowed from Q.
pub fn fuse_qcap() -> usize { if pool_size(kp(), QB, SW) >= 64 { 121 } else { 116 } }
/// col (odd, 121..=201) starts a fused HT pair.
pub(crate) fn fused_at(cols: &[ColPar], col: usize) -> bool {
    fuse_on() && (121..=201).contains(&col) && col % 2 == 1 && col + 1 < cols.len()
        && cols[col].m <= fuse_qcap() && cols[col + 1].m <= fuse_qcap()
}
/// q765-HRF: fused pure-HR column pairs (1,2), (3,4), ... up to column HRF_LAST (default 18). On by default (measured -1.49M expected T);
/// env FD_HRF=0 turns it off. See hrf.rs and notes/q765/HRF_progress.md.
pub const HRF: bool = true;
pub fn hrf_on() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_HRF").map(|v| v.trim() != "0").unwrap_or(HRF))
}
pub fn hrf_last() -> usize {
    static P: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("HRF_LAST").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(18))
}
/// col (odd) starts a fused HR pair (col, col + 1).
pub(crate) fn hrf_at(cols: &[ColPar], col: usize) -> bool {
    hrf_on() && col % 2 == 1 && col + 1 <= hrf_last() && col + 1 < cols.len() && super::hrf::pair_ok(&cols[col], &cols[col + 1])
}
/// lane CURVE: dy / ndy top bits consumed into the two traversal-parked products (parent 5). Override FD_CONSUME.
pub const CONSUME: usize = 5; // q765 v5-p5shell: was 11 (FD_CONSUME=5 of the count of record)
pub fn consume() -> usize {
    static P: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_CONSUME").ok().and_then(|v| v.trim().parse::<usize>().ok()).unwrap_or(CONSUME))
}
/// lane CURVE: classical offsets loaded 128 bits at a time (payload shell's modadd_cl) and the in-place squaring
/// Horner for dx' (parent: false). Override FD_NARROW=1.
pub const NARROW: bool = true;
pub fn narrow() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_NARROW").map(|v| v.trim() != "0").unwrap_or(NARROW))
}
/// lane CURVE: pinned-plan key padding for KP < 30 (count-build override FD_NAPAD).
pub fn napad() -> usize {
    static P: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_NAPAD").ok().and_then(|v| v.trim().parse::<usize>().ok()).unwrap_or(30usize.saturating_sub(kp())))
}
/// lane CURVE: flag-free products for the dy recompute and ndy (parent: false). Override FD_NF=1.
pub const NF: bool = false;
/// lane CURVE: division 1's product seed with the lazy Ms add (255-lane inv addend); false = parent seed. FD_P1MS=1.
pub const P1MS: bool = true;
pub fn p1ms() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_P1MS").map(|v| v.trim() != "0").unwrap_or(P1MS))
}
/// lane CURVE: division 2's consume product with the Ms rounds; inv's top P5MS bits ride in the product's top lanes
/// (0 = parent product). Override FD_P5MS.
pub const P5MS: usize = 5; // q765 v5-p5shell: was 11 (FD_P5MS=5)
/// FD: measured-activation consume seeds (P1, P5). Override FD_MSEED=0 for the parent seeds.
pub const MSEED: bool = true;
pub fn mseed() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_MSEED").map(|v| v.trim() != "0").unwrap_or(MSEED))
}
/// FD: P1 Horner rounds with the lazy Ms add (mod_double + ctrl_modadd255) instead of canonical_bank. FD_P1R=0: parent.
/// FD: signed-digit Horner rounds (fd_shell), uncontrolled adds. FD_SIGNED=0: controlled Ms rounds.
pub fn signed() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_SIGNED").map(|v| v.trim() != "0").unwrap_or(true))
}
pub fn p1r() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_P1R").map(|v| v.trim() != "0").unwrap_or(true))
}
pub fn p5ms() -> usize {
    static P: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_P5MS").ok().and_then(|v| v.trim().parse::<usize>().ok()).unwrap_or(P5MS))
}
/// lane CURVE: dy-recompute and ndy products consume the multiplier's (lambda's) top PCONSUME bits into the product's
/// top lanes (0 = parent products). Override FD_PCONSUME.
pub const PCONSUME: usize = 5;
pub fn pconsume() -> usize {
    static P: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_PCONSUME").ok().and_then(|v| v.trim().parse::<usize>().ok()).unwrap_or(PCONSUME))
}
pub fn nf_products() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_NF").map(|v| v.trim() != "0").unwrap_or(NF))
}
pub fn poolx_mode() -> usize {
    static P: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_POOLX_MODE").ok().and_then(|v| v.trim().parse::<usize>().ok()).unwrap_or(POOLX_MODE))
}
pub fn poolx() -> usize {
    static P: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_POOLX").ok().and_then(|v| v.trim().parse::<usize>().ok()).unwrap_or(POOLX))
}

pub(crate) fn ck(b: &mut B, name: &str) {
    if std::env::var("FROGDROP_CK").is_ok() {
        let (o, c, e) = b.census();
        eprintln!("ck {:24} live {} peak {} peak_op {} ops {} tof {} CENSUS ops {} ccx {} exp {:.3}", name, b.live, b.peak, b.peak_op, b.ops.len(),
                  b.tof, o, c, e);
        // census only (FROGDROP_CKRESET): per-stage peaks; the build's reported peak is then the last stage's
        if std::env::var("FROGDROP_CKRESET").is_ok() { b.peak = b.live; }
    }
}

fn base_par() -> ColPar {
    ColPar { n: N, nq: NQ, h: N - 257, k: K, kp: kp(), qb: QB, tot: TOT, sz: (0, 0), sy: (0, 0), smax: (0, 0), m: 0,
             tail: TAIL, emax: EMAX, hr: false, ht: false, sw: false, l0: lam_l0(), swl: (0, 0), dn: false, fin: false,
             nomap: false, tt: false, kpx: 0, qbx: 0, rp: false }
}

/// LAM: per-column counter-lane loans from env specs "lo-hi:+d,..." (LAM_KPX, LAM_QBX; count builds) or the
/// committed defaults. A done column may lend top lanes only while cnt < 2^(CNTB - lend) (cnt <= column - first_fin + 1).
fn lam_spec(var: &str, default: &str, ncol: usize) -> Vec<usize> {
    let s = std::env::var(var).unwrap_or_else(|_| default.to_string());
    let mut v = vec![0usize; ncol];
    for part in s.split(',').filter(|p| !p.trim().is_empty()) {
        let (r, d) = part.split_once(':').unwrap();
        let (lo, hi) = r.split_once('-').unwrap();
        let d: usize = d.trim().trim_start_matches('+').parse().unwrap();
        for c in lo.trim().parse::<usize>().unwrap()..=hi.trim().parse::<usize>().unwrap().min(ncol.saturating_sub(1)) { v[c] = d; }
    }
    v
}
/// Rho loans run into MAP's fused HT pairs (123/124 ..): the fused inverse's phase restore (ht_fusion_qphase::restore_phase)
/// reads only the live counter lanes (frogdrop_col::cnt_split). Before that fix, loans there gave phase garbage (FD stream i1).
pub const LAM_KPX_DEFAULT: &str = "0-96:+4,97-100:+4,101-108:+3,109-124:+2,125-156:+1";
pub const LAM_QBX_DEFAULT: &str = "0-96:+3";
/// DOSE: columns whose HT bq erasure uses the rounded predicate [rho < Xh] (no certified box; it only matters in the
/// inverse walk, which replays the erasure). Chosen from a random-input census only (notes/q765/DOSE_progress.md):
/// every column (the certified box is dropped): census +0.040 expected failing shots per 9,024 (143 in-domain
/// disagreements in 64M random walks; model checked against the real column on 21 flagged inputs), about -9.4M T.
/// Count-build override: DOSE_RP ("lo-hi:+1,..."; "" = none).
pub const DOSE_RP_DEFAULT: &str = "0-202:+1";
/// ENV: per-column width (lanes above the batch top) of the inverse batch rows' borrow chain; 0 = full height.
/// Count-build override: ENV_TRWC ("lo-hi:+w,..."; "" = full height everywhere). Default: table T2 from the selection sweep
/// (notes/q765/ENV_pricing.md): census lambda 0.0040 (selection) / 0.0046 (evaluation), -6.24M T.
pub const ENV_TRWC_DEFAULT: &str = "0-48:+12,49-57:+18,58-102:+24,103-109:+18,110-122:+12";

/// Per-column parameters from the schedule (envelopes clamped to the machine).
pub fn col_pars(sc: &Sched) -> (Vec<ColPar>, Option<ColPar>, ColPar) {
    let cl = |r: (usize, usize), hi: usize| (r.0.min(hi), r.1.min(hi));
    let ncol = sc.cols.len();
    let kpxv = lam_spec("LAM_KPX", LAM_KPX_DEFAULT, ncol);
    let qbxv = lam_spec("LAM_QBX", LAM_QBX_DEFAULT, ncol);
    let rpv = lam_spec("DOSE_RP", DOSE_RP_DEFAULT, ncol);
    let first_fin = sc.cols.iter().position(|e| e.fin).unwrap_or(ncol);
    let cols = sc.cols.iter().enumerate().map(|(i, e)| {
        let mut c = base_par();
        c.tt = i == 1; // j = 2: T = t = 1 when q_1 = 1 (dx > p/2, unreflected)
        c.hr = e.hr;
        c.ht = e.ht;
        c.sw = e.sw;
        c.dn = e.dn;
        c.fin = e.fin;
        c.sz = cl(e.sz, 256);
        c.sy = cl(e.sy, 255);
        c.smax = cl(e.smax, NQ);
        c.m = c.smax.1;
        c.swl = (e.swl.0.min(NQ), e.swl.1.min(NQ));
        c.kpx = kpxv[i];
        c.qbx = qbxv[i];
        c.rp = rpv[i] > 0;
        if c.dn {
            let lend = c.kpx + c.qbx;
            assert!(i + 1 >= first_fin);
            let cmax = i + 1 - first_fin + 1;
            assert!(lend == 0 || cmax < 1usize << (CNTB - lend), "LAM: column {i} cannot lend {lend} counter lanes (cnt <= {cmax})");
        }
        c
    }).collect();
    let mut b0 = base_par();
    b0.smax = cl(sc.b0, NQ);
    b0.m = b0.smax.1;
    let mut last = base_par();
    last.ht = true;
    last.nomap = true;
    last.sz = cl(sc.lsz, 255);
    last.sy = (1, 1);
    (cols, Some(b0), last)
}

/// A traversal's state between its forward and inverse runs.
pub(crate) struct Trav {
    pub(crate) fd: Fd,
    pub(crate) pool: Vec<QubitId>,
    /// qubits released after the forward run (|0> for every shot), re-acquired before the inverse
    parked: Vec<QubitId>,
}

/// Every Fd/pool qubit that is |0> after the forward run's cleanup: all but ring[0..256] (t_{N-1} in [0, 255),
/// the counter's top bit parked in lane 255) and cnt[0..6].
fn parked_of(t: &Trav) -> Vec<QubitId> {
    let mut v: Vec<QubitId> = t.fd.ring[256..].to_vec();
    v.extend(&t.fd.q);
    v.extend(&t.fd.sy);
    v.extend(&t.fd.sx);
    v.push(t.fd.ph);
    v.push(t.fd.cnt[CNTB - 1]);
    v.extend(&t.pool);
    v
}

/// Final constants of every shot: ring top lane 1, sy = 1, ph = 1. Then the counter's top bit moves into ring lane
/// 255 (t_{N-1} <= p / 2 < 2^255 leaves it 0).
fn final_consts(b: &mut B, fd: &Fd) {
    b.x(fd.ring[N - 1]);
    b.x(fd.sy[0]);
    b.x(fd.ph);
    b.swap(fd.cnt[CNTB - 1], fd.ring[255]);
}

/// One column (or the end) recorded, so the inverse traversal can replay it backwards.
fn rec_col(b: &mut B, fd: &mut Fd, cp: &ColPar, pool: &[QubitId], dirty: &[QubitId]) -> Vec<G> {
    let sc = ColScr::carve(pool, &fd.sx, dirty, kp(), QB, TAIL);
    b.begin();
    column(b, fd, cp, &sc);
    b.end()
}

/// Forward traversal on x' (reflected below 2^255, in `xq`): returns the traversal state and the 256 lanes holding
/// +-t_{N-1} (sign fixed by the caller).
pub(crate) fn trav_forward(b: &mut B, xq: &[QubitId], dirty: &[QubitId]) -> Trav {
    let mut ring: Vec<QubitId> = xq.to_vec();
    ring.extend(b.alloc_n(N - 256));
    let fd = Fd { ring, q: b.alloc_n(NQ), sy: b.alloc_n(SW), sx: b.alloc_n(SW), ph: b.alloc(), cnt: b.alloc_n(CNTB) };
    let pool = b.alloc_n(pool_size(kp(), QB, SW));
    let mut t = Trav { fd, pool, parked: vec![] };
    // HR(1): Z = x', Q = t_0 = 0, top = t_1 = 1, sy = 1
    b.x(t.fd.ring[N - 1]);
    b.x(t.fd.sy[0]);
    ck(b, "trav pre");
    b.prof.dump("pre");
    let (cols, b0, last) = col_pars(&sched());
    let fwdv = lam_spec("ENV_FWDC", ENV_TRWC_DEFAULT, cols.len());
    for (col, cp) in cols.iter().enumerate() {
        b.pctx(&format!("col{:03}",col),true);
        b.fwd_w = fwdv[col];
        if b.allow_booth && col >= 1 && fused_at(&cols, col - 1) { continue; }
        if b.allow_booth && col >= 1 && hrf_at(&cols, col - 1) { b.pctx(&format!("col{:03}",col),false); continue; }
        b.header_erasure_enabled = hdr_all() || col < 121 || col == 203;
        if b.allow_booth && hrf_at(&cols, col) {
            super::hrf::pair(b, &mut t.fd, cp, &cols[col + 1], &t.pool, dirty);
        } else if b.allow_booth && fused_at(&cols, col) {
            super::ht_fusion_pair::forward(b, &mut t.fd, cp, &cols[col + 1], &t.pool, dirty, col);
        } else {
            let sc = ColScr::carve(&t.pool, &t.fd.sx, dirty, kp(), QB, TAIL);
            column(b, &mut t.fd, cp, &sc);
        }
        b.pctx(&format!("col{:03}",col),false);
    }
    b.fwd_w = 0;
    b.pctx("colEND",true);
    b.header_erasure_enabled = true; // original final boundary203
    let pool = t.pool.clone();
    let carve = |sx: &[QubitId]| ColScr::carve(&pool, sx, dirty, kp(), QB, TAIL);
    traversal_end(b, &mut t.fd, b0.as_ref(), &last, &carve);
    b.pctx("colEND",false);
    b.prof.dump("FWD");
    ck(b, "trav post");
    final_consts(b, &t.fd);
    t.parked = parked_of(&t);
    b.free_n(&t.parked);
    t
}

/// Exact inverse of trav_forward (re-acquires the parked qubits, replays every column backwards, frees all).
fn trav_inverse(b: &mut B, mut t: Trav, dirty: &[QubitId]) {
    for &q in &t.parked {
        b.acquire(q);
    }
    final_consts(b, &t.fd);
    b.prof.dump("preinv");
    b.pctx("colEND",true);
    let (cols, b0, last) = col_pars(&sched());
    // the end: forward names at its start; traversal_end swaps sy/sx once when b0 is present
    b.header_erasure_enabled = true; // matched original final boundary203
    {
        let mut fd = Fd { ring: t.fd.ring.clone(), q: t.fd.q.clone(), sy: t.fd.sy.clone(), sx: t.fd.sx.clone(),
                          ph: t.fd.ph, cnt: t.fd.cnt.clone() };
        if b0.is_some() {
            std::mem::swap(&mut fd.sy, &mut fd.sx);
        }
        let start = (fd.sy.clone(), fd.sx.clone());
        let pool = t.pool.clone();
        let carve = |sx: &[QubitId]| ColScr::carve(&pool, sx, dirty, kp(), QB, TAIL);
        b.begin();
        traversal_end(b, &mut fd, b0.as_ref(), &last, &carve);
        let r = b.end();
        b.play(&r, true);
        t.fd.sy = start.0;
        t.fd.sx = start.1;
    }
    b.pctx("colEND",false);
    let trwv = lam_spec("ENV_TRWC", ENV_TRWC_DEFAULT, cols.len());
    for col in (0..cols.len()).rev() {
        b.pctx(&format!("col{:03}",col),true);
        b.trw_col = trwv[col];
        if b.allow_booth && col >= 1 && fused_at(&cols, col - 1) { continue; }
        if b.allow_booth && col >= 1 && hrf_at(&cols, col - 1) { b.pctx(&format!("col{:03}",col),false); continue; }
        let cp = &cols[col];
        b.header_erasure_enabled = hdr_all() || col < 121 || col == 203;
        if b.allow_booth && hrf_at(&cols, col) {
            // the pair keeps the sy/sx names; regenerate its recording and replay it backwards
            b.begin();
            super::hrf::pair(b, &mut t.fd, cp, &cols[col + 1], &t.pool, dirty);
            let r = b.end();
            b.play(&r, true);
            b.pctx(&format!("col{:03}",col),false);
            continue;
        }
        if b.allow_booth && fused_at(&cols, col) {
            super::ht_fusion_pair::inverse(b, &mut t.fd, cp, &cols[col + 1], &t.pool, dirty, col);
            continue;
        }
        // names at the column's start: every mapped column swapped them once
        if !cp.nomap {
            std::mem::swap(&mut t.fd.sy, &mut t.fd.sx);
        }
        let start = (t.fd.sy.clone(), t.fd.sx.clone());
        let r = rec_col(b, &mut t.fd, cp, &t.pool, dirty);
        b.play(&r, true);
        t.fd.sy = start.0;
        t.fd.sx = start.1;
        b.pctx(&format!("col{:03}",col),false);
    }
    b.trw_col = 0;
    b.prof.dump("INV");
    if b.prof.on && std::env::var("MAPPROF_STOP").is_ok() { eprintln!("MAPPROF_STOP after first inverse walk"); std::process::exit(0); }
    b.x(t.fd.ring[N - 1]);
    b.x(t.fd.sy[0]);
    b.free_n(&t.fd.ring[256..]);
    b.free_n(&t.fd.q);
    b.free_n(&t.fd.sy);
    b.free_n(&t.fd.sx);
    b.free(t.fd.ph);
    b.free_n(&t.fd.cnt);
    b.free_n(&t.pool);
}

/// Everything a division needs between its forward and inverse traversal.
struct Div {
    t: Trav,
}

/// 1/dx = (-1)^N t_{N-1} with N = C + 2 - cnt (cnt = 1 + idle columns): negate iff cnt[0] ^ (C & 1). Returns the
/// control (qubit, flip) meaning "negate iff qubit ^ flip".
fn sign_ctl(t: &Trav) -> (QubitId, bool) {
    let c = sched().cols.len();
    (t.fd.cnt[0], c % 2 == 1)
}

/// Forward traversal on dx (in `xq`): the inverse's magnitude t_{N-1} sits in xq[0..255].
fn div_forward(b: &mut B, xq: &[QubitId], dirty: &[QubitId]) -> (Div, Vec<QubitId>) {
    // Keep the boundary HMR masks through both traversals. Field products run
    // with recording suspended and preserve the retained inverse and sign.
    b.deferred_forward();
    let t = trav_forward(b, xq, dirty);
    b.deferred_suspend();
    let inv: Vec<QubitId> = t.fd.ring[0..255].to_vec();
    ck(b, "div_forward end");
    (Div { t }, inv)
}

fn div_inverse(b: &mut B, dv: Div, dirty: &[QubitId]) {
    b.deferred_inverse();
    trav_inverse(b, dv.t, dirty);
    b.deferred_finish();
}

/// z = a * y (mod p), negated iff neg.0 ^ neg.1 (when given), recorded.
fn rec_product_s(b: &mut B, ms: &Ms, z: &[QubitId], a: &[QubitId], y: &[QubitId], neg: Option<(QubitId, bool)>)
                 -> Vec<G> {
    b.begin();
    let mut zz = z.to_vec();
    product(b, ms, &mut zz, a, y);
    let mut pos: Vec<QubitId> = zz.clone();
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
    if let Some((c, flip)) = neg {
        if flip { b.x(c); }
        ctrl_neg(b, ms, z, Some(c), y);
        if flip { b.x(c); }
    }
    b.end()
}

/// rec_product_s with no clean scratch (flag-free modular adds): for the products made while a traversal is parked.
fn rec_product_nf(b: &mut B, z: &[QubitId], a: &[QubitId], y: &[QubitId], neg: Option<(QubitId, bool)>) -> Vec<G> {
    b.begin();
    let mut zz = z.to_vec();
    product_nf(b, &mut zz, a, y);
    let mut pos: Vec<QubitId> = zz.clone();
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
    if let Some((c, flip)) = neg {
        if flip { b.x(c); }
        ctrl_neg_nm(b, z, Some(c), y);
        if flip { b.x(c); }
    }
    b.end()
}

/// Parked-traversal product consuming y's top five bits in z[251..256].
/// On entry z[..251] is clean and ylow is the original y[..251]. On exit z
/// is the signed full product while ylow is preserved. Inverse replay restores
/// all five consumed top bits. The explicit clean flag is zero at both ends.
/// Sign borrows only ylow; scaling may temporarily borrow and restore source lanes.
/// The consumed top wires are outputs and are never borrowed.
fn rec_product_consume(b: &mut B, z: &[QubitId], a: &[QubitId], ylow: &[QubitId],
                       neg: Option<(QubitId, bool)>, clean: QubitId) -> Vec<G> {
    assert_eq!(z.len(), 256);
    assert_eq!(a.len(), 255);
    assert_eq!(ylow.len(), 256 - consume());
    assert!(ylow.iter().all(|q| !z.contains(q)));
    assert!(!z.contains(&clean) && !a.contains(&clean) && !ylow.contains(&clean));
    b.begin();
    let mut zz = z.to_vec();
    product_consume_five_high_clean(b, &mut zz, a, ylow, clean);
    // Modular doubling may relabel the product lanes. Restore the declared physical
    // output order before conditional sign, measurement phase, or partial transfer.
    let mut pos = zz;
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
    if let Some((c, flip)) = neg {
        if flip { b.x(c); }
        ctrl_neg_nm(b, z, Some(c), ylow);
        if flip { b.x(c); }
    }
    b.end()
}

/// z = a * y (mod p) recorded, so the caller can uncompute it.
fn rec_product(b: &mut B, ms: &Ms, z: &[QubitId], a: &[QubitId], y: &[QubitId], negate: bool) -> Vec<G> {
    b.begin();
    let mut zz = z.to_vec();
    product(b, ms, &mut zz, a, y);
    let mut pos: Vec<QubitId> = zz.clone();
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
    if negate {
        ctrl_neg(b, ms, z, None, y);
    }
    b.end()
}

pub fn point_add(b: &mut B) -> (Vec<QubitId>, Vec<QubitId>) {
    if std::env::var("FD_NOBATCH").is_ok() { b.signed_batch_enabled = false; }
    let x = b.alloc_n(256);
    let y = b.alloc_n(256);
    b.declare_qubits(0, &x);
    b.declare_qubits(1, &y);
    let ox: Vec<BitId> = b.declare_bits(2, 256);
    let oy: Vec<BitId> = b.declare_bits(3, 256);

    // dx, dy
    if narrow() {
        cl_op(b, &x, &ox, true, &y);
        cl_op(b, &y, &oy, true, &x);
    } else {
        let ms = Ms::alloc(b);
        let t = b.alloc_n(256);
        load_bits(b, &t, &ox);
        modsub(b, &ms, &x, &t, y[0]);
        load_bits(b, &t, &ox);
        load_bits(b, &t, &oy);
        modsub(b, &ms, &y, &t, x[0]);
        load_bits(b, &t, &oy);
        b.free_n(&t);
        ms.release(b);
    }
    let nl = 256 - consume();

    // ---------------- division 1
    ck(b, "-- division 1");
    let (dv, inv) = div_forward(b, &x, &y); super::fd_natinv::s0_park(b, &dv.t.fd.cnt, dv.t.fd.ring[255]);
    let sq = sign_ctl(&dv.t);
    // The top five dy bits are reversibly consumed into the product's top wires.
    // Only the preserved low 251 dy bits need measurement erasure and phase repair.
    let m1 = b.fresh_bits(nl);
    let mut debts1: Vec<BitId> = vec![];
    {
        let zlow = b.alloc_n(nl);
        let clean = b.alloc();
        let mut z = zlow.clone();
        z.extend_from_slice(&y[nl..256]);
        // Forward-only: HMR is emitted outside every B recording.
        let mut zz = z.clone();
        if p1ms() {
            let ms = Ms::alloc(b);
            if mseed() {
                let (zc, ic, y0, y1, k) = (zz.clone(), inv.clone(), y[0], y[1], ms.k);
                debts1 = super::fd_seed::seed_fwd(b, &zz, clean, k, 256 - nl, &inv, &mut |b: &mut B| {
                    ctrl_modadd255(b, &Ms { k }, &zc, &ic, clean, y0, y1);
                });
            } else {
                seed_ms255(b, &ms, &zz, &inv, &y[..nl], clean, 256 - nl);
            }
            if p1r() && signed() {
                let gp = super::fd_gidney::gidney_on();
                if gp { b.gpool = vec![clean]; }
                super::fd_shell::pre(b, &ms, &mut zz, &inv, y[0]);
                for i in (0..nl).rev() {
                    if gp { b.gpool.clear(); b.gpool.push(clean); b.gpool.extend_from_slice(&y[i + 1..nl]); }
                    super::fd_shell::sround(b, &ms, &mut zz, &inv, y[i], y[(i + 1) % nl]);
                    b.hmr_to(y[i], m1[i]);
                }
                if gp { b.gpool.clear(); b.gpool.push(clean); b.gpool.extend_from_slice(&y[..nl]); }
                super::fd_shell::post(b, &ms, &mut zz, &inv, y[0]);
                b.gpool.clear();
                ms.release(b);
            } else if p1r() {
                for i in (0..nl).rev() {
                    super::modp_frogdrop::mod_double(b, &ms, &mut zz, &inv);
                    ctrl_modadd255(b, &ms, &zz, &inv, y[i], y[(i + 1) % nl], y[(i + 2) % nl]);
                    b.hmr_to(y[i], m1[i]);
                }
                ms.release(b);
            } else {
            ms.release(b);
            for i in (0..nl).rev() {
                super::early_product_fifth::round(b, &mut zz, &inv, &y[..nl], i, clean, m1[i]);
            }
            }
        } else {
            super::early_product_fifth::product(b, &mut zz, &inv, &y[..nl], clean, &m1);
        }
        let mut pos = zz;
        for i in 0..256 {
            if pos[i] != z[i] {
                let j = pos.iter().position(|&q| q == z[i]).unwrap();
                b.swap(pos[i], pos[j]);
                pos.swap(i, j);
            }
        }
        let (c, flip) = sq;
        if flip { b.x(c); }
        ctrl_neg_nm(b, &z, Some(c), &y[..nl]);
        if flip { b.x(c); }
        ck(b, "lambda = inv * dy");
        for i in 0..nl { b.swap(zlow[i], y[i]); }
        b.free_n(&zlow);
        b.free(clean);
    }
    super::fd_natinv::s0_unpark(b, &dv.t.fd.cnt, dv.t.fd.ring[255]); div_inverse(b, dv, &y);
    ck(b, "div_inverse end");
    // dy = lambda * dx: recompute, fix the phase of the dy measurement, uncompute
    if pconsume() > 0 {
        let w = super::fd_natinv::p2w();
        let ms = Ms::alloc(b);
        let flag = b.alloc();
        let zlow = b.alloc_n(256 - w);
        let mut z = zlow.clone();
        z.extend_from_slice(&y[256 - w..]);
        if mseed() {
            let (zc, xc, d, k) = (z.clone(), x.clone(), y[0], ms.k);
            let mut dirty: Vec<QubitId> = y[..256 - w].to_vec();
            dirty.extend_from_slice(&x);
            let debts2 = super::fd_seed::seed_fwd(b, &z, flag, k, w, &dirty, &mut |b: &mut B| {
                super::modp_frogdrop::ctrl_modadd(b, &Ms { k }, &zc, &xc, flag, d);
            });
            b.begin();
            super::modp_frogdrop::ctrl_modadd(b, &Ms { k }, &z, &x, flag, y[0]);
            let addrec = b.end();
            let (nat, r) = if super::fd_natinv::on() { super::fd_natinv::rounds_fwd(b, &ms, &z, &y[..256 - w], &x, None, flag, super::fd_natinv::p2x()) } else { (super::fd_natinv::Nat::off(), rec_rounds_ms_w(b, &ms, &z, &y[..256 - w], &x, None, false)) };
            b.play(&r, false);
            if !debts1.is_empty() {
                super::fd_seed::pay_debts2(b, &z[256 - (256 - nl)..], &debts1, k, flag, &x);
            }
            for i in 0..nl {
                b.z_if(z[i], m1[i]);
            }
            b.play(&r, true);
            nat.inverse(b, &ms); super::fd_seed::seed_inv(b, &z, flag, k, w, &dirty, &addrec);
            super::fd_seed::pay_debts(b, &y[256 - w..], &debts2, k, &x);
        } else {
        let r = rec_product_consume_ms(b, &ms, &z, &y[..256 - w], &x, flag, false);
        b.play(&r, false);
        if !debts1.is_empty() {
            super::fd_seed::pay_debts(b, &z[256 - (256 - nl)..], &debts1, ms.k, &x);
        }
        for i in 0..nl {
            b.z_if(z[i], m1[i]);
        }
        b.play(&r, true);
        }
        b.free_n(&zlow);
        b.free(flag);
        ms.release(b);
    } else if nf_products() {
        let z = b.alloc_n(256);
        let r = rec_product_nf(b, &z, &y, &x, None);
        b.play(&r, false);
        for i in 0..nl {
            b.z_if(z[i], m1[i]);
        }
        b.play(&r, true);
        b.free_n(&z);
    } else {
        let ms = Ms::alloc(b);
        let z = b.alloc_n(256);
        let r = rec_product(b, &ms, &z, &y, &x, false);
        b.play(&r, false);
        for i in 0..nl {
            b.z_if(z[i], m1[i]);
        }
        b.play(&r, true);
        b.free_n(&z);
        ms.release(b);
    }

    // ---------------- x: dx' = lambda^2 - dx - 3 ox
    ck(b, "-- x: dx' = lambda^2 - ");
    if narrow() {
        let d = b.alloc();
        sq_horner(b, &x, &y, d);
        b.free(d);
        for _ in 0..3 {
            cl_op(b, &x, &ox, true, &y);
        }
    } else {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, None, &y);
        let t = b.alloc_n(256);
        for i in 0..256 {
            b.cx(y[i], t[i]);
        }
        let mut yy = y.clone();
        mac(b, &ms, &x, &t, &mut yy);
        assert_eq!(yy, y);
        for i in 0..256 {
            b.cx(y[i], t[i]);
        }
        load_bits(b, &t, &ox);
        for _ in 0..3 {
            modsub(b, &ms, &x, &t, y[0]);
        }
        load_bits(b, &t, &ox);
        b.free_n(&t);
        ms.release(b);
    }
    // ---------------- ndy = -lambda * dx', measure lambda away
    ck(b, "-- ndy = -lambda * dx',");
    let m2 = b.fresh_bits(256);
    let mut debts4: Vec<BitId> = vec![];
    let w4 = pconsume();
    let mut lambda_measured = false;
    if w4 > 0 {
        let ms = Ms::alloc(b);
        let flag = b.alloc();
        let zlow = b.alloc_n(256 - w4);
        let mut z = zlow.clone();
        z.extend_from_slice(&y[256 - w4..]);
        if mseed() {
            let (zc, xc, d, k) = (z.clone(), x.clone(), y[0], ms.k);
            let mut dirty: Vec<QubitId> = y[..256 - w4].to_vec();
            dirty.extend_from_slice(&x);
            debts4 = super::fd_seed::seed_fwd(b, &z, flag, k, w4, &dirty, &mut |b: &mut B| {
                super::modp_frogdrop::ctrl_modadd(b, &Ms { k }, &zc, &xc, flag, d);
            });
            if p4stream() {
                rounds_ms_w_stream(b, &ms, &z, &y[..256 - w4], &x, flag, &m2);
                lambda_measured = true;
            } else {
                let r = rec_rounds_ms_w(b, &ms, &z, &y[..256 - w4], &x, None, true);
                b.play(&r, false);
            }
        } else {
        let r = rec_product_consume_ms(b, &ms, &z, &y[..256 - w4], &x, flag, true);
        b.play(&r, false);
        }
        b.free(flag);
        ms.release(b);
        // lambda's low lanes are measured; its top w4 bits live on inside ndy (lambda = -ndy / dx')
        if !lambda_measured {
            for i in 0..256 - w4 {
                b.hmr_to(y[i], m2[i]);
            }
        }
        for i in 0..256 - w4 {
            b.swap(zlow[i], y[i]);
        }
        b.free_n(&zlow);
    } else if nf_products() {
        let z = b.alloc_n(256);
        b.begin();
        let mut zz = z.to_vec();
        product_nf(b, &mut zz, &y, &x);
        let mut pos: Vec<QubitId> = zz.clone();
        for i in 0..256 {
            if pos[i] != z[i] {
                let j = pos.iter().position(|&q| q == z[i]).unwrap();
                b.swap(pos[i], pos[j]);
                pos.swap(i, j);
            }
        }
        ctrl_neg_nm(b, &z, None, &x);
        let r = b.end();
        b.play(&r, false);
        for i in 0..256 {
            b.hmr_to(y[i], m2[i]);
        }
        for i in 0..256 {
            b.swap(z[i], y[i]);
        }
        b.free_n(&z);
    } else {
        let ms = Ms::alloc(b);
        let z = b.alloc_n(256);
        let r = rec_product(b, &ms, &z, &y, &x, true);
        b.play(&r, false);
        ms.release(b);
        for i in 0..256 {
            b.hmr_to(y[i], m2[i]);
        }
        for i in 0..256 {
            b.swap(z[i], y[i]);
        }
        b.free_n(&z);
    }

    // ---------------- division 2: recompute lambda = -ndy / dx' to fix its phase
    ck(b, "-- division 2: recomput");
    let (dv, inv) = div_forward(b, &x, &y); super::fd_natinv::s0_park(b, &dv.t.fd.cnt, dv.t.fd.ring[255]);
    let (sqq, sqf) = sign_ctl(&dv.t);
    {
        if p5ms() > 0 {
        let w = p5ms();
        assert_eq!(inv.len(), 255);
        let ms = Ms::alloc(b);
        let flag = b.alloc();
        let zlow = b.alloc_n(256 - w);
        let mut z = zlow.clone();
        z.extend_from_slice(&inv[255 - w..255]);
        if mseed() {
            let (zc, yc, d, k) = (z.clone(), y.clone(), inv[0], ms.k);
            let mut dirty: Vec<QubitId> = inv[..255 - w].to_vec();
            dirty.extend_from_slice(&y);
            let debts5 = super::fd_seed::seed_fwd(b, &z, flag, k, w, &dirty, &mut |b: &mut B| {
                super::modp_frogdrop::ctrl_modadd(b, &Ms { k }, &zc, &yc, flag, d);
            });
            b.begin();
            super::modp_frogdrop::ctrl_modadd(b, &Ms { k }, &z, &y, flag, inv[0]);
            let addrec = b.end();
            let (nat, r) = if super::fd_natinv::on() { super::fd_natinv::rounds_fwd(b, &ms, &z, &inv[..255 - w], &y, Some((sqq, !sqf)), flag, super::fd_natinv::p5x()) } else { (super::fd_natinv::Nat::off(), rec_rounds_ms_w(b, &ms, &z, &inv[..255 - w], &y, Some((sqq, !sqf)), false)) };
            b.play(&r, false);
            for i in 0..256 - w4 {
                b.z_if(z[i], m2[i]);
            }
            if !debts4.is_empty() {
                super::fd_seed::pay_debts(b, &z[256 - w4..], &debts4, k, &y);
            }
            b.play(&r, true);
            nat.inverse(b, &ms); super::fd_seed::seed_inv(b, &z, flag, k, w, &dirty, &addrec);
            super::fd_seed::pay_debts2(b, &inv[255 - w..255], &debts5, k, flag, &y);
        } else {
        let r = rec_product_consume_ms_w(b, &ms, &z, &inv[..255 - w], &y, flag, w, Some((sqq, !sqf)));
        b.play(&r, false);
        for i in 0..256 - w4 {
            b.z_if(z[i], m2[i]);
        }
        b.play(&r, true);
        }
        b.free_n(&zlow);
        b.free(flag);
        ms.release(b);
        } else {
        let zlow = b.alloc_n(nl);
        let clean = b.alloc();
        let mut z = zlow.clone();
        z.extend_from_slice(&y[nl..256]);
        let r = rec_product_consume(b, &z, &inv, &y[..nl], Some((sqq, !sqf)), clean);
        b.play(&r, false);
        // All 256 lambda bits were measured; the consumed-input product exposes
        // all 256 recomputed bits. Its inverse then restores all five original ndy top bits.
        for i in 0..256 - w4 {
            b.z_if(z[i], m2[i]);
        }
        b.play(&r, true);
        b.free_n(&zlow);
        b.free(clean);
    }
        }
    ck(b, "div2 consume product");
    super::fd_natinv::s0_unpark(b, &dv.t.fd.cnt, dv.t.fd.ring[255]); div_inverse(b, dv, &y);
    ck(b, "div_inverse end");

    // ---------------- x3 = dx' + ox, y3 = ndy - oy
    ck(b, "-- x3 = dx' + ox, y3 = ");
    if narrow() {
        cl_op(b, &x, &ox, false, &y);
        cl_op(b, &y, &oy, true, &x);
    } else {
        let ms = Ms::alloc(b);
        let t = b.alloc_n(256);
        load_bits(b, &t, &ox);
        modadd(b, &ms, &x, &t, y[0]);
        load_bits(b, &t, &ox);
        load_bits(b, &t, &oy);
        modsub(b, &ms, &y, &t, x[0]);
        load_bits(b, &t, &oy);
        b.free_n(&t);
        ms.release(b);
    }
    // Fiat-Shamir nonce: one X X pair (identity) on qubit NONCE; fixed op count, so a nonce scan re-hashes only
    // the tail
    b.x(QubitId(super::NONCE as u64));
    b.x(QubitId(super::NONCE as u64));
    ck(b, "end");
    b.flush_dependency(); // publish pending physical tail for direct ops consumers
    (x, y)
}

// ---- lane CURVE: ported from the payload shell (gnuchev d1a7715a / BitWonka b98ba94), unchanged
/// x <- lambda^2 - x (mod p) in place (lambda in `lam`, untouched): x <- -x 2^-256, then 256 rounds x = 2x + lam_i lam.
pub(crate) fn sq_horner(b: &mut B, x: &[QubitId], lam: &[QubitId], d: QubitId) {
    if super::fd_clean::xclean() && signed() {
        return super::fd_clean::sq_horner_c(b, x, lam);
    }
    let ms = Ms::alloc(b);
    let c = b.alloc();
    ctrl_neg(b, &ms, x, None, lam);
    let mut xv = x.to_vec();
    for _ in 0..256 {
        super::modp_frogdrop::mod_halve(b, &ms, &mut xv, lam);
    }
    if signed() {
        super::fd_shell::pre(b, &ms, &mut xv, lam, d);
        for i in (0..256).rev() {
            b.cx(lam[i], c);
            super::fd_shell::sround(b, &ms, &mut xv, lam, c, d);
            b.cx(lam[i], c);
        }
        super::fd_shell::post(b, &ms, &mut xv, lam, d);
    } else {
    for i in (0..256).rev() {
        super::modp_frogdrop::mod_double(b, &ms, &mut xv, lam);
        b.cx(lam[i], c);
        super::modp_frogdrop::ctrl_modadd(b, &ms, &xv, lam, c, d);
        b.cx(lam[i], c);
    }
    }
    assert_eq!(xv, x.to_vec());
    b.free(c);
    ms.release(b);
}

/// z <- z - c (sub) or z + c (mod p, lazy reduction as the shell's other modular adds) for a classical 256-bit c
/// (bits of an input register), with a 128-lane loading register `t`, flags `fb` (half carry/borrow) and `fk`
/// (overflow), carry-in `c0` (all |0>), and >= 65 borrowed lanes `dirty` outside z/t/flags.
fn modadd_cl(b: &mut B, z: &[QubitId], c: &[BitId], sub: bool, t: &[QubitId], fb: QubitId, fk: QubitId, c0: QubitId,
             dirty: &[QubitId]) {
    use super::arith::{down_m, up_m, Dm};
    assert!(z.len() == 256 && c.len() == 256 && t.len() == 128);
    let (zl, zh) = (&z[..128], &z[128..]);
    let (cl, ch) = (&c[..128], &c[128..]);
    // flag ^= carry of (T~ + t + cin) (cmpl: borrow of T - t - cin) with optional write
    let half = |b: &mut B, tt: &[QubitId], cb: &[BitId], cin: QubitId, flag: QubitId, cmpl: bool, write: bool| {
        load_bits(b, t, cb);
        let u = up_m(b, tt, t, cin, cmpl);
        b.play(&u, false);
        b.cx(t[127], flag);
        let d = down_m(b, tt, t, cin, if write { Dm::Sum } else { Dm::Restore }, cmpl);
        b.play(&d, false);
        if !write && cmpl {
            // Restore mode re-complements nothing: up_m complemented tt, down_m(Restore, cmpl) undoes it
        }
        load_bits(b, t, cb);
    };
    let ms = Ms { k: fk };
    // z +-= c mod 2^256: fb = low carry/borrow, fk = overall
    half(b, zl, cl, c0, fb, sub, true);
    half(b, zh, ch, fb, fk, sub, true);
    // erase fb: add: fb = borrow(z_lo' - c_lo); sub: fb = carry(z_lo' + c_lo)
    half(b, zl, cl, c0, fb, !sub, false);
    // reduce: add C (add) / subtract C (sub) where fk
    if sub {
        b.begin();
        super::modp_frogdrop::add_small(b, &ms, z, 0, Some(fk), super::modp_frogdrop::C, dirty);
        let r = b.end();
        b.play(&r, true);
    } else {
        super::modp_frogdrop::add_small(b, &ms, z, 0, Some(fk), super::modp_frogdrop::C, dirty);
    }
    // erase fk: add: fk = borrow(z_f - c) (z_f < c); sub: fk = carry(z_f + c) (>= 2^256); both via the halves
    half(b, zl, cl, c0, fb, !sub, false);
    half(b, zh, ch, fb, fk, !sub, false);
    half(b, zl, cl, c0, fb, !sub, false);
}

/// z <- z -+ c mod p for a classical 256-bit c through a 128-lane loading register (payload shell's cl_op).
fn cl_op(b: &mut B, z: &[QubitId], c: &[BitId], sub: bool, dirty: &[QubitId]) {
    let t = b.alloc_n(128);
    let f = b.alloc_n(3);
    modadd_cl(b, z, c, sub, &t, f[0], f[1], f[2], dirty);
    b.free_n(&f);
    b.free_n(&t);
}

/// lane CURVE (P1MS): w-bit descending seed z: (j in z's top w lanes, rest |0>) -> j * a mod p for the 255-lane
/// multiplicand a (a != 0 mod p), one lazy Ms add per transposition; `flag` |0> in and out, ms.k |0> in and out,
/// ylow[0..2] borrowed. Same transposition schedule as joint_seed::seed_bits.
pub(crate) fn seed_ms255(b: &mut B, ms: &Ms, z: &[QubitId], a: &[QubitId], ylow: &[QubitId], flag: QubitId, w: usize) {
    assert!(z.len() == 256 && a.len() == 255 && ylow.len() >= 2 && w >= 1 && w <= 13);
    assert!(!z.contains(&flag) && !a.contains(&flag) && !ylow.contains(&flag) && !z.contains(&ms.k));
    for j in (1..(1usize << w)).rev() {
        super::joint_seed::activate_bits(b, z, flag, j, a, w);
        ctrl_modadd255(b, ms, z, a, flag, ylow[0], ylow[1]);
    }
    b.x(flag);
    super::descending_seed::xor_eq(b, z, [0; 5], flag, a);
}

/// lane CURVE (P1MS): z <- z + (ctl ? a : 0) mod p, lazy as modp_frogdrop::ctrl_modadd, for a 255-lane addend a
/// (top bit 0). ms.k |0> in and out; d, d2 borrowed (any state, restored; outside z, a, ctl, k).
/// The 255-lane ripple leaves its carry c in k; z[255] ^= c; then k ^= ctl & z[255] & [r < a] turns k into the 2^256
/// overflow c & z255_old (= c & !z255_new); the fold adds k * c; k is erased by ctl & !z[255] & [z_low < a].
/// Both compares use the top CMPT lanes (differ w.p. <= 2^-32, as the tree's own erase).
pub(crate) fn ctrl_modadd255(b: &mut B, ms: &Ms, z: &[QubitId], a: &[QubitId], ctl: QubitId, d: QubitId, d2: QubitId) {
    use super::modp_frogdrop::{add_small, C, CMPT};
    assert!(z.len() == 256 && a.len() == 255);
    let k = ms.k;
    let at = &a[255 - CMPT..255];
    let rt = &z[255 - CMPT..255];
    if super::fd_shell::ovf_on() {
        // FD: exact overflow (k = ctl & carry_255 & z255_old) in place of the first compare
        super::fd_shell::ttk_add255_ovf(b, a, z, Some(ctl), k, d, d2);
    } else {
        super::arith::ttk_add(b, a, &z[..255], Some(ctl), Some((k, d)));
        b.cx(k, z[255]);
        dctl_lt(b, at, rt, ctl, z[255], k, d, d2);
    }
    add_small(b, ms, z, 0, Some(k), C, a);
    b.x(z[255]);
    if super::fd_clean::measured_ok(b) {
        super::fd_clean::measured_erase(b, k, at, rt, &[ctl, z[255]], d, d2);
    } else {
        dctl_lt(b, at, rt, ctl, z[255], k, d, d2);
    }
    b.x(z[255]);
}

/// k ^= c1 & c2 & [t < a] (equal-length lanes; carry of ~t + a; t and a restored). The double control runs through
/// the borrowed d2 (k ^= d2 f; d2 ^= c1 c2; k ^= d2 f; d2 ^= c1 c2); d is ttk_carry's own borrowed lane.
fn dctl_lt(b: &mut B, a: &[QubitId], t: &[QubitId], c1: QubitId, c2: QubitId, k: QubitId, d: QubitId, d2: QubitId) {
    for &q in t {
        b.x(q);
    }
    if super::fd_shell::ovf_on() {
        super::fd_shell::ttk_carry_cc(b, a, t, c1, c2, k, d, d2);
    } else {
    super::arith::ttk_carry(b, a, t, d2, k, d);
    b.ccx(c1, c2, d2);
    super::arith::ttk_carry(b, a, t, d2, k, d);
    b.ccx(c1, c2, d2);
    }
    for &q in t {
        b.x(q);
    }
}

/// TRACK2: P4 rounds emitted straight-line (no recording, as P1's) with lambda's HMR inside the round loop; the Gidney folds
/// and the Track 1 measured flag erase need an open-recording-free stream. Off (FD_GIDNEY=0): the recorded rounds.
fn p4stream() -> bool { super::fd_gidney::gidney_on() && signed() && mseed() }

/// Same gates as `rec_rounds_ms_w(.., neg None, always_neg true)` played forward, with `alow[i]` measured into `m[i]` right
/// after round i (its last use) and the measured lanes offered to the folds through `b.gpool` (plus the idle flag `clean`).
fn rounds_ms_w_stream(b: &mut B, ms: &Ms, z: &[QubitId], alow: &[QubitId], y: &[QubitId], clean: QubitId, m: &[BitId]) {
    assert!(!b.fusion_recording());
    let mut zz = z.to_vec();
    let n = alow.len();
    b.gpool = vec![clean];
    super::fd_shell::pre(b, ms, &mut zz, y, alow[0]);
    for i in (0..n).rev() {
        b.gpool.clear();
        b.gpool.push(clean);
        b.gpool.extend_from_slice(&alow[i + 1..n]);
        super::fd_shell::sround(b, ms, &mut zz, y, alow[i], alow[(i + 1) % n]);
        b.hmr_to(alow[i], m[i]);
    }
    b.gpool.clear();
    b.gpool.push(clean);
    b.gpool.extend_from_slice(&alow[..n]);
    super::fd_shell::post(b, ms, &mut zz, y, alow[0]);
    b.gpool.clear();
    let mut pos: Vec<QubitId> = zz.clone();
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
    ctrl_neg(b, ms, z, None, y);
}

/// FD (MSEED): the Horner part of rec_product_consume_ms_w only (z holds the seed's j * y on entry).
fn rec_rounds_ms_w(b: &mut B, ms: &Ms, z: &[QubitId], alow: &[QubitId], y: &[QubitId], neg: Option<(QubitId, bool)>,
                   always_neg: bool) -> Vec<G> {
    b.begin();
    let mut zz = z.to_vec();
    let n = alow.len();
    if signed() {
        super::fd_shell::pre(b, ms, &mut zz, y, alow[0]);
        for i in (0..n).rev() {
            super::fd_shell::sround(b, ms, &mut zz, y, alow[i], alow[(i + 1) % n]);
        }
        super::fd_shell::post(b, ms, &mut zz, y, alow[0]);
    } else {
    for i in (0..n).rev() {
        super::modp_frogdrop::mod_double(b, ms, &mut zz, y);
        super::modp_frogdrop::ctrl_modadd(b, ms, &zz, y, alow[i], alow[(i + 1) % n]);
    }
    }
    let mut pos: Vec<QubitId> = zz.clone();
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
    if let Some((c, flip)) = neg {
        if flip { b.x(c); }
        ctrl_neg(b, ms, z, Some(c), y);
        if flip { b.x(c); }
    }
    if always_neg {
        ctrl_neg(b, ms, z, None, y);
    }
    b.end()
}

/// lane CURVE (P5MS): z = +-(a * y) (mod p), recorded, for a multiplier a of alow.len() + w bits whose top w bits
/// sit in z's top lanes (z = zlow ++ a_top, zlow |0>), the 256-lane addend y != 0 mod p, `flag` |0>; the sign is
/// controlled by c (xor flip) as in the parent consume product. Seed and rounds as rec_product_consume_ms.
fn rec_product_consume_ms_w(b: &mut B, ms: &Ms, z: &[QubitId], alow: &[QubitId], y: &[QubitId], flag: QubitId,
                            w: usize, neg: Option<(QubitId, bool)>) -> Vec<G> {
    assert_eq!(z.len(), 256);
    assert_eq!(y.len(), 256);
    assert!(w >= 1 && w <= 13 && alow.len() + w <= 256 && !alow.is_empty());
    assert!(alow.iter().all(|q| !z.contains(q) && !y.contains(q)) && z.iter().all(|q| !y.contains(q)));
    assert!(!z.contains(&flag) && !y.contains(&flag) && !alow.contains(&flag) && !z.contains(&ms.k));
    b.begin();
    let mut zz = z.to_vec();
    for j in (1..(1usize << w)).rev() {
        super::joint_seed::activate_bits(b, &zz, flag, j, y, w);
        super::modp_frogdrop::ctrl_modadd(b, ms, &zz, y, flag, alow[0]);
    }
    b.x(flag);
    super::descending_seed::xor_eq(b, &zz, [0; 5], flag, y);
    let n = alow.len();
    for i in (0..n).rev() {
        super::modp_frogdrop::mod_double(b, ms, &mut zz, y);
        super::modp_frogdrop::ctrl_modadd(b, ms, &zz, y, alow[i], alow[(i + 1) % n]);
    }
    let mut pos: Vec<QubitId> = zz.clone();
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
    if let Some((c, flip)) = neg {
        if flip { b.x(c); }
        ctrl_neg(b, ms, z, Some(c), y);
        if flip { b.x(c); }
    }
    b.end()
}

/// lane CURVE: z = -?(a * y) (mod p), recorded, where the multiplier a has its low 256 - w bits in `alow` and its top w
/// bits already in z's top lanes (z = zlow ++ a_top, zlow |0>); `flag` |0>. A w-bit descending seed maps the anchor
/// (j in the top w lanes) to j * y mod p (y != 0 mod p), then Horner over alow with the parent's Ms rounds (mod_double,
/// ctrl_modadd). The inverse replay restores a's top bits. Peak: the parent product's minus w lanes, plus `flag`.
fn rec_product_consume_ms(b: &mut B, ms: &Ms, z: &[QubitId], alow: &[QubitId], y: &[QubitId], flag: QubitId,
                          negate: bool) -> Vec<G> {
    assert_eq!(z.len(), 256);
    assert_eq!(y.len(), 256);
    let w = 256 - alow.len();
    assert!(w >= 1 && w <= 12);
    b.begin();
    let mut zz = z.to_vec();
    for j in (1..(1usize << w)).rev() {
        super::joint_seed::activate_bits(b, &zz, flag, j, y, w);
        super::modp_frogdrop::ctrl_modadd(b, ms, &zz, y, flag, alow[0]);
    }
    b.x(flag);
    super::descending_seed::xor_eq(b, &zz, [0; 5], flag, y);
    let n = alow.len();
    for i in (0..n).rev() {
        super::modp_frogdrop::mod_double(b, ms, &mut zz, y);
        super::modp_frogdrop::ctrl_modadd(b, ms, &zz, y, alow[i], alow[(i + 1) % n]);
    }
    let mut pos: Vec<QubitId> = zz.clone();
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
    if negate {
        ctrl_neg(b, ms, z, None, y);
    }
    b.end()
}

// ---- q765 v5-p5shell (op-p5, 2026-11-13): the product stage around an external walk ------------------------------
/// A division walk F supplied by the caller (v5-sd: the marker walk's gate list). `forward` turns dx (on `x`, with
/// `pas` borrowed dirty and restored) into the inverse's magnitude: 255 lanes `inv` and the sign control (q, flip),
/// meaning 1/dx = -inv iff q ^ flip, the convention of `sign_ctl`. Every other lane it used is freed |0>.
/// `inverse` is its exact inverse (same x lanes, same `inv` lanes and sign holding the same values).
pub trait Walk {
    fn forward(&mut self, b: &mut B, x: &[QubitId], pas: &[QubitId]) -> (Vec<QubitId>, (QubitId, bool));
    fn inverse(&mut self, b: &mut B, x: &[QubitId], pas: &[QubitId]);
}
/// Copy of `point_add` (text-generated, see team40/p5/SHELL_PORT.md) with div_forward / sign_ctl / s0_park ->
/// walk.forward and s0_unpark / div_inverse -> walk.inverse; nothing else changed except the nonce pair dropped.
pub fn point_add_walk(b: &mut B, walk: &mut dyn Walk) -> (Vec<QubitId>, Vec<QubitId>) {
    if std::env::var("FD_NOBATCH").is_ok() { b.signed_batch_enabled = false; }
    let x = b.alloc_n(256);
    let y = b.alloc_n(256);
    b.declare_qubits(0, &x);
    b.declare_qubits(1, &y);
    let ox: Vec<BitId> = b.declare_bits(2, 256);
    let oy: Vec<BitId> = b.declare_bits(3, 256);

    // dx, dy
    if narrow() {
        cl_op(b, &x, &ox, true, &y);
        cl_op(b, &y, &oy, true, &x);
    } else {
        let ms = Ms::alloc(b);
        let t = b.alloc_n(256);
        load_bits(b, &t, &ox);
        modsub(b, &ms, &x, &t, y[0]);
        load_bits(b, &t, &ox);
        load_bits(b, &t, &oy);
        modsub(b, &ms, &y, &t, x[0]);
        load_bits(b, &t, &oy);
        b.free_n(&t);
        ms.release(b);
    }
    let nl = 256 - consume();

    // ---------------- division 1
    ck(b, "-- division 1");
    let (inv, sq) = walk.forward(b, &x, &y);
    // The top five dy bits are reversibly consumed into the product's top wires.
    // Only the preserved low 251 dy bits need measurement erasure and phase repair.
    let m1 = b.fresh_bits(nl);
    let mut debts1: Vec<BitId> = vec![];
    {
        let zlow = b.alloc_n(nl);
        let clean = b.alloc();
        let mut z = zlow.clone();
        z.extend_from_slice(&y[nl..256]);
        // Forward-only: HMR is emitted outside every B recording.
        let mut zz = z.clone();
        if p1ms() {
            let ms = Ms::alloc(b);
            if mseed() {
                let (zc, ic, y0, y1, k) = (zz.clone(), inv.clone(), y[0], y[1], ms.k);
                debts1 = super::fd_seed::seed_fwd(b, &zz, clean, k, 256 - nl, &inv, &mut |b: &mut B| {
                    ctrl_modadd255(b, &Ms { k }, &zc, &ic, clean, y0, y1);
                });
            } else {
                seed_ms255(b, &ms, &zz, &inv, &y[..nl], clean, 256 - nl);
            }
            if p1r() && signed() {
                let gp = super::fd_gidney::gidney_on();
                if gp { b.gpool = vec![clean]; }
                super::fd_shell::pre(b, &ms, &mut zz, &inv, y[0]);
                for i in (0..nl).rev() {
                    if gp { b.gpool.clear(); b.gpool.push(clean); b.gpool.extend_from_slice(&y[i + 1..nl]); }
                    super::fd_shell::sround(b, &ms, &mut zz, &inv, y[i], y[(i + 1) % nl]);
                    b.hmr_to(y[i], m1[i]);
                }
                if gp { b.gpool.clear(); b.gpool.push(clean); b.gpool.extend_from_slice(&y[..nl]); }
                super::fd_shell::post(b, &ms, &mut zz, &inv, y[0]);
                b.gpool.clear();
                ms.release(b);
            } else if p1r() {
                for i in (0..nl).rev() {
                    super::modp_frogdrop::mod_double(b, &ms, &mut zz, &inv);
                    ctrl_modadd255(b, &ms, &zz, &inv, y[i], y[(i + 1) % nl], y[(i + 2) % nl]);
                    b.hmr_to(y[i], m1[i]);
                }
                ms.release(b);
            } else {
            ms.release(b);
            for i in (0..nl).rev() {
                super::early_product_fifth::round(b, &mut zz, &inv, &y[..nl], i, clean, m1[i]);
            }
            }
        } else {
            super::early_product_fifth::product(b, &mut zz, &inv, &y[..nl], clean, &m1);
        }
        let mut pos = zz;
        for i in 0..256 {
            if pos[i] != z[i] {
                let j = pos.iter().position(|&q| q == z[i]).unwrap();
                b.swap(pos[i], pos[j]);
                pos.swap(i, j);
            }
        }
        let (c, flip) = sq;
        if flip { b.x(c); }
        ctrl_neg_nm(b, &z, Some(c), &y[..nl]);
        if flip { b.x(c); }
        ck(b, "lambda = inv * dy");
        for i in 0..nl { b.swap(zlow[i], y[i]); }
        b.free_n(&zlow);
        b.free(clean);
    }
    walk.inverse(b, &x, &y);
    ck(b, "div_inverse end");
    // dy = lambda * dx: recompute, fix the phase of the dy measurement, uncompute
    if pconsume() > 0 {
        let w = super::fd_natinv::p2w();
        let ms = Ms::alloc(b);
        let flag = b.alloc();
        let zlow = b.alloc_n(256 - w);
        let mut z = zlow.clone();
        z.extend_from_slice(&y[256 - w..]);
        if mseed() {
            let (zc, xc, d, k) = (z.clone(), x.clone(), y[0], ms.k);
            let mut dirty: Vec<QubitId> = y[..256 - w].to_vec();
            dirty.extend_from_slice(&x);
            let debts2 = super::fd_seed::seed_fwd(b, &z, flag, k, w, &dirty, &mut |b: &mut B| {
                super::modp_frogdrop::ctrl_modadd(b, &Ms { k }, &zc, &xc, flag, d);
            });
            b.begin();
            super::modp_frogdrop::ctrl_modadd(b, &Ms { k }, &z, &x, flag, y[0]);
            let addrec = b.end();
            let (nat, r) = if super::fd_natinv::on() { super::fd_natinv::rounds_fwd(b, &ms, &z, &y[..256 - w], &x, None, flag, super::fd_natinv::p2x()) } else { (super::fd_natinv::Nat::off(), rec_rounds_ms_w(b, &ms, &z, &y[..256 - w], &x, None, false)) };
            b.play(&r, false);
            if !debts1.is_empty() {
                super::fd_seed::pay_debts2(b, &z[256 - (256 - nl)..], &debts1, k, flag, &x);
            }
            for i in 0..nl {
                b.z_if(z[i], m1[i]);
            }
            b.play(&r, true);
            nat.inverse(b, &ms); super::fd_seed::seed_inv(b, &z, flag, k, w, &dirty, &addrec);
            super::fd_seed::pay_debts(b, &y[256 - w..], &debts2, k, &x);
        } else {
        let r = rec_product_consume_ms(b, &ms, &z, &y[..256 - w], &x, flag, false);
        b.play(&r, false);
        if !debts1.is_empty() {
            super::fd_seed::pay_debts(b, &z[256 - (256 - nl)..], &debts1, ms.k, &x);
        }
        for i in 0..nl {
            b.z_if(z[i], m1[i]);
        }
        b.play(&r, true);
        }
        b.free_n(&zlow);
        b.free(flag);
        ms.release(b);
    } else if nf_products() {
        let z = b.alloc_n(256);
        let r = rec_product_nf(b, &z, &y, &x, None);
        b.play(&r, false);
        for i in 0..nl {
            b.z_if(z[i], m1[i]);
        }
        b.play(&r, true);
        b.free_n(&z);
    } else {
        let ms = Ms::alloc(b);
        let z = b.alloc_n(256);
        let r = rec_product(b, &ms, &z, &y, &x, false);
        b.play(&r, false);
        for i in 0..nl {
            b.z_if(z[i], m1[i]);
        }
        b.play(&r, true);
        b.free_n(&z);
        ms.release(b);
    }

    // ---------------- x: dx' = lambda^2 - dx - 3 ox
    ck(b, "-- x: dx' = lambda^2 - ");
    if narrow() {
        let d = b.alloc();
        sq_horner(b, &x, &y, d);
        b.free(d);
        for _ in 0..3 {
            cl_op(b, &x, &ox, true, &y);
        }
    } else {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, None, &y);
        let t = b.alloc_n(256);
        for i in 0..256 {
            b.cx(y[i], t[i]);
        }
        let mut yy = y.clone();
        mac(b, &ms, &x, &t, &mut yy);
        assert_eq!(yy, y);
        for i in 0..256 {
            b.cx(y[i], t[i]);
        }
        load_bits(b, &t, &ox);
        for _ in 0..3 {
            modsub(b, &ms, &x, &t, y[0]);
        }
        load_bits(b, &t, &ox);
        b.free_n(&t);
        ms.release(b);
    }
    // ---------------- ndy = -lambda * dx', measure lambda away
    ck(b, "-- ndy = -lambda * dx',");
    let m2 = b.fresh_bits(256);
    let mut debts4: Vec<BitId> = vec![];
    let w4 = pconsume();
    let mut lambda_measured = false;
    if w4 > 0 {
        let ms = Ms::alloc(b);
        let flag = b.alloc();
        let zlow = b.alloc_n(256 - w4);
        let mut z = zlow.clone();
        z.extend_from_slice(&y[256 - w4..]);
        if mseed() {
            let (zc, xc, d, k) = (z.clone(), x.clone(), y[0], ms.k);
            let mut dirty: Vec<QubitId> = y[..256 - w4].to_vec();
            dirty.extend_from_slice(&x);
            debts4 = super::fd_seed::seed_fwd(b, &z, flag, k, w4, &dirty, &mut |b: &mut B| {
                super::modp_frogdrop::ctrl_modadd(b, &Ms { k }, &zc, &xc, flag, d);
            });
            if p4stream() {
                rounds_ms_w_stream(b, &ms, &z, &y[..256 - w4], &x, flag, &m2);
                lambda_measured = true;
            } else {
                let r = rec_rounds_ms_w(b, &ms, &z, &y[..256 - w4], &x, None, true);
                b.play(&r, false);
            }
        } else {
        let r = rec_product_consume_ms(b, &ms, &z, &y[..256 - w4], &x, flag, true);
        b.play(&r, false);
        }
        b.free(flag);
        ms.release(b);
        // lambda's low lanes are measured; its top w4 bits live on inside ndy (lambda = -ndy / dx')
        if !lambda_measured {
            for i in 0..256 - w4 {
                b.hmr_to(y[i], m2[i]);
            }
        }
        for i in 0..256 - w4 {
            b.swap(zlow[i], y[i]);
        }
        b.free_n(&zlow);
    } else if nf_products() {
        let z = b.alloc_n(256);
        b.begin();
        let mut zz = z.to_vec();
        product_nf(b, &mut zz, &y, &x);
        let mut pos: Vec<QubitId> = zz.clone();
        for i in 0..256 {
            if pos[i] != z[i] {
                let j = pos.iter().position(|&q| q == z[i]).unwrap();
                b.swap(pos[i], pos[j]);
                pos.swap(i, j);
            }
        }
        ctrl_neg_nm(b, &z, None, &x);
        let r = b.end();
        b.play(&r, false);
        for i in 0..256 {
            b.hmr_to(y[i], m2[i]);
        }
        for i in 0..256 {
            b.swap(z[i], y[i]);
        }
        b.free_n(&z);
    } else {
        let ms = Ms::alloc(b);
        let z = b.alloc_n(256);
        let r = rec_product(b, &ms, &z, &y, &x, true);
        b.play(&r, false);
        ms.release(b);
        for i in 0..256 {
            b.hmr_to(y[i], m2[i]);
        }
        for i in 0..256 {
            b.swap(z[i], y[i]);
        }
        b.free_n(&z);
    }

    // ---------------- division 2: recompute lambda = -ndy / dx' to fix its phase
    ck(b, "-- division 2: recomput");
    let (inv, (sqq, sqf)) = walk.forward(b, &x, &y);
    {
        if p5ms() > 0 {
        let w = p5ms();
        assert_eq!(inv.len(), 255);
        let ms = Ms::alloc(b);
        let flag = b.alloc();
        let zlow = b.alloc_n(256 - w);
        let mut z = zlow.clone();
        z.extend_from_slice(&inv[255 - w..255]);
        if mseed() {
            let (zc, yc, d, k) = (z.clone(), y.clone(), inv[0], ms.k);
            let mut dirty: Vec<QubitId> = inv[..255 - w].to_vec();
            dirty.extend_from_slice(&y);
            let debts5 = super::fd_seed::seed_fwd(b, &z, flag, k, w, &dirty, &mut |b: &mut B| {
                super::modp_frogdrop::ctrl_modadd(b, &Ms { k }, &zc, &yc, flag, d);
            });
            b.begin();
            super::modp_frogdrop::ctrl_modadd(b, &Ms { k }, &z, &y, flag, inv[0]);
            let addrec = b.end();
            let (nat, r) = if super::fd_natinv::on() { super::fd_natinv::rounds_fwd(b, &ms, &z, &inv[..255 - w], &y, Some((sqq, !sqf)), flag, super::fd_natinv::p5x()) } else { (super::fd_natinv::Nat::off(), rec_rounds_ms_w(b, &ms, &z, &inv[..255 - w], &y, Some((sqq, !sqf)), false)) };
            b.play(&r, false);
            for i in 0..256 - w4 {
                b.z_if(z[i], m2[i]);
            }
            if !debts4.is_empty() {
                super::fd_seed::pay_debts(b, &z[256 - w4..], &debts4, k, &y);
            }
            b.play(&r, true);
            nat.inverse(b, &ms); super::fd_seed::seed_inv(b, &z, flag, k, w, &dirty, &addrec);
            super::fd_seed::pay_debts2(b, &inv[255 - w..255], &debts5, k, flag, &y);
        } else {
        let r = rec_product_consume_ms_w(b, &ms, &z, &inv[..255 - w], &y, flag, w, Some((sqq, !sqf)));
        b.play(&r, false);
        for i in 0..256 - w4 {
            b.z_if(z[i], m2[i]);
        }
        b.play(&r, true);
        }
        b.free_n(&zlow);
        b.free(flag);
        ms.release(b);
        } else {
        let zlow = b.alloc_n(nl);
        let clean = b.alloc();
        let mut z = zlow.clone();
        z.extend_from_slice(&y[nl..256]);
        let r = rec_product_consume(b, &z, &inv, &y[..nl], Some((sqq, !sqf)), clean);
        b.play(&r, false);
        // All 256 lambda bits were measured; the consumed-input product exposes
        // all 256 recomputed bits. Its inverse then restores all five original ndy top bits.
        for i in 0..256 - w4 {
            b.z_if(z[i], m2[i]);
        }
        b.play(&r, true);
        b.free_n(&zlow);
        b.free(clean);
    }
        }
    ck(b, "div2 consume product");
    walk.inverse(b, &x, &y);
    ck(b, "div_inverse end");

    // ---------------- x3 = dx' + ox, y3 = ndy - oy
    ck(b, "-- x3 = dx' + ox, y3 = ");
    if narrow() {
        cl_op(b, &x, &ox, false, &y);
        cl_op(b, &y, &oy, true, &x);
    } else {
        let ms = Ms::alloc(b);
        let t = b.alloc_n(256);
        load_bits(b, &t, &ox);
        modadd(b, &ms, &x, &t, y[0]);
        load_bits(b, &t, &ox);
        load_bits(b, &t, &oy);
        modsub(b, &ms, &y, &t, x[0]);
        load_bits(b, &t, &oy);
        b.free_n(&t);
        ms.release(b);
    }
    // (q765 v5-p5shell: the identity X X nonce pair of point_add is not emitted: no nonce scans)
    ck(b, "end");
    b.flush_dependency(); // publish pending physical tail for direct ops consumers
    (x, y)
}
