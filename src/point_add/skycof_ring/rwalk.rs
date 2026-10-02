//! SKY-COF masked-ring walk: `R` swap-first Kaliski ticks on the shared registers `A = [u | s]`,
//! `B = [v | r]` (see [`super::ring`]), the letter disposal (masked decoder + history, [`super::dec`]),
//! park bookkeeping (odometer, gated ticks, fold) and the exact walk back. Generic in the register width
//! `n` and the odd modulus `p < 2^(n-1)` (secp256k1: `n = 257`), so the whole walk is checked exhaustively
//! on small moduli.
//!
//! # Persistent walk state
//! `A`, `B` (`n` wires each), `KA`, `VB` (`bitlen(n)` each), the history `H` (width `h[t]`), the odometer
//! `odo` (`odo_bits`, counts the ticks whose post-state is parked) and `sign` (parity of the C ticks).
//!
//! # Tick `t` (forward)
//! 1. `t >= tp`: `fpre = [odo != 0]` (parked at entry); the ring tick runs with its conversions gated by
//!    `NOT fpre` (a parked lane has `u = 0`, so `c = 0` and every other step is the identity; the tick is the
//!    rotation `s <- 2s`).
//! 2. Ring tick -> `c = [B or C]`, `isC = [C]`; `sign ^= isC`.
//! 3. `t >= tp`: `F = [VB == 1] AND [top park_j bits of r == p's]` (= parked after the tick: `B = (1 | p)`).
//!    `isC` is erased against `s[1] AND NOT F` (measurement; before `tp`: one CNOT from `s[1]`);
//!    `c ^= F AND NOT fpre` (the park tick's letter is B, post-park letters are A); `fpre` erased;
//!    `odo += F`; fold: `g = A[0] AND F` (`A[0]` = cofactor bit `n-1` once `u = 0`), `s_low -= g * r_low`
//!    over `fold_w` cells (`r = p` there: `s <- s - p`), `A[0] ^= s[0]`, `g ^= s[0]`.
//! 4. Letter disposal: `t = 0`: `c ^= s[1]` (A or C only). `t >= 1`: `typ = c XOR NOT F` (`= [A]` unparked,
//!    0 parked), [`dec::push`] with `en = NOT F` (None before `tp`), `F` erased.
//!
//! The walk back runs the exact inverse of every step in reverse order. After the last tick every
//! supported lane is parked: `B = (1 | p)` and `VB = 1` are classical constants (freed), `A[0] = 0`, and
//! `s = -+2^R / d (mod p)` (`+` iff `sign = 1`) sits on `A`'s cofactor cells.
use super::dec::{self, DecZ};
use super::engine::{and_clear, and_into, frozen_and, Lit};
use super::ring::{self, kbits, Ring, Rng, StepLog, TickZ};
use crate::circuit::QubitId as Q;
use crate::point_add::builder::Builder;
use crate::point_add::skycof::adder;
use crate::point_add::skycof::decoder::Hreg;
use crate::point_add::skycof_mm as mm;

/// Literals per part of the park test's held AND.
const PARK_PART: usize = 6;

/// Walk envelope (public per-tick windows) and parameters.
#[derive(Clone, Debug)]
pub struct WEnv {
    pub n: usize,
    /// bits of p (LSB first, `n - 1` of them; `p` has exactly `n - 1` bits)
    pub p: Vec<bool>,
    pub r: usize,
    /// first tick whose post-state may be parked
    pub tp: usize,
    pub park_j: usize,
    pub fold_w: usize,
    pub odo_bits: usize,
    pub cap: Option<usize>,
    /// ring windows per tick (None: every supported lane is parked at entry)
    pub z: Vec<Option<TickZ>>,
    /// decoder windows per tick (None: no unparked post-state)
    pub dz: Vec<Option<DecZ>>,
    /// history width per tick (non-decreasing)
    pub h: Vec<usize>,
}

impl WEnv {
    /// secp256k1 envelope from a model table (`#` header with `R=`, `TP=`, `W=`, `FOLDW=`; then per tick
    /// `t ka ua vb kap uap vbp dka dvb drb` as lo/hi pairs and `H`).
    pub fn from_tsv(text: &str, cap: Option<usize>, park_j: usize, odo_bits: usize) -> WEnv {
        let mut hdr = std::collections::HashMap::new();
        let mut rows: Vec<Vec<usize>> = Vec::new();
        for l in text.lines() {
            if let Some(h) = l.strip_prefix('#') {
                for kv in h.split_whitespace() {
                    if let Some((k, v)) = kv.split_once('=') {
                        hdr.insert(k.to_string(), v.to_string());
                    }
                }
                continue;
            }
            if l.starts_with('t') || l.trim().is_empty() {
                continue;
            }
            let f: Vec<i64> = l.split(char::from(9u8)).map(|x| x.trim().parse().unwrap()).collect();
            assert_eq!(f[0] as usize, rows.len(), "envelope rows out of order");
            rows.push(f.iter().map(|&x| x.max(-1) as usize).collect::<Vec<usize>>());
            if f.iter().any(|&x| x < 0) {
                // an empty zone is written as lo=0 hi=-1: keep it marked
                let last = rows.last_mut().unwrap();
                for (i, &x) in f.iter().enumerate() {
                    if x < 0 {
                        last[i] = usize::MAX;
                    }
                }
            }
        }
        let gi = |k: &str| -> usize { hdr[k].parse().unwrap() };
        let r = gi("R");
        assert_eq!(rows.len(), r);
        let w = gi("W");
        let rg = |row: &Vec<usize>, f: usize| -> Option<Rng> {
            let (lo, hi) = (row[1 + 2 * f], row[2 + 2 * f]);
            (hi != usize::MAX && lo <= hi).then(|| Rng::new(lo, hi))
        };
        let mut z = Vec::with_capacity(r);
        let mut dz = Vec::with_capacity(r);
        let mut h = Vec::with_capacity(r);
        for (t, row) in rows.iter().enumerate() {
            let zz: Option<Vec<Rng>> = (0..6).map(|f| rg(row, f)).collect();
            z.push(zz.map(|v| TickZ { ka: v[0], ua: v[1], vb: v[2], kap: v[3], uap: v[4], vbp: v[5] }));
            let dd: Option<Vec<Rng>> = (6..9).map(|f| rg(row, f)).collect();
            dz.push(if t == 0 { None } else { dd.map(|v| DecZ { ka: v[0], vb: v[1], rb: v[2], w }) });
            h.push(row[19]);
        }
        for t in 1..r {
            h[t] = h[t].max(h[t - 1]);
        }
        let n = 257;
        let pv = crate::point_add::SECP256K1_P;
        let p: Vec<bool> = (0..n - 1).map(|j| pv.bit(j)).collect();
        WEnv { n, p, r, tp: gi("TP"), park_j, fold_w: gi("FOLDW"), odo_bits, cap, z, dz, h }
    }
}

/// State after the forward walk (rails freed).
pub struct Parked {
    /// `s` (LSB first, `n - 1` wires)
    pub s: Vec<Q>,
    pub ka: Vec<Q>,
    pub h: Hreg,
    pub odo: Vec<Q>,
    pub sign: Q,
}

fn room(c: &Builder, cap: Option<usize>) -> usize {
    match cap {
        None => 64,
        Some(k) => k.saturating_sub(c.active_qubits() as usize).max(4),
    }
}

thread_local! {
    /// Research accounting: `(component, first op, end op)` ranges, recorded only when enabled.
    pub static ACCT: std::cell::RefCell<Option<Vec<(&'static str, usize, usize)>>> = const { std::cell::RefCell::new(None) };
}

fn acct(name: &'static str, a: usize, b: usize) {
    ACCT.with(|x| {
        if let Some(v) = x.borrow_mut().as_mut() {
            v.push((name, a, b));
        }
    });
}

fn acct_log(log: &StepLog, end: usize, dir: &'static str) {
    let names_f = ["r_conv1", "r_cmp", "r_swap", "r_conv2", "r_cof", "r_rail"];
    for w in log.marks.windows(2) {
        let nm = names_f.iter().find(|n| n[2..] == *w[1].0).copied().unwrap_or("r_other");
        acct(nm, w[0].1, w[1].1);
    }
    if let Some(l) = log.marks.last() {
        acct(if dir == "f" { "r_tail" } else { "r_tail" }, l.1, end);
    }
}

pub(crate) fn trace(c: &mut Builder, what: &str, t: usize) {
    if std::env::var_os("SKYCOF_RING_TRACE").is_some() {
        let pk = c.take_win_peak();
        eprintln!("SKYCOF_RING_STEP t={t} {what} live={} peak={pk} ops={}", c.active_qubits(), c.op_count());
    }
}

/// Literals of the park test `[VB == 1] AND [r's top park_j bits == p's]`.
fn park_lits(r: &Ring, env: &WEnv) -> Vec<Lit> {
    let n = env.n;
    // VB == 1 <=> VB[1..] == 0 (bits(v) >= 1 always)
    let mut l: Vec<Lit> = r.vb.iter().skip(1).map(|&q| Lit { q, pol: false }).collect();
    let bc = r.bcof();
    for j in (n - 1 - env.park_j)..(n - 1) {
        l.push(Lit { q: bc[j], pol: env.p[j] });
    }
    l
}

fn fresh_ring(c: &mut Builder, env: &WEnv, a: Vec<Q>) -> Ring {
    let n = env.n;
    let kb = kbits(n);
    let b = c.alloc_qubits(n);
    for j in 0..n - 1 {
        if env.p[j] {
            c.x(b[j]);
        }
    }
    let ka = c.alloc_qubits(kb);
    let vb = c.alloc_qubits(kb);
    Ring { n, cap: env.cap, a, b, ka, vb, gate: None }
}

/// Seed: `A = d` (+ a zero cofactor cell), `B = p + 2^(n-1)` (r = 1), `KA = 0`, `VB = n - 1`.
fn seed(c: &mut Builder, env: &WEnv, d: &[Q]) -> Ring {
    let n = env.n;
    assert_eq!(d.len(), n - 1);
    let mut a = d.to_vec();
    a.push(c.alloc_qubit());
    let r = fresh_ring(c, env, a);
    c.x(r.b[n - 1]);
    for (i, &q) in r.vb.iter().enumerate() {
        if ((n - 1) >> i) & 1 == 1 {
            c.x(q);
        }
    }
    r
}

fn unseed(c: &mut Builder, env: &WEnv, r: Ring) -> Vec<Q> {
    let n = env.n;
    for (i, &q) in r.vb.iter().enumerate() {
        if ((n - 1) >> i) & 1 == 1 {
            c.x(q);
        }
    }
    c.x(r.b[n - 1]);
    for j in 0..n - 1 {
        if env.p[j] {
            c.x(r.b[j]);
        }
    }
    c.free_vec(&r.b);
    c.free_vec(&r.ka);
    c.free_vec(&r.vb);
    c.free(r.a[n - 1]);
    r.a[..n - 1].to_vec()
}

/// Parked constants: `B = 1 + p 2^1...` i.e. `v = 1`, `r = p`; `VB = 1`.
fn park_consts(c: &mut Builder, env: &WEnv, r: &Ring) {
    let n = env.n;
    c.x(r.b[0]);
    let bc = r.bcof();
    for j in 0..n - 1 {
        if env.p[j] {
            c.x(bc[j]);
        }
    }
    c.x(r.vb[0]);
}

fn fold_fwd(c: &mut Builder, env: &WEnv, r: &Ring, f: Q) {
    let n = env.n;
    let g = and_into(c, &[Lit { q: r.a[0], pol: true }, Lit { q: f, pol: true }]).unwrap();
    let w = env.fold_w.min(n - 1);
    let (ac, bc) = (r.acof(), r.bcof());
    adder::sub(c, Some(g), &bc[..w], &ac[..w], None, env.cap);
    c.cx(ac[0], r.a[0]);
    c.cx(ac[0], g);
    c.free(g);
}

fn fold_rev(c: &mut Builder, env: &WEnv, r: &Ring, f: Q) {
    let n = env.n;
    let (ac, bc) = (r.acof(), r.bcof());
    let g = c.alloc_qubit();
    c.cx(ac[0], g);
    c.cx(ac[0], r.a[0]);
    let w = env.fold_w.min(n - 1);
    adder::add(c, Some(g), &bc[..w], &ac[..w], None, env.cap);
    and_clear(c, &[Lit { q: r.a[0], pol: true }, Lit { q: f, pol: true }], Some(g));
}

/// One forward tick.
fn tick_fwd(c: &mut Builder, env: &WEnv, t: usize, r: &mut Ring, h: &mut Hreg, odo: &[Q], sign: Q) {
    let n = env.n;
    let post = t >= env.tp;
    trace(c, "start", t);
    let o0 = c.op_count();
    // 1. parked-at-entry flag
    let fpre = if post {
        let q = c.alloc_qubit();
        let rm = room(c, env.cap);
        mm::odo_nonzero_xor(c, odo, q, rm);
        Some(q)
    } else {
        None
    };
    // 2. ring tick
    let mut log = StepLog::default();
    let (cq, isc) = match &env.z[t] {
        Some(z) => {
            if let Some(fp) = fpre {
                c.x(fp);
                r.gate = Some(fp);
            }
            let out = ring::tick_fwd(c, r, z, &mut log);
            r.gate = None;
            if let Some(fp) = fpre {
                c.x(fp);
            }
            out
        }
        None => {
            assert!(post, "tick {t}: no ring window before the park window");
            let cq = c.alloc_qubit();
            let isc = c.alloc_qubit();
            r.a.rotate_left(1);
            (cq, isc)
        }
    };
    trace(c, "ring", t);
    acct_log(&log, c.op_count(), "f");
    if let Some(m) = log.marks.first() {
        acct("park", o0, m.1);
    }
    c.cx(isc, sign);
    let s1 = r.a[n - 2];
    let o1 = c.op_count();
    if let Some(fp) = fpre {
        // 3. park bookkeeping. isC = s[1] AND NOT fpre (the park tick's s[1] is that of 2s, even s: 0)
        {
            let m = c.alloc_bit();
            c.hmr(isc, m);
            c.x(fp);
            c.cz_if(s1, fp, m);
            c.x(fp);
            c.free_bit(m);
            c.release_clean(isc);
        }
        let pl = park_lits(r, env);
        let fa = frozen_and(c, &pl, PARK_PART);
        let f = fa.z;
        c.x(fp);
        c.ccx(f, fp, cq);
        c.x(fp);
        let rm = room(c, env.cap);
        mm::odo_nonzero_xor(c, odo, fp, rm);
        c.free(fp);
        let rm = room(c, env.cap);
        mm::odo_inc(c, odo, f, rm);
        fold_fwd(c, env, r, f);
        trace(c, "park", t);
        // 4. letter disposal
        c.cx(f, cq);
        c.x(cq);
        let o2 = c.op_count();
        acct("park", o1, o2);
        if let Some(dz) = &env.dz[t] {
            h.grow_to(c, env.h[t]);
            c.x(f);
            dec::push(c, r, dz, Some(f), cq, h);
            c.x(f);
        }
        let o3 = c.op_count();
        acct("decoder", o2, o3);
        fa.clear(c);
        acct("park", o3, c.op_count());
    } else {
        c.cx(s1, isc);
        c.free(isc);
        if t == 0 {
            c.cx(s1, cq);
        } else {
            let dz = env.dz[t].as_ref().expect("decoder window before the park window");
            h.grow_to(c, env.h[t]);
            c.x(cq);
            let o2 = c.op_count();
            dec::push(c, r, dz, None, cq, h);
            acct("decoder", o2, c.op_count());
        }
    }
    c.free(cq);
    trace(c, "dec", t);
}

/// Exact inverse of [`tick_fwd`].
fn tick_rev(c: &mut Builder, env: &WEnv, t: usize, r: &mut Ring, h: &mut Hreg, odo: &[Q], sign: Q) {
    let n = env.n;
    let post = t >= env.tp;
    let cq = c.alloc_qubit();
    let isc;
    let mut fpre = None;
    if post {
        let pl = park_lits(r, env);
        let fa = frozen_and(c, &pl, PARK_PART);
        let f = fa.z;
        if let Some(dz) = &env.dz[t] {
            h.shrink_to(c, env.h[t]);
            c.x(f);
            dec::pop(c, r, dz, Some(f), cq, h);
            c.x(f);
        }
        c.x(cq);
        c.cx(f, cq);
        fold_rev(c, env, r, f);
        let rm = room(c, env.cap);
        mm::odo_dec(c, odo, f, rm);
        let fp = c.alloc_qubit();
        let rm = room(c, env.cap);
        mm::odo_nonzero_xor(c, odo, fp, rm);
        c.x(fp);
        c.ccx(f, fp, cq);
        c.x(fp);
        fa.clear(c);
        let s1 = r.a[n - 2];
        let q = c.alloc_qubit();
        c.x(fp);
        c.ccx(s1, fp, q);
        c.x(fp);
        isc = q;
        fpre = Some(fp);
    } else {
        let s1 = r.a[n - 2];
        if t == 0 {
            c.cx(s1, cq);
        } else {
            let dz = env.dz[t].as_ref().unwrap();
            h.shrink_to(c, env.h[t]);
            dec::pop(c, r, dz, None, cq, h);
            c.x(cq);
        }
        let q = c.alloc_qubit();
        c.cx(s1, q);
        isc = q;
    }
    c.cx(isc, sign);
    let mut log = StepLog::default();
    match &env.z[t] {
        Some(z) => {
            if let Some(fp) = fpre {
                c.x(fp);
                r.gate = Some(fp);
            }
            ring::tick_rev(c, r, z, cq, isc, &mut log);
            r.gate = None;
            if let Some(fp) = fpre {
                c.x(fp);
            }
        }
        None => {
            r.a.rotate_right(1);
            c.free(isc);
            c.free(cq);
        }
    }
    if let Some(fp) = fpre {
        let rm = room(c, env.cap);
        mm::odo_nonzero_xor(c, odo, fp, rm);
        c.free(fp);
    }
}

/// Forward walk on `d` (`n - 1` wires; they become part of `A`).
pub fn forward(c: &mut Builder, env: &WEnv, d: &[Q]) -> Parked {
    forward_hooked(c, env, d, &mut |_, _, _, _, _, _| {})
}

/// Tick hook: `(builder, t, ring, history, odometer, sign)` after every forward tick (probes).
pub type Hook<'a> = dyn FnMut(&mut Builder, usize, &Ring, &Hreg, &[Q], Q) + 'a;

/// [`forward`] with a hook after every tick.
pub fn forward_hooked(c: &mut Builder, env: &WEnv, d: &[Q], hook: &mut Hook) -> Parked {
    let mut r = seed(c, env, d);
    let mut h = Hreg::new();
    let odo = c.alloc_qubits(env.odo_bits);
    let sign = c.alloc_qubit();
    for t in 0..env.r {
        tick_fwd(c, env, t, &mut r, &mut h, &odo, sign);
        hook(c, t, &r, &h, &odo, sign);
    }
    park_consts(c, env, &r);
    let n = env.n;
    c.free_vec(&r.b);
    c.free_vec(&r.vb);
    c.free(r.a[0]);
    let s: Vec<Q> = (0..n - 1).map(|j| r.a[n - 1 - j]).collect();
    Parked { s, ka: r.ka, h, odo, sign }
}

/// Exact walk back; returns the wires holding `d`.
pub fn backward(c: &mut Builder, env: &WEnv, pk: Parked) -> Vec<Q> {
    let n = env.n;
    let Parked { s, ka, mut h, odo, sign } = pk;
    let mut a = vec![c.alloc_qubit()];
    for i in 1..n {
        a.push(s[n - 1 - i]);
    }
    let kb = kbits(n);
    let b = c.alloc_qubits(n);
    let vb = c.alloc_qubits(kb);
    assert_eq!(ka.len(), kb);
    let mut r = Ring { n, cap: env.cap, a, b, ka, vb, gate: None };
    park_consts(c, env, &r);
    for t in (0..env.r).rev() {
        tick_rev(c, env, t, &mut r, &mut h, &odo, sign);
    }
    h.shrink_to(c, 0);
    c.free_vec(&odo);
    c.free(sign);
    unseed(c, env, r)
}
