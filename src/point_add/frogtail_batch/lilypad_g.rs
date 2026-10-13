//! Lilypad-G (r6_tick): the Lilypad walk in G-coordinates G = 2g - f, C_G = 2c_g - c_f (C_F = c_f).
//! Same decisions, same Q words, same eraser as lilypad.rs; the tick is
//!   e ^= 1 ^ X.v[1] ^ Y.v[1] ^ rho                (e = g mod 2 of the Lilypad state; Clifford)
//!   sigma = e & [h >= 0]
//!   X.v += (-1)^(1+e+rho) Y.v ; Y.c += (-1)^(1+e+rho) X.c      (UNCONTROLLED signed adds: forced digit)
//!   halve (relabel), then in frame t+1: cswap(X, Y) on sigma (no negation; signs float), rho ^= sigma
//!   h ^= sigma, h += 1, cap, sigma ^= X.c[1]
//! Rings: X = (G | C_F), Y = (F | C_G); G, F odd; C_F, C_G even. Signs of the four fields float; only rho = swap
//! parity is tracked. The eraser reads c_g through an in-place window conversion Y.c <- X.c + (-1)^rho Y.c
//! (= 2 d c_g, d = sign of the stored C_F) and an offset view (bsig + 1).
use super::builder::{B, G, ONE};
use super::chunked::AddRole;
use super::frogstrip::{sec, SEC_INV};
use super::modp_ft::ctrl_add_pool;
use super::lilypad::{cap_logic, digit_add, eraser, fix_boundary, inc_unctl, lsc, mclear, win_len, PSched, PScr, PWalk, HB};
use crate::circuit::{BitId, QubitId};

pub const LILYPAD_G_SCHED: &str = include_str!("lilypad_g_sched.txt");

pub fn sched_g() -> PSched {
    PSched::from_text(LILYPAD_G_SCHED)
}

/// AUDIT (r6tick) negative controls: AUD_NEG = norho | flipsign | noconvrho | noconv | nofix | noz
fn neg(k: &str) -> bool {
    std::env::var("AUD_NEG").map(|v| v == k).unwrap_or(false)
}

/// target += (-1)^(XOR negs ^ inv) source (mod 2^len), uncontrolled; paired chunks when `pairing` is set.
#[allow(clippy::too_many_arguments)]
fn sadd(
    b: &mut B,
    src: &[QubitId],
    tgt: &[QubitId],
    negs: &[QubitId],
    inv: bool,
    pool: &[QubitId],
    pairing: Option<(usize, bool)>,
    t: usize,
    role: AddRole,
) {
    let flip = |b: &mut B| {
        for &q in tgt {
            for &n in negs {
                b.cx(n, q);
            }
            if inv {
                b.x(q);
            }
        }
    };
    flip(b);
    digit_add(b, src, tgt, ONE, pool, pairing, t, role);
    flip(b);
}

/// Initial state: X.v = 2x - p (x shifted up one lane by swaps, then the uncontrolled subtract of Y.v = p),
/// Y = (p | C_G = 2), X.c = 0. Recorded so the inverse walk can unplay it.
pub fn init_g(b: &mut B, w: &PWalk, sch: &PSched, sc: &PScr) {
    let p = super::frogdrop_sched::p();
    for f in 0..256 {
        if p.bit(f) {
            b.x(w.bf(f));
        }
    }
    b.x(w.bsig(1));
    for f in (0..256).rev() {
        b.swap(w.af(1, f), w.af(1, f + 1));
    }
    let kv = sch.kv[1];
    let av: Vec<QubitId> = (0..kv).map(|f| w.af(1, f)).collect();
    let bv: Vec<QubitId> = (0..kv).map(|f| w.bf(f)).collect();
    let mut pl = sc.pool.clone();
    pl.extend(&sc.tmp);
    // 2x - p = ~(~X + Y) with Y = p; X lanes above 257 are 0 (sign extension of 2x >= 0 -> of 2x - p by the add)
    sadd(b, &bv, &av, &[], true, &pl, None, 0, AddRole::Value);
    // sign-extend X.v to its region (lanes kv..c are |0> before; the circuit keeps them sign copies)
    for f in kv..sch.c[1] {
        b.cx(w.af(1, kv - 1), w.af(1, f));
    }
}

/// Step of tick t up to the halve: e computed into `e` (|0> forward; Q's lane in the regenerating walk), sigma, adds.
pub fn step_core_g(
    b: &mut B,
    w: &PWalk,
    t: usize,
    sch: &PSched,
    sc: &PScr,
    rho: QubitId,
    e: QubitId,
    extra: &[QubitId],
    pairing: Option<(usize, bool)>,
) {
    let (c, kv, kc) = (sch.c[t], sch.kv[t], sch.kc[t]);
    let sg = sc.sg;
    let h5 = w.h[HB - 1];
    sec(b, "lilyg.ctl", |b| {
        b.cx(w.af(t, 1), e);
        b.cx(w.bf(1), e);
        b.x(e);
        b.cx(rho, e);
        b.x(h5);
        b.and_c(e, h5, sg);
        b.x(h5);
    });
    let mut pl = lsc(b, w, t, c, kv, kc);
    pl.extend(&sc.pool);
    pl.extend(&sc.tmp);
    pl.extend(extra);
    let av: Vec<QubitId> = (0..kv).map(|f| w.af(t, f)).collect();
    let bv: Vec<QubitId> = (0..kv).map(|f| w.bf(f)).collect();
    let sinv = !neg("flipsign");
    sec(b, "lilyg.addv", |b| sadd(b, &bv, &av, &[e, rho], sinv, &pl, pairing, t, AddRole::Value));
    // cofactor sig 0 lanes are 0 in both rings (C_F, C_G even): add lanes 1..kc
    let ac: Vec<QubitId> = (1..kc).map(|s| w.asig(t, s)).collect();
    let bc: Vec<QubitId> = (1..kc).map(|s| w.bsig(s)).collect();
    sec(b, "lilyg.addc", |b| sadd(b, &ac, &bc, &[e, rho], sinv, &pl, pairing, t, AddRole::Cofactor));
    lsc(b, w, t, c, kv, kc);
}

/// Halve of tick t (relabel + boundary fixes), the deferred-to-frame-t+1 cswap, rho/delta update, cap, sigma decode.
pub fn halve_g(b: &mut B, w: &PWalk, t: usize, sch: &PSched, sc: &PScr, rho: QubitId) {
    sec(b, "lilyg.hv", |b| {
        if !neg("nofix") {
            fix_boundary(b, &|f| w.af(t + 1, f), sch.c[t] - 1, sch.c[t + 1]);
        }
        fix_boundary(b, &|f| w.bf(f), sch.c[t], sch.c[t + 1]);
    });
    let (c, kv, kc) = (sch.c[t + 1], sch.kv[t + 1], sch.kc[t + 1]);
    let sg = sc.sg;
    sec(b, "lilyg.swap", |b| {
        lsc(b, w, t + 1, c, kv, kc);
        for f in 1..kv {
            b.cswap(sg, w.af(t + 1, f), w.bf(f));
        }
        for s in 1..kc {
            b.cswap(sg, w.asig(t + 1, s), w.bsig(s));
        }
        lsc(b, w, t + 1, c, kv, kc);
    });
    sec(b, "lilyg.hv", |b| {
        if !neg("norho") {
            b.cx(sg, rho);
        }
        for &x in &w.h {
            b.cx(sg, x);
        }
        inc_unctl(b, &w.h, &sc.tmp);
    });
    if w.capq > 0 {
        sec(b, "lilyg.cap", |b| cap_logic(b, w, sc));
    }
    b.cx(w.asig(t + 1, 1), sg);
}

/// Window conversion for the eraser (frame t+1): Y.c[0..L] <- X.c[0..L] + (-1)^rho Y.c[0..L] (mod 2^L), so that
/// Y.c sig k+1 = bit k of d*c_g. Recording (unplay to restore).
fn conv_len(b: &mut B, w: &PWalk, t: usize, l: usize, rho: QubitId, pool: &[QubitId]) -> Vec<G> {
    let xs: Vec<QubitId> = (1..l).map(|k| w.asig(t + 1, k)).collect();
    let ys: Vec<QubitId> = (1..l).map(|k| w.bsig(k)).collect();
    b.begin();
    // rho = 1: Y <- X - Y = ~(Y + ~X)
    let nr = neg("noconvrho");
    for &q in &xs {
        if !nr { b.cx(rho, q); }
    }
    ctrl_add_pool(b, &xs, &ys, ONE, pool);
    for &q in &ys {
        if !nr { b.cx(rho, q); }
    }
    for &q in &xs {
        if !nr { b.cx(rho, q); }
    }
    b.end()
}

fn conv(b: &mut B, w: &PWalk, t: usize, sch: &PSched, rho: QubitId, pool: &[QubitId]) -> Vec<G> {
    let qb = w.q.len();
    let l = (qb.max(win_len(qb)) + 3).min(sch.w - sch.c[t + 1]);
    conv_len(b, w, t, l, rho, pool)
}

/// Record the public-end bridge from Lilypad-G's stored coordinates to the
/// shell interface. It leaves only key=[F<0], C_F, h and the cap log live:
/// C_G is converted to signed 2p and cleared, G and rho are cleared by their
/// audited invariants, and F is reduced to its sign key.
pub fn endpoint_adapter_g(
    b: &mut B,
    w: &PWalk,
    sch: &PSched,
    sc: &PScr,
    rho: QubitId,
) -> Vec<G> {
    let t = sch.s + 1;
    let value_len = sch.c[t];
    let cofactor_len = sch.w - value_len;
    let mut pool = sc.pool.clone();
    pool.extend(&sc.tmp);
    pool.extend(&sc.sp);
    pool.extend(&sc.d);
    pool.push(sc.e);
    pool.push(sc.sg);
    let cv = conv_len(b, w, sch.s, cofactor_len, rho, &pool);
    let sign_f = w.bf(1);
    let p2 = super::frogdrop_sched::p() << 1usize;
    let np2 = (!p2).wrapping_add(super::frogdrop_sched::N::from(1u64));

    b.begin();
    b.play(&cv, false);
    for s in 1..cofactor_len {
        let pos = p2.bit(s);
        let neg = np2.bit(s);
        if pos {
            b.x(w.bsig(s));
        }
        if pos != neg {
            b.cx(sign_f, w.bsig(s));
        }
    }
    // G = -(-1)^rho F at a successful endpoint.
    b.x(w.af(t, 0));
    for f in 1..value_len {
        b.x(w.af(t, f));
        b.cx(rho, w.af(t, f));
        b.cx(sign_f, w.af(t, f));
    }
    // rho = h0 xor (S mod 2) xor L0_0 xor L1_0 on clean walks.
    b.cx(w.h[0], rho);
    b.cx(w.log[0], rho);
    b.cx(w.log[4], rho);
    if sch.s % 2 == 1 {
        b.x(rho);
    }
    // F is +/-1: retain its sign in lane 1 as the shell key.
    b.x(w.bf(0));
    for f in 2..value_len {
        b.cx(sign_f, w.bf(f));
    }
    b.end()
}

pub struct GScr {
    pub rho: QubitId,
}

/// Forward walk: init, ticks 1..=S, e X-measured each tick. Returns the measurement bits (index t).
pub fn walk_forward_g(b: &mut B, w: &PWalk, sch: &PSched, sc: &PScr, g: &GScr, division: Option<usize>) -> Vec<BitId> {
    init_g(b, w, sch, sc);
    let m = b.fresh_bits(sch.s + 1);
    for t in 1..=sch.s {
        step_core_g(b, w, t, sch, sc, g.rho, sc.e, &[], division.map(|d| (d, false)));
        halve_g(b, w, t, sch, sc, g.rho);
        b.hmr_to(sc.e, m[t]);
    }
    m
}

/// Regenerating tick t as two recordings: (step core, halve + marker clear / converted eraser).
pub fn rec_regen_g(b: &mut B, w: &PWalk, t: usize, sch: &PSched, sc: &PScr, g: &GScr, division: Option<usize>) -> (Vec<G>, Vec<G>) {
    let qe = w.qfr(t)[w.q.len() - 1];
    let mut extra = vec![sc.e];
    extra.extend(&sc.d);
    extra.extend(&sc.sp);
    b.begin();
    step_core_g(b, w, t, sch, sc, g.rho, qe, &extra, division.map(|d| (d, true)));
    let p1 = b.end();
    b.begin();
    halve_g(b, w, t, sch, sc, g.rho);
    if t % 2 == 1 {
        mclear(b, w, t, sc);
    } else {
        let mut cp: Vec<QubitId> = sc.pool.clone();
        cp.extend(&sc.tmp);
        cp.extend(&sc.sp);
        cp.push(sc.e);
        let cv = conv(b, w, t, sch, g.rho, &cp);
        let nc = neg("noconv");
        if !nc { sec(b, "er.conv", |b| b.play(&cv, false)); }
        eraser(b, w, t, sch, sc, 1, t == sch.s);
        if !nc { sec(b, "er.conv", |b| b.play(&cv, true)); }
    }
    let p3 = b.end();
    (p1, p3)
}

/// Inverse of walk_forward_g (Q clean in w.q; clean again afterwards).
pub fn walk_inverse_g(b: &mut B, w: &PWalk, sch: &PSched, sc: &PScr, g: &GScr, m: &[BitId], division: Option<usize>) {
    SEC_INV.with(|c| c.set(true));
    for t in (1..=sch.s).rev() {
        let (p1, p3) = rec_regen_g(b, w, t, sch, sc, g, division);
        b.play(&p3, true);
        if !neg("noz") {
            b.z_if(w.qfr(t)[w.q.len() - 1], m[t]);
        }
        b.play(&p1, true);
    }
    b.begin();
    init_g(b, w, sch, sc);
    let ir = b.end();
    b.play(&ir, true);
    SEC_INV.with(|c| c.set(false));
}
