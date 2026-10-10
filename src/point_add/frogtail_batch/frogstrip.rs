//! frogstrip: frogtail's tape-free Stehle-Zimmermann 2-adic walk with one +-1 quotient digit per tick and the strip
//! done by a barrel, so a walk takes ~300 ticks instead of 556 (design: agent ft-holistic; integer model in
//! `strip_model`).
//!
//! Registers as frogtail (two rings of W lanes, value ascending from frame 0 and cofactor descending from the top
//! frame, classical boundary c(t), halving = relabel of ring A), plus a full counter j (JS bits, no parity lock) and
//! an exponent counter E (EB bits). Forward tick t:
//!   step end (t >= 2, e = [j <= -1] & A.v odd, plus the absorption flag from TABS on): j <- -j, parity ^= e,
//!     swap A <-> B, e erased as the new A.c's low bit; absorbed shots are then cleared (A = (0, 1), B.v = -2s).
//!   digit: a = B.v odd & [j >= 1]; r = a & (A.v1 ^ B.v1); with eq = [j = 1] the sign is r ^ eq; A.v += (-1)^sign
//!     B.v and B.c -= (-1)^sign A.c, both controlled by a; r is X-measured (the regenerating tick keeps it in Q).
//!   halve: relabel, boundary fixes, j -= 1 where B.v is odd.
//!   strip (j <= 0): k = min(nu(A.v), 3) from A.v's low lanes; ring A's segment (the cofactor's ksc lanes, 3 of its
//!     sign lanes below them, the value's ksv lanes) rotates down by k (rot4); the k value lanes at the segment's top
//!     take the value's sign; j -= k, E -= k; k and [j <= 0] are uncomputed from j (k = (-j) mod 4 there).
//! Absorbed shots hold j = 3 and B.v even: no digit, no decrement, no strip; A.c = 2^m counts the ticks.

use super::arith::{dec, inc, rot4_up};
use super::builder::{B, G};
use super::frogtail::{and_xor, Scr, QB};
use super::mask::mc_xor;
use super::modp_ft::{add_sext, ctrl_add_pool};
use super::strip_model::{SSched, EB, EOFF, ZL_S};
use crate::circuit::{BitId, QubitId};

/// counter bits: h = j >> 1 in [-13, 11]. j's low bit is not stored: j + t + S is even at the start of tick t (a
/// halve moves j and t together, a strip j and S, a step end negates j), so j0 = t0 ^ S0 = t0 ^ E0_0 ^ E_0. Absorbed
/// shots freeze h = 1 (j in {2, 3}: never <= 1, as frozen j = 3).
pub const JS: usize = 5;

thread_local! {
    /// profiling: section name -> (expected Toffoli sum, count), while Some
    pub(crate) static SEC: std::cell::RefCell<Option<std::collections::BTreeMap<String, (f64, u64)>>> =
        const { std::cell::RefCell::new(None) };
    /// profiling: sections are played inverted (inverse walk)
    pub(crate) static SEC_INV: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Profiling section: records `f`'s gates, measures their cost as they will be played, emits them.
pub(crate) fn sec(b: &mut B, name: &str, f: impl FnOnce(&mut B)) {
    if SEC.with(|s| s.borrow().is_none()) {
        f(b);
        return;
    }
    b.begin();
    f(b);
    let r = b.end();
    let inv = SEC_INV.with(|c| c.get());
    let c = b.measure(&r, inv);
    let key = format!("{}{}", if inv { "inv." } else { "fwd." }, name);
    SEC.with(|s| {
        let mut s = s.borrow_mut();
        let e = s.as_mut().unwrap().entry(key).or_insert((0.0, 0));
        e.0 += c;
        e.1 += 1;
    });
    b.play(&r, false);
}

/// Walk registers. `a` = A ring (physical lanes), `bb` = B ring, `q` = digit word (regenerating tick only), `ec` =
/// exponent counter E (init E0, -k per strip).
pub struct SWalk {
    pub a: Vec<QubitId>,
    pub bb: Vec<QubitId>,
    pub q: Vec<QubitId>,
    pub j: Vec<QubitId>,
    pub par: QubitId,
    pub ec: Vec<QubitId>,
    /// E0's low bit (j0 = t0 ^ e0p ^ E_0)
    pub e0p: bool,
}

impl SWalk {
    /// A ring lane at frame f during tick t (frame offset t - 1; the halve of tick t moves it to t).
    pub fn af(&self, t: usize, f: usize) -> QubitId {
        let w = self.a.len();
        self.a[(f + t - 1) % w]
    }
    pub fn asig(&self, t: usize, s: usize) -> QubitId {
        self.af(t, self.a.len() - 1 - s)
    }
    pub fn bf(&self, f: usize) -> QubitId {
        self.bb[f]
    }
    pub fn bsig(&self, s: usize) -> QubitId {
        self.bb[self.bb.len() - 1 - s]
    }
    /// Q's frame lanes during tick t: frame lane f is q[(f + t) mod QB]; tick t's digit lands in frame lane QB - 1.
    pub fn qfr(&self, t: usize) -> Vec<QubitId> {
        (0..QB).map(|f| self.q[(f + t) % QB]).collect()
    }
    fn js(&self) -> QubitId {
        self.j[JS - 1]
    }
    /// literal "j0 = v" in frame tt (tt = t before tick t's halve, t + 1 after it): a condition on E_0
    fn j0_is(&self, tt: usize, v: bool) -> (QubitId, bool) {
        let need = v ^ (tt & 1 == 1) ^ self.e0p;
        (self.ec[0], !need)
    }
}

/// E's initial value: E0 = H0 - T + EOFF, so at the end E + m - EOFF = H0 - (halvings to the absorption).
pub fn e0(sch: &SSched, h0: usize) -> i64 {
    h0 as i64 - sch.t as i64 + EOFF
}

/// Initial state: A = (p, 1), j = 1, E = E0 (B = (x', 0) is the caller's).
pub fn init(b: &mut B, w: &SWalk, e0: i64) {
    let p = super::frogdrop_sched::p();
    for f in 0..256 {
        if p.bit(f) {
            b.x(w.af(1, f));
        }
    }
    b.x(w.asig(1, 0));
    let m = (1i64 << EB) - 1;
    for i in 0..EB {
        if ((e0 & m) >> i) & 1 == 1 {
            b.x(w.ec[i]);
        }
    }
}

/// Local sign compression of tick t: lanes [kv, c) of both values and [kc, W - c) of both cofactors (A's from
/// `a_lo`, B's from `b_lo` on) hold the sign of lane kv - 1 (kc - 1); XORing it clears them, the same gates restore.
#[allow(clippy::too_many_arguments)]
fn lsc_from(
    b: &mut B,
    w: &SWalk,
    t: usize,
    c: usize,
    kv: usize,
    kc: usize,
    a_lo: usize,
    b_lo: usize,
) -> Vec<QubitId> {
    let wb = w.bb.len();
    let mut z = vec![];
    for f in kv..c {
        b.cx(w.af(t, kv - 1), w.af(t, f));
        b.cx(w.bf(kv - 1), w.bf(f));
        z.extend([w.af(t, f), w.bf(f)]);
    }
    for s in kc.max(a_lo)..wb - c {
        b.cx(w.asig(t, kc - 1), w.asig(t, s));
        z.push(w.asig(t, s));
    }
    for s in kc.max(b_lo)..wb - c {
        b.cx(w.bsig(kc - 1), w.bsig(s));
        z.push(w.bsig(s));
    }
    z
}

fn lsc(b: &mut B, w: &SWalk, t: usize, c: usize, kv: usize, kc: usize) -> Vec<QubitId> {
    lsc_from(b, w, t, c, kv, kc, 0, 0)
}

/// compressed widths of tick t's swap and adds (uncompressed at the closing step)
fn kvc(sch: &SSched, t: usize) -> (usize, usize) {
    if t <= sch.t {
        (sch.kv[t], sch.kc[t])
    } else {
        (sch.c[t], sch.w - sch.c[t])
    }
}

/// Controlled role swap of the shelves over the compressed widths.
fn swap_shelves(b: &mut B, w: &SWalk, t: usize, sch: &SSched, e: QubitId) {
    let c = sch.c[t];
    let (kv, kc) = kvc(sch, t);
    lsc(b, w, t, c, kv, kc);
    for f in 0..kv {
        b.cswap(e, w.af(t, f), w.bf(f));
    }
    for s in 0..kc {
        b.cswap(e, w.asig(t, s), w.bsig(s));
    }
    lsc(b, w, t, c, kv, kc);
}

/// Absorption flag (t >= TABS): e ^= [j <= -1] & B.v odd & [A.v lanes 0..min(ZL, c) all zero].
fn absorb_flag(b: &mut B, w: &SWalk, t: usize, sch: &SSched, sc: &Scr, temps: &[QubitId]) {
    let mut lits = vec![(w.js(), false), (w.bf(0), false)];
    lits.extend((0..sch.c[t].min(ZL_S)).map(|f| (w.af(t, f), true)));
    let mut tt = temps.to_vec();
    for &x in &sc.xs {
        if !tt.contains(&x) {
            tt.push(x);
        }
    }
    and_xor(b, &lits, sc.e, &tt, &sc.dirty);
}

/// Clear after an absorbing step end: A = (+-1, +-p) -> (0, 1), B.v = 0 -> -2s with s = [A.v = -1]
/// (frogtail's absorb_clear).
fn absorb_clear(b: &mut B, w: &SWalk, t: usize, sch: &SSched, sc: &Scr) {
    let c = sch.c[t];
    let cl = w.a.len() - c;
    let (f, fs, b0) = (sc.e, sc.a, w.bf(0));
    b.x(b0);
    b.and_c(b0, w.af(t, 0), f);
    b.x(b0);
    b.and_c(f, w.af(t, 1), fs);
    for l in 1..c {
        b.cx(fs, w.bf(l));
    }
    for l in 2..c {
        b.cx(fs, w.af(t, l));
    }
    let p = super::frogdrop_sched::p();
    let mp = (!p).wrapping_add(super::frogdrop_sched::N::from(1u64));
    for s in 1..cl {
        let pb = s < 384 && p.bit(s);
        let mb = if s < 384 { mp.bit(s) } else { true };
        if pb {
            b.cx(f, w.asig(t, s));
        }
        if pb != mb {
            b.cx(fs, w.asig(t, s));
        }
    }
    b.and_u(f, w.af(t, 1), fs);
    b.ccx(f, w.bf(1), w.af(t, 1));
    b.cx(f, w.af(t, 0));
    b.x(b0);
    b.and_u(b0, w.asig(t, 0), f);
    b.x(b0);
}

/// Step end of tick t (t >= 2; t = T + 1 is the closing absorption step). With `marker`, the ordinary step end
/// also sets the digit word's marker lane (regenerating tick).
fn step_end(b: &mut B, w: &SWalk, t: usize, sch: &SSched, sc: &Scr, marker: bool) {
    let e = sc.e;
    sec(b, "se.flag", |b| {
        b.and_c(w.js(), w.af(t, 0), e);
        if marker {
            b.cx(e, w.qfr(t)[QB - 2]);
        }
    });
    if t >= sch.tabs {
        sec(b, "se.absflag", |b| {
            let mut temps = sc.tmp.clone();
            temps.extend([sc.a, sc.eq, sc.one]);
            temps.extend(&sc.pool);
            absorb_flag(b, w, t, sch, sc, &temps);
        });
    }
    sec(b, "se.j", |b| {
        // j -> -j: h -> -h - j0 = ~h + !j0 (j0 unchanged)
        for &x in &w.j {
            b.cx(e, x);
        }
        let c = sc.tmp[0];
        and_lit(b, e, w.j0_is(t, false), c, true);
        inc(b, c, &w.j, &sc.tmp[1..JS]);
        and_lit(b, e, w.j0_is(t, false), c, false);
        b.cx(e, w.par);
    });
    sec(b, "se.swap", |b| swap_shelves(b, w, t, sch, e));
    b.cx(w.asig(t, 0), e);
    if t >= sch.tabs {
        sec(b, "se.absclear", |b| absorb_clear(b, w, t, sch, sc));
    }
}

/// [j = v] literals in frame tt (h = v >> 1 and the j0 literal)
fn j_eq(w: &SWalk, v: i64, tt: usize) -> Vec<(QubitId, bool)> {
    let m = (1i64 << JS) - 1;
    let h = v >> 1;
    let mut l: Vec<(QubitId, bool)> = w.j.iter().enumerate().map(|(i, &q)| (q, ((h & m) >> i) & 1 == 0)).collect();
    l.push(w.j0_is(tt, v & 1 == 1));
    l
}

/// out = AND of two literals (compute, out |0> before) or its measured uncompute
fn and_lit2(b: &mut B, l: [(QubitId, bool); 2], out: QubitId, compute: bool) {
    for &(q, ng) in &l {
        if ng {
            b.x(q);
        }
    }
    if compute {
        b.and_c(l[0].0, l[1].0, out);
    } else {
        b.and_u(l[0].0, l[1].0, out);
    }
    for &(q, ng) in &l {
        if ng {
            b.x(q);
        }
    }
}

/// `out[d] = [g1:g0 = d]` from one nonlinear witness instead of four independent ANDs.
/// All four one-hot predicates share `p = g0 & g1`:
/// `o3=p`, `o2=g1^p`, `o1=g0^p`, `o0=1^g0^g1^p`.
/// `clear_decode2_onehot_shared` reverses the Clifford fanout before measuring `p` away.
pub(crate) fn decode2_onehot_shared(b: &mut B, g0: QubitId, g1: QubitId, out: &[QubitId]) {
    assert_eq!(out.len(), 4);
    b.and_c(g0, g1, out[3]);
    b.cx(g1, out[2]);
    b.cx(out[3], out[2]);
    b.cx(g0, out[1]);
    b.cx(out[3], out[1]);
    b.x(out[0]);
    b.cx(g0, out[0]);
    b.cx(g1, out[0]);
    b.cx(out[3], out[0]);
}

pub(crate) fn clear_decode2_onehot_shared(b: &mut B, g0: QubitId, g1: QubitId, out: &[QubitId]) {
    assert_eq!(out.len(), 4);
    b.cx(out[3], out[0]);
    b.cx(g1, out[0]);
    b.cx(g0, out[0]);
    b.x(out[0]);
    b.cx(out[3], out[1]);
    b.cx(g0, out[1]);
    b.cx(out[3], out[2]);
    b.cx(g1, out[2]);
    b.and_u(g0, g1, out[3]);
}

/// `out[d] = e & [g4:g3:g2 = d]` for `d = 0..4`, using six nonlinear witnesses.
///
/// The first four output lanes double as the decision tree's `p0,u,v,w` witnesses. The
/// fifth output is `H4`; `q` is the only extra lane. All are borrowed clean lanes and are
/// returned to |0> by `clear_decode5_high_shared` after the decoded controls are consumed.
pub(crate) fn decode5_high_shared(
    b: &mut B,
    g2: QubitId,
    g3: QubitId,
    g4: QubitId,
    e: QubitId,
    out: &[QubitId],
    q: QubitId,
) {
    assert_eq!(out.len(), 5);
    // p0=e&!g4, u=p0&g2, v=p0&g3, w=u&g3.
    and_lit(b, e, (g4, true), out[0], true);
    b.and_c(out[0], g2, out[1]);
    b.and_c(out[0], g3, out[2]);
    b.and_c(out[1], g3, out[3]);

    // Temporarily turn p0 into p4=e^p0=e&g4, then q=p4&!g3 and H4=q&!g2.
    b.cx(e, out[0]);
    and_lit(b, out[0], (g3, true), q, true);
    b.cx(e, out[0]);
    and_lit(b, q, (g2, true), out[4], true);

    // H0=p0^u^v^w, H1=u^w, H2=v^w, H3=w.
    b.cx(out[1], out[0]);
    b.cx(out[2], out[0]);
    b.cx(out[3], out[0]);
    b.cx(out[3], out[1]);
    b.cx(out[3], out[2]);
}

pub(crate) fn clear_decode5_high_shared(
    b: &mut B,
    g2: QubitId,
    g3: QubitId,
    g4: QubitId,
    e: QubitId,
    out: &[QubitId],
    q: QubitId,
) {
    assert_eq!(out.len(), 5);
    // Reverse every Clifford fanout before measuring any parent witness.
    b.cx(out[3], out[2]);
    b.cx(out[3], out[1]);
    b.cx(out[3], out[0]);
    b.cx(out[2], out[0]);
    b.cx(out[1], out[0]);

    // Clear in reverse dependency order: H4, q, w, v, u, p0.
    and_lit(b, q, (g2, true), out[4], false);
    b.cx(e, out[0]);
    and_lit(b, out[0], (g3, true), q, false);
    b.cx(e, out[0]);
    b.and_u(out[1], g3, out[3]);
    b.and_u(out[0], g3, out[2]);
    b.and_u(out[0], g2, out[1]);
    and_lit(b, e, (g4, true), out[0], false);
}

/// out = ctl & lit (compute, out |0> before) or its measured uncompute
fn and_lit(b: &mut B, ctl: QubitId, lit: (QubitId, bool), out: QubitId, compute: bool) {
    if lit.1 {
        b.x(lit.0);
    }
    if compute {
        b.and_c(ctl, lit.0, out);
    } else {
        b.and_u(ctl, lit.0, out);
    }
    if lit.1 {
        b.x(lit.0);
    }
}

/// Digit of tick t: a = A.v[0] & [j >= 1], `r` = a & (A.v1 ^ B.v1) (|0> before), eq = [j = 1], adds with sign r ^ eq
/// under a. Leaves r; a and eq are uncomputed. `extra` = further clean lanes for the carry pool.
fn digit(b: &mut B, w: &SWalk, t: usize, sch: &SSched, sc: &Scr, r: QubitId, extra: &[QubitId]) {
    let c = sch.c[t];
    let js = w.js();
    let (a, eq) = (sc.a, sc.eq);
    let l1 = j_eq(w, 1, t);
    sec(b, "dg.ctl", |b| {
        // a = [j >= 1] & B.v odd (= A.v odd & [j >= 1] on every shot in the envelope; B.v is unchanged by the adds)
        b.x(js);
        b.and_c(w.bf(0), js, a);
        b.x(js);
        b.mbu_compute(eq, &l1, &sc.tmp[..JS - 1]);
        b.cx(w.af(t, 1), w.bf(1));
        b.and_c(a, w.bf(1), r);
        b.cx(w.af(t, 1), w.bf(1));
        b.cx(eq, r);
    });
    let (kv, kc) = kvc(sch, t);
    let mut pl = lsc(b, w, t, c, kv, kc);
    pl.extend(&sc.pool);
    pl.push(sc.e);
    if r != sc.one {
        pl.push(sc.one);
    }
    pl.extend(&sc.tmp);
    pl.extend(&sc.xs);
    pl.extend(extra);
    // A.v += (-1)^r a B.v on the value lanes
    let av: Vec<QubitId> = (0..kv).map(|f| w.af(t, f)).collect();
    let bv: Vec<QubitId> = (0..kv).map(|f| w.bf(f)).collect();
    sec(b, "dg.addv", |b| {
        for &x in &av {
            b.cx(r, x);
        }
        ctrl_add_pool(b, &bv, &av, a, &pl);
        for &x in &av {
            b.cx(r, x);
        }
    });
    // B.c -= (-1)^r a A.c on B's cofactor lanes
    let ac: Vec<QubitId> = (0..kc).map(|k| w.asig(t, k)).collect();
    let bc: Vec<QubitId> = (0..kc).map(|k| w.bsig(k)).collect();
    sec(b, "dg.addc", |b| {
        b.x(r);
        for &x in &bc {
            b.cx(r, x);
        }
        ctrl_add_pool(b, &ac, &bc, a, &pl);
        for &x in &bc {
            b.cx(r, x);
        }
        b.x(r);
    });
    lsc(b, w, t, c, kv, kc);
    sec(b, "dg.unctl", |b| {
        b.cx(eq, r);
        // [j = 1] now = [j = 0] after the halve (every unabsorbed shot has B.v odd; absorbed ones never j = 1): it
        // moves to e as the completion flag (the erase's control, then the strip's G, which erases it)
        b.cx(eq, sc.e);
        b.cx(sc.e, eq);
        b.x(js);
        b.and_u(w.bf(0), js, a);
        b.x(js);
    });
}

/// t -= d mod 2^|t| for a small unsigned d (`d` LSB first, its top lane |0>), as ~(~t + d) with logical-AND carries
/// on `pool` (>= |t| - 1).
fn sub_small(b: &mut B, d: &[QubitId], t: &[QubitId], pool: &[QubitId]) {
    use super::modp_ft::add_sext;
    for &q in t {
        b.x(q);
    }
    add_sext(b, d, t, pool);
    for &q in t {
        b.x(q);
    }
}

/// A ring boundary moves from c0 to c1: reassigned lanes take the new owner's sign.
fn fix_boundary(b: &mut B, lane: &dyn Fn(usize) -> QubitId, c0: usize, c1: usize) {
    if c1 > c0 {
        for l in c0..c1 {
            b.cx(lane(c1), lane(l));
            b.cx(lane(l - 1), lane(l));
        }
    } else if c1 < c0 {
        for l in (c1..c0).rev() {
            b.cx(lane(c1 - 1), lane(l));
            b.cx(lane(c0), lane(l));
        }
    }
}

/// Halve of tick t: relabel, boundary fixes, j -= 1 where B.v is odd.
fn halve(b: &mut B, w: &SWalk, t: usize, sch: &SSched, sc: &Scr) {
    sec(b, "hv", |b| {
        fix_boundary(b, &|f| w.af(t + 1, f), sch.c[t] - 1, sch.c[t + 1]);
        fix_boundary(b, &|f| w.bf(f), sch.c[t], sch.c[t + 1]);
        // j -= 1: h -= [j0 = 0] (frame t)
        let c = sc.tmp[0];
        and_lit(b, w.bf(0), w.j0_is(t, false), c, true);
        dec(b, c, &w.j, &sc.tmp[1..JS]);
        and_lit(b, w.bf(0), w.j0_is(t, false), c, false);
    });
}

/// Strip of tick t (frame t + 1): k = min(nu(A.v), 3) where j <= 0; ring A's barrel segment rotates down by k.
/// Scratch: G in e, k1 in a, k2 in eq, the rest in tmp; all clean again afterwards.
///
/// Exact three-Toffoli synthesis of the strip amount. With `t1 = G & !a0` and
/// `k2 = t1 & !a1`, the former predicate
///
///     k1 = t1 & (a1 | !a2)
///
/// is equivalently `k1 = t1 xor (k2 & a2)`. Thus the separate
/// `!a1 & a2` witness is unnecessary. `t1` is measurement-uncomputed after
/// the outputs have been formed; all input wires are restored.
pub(crate) fn strip_k_factor(
    b: &mut B,
    gq: QubitId,
    a0: QubitId,
    a1: QubitId,
    a2: QubitId,
    t1: QubitId,
    k1: QubitId,
    k2: QubitId,
) {
    b.x(a0);
    b.and_c(gq, a0, t1);
    b.x(a0);
    b.x(a1);
    b.and_c(t1, a1, k2);
    b.x(a1);
    b.cx(t1, k1);
    b.ccx(k2, a2, k1);
    b.x(a0);
    b.and_u(gq, a0, t1);
    b.x(a0);
}

fn strip(b: &mut B, w: &SWalk, t: usize, sch: &SSched, sc: &Scr) {
    let tn = t + 1;
    let wd = w.a.len();
    let js = w.js();
    let (gq, k1, k2) = (sc.e, sc.a, sc.eq);
    // G = [j <= 0] = sign ^ [j = 0]; e holds [j = 0] (the digit's completion flag)
    sec(b, "st.G", |b| b.cx(js, gq));
    // k: k2 = G & !a0 & !a1; k1 = G & !a0 & (a1 | !a2)
    let (a0, a1, a2) = (w.af(tn, 0), w.af(tn, 1), w.af(tn, 2));
    let t1 = sc.tmp[0];
    sec(b, "st.k", |b| {
        strip_k_factor(b, gq, a0, a1, a2, t1, k1, k2);
    });
    // barrel segment (frame order from the cofactor's sign lanes up to the value's top)
    let (ksv, ksc) = if t <= sch.t { (sch.ksv[t], sch.ksc[t]) } else { (sch.c[tn], wd - sch.c[tn] - 3) };
    let seg: Vec<QubitId> = (0..ksc + 3)
        .rev()
        .map(|s| w.asig(tn, s))
        .chain((0..ksv).map(|f| w.af(tn, f)))
        .collect();
    // d = value sign ^ cofactor sign, from lanes that hold them before and after the rotation (and are untouched
    // where k = 0)
    let d = sc.tmp[2];
    sec(b, "st.rot", |b| {
    b.cx(w.af(tn, ksv - 1), d);
    b.cx(w.asig(tn, ksc + 2), d);
    let rev: Vec<QubitId> = seg.iter().rev().cloned().collect();
    rot4_up(b, k1, k2, &rev);
    // the k lanes below the segment's top took cofactor sign lanes: lane ksv - i ^= d where k >= i
    let (u3, u1) = (sc.tmp[3], sc.tmp[4]);
    b.and_c(k1, k2, u3);
    b.ccx(d, u3, w.af(tn, ksv - 3));
    b.ccx(d, k2, w.af(tn, ksv - 2));
    b.cx(k1, u1);
    b.cx(k2, u1);
    b.cx(u3, u1);
    b.ccx(d, u1, w.af(tn, ksv - 1));
    b.cx(u3, u1);
    b.cx(k2, u1);
    b.cx(k1, u1);
    b.and_u(k1, k2, u3);
    b.cx(w.af(tn, ksv - 1), d);
    b.cx(w.asig(tn, ksc + 2), d);
    });
    // j -= k, E -= k
    sec(b, "st.cnt", |b| {
    // j -= k: h -= d = (k1 & [j0 = 0]) + k2 (E_0 still pre-strip), then E -= k; each one small ripple subtract
    let (u, d1, z) = (sc.tmp[0], sc.tmp[1], sc.tmp[2]);
    let cp = &sc.tmp[3..];
    and_lit(b, k1, w.j0_is(tn, false), u, true);
    b.and_c(u, k2, d1);
    b.cx(k2, u);
    sub_small(b, &[u, d1, z], &w.j, cp);
    b.cx(k2, u);
    b.and_u(u, k2, d1);
    and_lit(b, k1, w.j0_is(tn, false), u, false);
    sub_small(b, &[k1, k2, z], &w.ec, cp);
    });
    // G = sign(j) now and k = (-j) mod 4 there: k1 = j0, k2 = j0 ^ j1 (measured erase)
    sec(b, "st.erase", |b| {
        b.cx(js, gq);
        b.mbu_erase(k1, &[(js, false), w.j0_is(tn, true)], &[]);
        // k2 = j0 ^ h0 = E_0 ^ h0 ^ (t1 ^ e0p) (frame t + 1)
        let pol = (tn & 1 == 1) ^ w.e0p;
        b.cx(w.ec[0], w.j[0]);
        b.mbu_erase(k2, &[(js, false), (w.j[0], pol)], &[]);
        b.cx(w.ec[0], w.j[0]);
    });
}

/// Forward tick t: the digit record r (in `one`) is X-measured into `m`.
pub fn fwd_tick(b: &mut B, w: &SWalk, t: usize, sch: &SSched, sc: &Scr, m: BitId) {
    if t >= 2 {
        step_end(b, w, t, sch, sc, false);
    }
    digit(b, w, t, sch, sc, sc.one, &[]);
    b.hmr_to(sc.one, m);
    halve(b, w, t, sch, sc);
    strip(b, w, t, sch, sc);
}

/// Forward walk: init, ticks 1..=T, the closing absorption step. Returns the digit measurement bits (index t).
pub fn walk_forward(b: &mut B, w: &SWalk, sch: &SSched, sc: &Scr, e0: i64) -> Vec<BitId> {
    init(b, w, e0);
    let m = b.fresh_bits(sch.t + 1);
    for t in 1..=sch.t {
        fwd_tick(b, w, t, sch, sc, m[t]);
    }
    close_fwd(b, w, sch, sc);
    m
}

pub fn close_fwd(b: &mut B, w: &SWalk, sch: &SSched, sc: &Scr) {
    step_end(b, w, sch.t + 1, sch, sc, false);
}

// ---------------------------------------------------------------- regenerating tick (inverse walk)
//
// The regenerating tick keeps each step's digits r_i = a & (A.v1 ^ B.v1) in Q (ring layout: tick t's digit lands in
// frame lane QB - 1, one frame lane lower per tick) below a marker 1 set at the step end. At digit completion
// (j = 0 after the halve) the word W = 2D + 1 (D = sum r_i 2^i, g digits) satisfies W b = L mod 2^(g+1), where
// b = A.c >> g (odd) and L = B.c's low lanes: with s_i = 1 - 2 n_i and n_i = r_i ^ [i = g - 1], the step's quotient
// q = sum s_i 2^i obeys q b + L = 0 mod 2^(g+1), and -q = 2N + 1 - 2^g = 2D + 1 - 2^g + 2^g (mod 2^(g+1)).
// Erase: Q <- Q b mod 2^QB (the top g + 1 lanes become L mod 2^(g+1)), rotate up by g - 1 (L_0 to lane QB - 2,
// L_1 to QB - 1, L_k to k - 2), XOR L's bits back. Played backwards it regenerates the digits.

use super::frogdrop::crot_up;
use super::frogtail::{rot4_unit, GB, SB};

/// Lanes of the erase window (A.c significance 1..): g - 1 <= QB - 2 shifts plus b's QB lanes.
const WIN2: usize = 2 * QB - 1;

/// erase-time compressed widths (frame t + 1, after the halve)
fn kve(sch: &SSched, t: usize) -> (usize, usize, usize) {
    let c = sch.c[t + 1];
    if t <= sch.t {
        (c, sch.kev[t], sch.kec[t])
    } else {
        (c, c, sch.w - c)
    }
}

/// Lanes the normalizer's level k (k >= 2: shift 2^k; k = 1: the final rot4 by g' mod 4) must keep correct: a
/// completing shot with g' = g - 1 (g <= QB - 1) reads only b's bits 0..g from the window, which sit at lanes up to
/// g + (the shift still to come) after the level.
fn norm_need(k: usize) -> usize {
    let rest = |gp: usize| if k >= 2 { gp & ((1 << k) - 1) } else { gp & 3 };
    (0..QB - 1).filter(|&gp| k < 2 || (gp >> k) & 1 == 1).map(|gp| gp + 2 + rest(gp)).max().unwrap()
}

/// Add one exact modified-Booth radix-4 digit to `t`:
///
///     t += e * (y0 + y1 - 2*y2) * a  (mod 2^|t|),
///
/// where `y2` is the original low bit of `t` and `y0=None` denotes the
/// implicit zero below the least-significant multiplier bit. Both source
/// controls are snapshotted before `t` is touched. A degree-two HMR clear
/// removes every selected-source lane with only diagonal Z/CZ corrections.
/// `pool` is restored and needs `2*|t|+6` clean lanes.
pub(crate) fn radix4_digit_add(
    b: &mut B,
    a: &[QubitId],
    t: &[QubitId],
    e: QubitId,
    y1: QubitId,
    y0: Option<QubitId>,
    pool: &[QubitId],
) {
    let n = t.len();
    assert!(n >= 2 && a.len() >= n && pool.len() >= 2 * n + 6);
    let (sg, y1s, p, r, one, u, two) = (pool[0], pool[1], pool[2], pool[3], pool[4], pool[5], pool[6]);
    let src = &pool[7..7 + n];
    let carry = &pool[7 + n..7 + n + n - 1];

    // Snapshot both binary-row controls before touching either row. p=y0^y1
    // and r=y1^y2 encode the Booth magnitude: one=e&p, u=e&r,
    // two=u&!one. The one/two predicates are disjoint.
    b.quad_compute(sg, &[t[0]], &[]);
    b.quad_compute(y1s, &[y1], &[]);
    if let Some(q) = y0 {
        b.cx(q, p);
    }
    b.cx(y1s, p);
    b.cx(y1s, r);
    b.cx(sg, r);
    b.and_c(e, p, one);
    b.and_c(e, r, u);
    and_lit(b, u, (one, true), two, true);

    // |digit|*a: one selects a and two selects 2a. Each lane is a quadratic
    // XOR, so its later measurement correction is Clifford-only.
    for j in 0..n {
        let mut pairs = vec![(one, a[j])];
        if j > 0 {
            pairs.push((two, a[j - 1]));
        }
        b.quad_compute(src[j], &[], &pairs);
    }

    // y2 is the Booth sign. ~(~t + src) = t-src modulo 2^n.
    for &q in t {
        b.cx(sg, q);
    }
    add_sext(b, src, t, carry);
    for &q in t {
        b.cx(sg, q);
    }

    for j in 0..n {
        let mut pairs = vec![(one, a[j])];
        if j > 0 {
            pairs.push((two, a[j - 1]));
        }
        b.quad_erase(src[j], &[], &pairs);
    }

    // Clear the decode before the sign snapshot. The final low target bit is
    // y2 ^ (one & a0), independent of whether the digit was added or subtracted.
    and_lit(b, u, (one, true), two, false);
    b.and_u(e, r, u);
    b.cx(sg, r);
    b.cx(y1s, r);
    b.quad_erase(sg, &[t[0]], &[(one, a[0])]);
    b.and_u(e, p, one);
    b.cx(y1s, p);
    if let Some(q) = y0 {
        b.cx(q, p);
    }
    b.quad_erase(y1s, &[y1], &[]);
}

/// Digit erase of tick t (after the halve; e = [j = 0]).
fn finish_digits(b: &mut B, w: &SWalk, t: usize, sch: &SSched, sc: &Scr) {
    let q = w.qfr(t);
    if t == 1 {
        // every shot completes its first step here: g = 1, b = 1, W = 2 r + 1 = L mod 4, so r = L_1
        b.cx(w.bsig(1), q[QB - 1]);
        b.x(q[QB - 2]);
        return;
    }
    let (cz, kv, kc) = kve(sch, t);
    let zl = lsc_from(b, w, t + 1, cz, kv, kc, 1 + WIN2, QB);
    let g = &sc.sp[..GB];
    let a0 = w.asig(t + 1, 0);
    let win: Vec<QubitId> = (0..WIN2).map(|k| w.asig(t + 1, 1 + k)).collect();
    // normalizer on A.c >> 1: g' = nu(A.c) - 1 = g - 1 for completing shots (frogtail's, rot4 for the low pair);
    // e (the completion flag) is busy, so the zero tests borrow the pool and LSC lanes, else split the long test
    b.begin();
    for k in (0..SB).rev() {
        let s = 1usize << k;
        let lits: Vec<(QubitId, bool)> = win[..s].iter().map(|&x| (x, true)).collect();
        let mut temps = sc.tmp.clone();
        temps.push(a0);
        temps.extend(&sc.sp[..k]);
        temps.extend(&sc.pool);
        temps.extend(&zl);
        if temps.len() + 2 >= s {
            b.mbu_compute(sc.sp[k], &lits, &temps);
        } else {
            let (pq, rest) = temps.split_last().unwrap();
            b.mbu_compute(*pq, &lits[..s / 2], rest);
            let mut l2 = vec![(*pq, false)];
            l2.extend(&lits[s / 2..]);
            b.mbu_compute(sc.sp[k], &l2, rest);
            b.mbu_erase(*pq, &lits[..s / 2], rest);
        }
        if k == 1 {
            let tt = sc.tmp[0];
            b.and_c(sc.sp[1], win[2], tt);
            b.mbu_compute(sc.sp[0], &[(win[0], true), (tt, true)], &[]);
            b.and_u(sc.sp[1], win[2], tt);
            let rv: Vec<QubitId> = win[..norm_need(1)].iter().rev().cloned().collect();
            rot4_up(b, sc.sp[0], sc.sp[1], &rv);
            break;
        }
        for x in 0..norm_need(k) {
            b.cswap(sc.sp[k], win[x], win[x + s]);
        }
    }
    let nr = b.end();
    sec(b, "fd.norm1", |b| b.play(&nr, false));
    let e = sc.e;
    // Q <- Q b mod 2^QB: b odd, Q b = Q + sum_i Q_i 2^(i+1) (b >> 1); top-down rows under Q_i & e
    let mut pool: Vec<QubitId> = sc.tmp.clone();
    pool.push(a0);
    pool.extend(&sc.pool);
    pool.extend(&zl);
    sec(b, "fd.mul", |b| {
        // Modified-Booth groups (q[2j+1],q[2j],q[2j-1]), high to low.
        // The omitted q[20] group starts at bit 21 after multiplication by 2a
        // and is therefore zero modulo 2^QB.
        for j in (0..QB / 2).rev() {
            let lo = 2 * j;
            let hi = lo + 1;
            let nm = QB - hi;
            radix4_digit_add(
                b,
                &win[1..1 + nm],
                &q[hi..QB],
                e,
                q[lo],
                lo.checked_sub(1).map(|k| q[k]),
                &pool,
            );
        }
    });
    // rotate Q up by g' where e
    let (c1, c2) = (sc.tmp[0], sc.tmp[1]);
    sec(b, "fd.rot", |b| {
    for k in [0usize, 2] {
        b.and_c(g[k], e, c1);
        b.and_c(g[k + 1], e, c2);
        rot4_unit(b, c1, c2, &q, 1 << k);
        b.and_u(g[k + 1], e, c2);
        b.and_u(g[k], e, c1);
    }
    b.and_c(g[4], e, c1);
    crot_up(b, c1, &q, 16);
    b.and_u(g[4], e, c1);
    });
    // XOR L back where e: L_0 = 1 in lane QB - 2, L_1 in lane QB - 1, L_k in lane k - 2 for 2 <= k <= g (lane l < g')
    sec(b, "fd.mask", |b| {
    b.cx(e, q[QB - 2]);
    b.ccx(e, w.bsig(1), q[QB - 1]);
    // f = e & [l < g'] by toggles f ^= [g' = l] & e = H_(l >> 2) & L_(l & 3): L = one-hot of g' mod 4 (held),
    // H = e & [g' >> 2 = c] from a prefix chain over (e, g4, g3, g2)
    let f = sc.tmp[0];
    let lo: Vec<QubitId> = sc.tmp[4..8].to_vec();
    decode2_onehot_shared(b, g[0], g[1], &lo);
    let hi = &sc.pool[..5];
    let hq = sc.pool[5];
    decode5_high_shared(b, g[2], g[3], g[4], e, hi, hq);
    b.cx(e, f);
    for l in 0..QB - 1 {
        let c = l >> 2;
        debug_assert!(c < 5);
        b.ccx(hi[c], lo[l & 3], f);
        if l + 2 < QB {
            b.ccx(f, w.bsig(l + 2), q[l]);
        }
    }
    clear_decode5_high_shared(b, g[2], g[3], g[4], e, hi, hq);
    clear_decode2_onehot_shared(b, g[0], g[1], &lo);
    });
    sec(b, "fd.norm2", |b| b.play(&nr, true));
    lsc_from(b, w, t + 1, cz, kv, kc, 1 + WIN2, QB);
}

#[cfg(test)]
pub fn finish_digits_pub(b: &mut B, w: &SWalk, t: usize, sch: &SSched, sc: &Scr) {
    finish_digits(b, w, t, sch, sc);
}

/// Regenerating tick t as two recordings: (step end + digit, halve + erase + strip).
pub fn rec_regen_tick(b: &mut B, w: &SWalk, t: usize, sch: &SSched, sc: &Scr) -> (Vec<G>, Vec<G>) {
    b.begin();
    if t >= 2 {
        step_end(b, w, t, sch, sc, true);
    }
    digit(b, w, t, sch, sc, w.qfr(t)[QB - 1], &[]);
    let p1 = b.end();
    b.begin();
    halve(b, w, t, sch, sc);
    finish_digits(b, w, t, sch, sc);
    strip(b, w, t, sch, sc);
    let p3 = b.end();
    (p1, p3)
}

pub fn rec_regen_close(b: &mut B, w: &SWalk, sch: &SSched, sc: &Scr) -> Vec<G> {
    b.begin();
    step_end(b, w, sch.t + 1, sch, sc, true);
    b.end()
}

/// Inverse of walk_forward (Q, clean, in `w.q`; |0> again afterwards): the regenerating closing step and ticks
/// played backwards, cancelling each digit measurement's phase.
pub fn walk_inverse(b: &mut B, w: &SWalk, sch: &SSched, sc: &Scr, m: &[BitId], e0: i64) {
    SEC_INV.with(|c| c.set(true));
    let ce = rec_regen_close(b, w, sch, sc);
    b.play(&ce, true);
    for t in (1..=sch.t).rev() {
        let (p1, p3) = rec_regen_tick(b, w, t, sch, sc);
        b.play(&p3, true);
        b.z_if(w.qfr(t)[QB - 1], m[t]);
        b.play(&p1, true);
    }
    init_q(b, w, e0);
    SEC_INV.with(|c| c.set(false));
}

/// init with the first step's digit-word marker (regenerating walk)
pub fn init_q(b: &mut B, w: &SWalk, e0: i64) {
    init(b, w, e0);
    b.x(w.qfr(1)[QB - 2]);
}

/// bits of m (ticks since the absorption) and of the combined shift sh = m + E
pub const MBS: usize = 6;
pub const SHB: usize = 7;

/// After walk_forward every finished shot is absorbed: A = (0, 2^m), B = (-2s, C), j = 3, E = E0 - S. Rebuilds
/// C' = C 2^(m + E) (x'^-1 = (-1)^S' C' 2^-H0) in R = B's cofactor lanes followed by lanes of A, two's complement
/// over `rlen` lanes. `mr` (SHB lanes, |0> before) ends holding m; `tm` = 1 + (MBS - 1) clean qubits (|0> again
/// afterwards). Recorded; returns (R, key qubit holding s, recording).
pub fn unabsorb(
    b: &mut B,
    w: &SWalk,
    sch: &SSched,
    rlen: usize,
    mr: &[QubitId],
    tm: &[QubitId],
    dirty: &[QubitId],
) -> (Vec<QubitId>, QubitId, Vec<G>) {
    use super::arith::ttk_add;
    use super::mask::onehot_scan;
    let t = sch.t + 1;
    let nm = 1usize << MBS;
    let oh: Vec<QubitId> = (0..nm).map(|k| w.asig(t, k)).collect();
    let cl = sch.w - sch.c[t];
    let mut r: Vec<QubitId> = (0..cl).map(|s| w.bsig(s)).collect();
    let ext: Vec<QubitId> = (0..rlen - cl).map(|f| w.af(t, f)).collect();
    assert!(sch.w - sch.c[t] - (rlen - cl) >= nm, "one-hot lanes overlap the C' extension");
    r.extend(&ext);
    let sg = tm[0];
    b.begin();
    // m from the one-hot
    for k in 0..nm {
        for i in 0..MBS {
            if (k >> i) & 1 == 1 {
                b.cx(oh[k], mr[i]);
            }
        }
    }
    // sh = m + E - EOFF (mod 2^SHB; E unsigned, zero-extended by a clean lane; EOFF by decrements under a |1>)
    assert!(EB < SHB);
    let mut ev: Vec<QubitId> = w.ec.clone();
    ev.extend(&tm[1..1 + SHB - EB]);
    let one = tm[0];
    b.begin();
    ttk_add(b, &ev, &mr[..SHB], None, None);
    b.x(one);
    for i in 0..SHB {
        if (EOFF >> i) & 1 == 1 {
            dec(b, one, &mr[i..SHB], &tm[1..SHB - i]);
        }
    }
    b.x(one);
    let ad = b.end();
    b.play(&ad, false);
    // sign-extend C over R; per level: clear the 2^i top lanes (sign copies) where sh_i, rotate up by 2^i
    b.cx(r[cl - 1], sg);
    for &q in &ext {
        b.cx(sg, q);
    }
    for i in 0..SHB {
        for k in 0..(1usize << i) {
            b.ccx(mr[i], sg, r[rlen - 1 - k]);
        }
        crot_up(b, mr[i], &r, 1 << i);
    }
    b.cx(r[rlen - 1], sg);
    // back to m, then the one-hot erased against it
    b.play(&ad, true);
    onehot_scan(b, &mr[..MBS], &tm[1..MBS], 0, nm, 0, |b, v, ctrls| {
        mc_xor(b, ctrls, oh[v], &[], dirty);
    });
    let rec = b.end();
    b.play(&rec, false);
    (r, w.bf(1), rec)
}
