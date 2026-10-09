//! SKY-COF k2 letter decoder: the k = 0 decoder plus two steps of lookback through the Kaliski
//! predecessors, so that fewer ticks push a history bit.
//!
//! # Rule (post-state `(s, r)` of a non-parked tick `t >= 3`, not C, i.e. `bit1(s) = 0`)
//! With `rho = r / s`, `b2 = bit2(s)`, `b3 = bit3(s)`, `beta = bit1(r) xor bit3(s)`:
//! * A when `rho < 1/2` (the k = 0 rule), or `b2 = 0, b3 = 1, rho < 5/8`, or `b2 = 1, rho < 3/4`,
//!   or `b2 = 1, beta = 0, rho > 5/4`;
//! * B when `b2 = 1, beta = 1, rho > 3/4`;
//! * otherwise ambiguous (one bit pushed).
//! Each "rho < theta" / "rho > theta" is certified, never guessed: the tests below only claim a
//! relation that holds exactly for every value consistent with the window bits.
//!
//! # Window arithmetic
//! `lo = max(1, e - w)`, `n = e - lo`, `R = r[lo..e)`, `S = s[lo..e)`, `S_k = S >> k = s[lo+k..e)`.
//! An (n+1)-bit two's-complement accumulator `A = [r[lo..e), s[0]]` (s[0] = 0 on every pre-park
//! post-state; the accumulator is restored exactly whatever it holds) visits
//! * `L1 = R - S_1`                 : `N1 = [L1 < 0]`, `N2 = [L1 < S_3]`, `N3 = [L1 < S_2]`;
//! * `U1 = R - S_1 - 1`             : `P3 = [U1 > S_2]`;
//! * `V  = U1 - S_1 - s[lo] = R-S-1`: `P5 = [V > S_2]`.
//! (`r odd`, `s even` give: `N1 => r < s/2`, `N2 => r < 5s/8`, `N3 => r < 3s/4`, `P3 => r > 3s/4`,
//! `P5 => r > 5s/4`, exactly.)
//!
//! # Circuit
//! `GA = [A certain]`, `GB = [B certain]` are accumulated term by term while the accumulator moves
//! (each compare is a carry chain whose top carry is used once and erased), then
//! `amb = D & !GA & !GB` controls the history shift and `typ ^= D & GA` erases a certain A.
//! `GA` and `GB` are then measured; the phase repair recomputes only the terms whose register
//! measured 1 while the accumulator walks back (expected half the compares).
//!
//! [`push`] / [`pop`] are exact inverses on the same post-state; [`model`] is the bit-exact
//! classical replica for every input.
use super::decoder::{shift_in, shift_out, Hreg, TickIo};
use crate::circuit::{BitId, QubitId as Q};
use crate::point_add::builder::Builder;

/// Smallest compare width the circuit supports.
pub const MIN_N: usize = 5;

#[derive(Clone, Copy, Debug)]
pub struct K2Cfg {
    /// window bits
    pub w: usize,
    /// qubit cap the call must stay under (scratch is taken from `cap - active`)
    pub cap: usize,
    /// a wire that holds 0 whenever `D` can be 1 (the walk's odometer bit: zero until the walk
    /// parks, and `D = 0` from the park on); used as a carry-in so that no step needs a fresh wire
    pub zero_hint: Option<Q>,
}

pub fn geom(e: usize, w: usize) -> (usize, usize) {
    let lo = e.saturating_sub(w).max(1);
    (lo, e - lo)
}

fn avail(c: &Builder, cap: usize) -> usize {
    cap.saturating_sub(c.active_qubits() as usize)
}

// ─── literals and small ANDs ────────────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug)]
pub struct L(pub Q, pub bool);

fn neg(c: &mut Builder, ls: &[L]) {
    for l in ls {
        if l.1 {
            c.x(l.0);
        }
    }
}

/// fresh `t = a & b` (1 CCX)
fn and2(c: &mut Builder, a: L, b: L) -> Q {
    neg(c, &[a, b]);
    let t = c.alloc_qubit();
    c.ccx(a.0, b.0, t);
    neg(c, &[a, b]);
    t
}

/// erase `t = a & b` by measurement (0 CCX)
fn and2_erase(c: &mut Builder, t: Q, a: L, b: L) {
    let m = c.alloc_bit();
    c.hmr(t, m);
    neg(c, &[a, b]);
    c.cz_if(a.0, b.0, m);
    neg(c, &[a, b]);
    c.free_bit(m);
    c.release_clean(t);
}

/// `tgt ^= AND(lits)` (len - 1 CCX for len >= 2; temps: len - 2)
fn xor_and(c: &mut Builder, lits: &[L], tgt: Q) {
    match lits.len() {
        0 => c.x(tgt),
        1 => {
            neg(c, lits);
            c.cx(lits[0].0, tgt);
            neg(c, lits);
        }
        _ => {
            let mut chain: Vec<(Q, L, L)> = Vec::new();
            let mut acc = lits[0];
            for &l in &lits[1..lits.len() - 1] {
                let t = and2(c, acc, l);
                chain.push((t, acc, l));
                acc = L(t, false);
            }
            let last = lits[lits.len() - 1];
            neg(c, &[acc, last]);
            c.ccx(acc.0, last.0, tgt);
            neg(c, &[acc, last]);
            for (t, a, b) in chain.into_iter().rev() {
                and2_erase(c, t, a, b);
            }
        }
    }
}

/// phase `(-1)^AND(lits)` (len - 2 CCX for len >= 2)
fn phase_and(c: &mut Builder, lits: &[L]) {
    match lits.len() {
        0 => {}
        1 => {
            neg(c, lits);
            c.z_if(lits[0].0, crate::circuit::NO_BIT);
            neg(c, lits);
        }
        _ => {
            let mut chain: Vec<(Q, L, L)> = Vec::new();
            let mut acc = lits[0];
            for &l in &lits[1..lits.len() - 1] {
                let t = and2(c, acc, l);
                chain.push((t, acc, l));
                acc = L(t, false);
            }
            let last = lits[lits.len() - 1];
            neg(c, &[acc, last]);
            c.cz(acc.0, last.0);
            neg(c, &[acc, last]);
            for (t, a, b) in chain.into_iter().rev() {
                and2_erase(c, t, a, b);
            }
        }
    }
}

// ─── in-place add of a short operand ─────────────────────────────────────────────────────────

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Gid,
    Maj,
    Ext,
    None_,
}

/// `t += a + cin (mod 2^m)`, `a` (k <= m - 1 bits) zero-extended. The first `fresh` operand
/// positions carry on fresh wires (Gidney, 1 CCX), the rest in place (Cuccaro MAJ / UMA, 2 CCX).
/// Above the operand: with two positions left (one carry position and the top) the carry is
/// applied in place (CCX + CX); with more, the carries go on fresh wires (1 CCX each).
fn add_short(c: &mut Builder, a: &[Q], t: &[Q], cin: Option<Q>, fresh: usize) {
    let m = t.len();
    let k = a.len();
    assert!(k + 1 <= m && m >= 2 && k >= 1);
    let mut carry: Vec<Option<Q>> = vec![None; m];
    carry[0] = cin;
    let inplace_top = m - k == 2;
    let ext_end = if inplace_top { k } else { m - 1 };
    let mut kind = vec![Kind::None_; m - 1];
    for i in 0..ext_end {
        let ci = carry[i];
        if i < k {
            let ai = a[i];
            if i < fresh || ci.is_none() {
                if let Some(ci) = ci {
                    c.cx(ci, ai);
                    c.cx(ci, t[i]);
                }
                let nt = c.alloc_qubit();
                c.ccx(ai, t[i], nt);
                if let Some(ci) = ci {
                    c.cx(ci, nt);
                }
                carry[i + 1] = Some(nt);
                kind[i] = Kind::Gid;
            } else {
                let ci = ci.unwrap();
                c.cx(ai, t[i]);
                c.cx(ai, ci);
                c.ccx(ci, t[i], ai);
                carry[i + 1] = Some(ai);
                kind[i] = Kind::Maj;
            }
        } else if let Some(ci) = ci {
            let nt = c.alloc_qubit();
            c.ccx(t[i], ci, nt);
            carry[i + 1] = Some(nt);
            kind[i] = Kind::Ext;
        } else {
            kind[i] = Kind::None_;
        }
    }
    if inplace_top {
        // positions k (no operand) and k + 1 = m - 1 (top): t[k+1] ^= c & t[k]; t[k] ^= c
        if let Some(ck) = carry[k] {
            c.ccx(ck, t[k], t[k + 1]);
            c.cx(ck, t[k]);
        }
    } else if let Some(ct) = carry[m - 1] {
        c.cx(ct, t[m - 1]);
    }
    for i in (0..ext_end).rev() {
        let ci = carry[i];
        match kind[i] {
            Kind::None_ => {}
            Kind::Ext => {
                let nt = carry[i + 1].unwrap();
                let ci = ci.unwrap();
                let mb = c.alloc_bit();
                c.hmr(nt, mb);
                c.cz_if(t[i], ci, mb);
                c.free_bit(mb);
                c.release_clean(nt);
                c.cx(ci, t[i]);
            }
            Kind::Gid => {
                let ai = a[i];
                let nt = carry[i + 1].unwrap();
                if let Some(ci) = ci {
                    c.cx(ci, nt);
                }
                let mb = c.alloc_bit();
                c.hmr(nt, mb);
                c.cz_if(ai, t[i], mb);
                c.free_bit(mb);
                c.release_clean(nt);
                c.cx(ai, t[i]);
                if let Some(ci) = ci {
                    c.cx(ci, ai);
                    c.cx(ci, t[i]);
                }
            }
            Kind::Maj => {
                let ai = a[i];
                let ci = ci.unwrap();
                c.ccx(ci, t[i], ai);
                c.cx(ai, ci);
                c.cx(ai, t[i]);
                c.cx(ci, ai);
                c.cx(ai, t[i]);
                c.cx(ci, ai);
            }
        }
    }
}

/// Fresh wires [`add_short`] needs above its operand.
fn ext_wires(m: usize, k: usize) -> usize {
    if m - k <= 2 { 0 } else { m - 1 - k }
}

/// Carry-in of an in-place step.
#[derive(Clone, Copy)]
enum Cin {
    /// no carry-in (position 0 then needs a fresh wire)
    None,
    /// no carry-in, with a wire known to hold 0 that serves as the chain's carry-in
    Zero(Q),
    /// carry-in = the wire's value
    Wire(Q),
}

/// `t -= a + cin` or `t += a + cin` with the cheapest plan the room allows.
fn ip(c: &mut Builder, a: &[Q], t: &[Q], cin: Cin, sub: bool, cap: usize) {
    let (m, k) = (t.len(), a.len());
    let free = avail(c, cap);
    let (cw, need_g0) = match cin {
        Cin::None => (None, 1usize),
        Cin::Zero(q) | Cin::Wire(q) => (Some(q), 0),
    };
    let need_min = ext_wires(m, k) + need_g0;
    assert!(free >= need_min, "k2 ip: room {free} < {need_min}");
    let fresh = (free - ext_wires(m, k)).min(k).max(need_g0);
    if sub {
        c.x_all(t);
    }
    add_short(c, a, t, cw, fresh);
    if sub {
        c.x_all(t);
    }
}

// ─── multi-controlled X / Z with clean or borrowed scratch ───────────────────────────────────

/// `tgt ^= AND(lits)`. With `k - 2` clean wires available: a Toffoli ladder (`k - 1` CCX). Otherwise
/// borrowed wires (`dirty`, any state, restored): the borrowed-ancilla V-chain, `4 (k - 2)` CCX.
pub fn mcx(c: &mut Builder, lits: &[L], tgt: Q, dirty: &[Q], cap: usize) {
    let k = lits.len();
    if k <= 2 || avail(c, cap) >= k - 2 {
        xor_and(c, lits, tgt);
        return;
    }
    let anc: Vec<Q> = dirty.iter().copied().filter(|q| *q != tgt && lits.iter().all(|l| l.0 != *q)).take(k - 2).collect();
    assert!(anc.len() == k - 2, "k2 mcx: {} borrowable wires for {k} controls", anc.len());
    neg(c, lits);
    let w: Vec<Q> = lits.iter().map(|l| l.0).collect();
    vchain(c, &w, &anc, Tgt::X(tgt));
    neg(c, lits);
}

/// Phase `(-1)^AND(lits)`: a clean ladder (`k - 2` CCX) when `k - 2` wires are free, otherwise a
/// borrowed wire `d` toggled by AND(lits) around a Z: `X^f Z X^f Z = (-1)^f`.
pub fn mcz(c: &mut Builder, lits: &[L], dirty: &[Q], cap: usize) {
    let k = lits.len();
    if k <= 2 || avail(c, cap) >= k - 2 {
        phase_and(c, lits);
        return;
    }
    let d = *dirty.iter().find(|q| lits.iter().all(|l| l.0 != **q)).expect("k2 mcz: no borrowable wire");
    let rest: Vec<Q> = dirty.iter().copied().filter(|q| *q != d).collect();
    mcx(c, lits, d, &rest, cap);
    c.z_if(d, crate::circuit::NO_BIT);
    mcx(c, lits, d, &rest, cap);
    c.z_if(d, crate::circuit::NO_BIT);
}

#[derive(Clone, Copy)]
enum Tgt {
    X(Q),
}

/// Borrowed-ancilla V-chain (Barenco et al., Lemma 7.2) for `k >= 3` controls `w` and `k - 2`
/// borrowed wires `a`: applies X on `t` controlled by AND(w).
fn vchain(c: &mut Builder, w: &[Q], a: &[Q], t: Tgt) {
    let k = w.len();
    assert!(k >= 3 && a.len() == k - 2);
    let top = |c: &mut Builder| match t {
        Tgt::X(q) => c.ccx(w[k - 1], a[k - 3], q),
    };
    let down = |c: &mut Builder| {
        for i in (1..k - 2).rev() {
            c.ccx(w[i + 1], a[i - 1], a[i]);
        }
    };
    let up = |c: &mut Builder| {
        for i in 1..k - 2 {
            c.ccx(w[i + 1], a[i - 1], a[i]);
        }
    };
    for _ in 0..2 {
        top(c);
        down(c);
        c.ccx(w[0], w[1], a[0]);
        up(c);
    }
}

// ─── compares ────────────────────────────────────────────────────────────────────────────────

/// Open carry chain of `a + ~b + 1` over `j = a.len() = b.len()` positions (`cin` holds 1; `b` is
/// inverted in place for the duration). The first `gid` positions carry on fresh wires (1 CCX
/// each, erased by measurement), the rest in place on `a` (MAJ, 1 CCX forward, 1 back).
/// [`Cmp::top`] = carry-out = `[a >= b]`.
struct Cmp {
    a: Vec<Q>,
    b: Vec<Q>,
    cin: Q,
    gid: usize,
    fresh: Vec<Q>,
}

impl Cmp {
    fn top(&self) -> Q {
        let j = self.a.len();
        if self.gid == j { self.fresh[j - 1] } else { self.a[j - 1] }
    }
    fn carry(&self, i: usize) -> Q {
        if i == 0 {
            self.cin
        } else if i <= self.gid {
            self.fresh[i - 1]
        } else {
            self.a[i - 1]
        }
    }
}

fn cmp_open(c: &mut Builder, a: &[Q], b: &[Q], cin: Q, gid_room: usize) -> Cmp {
    let j = a.len();
    assert!(j >= 1 && b.len() == j);
    let gid = gid_room.min(j);
    let mut cm = Cmp { a: a.to_vec(), b: b.to_vec(), cin, gid, fresh: Vec::new() };
    c.x_all(b);
    for i in 0..j {
        let ci = cm.carry(i);
        if i < gid {
            c.cx(ci, a[i]);
            c.cx(ci, b[i]);
            let t = c.alloc_qubit();
            c.ccx(a[i], b[i], t);
            c.cx(ci, t);
            cm.fresh.push(t);
        } else {
            c.cx(a[i], b[i]);
            c.cx(a[i], ci);
            c.ccx(ci, b[i], a[i]);
        }
    }
    cm
}

fn cmp_close(c: &mut Builder, cm: Cmp) {
    let j = cm.a.len();
    for i in (0..j).rev() {
        let ci = cm.carry(i);
        if i < cm.gid {
            let t = cm.fresh[i];
            c.cx(ci, t);
            let mb = c.alloc_bit();
            c.hmr(t, mb);
            c.cz_if(cm.a[i], cm.b[i], mb);
            c.free_bit(mb);
            c.release_clean(t);
            c.cx(ci, cm.a[i]);
            c.cx(ci, cm.b[i]);
        } else {
            c.ccx(ci, cm.b[i], cm.a[i]);
            c.cx(cm.a[i], ci);
            c.cx(cm.a[i], cm.b[i]);
        }
    }
    c.x_all(&cm.b);
}

// ─── the decoder ─────────────────────────────────────────────────────────────────────────────

struct Wires {
    n: usize,
    acc: Vec<Q>,
    sw1: Vec<Q>,
    sw2: Vec<Q>,
    sw3: Vec<Q>,
    slo: Q,
    r0: Q,
    b2: Q,
    b3: Q,
    beta: Q,
    copies: bool,
    d: Q,
    d_mode: DMode,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum DMode {
    /// supplied by the caller (already `en & !s1`)
    Given,
    /// fresh `en & !s1`
    FreshEn,
    /// fresh copy of `!s1`
    FreshCopy,
    /// `s1` inverted in place
    InPlace,
}

fn setup(c: &mut Builder, io: &TickIo, w: usize, d_given: Option<Q>) -> Wires {
    let (lo, n) = geom(io.e, w);
    assert!(n >= MIN_N, "k2 decoder: compare width {n} < {MIN_N}");
    assert!(io.s.len() >= io.e && io.r.len() >= io.e);
    assert!(io.park.is_none() && io.cflag.is_none(), "k2 decoder: no park / cflag options");
    let (s, r) = (io.s, io.r);
    let mut acc: Vec<Q> = r[lo..io.e].to_vec();
    acc.push(s[0]);
    let s1 = s[1];
    let (d, d_mode) = match (d_given, io.en) {
        (Some(d), _) => (d, DMode::Given),
        (None, Some(en)) => {
            let d = c.alloc_qubit();
            c.x(s1);
            c.ccx(en, s1, d);
            c.x(s1);
            (d, DMode::FreshEn)
        }
        (None, None) if lo == 1 => {
            // s[1] is the window's low bit (the V step reads it as carry-in): D on a copy
            let d = c.alloc_qubit();
            c.cx(s1, d);
            c.x(d);
            (d, DMode::FreshCopy)
        }
        (None, None) => {
            c.x(s1);
            (s1, DMode::InPlace)
        }
    };
    let copies = lo == 1;
    let (b2, b3, beta) = if copies {
        let b2 = c.alloc_qubit();
        c.cx(s[2], b2);
        let b3 = c.alloc_qubit();
        c.cx(s[3], b3);
        let be = c.alloc_qubit();
        c.cx(r[1], be);
        c.cx(s[3], be);
        (b2, b3, be)
    } else {
        c.cx(s[3], r[1]);
        (s[2], s[3], r[1])
    };
    Wires {
        n,
        acc,
        sw1: s[lo + 1..io.e].to_vec(),
        sw2: s[lo + 2..io.e].to_vec(),
        sw3: s[lo + 3..io.e].to_vec(),
        slo: s[lo],
        r0: r[0],
        b2,
        b3,
        beta,
        copies,
        d,
        d_mode,
    }
}

fn teardown(c: &mut Builder, io: &TickIo, wr: Wires) {
    let (s, r) = (io.s, io.r);
    if wr.copies {
        c.cx(s[3], wr.beta);
        c.cx(r[1], wr.beta);
        c.release_clean(wr.beta);
        c.cx(s[3], wr.b3);
        c.release_clean(wr.b3);
        c.cx(s[2], wr.b2);
        c.release_clean(wr.b2);
    } else {
        c.cx(s[3], r[1]);
    }
    let s1 = s[1];
    match wr.d_mode {
        DMode::Given => {}
        DMode::FreshEn => {
            let en = io.en.unwrap();
            let m = c.alloc_bit();
            c.hmr(wr.d, m);
            c.x(s1);
            c.cz_if(en, s1, m);
            c.x(s1);
            c.free_bit(m);
            c.release_clean(wr.d);
        }
        DMode::FreshCopy => {
            c.x(wr.d);
            c.cx(s1, wr.d);
            c.release_clean(wr.d);
        }
        DMode::InPlace => c.x(s1),
    }
}

/// What a term does: XOR into the accumulator `K` (and into `typ` for an A term), or apply its
/// phase (repair of a measured `K`).
#[derive(Clone, Copy)]
enum Act {
    Xor { k: Q, typ: Option<Q> },
    Phase,
}

struct Ctx<'a> {
    cap: usize,
    dirty: &'a [Q],
}

fn apply(c: &mut Builder, lits: &[L], act: Act, cx: &Ctx) {
    match act {
        Act::Xor { k, typ } => {
            mcx(c, lits, k, cx.dirty, cx.cap);
            if let Some(t) = typ {
                mcx(c, lits, t, cx.dirty, cx.cap);
            }
        }
        Act::Phase => mcz(c, lits, cx.dirty, cx.cap),
    }
}

/// Fresh compare positions to use, leaving room for a term's clean ladder when possible.
fn gid_room(c: &Builder, cap: usize, ladder: usize) -> usize {
    let free = avail(c, cap);
    if free > ladder { free - ladder } else { 0 }
}

/// At L1: terms a, b, c (A terms).
fn terms_l1(c: &mut Builder, wr: &Wires, act: Act, cx: &Ctx) {
    let n = wr.n;
    let a = &wr.acc;
    let x1 = a[n];
    let typ_act = |act: Act| act;
    // a: D & x1
    apply(c, &[L(wr.d, false), L(x1, false)], typ_act(act), cx);
    // b: D & !b2 & b3 & !x1 & a[n-3..n) == 0 & ![a[0..n-3) >= S_3]
    let g = gid_room(c, cx.cap, 6);
    let cm = cmp_open(c, &a[..n - 3], &wr.sw3, wr.r0, g);
    let ge = cm.top();
    apply(c, &[L(wr.d, false), L(wr.b2, true), L(wr.b3, false), L(x1, true), L(a[n - 3], true), L(a[n - 2], true),
        L(a[n - 1], true), L(ge, true)], act, cx);
    cmp_close(c, cm);
    // c: D & b2 & !x1 & a[n-2..n) == 0 & ![a[0..n-2) >= S_2]
    let g = gid_room(c, cx.cap, 4);
    let cm = cmp_open(c, &a[..n - 2], &wr.sw2, wr.r0, g);
    let ge = cm.top();
    apply(c, &[L(wr.d, false), L(wr.b2, false), L(x1, true), L(a[n - 2], true), L(a[n - 1], true), L(ge, true)], act, cx);
    cmp_close(c, cm);
}

/// At U1 (B term e, `beta`) or V (A term d, `!beta`):
/// D & b2 & [beta] & !x & (a[n-2] | a[n-1] | ![S_2 >= a[0..n-2)])
///   = (D & b2 & [beta] & !x)  xor  (D & b2 & [beta] & !x & !a[n-2] & !a[n-1] & [S_2 >= a[0..n-2)]).
fn term_upper(c: &mut Builder, wr: &Wires, beta_val: bool, act: Act, cx: &Ctx) {
    let n = wr.n;
    let a = &wr.acc;
    let x = a[n];
    let base = [L(wr.d, false), L(wr.b2, false), L(wr.beta, !beta_val), L(x, true)];
    apply(c, &base, act, cx);
    let g = gid_room(c, cx.cap, 5);
    let cm = cmp_open(c, &wr.sw2, &a[..n - 2], wr.r0, g);
    let rge = cm.top();
    let mut lits = base.to_vec();
    lits.extend_from_slice(&[L(a[n - 2], true), L(a[n - 1], true), L(rge, false)]);
    apply(c, &lits, act, cx);
    cmp_close(c, cm);
}

fn run(c: &mut Builder, io: &TickIo, h: &Hreg, cfg: K2Cfg, d_given: Option<Q>, dirty: &[Q], fwd: bool) {
    let cx = Ctx { cap: cfg.cap, dirty };
    let cap = cfg.cap;
    let wr = setup(c, io, cfg.w, d_given);
    let k = c.alloc_qubit();
    let xa = Act::Xor { k, typ: Some(io.typ) };
    let xb = Act::Xor { k, typ: None };
    // ── phase A: R -> L1 -> R -> U1 -> V; K = D & (GA xor GB), typ ^= D & GA
    // with a zero hint o the walk is R -> L1 -> R + o -> U1 = R + o - S_1 - 1 -> V (o = 0 whenever D = 1)
    let back = match cfg.zero_hint { Some(o) => Cin::Wire(o), None => Cin::None };
    ip(c, &wr.sw1, &wr.acc, Cin::Zero(k), true, cap);
    terms_l1(c, &wr, xa, &cx);
    ip(c, &wr.sw1, &wr.acc, back, false, cap);
    ip(c, &wr.sw1, &wr.acc, Cin::Wire(wr.r0), true, cap);
    term_upper(c, &wr, true, xb, &cx);
    ip(c, &wr.sw1, &wr.acc, Cin::Wire(wr.slo), true, cap);
    term_upper(c, &wr, false, xa, &cx);
    // ── phase B: amb = D & !K controls the history shift
    // every term carries D, so K <= D and amb = D & !K = K xor D, formed in place
    c.cx(wr.d, k);
    if fwd {
        shift_in(c, k, io.typ, &h.wires);
    } else {
        shift_out(c, k, io.typ, &h.wires);
    }
    c.cx(wr.d, k);
    let mk: BitId = c.alloc_bit();
    c.hmr(k, mk); // k is |0> again: it serves as the carry-in of the last step
    // ── phase C: walk back V -> U1 -> R -> L1 -> R, repairing the measured K's phase
    c.push_condition(mk);
    term_upper(c, &wr, false, Act::Phase, &cx);
    c.pop_condition();
    ip(c, &wr.sw1, &wr.acc, Cin::Wire(wr.slo), false, cap);
    c.push_condition(mk);
    term_upper(c, &wr, true, Act::Phase, &cx);
    c.pop_condition();
    ip(c, &wr.sw1, &wr.acc, Cin::Wire(wr.r0), false, cap);
    ip(c, &wr.sw1, &wr.acc, back, true, cap);
    c.push_condition(mk);
    terms_l1(c, &wr, Act::Phase, &cx);
    c.pop_condition();
    ip(c, &wr.sw1, &wr.acc, Cin::Zero(k), false, cap);
    c.release_clean(k);
    c.free_bit(mk);
    teardown(c, io, wr);
}

/// Forward: erase the tick's letter from the post-state, pushing `typ` on an ambiguous tick.
/// `d_given`: the caller's `D = en & !s1` (then `io.en` is ignored); `dirty`: wires the call may
/// borrow (any state, restored) when the room is short.
pub fn push(c: &mut Builder, io: &TickIo, h: &Hreg, cfg: K2Cfg, d_given: Option<Q>, dirty: &[Q]) {
    run(c, io, h, cfg, d_given, dirty, true);
}

/// Reverse: recreate the tick's letter (`typ = 0` on entry), popping where [`push`] pushed.
pub fn pop(c: &mut Builder, io: &TickIo, h: &Hreg, cfg: K2Cfg, d_given: Option<Q>, dirty: &[Q]) {
    run(c, io, h, cfg, d_given, dirty, false);
}

/// Bit-exact classical replica of the circuit's decisions, for any input.
pub mod model {
    use super::geom;

    fn bit(v: &[u64], i: usize) -> bool {
        i / 64 < v.len() && (v[i / 64] >> (i % 64)) & 1 == 1
    }
    fn field(v: &[u64], lo: usize, n: usize) -> u128 {
        let mut x = 0u128;
        for i in 0..n {
            if bit(v, lo + i) {
                x |= 1u128 << i;
            }
        }
        x
    }

    /// `(D, GA, GB)`: `amb = D & !GA & !GB`, `typ ^= D & GA`.
    pub fn decide(s: &[u64], r: &[u64], e: usize, w: usize, en: bool) -> (bool, bool, bool) {
        decide_o(s, r, e, w, en, false)
    }

    /// [`decide`] with the zero-hint wire's value `o` (0 on every valid call).
    pub fn decide_o(s: &[u64], r: &[u64], e: usize, w: usize, en: bool, o: bool) -> (bool, bool, bool) {
        let (lo, n) = geom(e, w);
        assert!(n <= 120);
        let m: u128 = 1u128 << (n + 1);
        let mask = m - 1;
        let half = 1u128 << n;
        let rr = field(r, lo, n);
        let ss = field(s, lo, n);
        let s0 = bit(s, 0) as u128;
        let r0 = bit(r, 0) as u128;
        let slo = ss & 1;
        let (sw1, sw2, sw3) = (ss >> 1, ss >> 2, ss >> 3);
        let a0 = rr | (s0 << n);
        let l1 = a0.wrapping_sub(sw1) & mask;
        let x1 = l1 >= half;
        let l1low = l1 & (half - 1);
        // carry-out of x + ~y + cin over n bits: x - y - 1 + cin >= 0
        let ge = |x: u128, y: u128, cin: u128| x + cin >= y + 1;
        let ge3 = ge(l1low, sw3, r0);
        let ge2 = ge(l1low, sw2, r0);
        let u1 = a0.wrapping_add(o as u128).wrapping_sub(sw1).wrapping_sub(r0) & mask;
        let xu = u1 >= half;
        // the upper compares run as [S_2 >= x] with carry-in r0 and are negated: [x >= S_2 + r0]
        let gt2 = ge(u1 & (half - 1), sw2, 1 - r0);
        let v = u1.wrapping_sub(sw1).wrapping_sub(slo) & mask;
        let xv = v >= half;
        let gt2v = ge(v & (half - 1), sw2, 1 - r0);
        let b2 = bit(s, 2);
        let b3 = bit(s, 3);
        let beta = bit(r, 1) ^ b3;
        let d = en && !bit(s, 1);
        let ga = x1 ^ (!b2 && b3 && !x1 && !ge3) ^ (b2 && !x1 && !ge2) ^ (b2 && !beta && !xv && gt2v);
        let gb = b2 && beta && !xu && gt2;
        (d, ga, gb)
    }

    /// `(D, amb, A-certain)` for a valid post-state.
    pub fn letters(s: &[u64], r: &[u64], e: usize, w: usize, en: bool) -> (bool, bool, bool) {
        let (d, ga, gb) = decide(s, r, e, w, en);
        (d, d && !ga && !gb, d && ga)
    }
}
