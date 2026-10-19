//! SKY-COF rails-frame walk (research): the Skywalk rails with cofactors kept in the rails' own frame,
//! `a * R1 + b * R2 = p` (two's complement, LSB first). Same rails, letters, history and odometer as
//! [`super::walk`]; only the cofactor update, the letter decoder and the park handling differ.
//!
//! # Cofactor update (tick t)
//! The rail tick swaps the rails on `c_t = typ_t ^ typ_{t-1}` and then does `R2 -/+= H` (`H = R1 / 2`). In the
//! frame this is: swap `(a, b)` on `c_t` (Fredkins), then the UNCONDITIONAL signed add `a <- 2a + sig * b`
//! (`sig = +1` when the add agrees, i.e. `nag = 0`): no controlled add.
//!
//! # Decoder (letter `t-1`, disposed in tick t after the swap, before the add)
//! On the swapped pair `J' = (a', b')` the Kaliski cofactors of post(t-1) are `r = J'[typ_t]`, `q = J'[!typ_t]`,
//! `s = r +- |q|` (`+` iff `sign(q) == sign(R_q)`, `R_q` the swapped rail paired with q). Hence
//! `C = a'1 ^ b'1 ^ sign(R_q) ^ 1` (exact), certain-A iff `!C & sigma & |q| > r`, else (not C) ambiguous:
//! a top-window compare `ge = [r_top >= |q|_top]` (one's complement abs, conservative). The push envelope is
//! the Kaliski decoder's (measured equal tick by tick).
//!
//! # Park
//! `z = [b' == p]` (top `park_j` magnitude bits of b' all one, sign 0) is 1 from tick T0+1 on, exactly the
//! ticks whose add is `x <- 2x + p`. Entry (`E = z & [odo == 0]`, the first such tick): `a' = q` has an
//! arbitrary sign; when `q >= 0` the add sign is flipped (`2q - p`, F_e XORed into the sign wire: 0 Toffoli),
//! and F_e is recovered after the add as bit 1 of the result (`2q + p = 1`, `2q - p = 3` mod 4).
//! Every clamp tick then folds `x -= p` when `z & x >= 0` (window add of c, top-bit decrement); the fold flag
//! is the result's LSB complement. Post-park invariant `x in [-p, 2c)`; the parked output is `s = x + p`.
use super::adder;
use super::decoder::{self as dec, Hreg};
use super::tick::{self, resize_signed};
use super::walk::{self, Envelope, WalkParams};
use crate::circuit::{QubitId as Q, NO_QUBIT};
use crate::point_add::builder::Builder;
use crate::point_add::heo::Rails;
use crate::point_add::skycof_mm as mm;
use crate::point_add::N;
use alloy_primitives::U256;

/// Frame clamp: signed width of the cofactors at the Kaliski clamp (256 magnitude bits + sign).
pub const FCL: usize = N + 1;

/// Frame field width post(t): Kaliski design width + 1 sign bit, clamped.
pub fn fw(env: &Envelope, t: usize) -> usize {
    (env.cof[t] + 1).min(FCL)
}

pub struct FCof {
    pub a: Vec<Q>,
    pub b: Vec<Q>,
}

pub struct FParked {
    pub s: Vec<Q>,
    pub h: Hreg,
    pub odo: Vec<Q>,
    prev: Vec<(usize, usize)>,
}

fn room(c: &Builder, cap: usize) -> usize {
    cap.saturating_sub(c.active_qubits() as usize)
}

fn secp_c() -> u128 {
    mm::Field::secp().c
}

fn fredkin(c: &mut Builder, ctrl: Q, a: Q, b: Q) {
    c.cx(b, a);
    c.ccx(ctrl, a, b);
    c.cx(b, a);
}

/// HMR `t` (holding `x & y`) and repair the phase.
fn meas_cz(c: &mut Builder, t: Q, x: Q, y: Q) {
    let m = c.alloc_bit();
    c.hmr(t, m);
    c.cz_if(x, y, m);
    c.free_bit(m);
    c.release_clean(t);
}

// ─── park test (AND of literal wires; the caller applies negations around compute and uncompute) ─────

fn tree(c: &mut Builder, lits: &[Q]) -> (Q, Vec<(Q, Q, Q)>) {
    assert!(lits.len() >= 2);
    let mut nodes = Vec::new();
    let mut level: Vec<Q> = lits.to_vec();
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len() / 2 + 1);
        let mut i = 0;
        while i + 1 < level.len() {
            let n = c.alloc_qubit();
            c.ccx(level[i], level[i + 1], n);
            nodes.push((n, level[i], level[i + 1]));
            next.push(n);
            i += 2;
        }
        if i < level.len() {
            next.push(level[i]);
        }
        level = next;
    }
    (level[0], nodes)
}

fn erase_nodes(c: &mut Builder, nodes: &[(Q, Q, Q)]) {
    for &(n, a, b) in nodes.iter().rev() {
        meas_cz(c, n, a, b);
    }
}

fn and_frozen(c: &mut Builder, lits: &[Q]) -> Q {
    if lits.len() == 1 {
        let o = c.alloc_qubit();
        c.cx(lits[0], o);
        return o;
    }
    let (root, nodes) = tree(c, lits);
    erase_nodes(c, &nodes[..nodes.len() - 1]);
    root
}

fn mcz(c: &mut Builder, lits: &[Q]) {
    match lits.len() {
        0 => {}
        1 => c.z_if(lits[0], crate::circuit::NO_BIT),
        2 => c.cz(lits[0], lits[1]),
        n => {
            let (root, nodes) = tree(c, &lits[..n - 1]);
            c.cz(root, lits[n - 1]);
            erase_nodes(c, &nodes);
        }
    }
}

fn erase_frozen(c: &mut Builder, w: Q, lits: &[Q]) {
    if lits.len() == 1 {
        c.cx(lits[0], w);
        c.release_clean(w);
        return;
    }
    let m = c.alloc_bit();
    c.hmr(w, m);
    c.push_condition(m);
    mcz(c, lits);
    c.pop_condition();
    c.free_bit(m);
    c.release_clean(w);
}

const PARK_PART: usize = 5;

/// `z = [b == p]` on a frame register at `FCL` wires: AND of the top `j` magnitude bits and `!sign`.
struct FPark {
    z: Q,
    parts: Vec<Vec<Q>>,
    sign: Q,
}

impl FPark {
    fn compute(c: &mut Builder, b: &[Q], j: usize) -> Self {
        assert_eq!(b.len(), FCL);
        let sign = b[N];
        let mut lits: Vec<Q> = b[N - j..N].to_vec();
        lits.push(sign);
        let parts: Vec<Vec<Q>> = lits.chunks(PARK_PART).map(|p| p.to_vec()).collect();
        c.x(sign);
        let a: Vec<Q> = parts.iter().map(|p| and_frozen(c, p)).collect();
        let z = and_frozen(c, &a);
        for (ai, p) in a.iter().zip(&parts).rev() {
            erase_frozen(c, *ai, p);
        }
        c.x(sign);
        FPark { z, parts, sign }
    }
    fn uncompute(self, c: &mut Builder) {
        let m = c.alloc_bit();
        c.hmr(self.z, m);
        c.release_clean(self.z);
        c.x(self.sign);
        c.push_condition(m);
        let a: Vec<Q> = self.parts.iter().map(|p| and_frozen(c, p)).collect();
        mcz(c, &a);
        for (ai, p) in a.iter().zip(&self.parts).rev() {
            erase_frozen(c, *ai, p);
        }
        c.pop_condition();
        c.x(self.sign);
        c.free_bit(m);
    }
}

/// Live clamp-tick state between the dispose and the fold: park flag, `[odo != 0]`, entry flag.
struct ClampSt {
    zt: FPark,
    nz: Q,
    e: Q,
}

/// First clamp tick (the first tick whose previous field width is the clamp): the odometer is 0 before it.
fn first_clamp(env: &Envelope, r: usize) -> usize {
    (1..r).find(|&t| fw(env, t - 1) == FCL).expect("frame walk: no clamp tick")
}

/// Lazy odometer: allocated at the first clamp tick, released (it is 0 again) when the walk back leaves it.
fn lazy_odo() -> bool {
    super::pointadd::knob("SKYCOF_LAZYODO").map(|v| v != "0").unwrap_or(super::pointadd::LAZY_ODO)
}

fn odo_room(c: &Builder, cap: usize) -> usize {
    room(c, cap).max(4)
}

// ─── decoder ──────────────────────────────────────────────────────────────────────────────────────

/// Wires of one decode on the swapped pair `J'` (tick t, letter t-1).
struct Dctx<'a> {
    a: &'a [Q],
    b: &'a [Q],
    /// frame width of `J'` (= post(t-1))
    f: usize,
    /// typ_t
    t: Q,
    /// isC_t (rails post(t): sign(R2') = sign(R2_t) ^ isC_t)
    isc: Q,
    r1s: Q,
    r2s: Q,
    en: Option<Q>,
}

/// `w ^= sign(R_q)`, `R_q = typ_t ? R1' : R2'`. 1 CCX.
fn sigr_xor(c: &mut Builder, x: &Dctx, w: Q) {
    c.cx(x.r2s, w);
    c.cx(x.isc, w);
    c.cx(x.r2s, x.r1s);
    c.cx(x.isc, x.r1s);
    c.ccx(x.t, x.r1s, w);
    c.cx(x.isc, x.r1s);
    c.cx(x.r2s, x.r1s);
}

/// Measured erase of `w = sign(R_q)`. 0 CCX.
fn sigr_erase(c: &mut Builder, x: &Dctx, w: Q) {
    let m = c.alloc_bit();
    c.hmr(w, m);
    c.z_if(x.r2s, m);
    c.z_if(x.isc, m);
    c.cx(x.r2s, x.r1s);
    c.cx(x.isc, x.r1s);
    c.cz_if(x.t, x.r1s, m);
    c.cx(x.isc, x.r1s);
    c.cx(x.r2s, x.r1s);
    c.free_bit(m);
    c.release_clean(w);
}

/// Toggle `w` between `sigma = !(sa ^ sb ^ sR)` and `!C = a1 ^ b1 ^ sR` (self-inverse; CNOTs only).
fn toggle_sigma_nc(c: &mut Builder, x: &Dctx, w: Q) {
    let (sa, sb) = (x.a[x.f - 1], x.b[x.f - 1]);
    for q in [x.a[1], x.b[1], sa, sb] {
        c.cx(q, w);
    }
    c.x(w);
}

/// `sR <-> sigma` on `w` (self-inverse).
fn toggle_sr_sigma(c: &mut Builder, x: &Dctx, w: Q) {
    c.cx(x.a[x.f - 1], w);
    c.cx(x.b[x.f - 1], w);
    c.x(w);
}

struct Scope {
    w: Q,
    d: Q,
    d_fresh: bool,
    j: usize,
    gid: Vec<Q>,
    xa: Vec<Q>,
    yb: Vec<Q>,
    cin0: Q,
    ge: Q,
    u: Q,
    amb: Q,
    lo: usize,
}

impl Scope {
    fn cin(&self, i: usize) -> Q {
        if i == 0 {
            self.cin0
        } else if i <= self.j {
            self.gid[i - 1]
        } else {
            self.xa[i - 1]
        }
    }
}

fn dec_open(c: &mut Builder, x: &Dctx, cap: usize, w_dec: usize) -> Scope {
    let f = x.f;
    let lo = (f - 1).saturating_sub(w_dec).max(1);
    let n = f - 1 - lo;
    assert!(n >= 1, "frame decoder: empty window at f={f}");
    // w = sigma
    let w = c.alloc_qubit();
    sigr_xor(c, x, w);
    toggle_sr_sigma(c, x, w);
    // D = en & !C
    let (d, d_fresh) = match x.en {
        Some(en) => {
            let d = c.alloc_qubit();
            toggle_sigma_nc(c, x, w);
            c.ccx(en, w, d);
            toggle_sigma_nc(c, x, w);
            (d, true)
        }
        None => {
            // b'0 is a virtual constant one, so use a fresh decoder bit.
            let d = c.alloc_qubit();
            toggle_sigma_nc(c, x, w);
            c.cx(w, d);
            toggle_sigma_nc(c, x, w);
            (d, true)
        }
    };
    // windows: X = |a'| ^ typ, Y = |b'| ^ typ, complemented for the chain
    let (sa, sb) = (x.a[f - 1], x.b[f - 1]);
    let xa: Vec<Q> = x.a[lo..f - 1].to_vec();
    let yb: Vec<Q> = x.b[lo..f - 1].to_vec();
    for i in 0..n {
        c.cx(sa, xa[i]);
        c.cx(x.t, xa[i]);
        c.cx(sb, yb[i]);
        c.cx(x.t, yb[i]);
        c.x(yb[i]);
    }
    let rm = room(c, cap);
    let j = n.min(rm.saturating_sub(2));
    let mut sc = Scope { w, d, d_fresh, j, gid: Vec::with_capacity(j), xa, yb, cin0: x.a[0], ge: x.a[0], u: x.a[0], amb: x.a[0], lo };
    for i in 0..j {
        let ci = sc.cin(i);
        c.cx(ci, sc.xa[i]);
        c.cx(ci, sc.yb[i]);
        let t = c.alloc_qubit();
        c.ccx(sc.xa[i], sc.yb[i], t);
        c.cx(ci, t);
        sc.gid.push(t);
    }
    for i in j..n {
        let ci = sc.cin(i);
        c.cx(sc.xa[i], sc.yb[i]);
        c.cx(sc.xa[i], ci);
        c.ccx(ci, sc.yb[i], sc.xa[i]);
    }
    sc.ge = if j == n { sc.gid[n - 1] } else { sc.xa[n - 1] };
    // u = sigma & !ge ; amb = D & !u
    sc.u = c.alloc_qubit();
    c.x(sc.ge);
    c.ccx(sc.w, sc.ge, sc.u);
    c.x(sc.ge);
    sc.amb = c.alloc_qubit();
    c.x(sc.u);
    c.ccx(sc.d, sc.u, sc.amb);
    c.x(sc.u);
    sc
}

fn dec_close(c: &mut Builder, x: &Dctx, sc: Scope) {
    // amb = D & !u
    let m = c.alloc_bit();
    c.hmr(sc.amb, m);
    c.x(sc.u);
    c.cz_if(sc.d, sc.u, m);
    c.x(sc.u);
    c.free_bit(m);
    c.release_clean(sc.amb);
    // u = sigma & !ge
    let m = c.alloc_bit();
    c.hmr(sc.u, m);
    c.x(sc.ge);
    c.cz_if(sc.w, sc.ge, m);
    c.x(sc.ge);
    c.free_bit(m);
    c.release_clean(sc.u);
    let n = sc.xa.len();
    for i in (sc.j..n).rev() {
        let ci = sc.cin(i);
        c.ccx(ci, sc.yb[i], sc.xa[i]);
        c.cx(sc.xa[i], ci);
        c.cx(sc.xa[i], sc.yb[i]);
    }
    for i in (0..sc.j).rev() {
        let ci = sc.cin(i);
        let t = sc.gid[i];
        c.cx(ci, t);
        meas_cz(c, t, sc.xa[i], sc.yb[i]);
        c.cx(ci, sc.xa[i]);
        c.cx(ci, sc.yb[i]);
    }
    let f = x.f;
    let (sa, sb) = (x.a[f - 1], x.b[f - 1]);
    for i in 0..n {
        c.x(sc.yb[i]);
        c.cx(x.t, sc.yb[i]);
        c.cx(sb, sc.yb[i]);
        c.cx(x.t, sc.xa[i]);
        c.cx(sa, sc.xa[i]);
    }
    let _ = sc.lo;
    let w = sc.w;
    if sc.d_fresh {
        if let Some(en) = x.en {
            let m = c.alloc_bit();
            c.hmr(sc.d, m);
            toggle_sigma_nc(c, x, w);
            c.cz_if(en, w, m);
            toggle_sigma_nc(c, x, w);
            c.free_bit(m);
            c.release_clean(sc.d);
        } else {
            toggle_sigma_nc(c, x, w);
            c.cx(w, sc.d);
            toggle_sigma_nc(c, x, w);
            c.release_clean(sc.d);
        }
    } else {
        let b0 = x.b[0];
        toggle_sigma_nc(c, x, w);
        c.x(b0);
        c.cx(w, b0);
        toggle_sigma_nc(c, x, w);
    }
    toggle_sr_sigma(c, x, w);
    sigr_erase(c, x, w);
}

fn dec_push(c: &mut Builder, x: &Dctx, typ: Q, h: &Hreg, cap: usize, w_dec: usize) {
    let sc = dec_open(c, x, cap, w_dec);
    dec::shift_in(c, sc.amb, typ, &h.wires);
    c.cx(sc.d, typ);
    c.cx(sc.amb, typ);
    dec_close(c, x, sc);
}

fn dec_pop(c: &mut Builder, x: &Dctx, typ: Q, h: &Hreg, cap: usize, w_dec: usize) {
    let sc = dec_open(c, x, cap, w_dec);
    c.cx(sc.amb, typ);
    c.cx(sc.d, typ);
    dec::shift_out(c, sc.amb, typ, &h.wires);
    dec_close(c, x, sc);
}

/// Letter 0 (A or C): `typ ^= !C`. Self-inverse, 1 CCX.
fn dec_first(c: &mut Builder, x: &Dctx, typ: Q) {
    let w = c.alloc_qubit();
    sigr_xor(c, x, w);
    c.cx(x.a[1], typ);
    c.cx(x.b[1], typ);
    c.cx(w, typ);
    sigr_erase(c, x, w);
}

// ─── letter disposal ────────────────────────────────────────────────────────────────────────────

#[allow(clippy::too_many_arguments)]
fn dispose_fwd(c: &mut Builder, p: &WalkParams, env: &Envelope, t1: usize, typ: Q, tt: Q, isc: Q, cof: &FCof,
               rails: &Rails, h: &mut Hreg, odo: &[Q]) -> Option<ClampSt> {
    h.grow_to(c, env.h[t1]);
    let f = cof.a.len();
    assert_eq!(f, fw(env, t1));
    let mut x = Dctx { a: &cof.a, b: &cof.b, f, t: tt, isc, r1s: *rails.r1.last().unwrap(), r2s: *rails.r2.last().unwrap(), en: None };
    let out = if t1 == 0 {
        dec_first(c, &x, typ);
        None
    } else if f == FCL {
        let zt = FPark::compute(c, &cof.b, p.park_j);
        let z = zt.z;
        // odometer: g = z & typ; odo += g; typ ^= g; g ^= z & [odo != 0]  (nz kept live)
        let g = c.alloc_qubit();
        c.ccx(z, typ, g);
        let rm = odo_room(c, p.cap);
        mm::odo_inc(c, odo, g, rm);
        c.cx(g, typ);
        let nz = c.alloc_qubit();
        let rm = odo_room(c, p.cap);
        mm::odo_nonzero_xor(c, odo, nz, rm);
        c.ccx(z, nz, g);
        c.release_clean(g);
        // entry flag E = z & !nz
        let e = c.alloc_qubit();
        c.x(nz);
        c.ccx(z, nz, e);
        c.x(nz);
        c.x(z);
        x.en = Some(z);
        dec_push(c, &x, typ, h, p.cap, p.w_dec);
        c.x(z);
        Some(ClampSt { zt, nz, e })
    } else {
        dec_push(c, &x, typ, h, p.cap, p.w_dec);
        None
    };
    c.release_clean(typ);
    out
}

#[allow(clippy::too_many_arguments)]
fn dispose_rev(c: &mut Builder, p: &WalkParams, env: &Envelope, t1: usize, tt: Q, isc: Q, cof: &FCof,
               rails: &Rails, h: &mut Hreg, odo: &[Q], cst: Option<ClampSt>) -> Q {
    h.shrink_to(c, env.h[t1]);
    let typ = c.alloc_qubit();
    let f = cof.a.len();
    assert_eq!(f, fw(env, t1));
    let mut x = Dctx { a: &cof.a, b: &cof.b, f, t: tt, isc, r1s: *rails.r1.last().unwrap(), r2s: *rails.r2.last().unwrap(), en: None };
    if t1 == 0 {
        assert!(cst.is_none());
        dec_first(c, &x, typ);
    } else if let Some(ClampSt { zt, nz, e }) = cst {
        let z = zt.z;
        c.x(z);
        x.en = Some(z);
        dec_pop(c, &x, typ, h, p.cap, p.w_dec);
        c.x(z);
        // E = z & !nz
        let m = c.alloc_bit();
        c.hmr(e, m);
        c.x(nz);
        c.cz_if(z, nz, m);
        c.x(nz);
        c.free_bit(m);
        c.release_clean(e);
        // odometer reverse (nz live)
        let g = c.alloc_qubit();
        c.ccx(z, nz, g);
        let rm = odo_room(c, p.cap);
        mm::odo_nonzero_xor(c, odo, nz, rm);
        c.release_clean(nz);
        c.cx(g, typ);
        let rm = odo_room(c, p.cap);
        mm::odo_dec(c, odo, g, rm);
        c.ccx(z, typ, g);
        c.release_clean(g);
        zt.uncompute(c);
    } else {
        assert!(f < FCL);
        dec_pop(c, &x, typ, h, p.cap, p.w_dec);
    }
    typ
}

// ─── cofactor swap / add / fold / isC ───────────────────────────────────────────────────────────

/// `swap(a, b)` on `c = tt ^ tp` (bit 0 skipped: both odd whenever c = 1). Self-inverse.
fn cswap(c: &mut Builder, cof: &FCof, tt: Q, tp: Option<Q>) {
    assert_eq!(cof.a.len(), cof.b.len());
    if let Some(tp) = tp {
        c.cx(tp, tt);
    }
    for i in 1..cof.a.len() {
        fredkin(c, tt, cof.a[i], cof.b[i]);
    }
    if let Some(tp) = tp {
        c.cx(tp, tt);
    }
}

/// `a <- 2a + (nag ? -b : b)` (mod 2^wadd), `wadd = max(wt, fprev + 1)`; `e` = entry flag (F_e = e & a' >= 0
/// is XORed into the sign wire for the add and removed after it from bit 1 of the result).
#[allow(clippy::too_many_arguments)]
fn cof_add_fwd(c: &mut Builder, cof: &mut FCof, isc: Q, rails: &Rails, fprev: usize, wt: usize, e: Option<Q>, cap: usize) {
    assert_eq!(cof.a.len(), fprev);
    assert_eq!(cof.b.len(), fprev);
    let (r1s, r2s) = (*rails.r1.last().unwrap(), *rails.r2.last().unwrap());
    if let Some(e) = e {
        let sa = cof.a[fprev - 1];
        c.x(sa);
        c.ccx(e, sa, isc);
        c.x(sa);
    }
    c.cx(r1s, isc);
    c.cx(r2s, isc);
    let z0 = c.alloc_qubit();
    cof.a.insert(0, z0);
    let wadd = wt.max(fprev + 1);
    resize_signed(c, &mut cof.a, wadd);
    let mut op = cof.b.clone();
    let mut ext = Vec::new();
    while op.len() + 1 < wadd {
        let q = c.alloc_qubit();
        c.cx(*op.last().unwrap(), q);
        op.push(q);
        ext.push(q);
    }
    c.cx_all(isc, &op[1..]);
    c.x(cof.a[0]); // 0 + (1 XOR isc) + isc = 1, carry 0.
    adder::add_defer(c, &op[1..], &cof.a[1..], None, Some(cap), 2);
    c.cx(*op.last().unwrap(), cof.a[wadd - 1]);
    c.cx_all(isc, &op[1..]);
    for &q in ext.iter().rev() {
        let i = op.iter().position(|&w| w == q).unwrap();
        c.cx(op[i - 1], q);
        c.free(q);
    }
    c.cx(r2s, isc);
    c.cx(r1s, isc);
    if let Some(e) = e {
        c.ccx(e, cof.a[1], isc);
    }
}

/// Exact inverse of [`cof_add_fwd`]; `a` enters at `wadd` wires, leaves at `fprev`.
#[allow(clippy::too_many_arguments)]
fn cof_add_rev(c: &mut Builder, cof: &mut FCof, isc: Q, rails: &Rails, fprev: usize, wt: usize, e: Option<Q>, cap: usize) {
    let wadd = wt.max(fprev + 1);
    assert_eq!(cof.a.len(), wadd);
    assert_eq!(cof.b.len(), fprev);
    let (r1s, r2s) = (*rails.r1.last().unwrap(), *rails.r2.last().unwrap());
    if let Some(e) = e {
        c.ccx(e, cof.a[1], isc);
    }
    c.cx(r1s, isc);
    c.cx(r2s, isc);
    let mut op = cof.b.clone();
    let mut ext = Vec::new();
    while op.len() + 1 < wadd {
        let q = c.alloc_qubit();
        c.cx(*op.last().unwrap(), q);
        op.push(q);
        ext.push(q);
    }
    c.cx_all(isc, &op[1..]);
    c.cx(*op.last().unwrap(), cof.a[wadd - 1]);
    adder::sub_pay(c, &op[1..], &cof.a[1..], None, Some(cap), 2);
    c.x(cof.a[0]);
    c.cx_all(isc, &op[1..]);
    for &q in ext.iter().rev() {
        let i = op.iter().position(|&w| w == q).unwrap();
        c.cx(op[i - 1], q);
        c.free(q);
    }
    c.cx(r2s, isc);
    c.cx(r1s, isc);
    resize_signed(c, &mut cof.a, fprev + 1);
    let z0 = cof.a.remove(0);
    c.free(z0);
    if let Some(e) = e {
        let sa = cof.a[fprev - 1];
        c.x(sa);
        c.ccx(e, sa, isc);
        c.x(sa);
    }
}

/// Clamp fold on `x` (FCL + 1 wires): `F = z & x >= 0`; `x -= F p` (low window += F c, top decrement);
/// `F = !x[0]` erased; top wire (a sign copy) trimmed.
fn fold(c: &mut Builder, x: &mut Vec<Q>, b: &[Q], z: Q, p: &WalkParams) {
    assert_eq!(x.len(), FCL + 1);
    let (t256, t257) = (x[N], x[N + 1]);
    let f = c.alloc_qubit();
    c.x(t257);
    c.ccx(z, t257, f);
    c.x(t257);
    let w = p.fold_w;
    let rm = room(c, p.cap);
    if rm >= 12 {
        mm::cadd_k(c, &x[..w], secp_c(), f, rm);
    } else {
        // b = p whenever F can be set: x -= F (p mod 2^w)
        c.cx(f, x[0]); // x[0] enters as 1: no borrow into bit 1.
        adder::sub(c, Some(f), &b[1..w], &x[1..w], None, Some(p.cap));
    }
    c.cx(f, t256);
    c.ccx(f, t256, t257);
    c.cx(x[0], f);
    c.x(f);
    c.release_clean(f);
    let top = x.pop().unwrap();
    c.cx(x[N], top);
    c.free(top);
}

/// Exact inverse of [`fold`].
fn unfold(c: &mut Builder, x: &mut Vec<Q>, b: &[Q], z: Q, p: &WalkParams) {
    assert_eq!(x.len(), FCL);
    let top = c.alloc_qubit();
    c.cx(x[N], top);
    x.push(top);
    let (t256, t257) = (x[N], x[N + 1]);
    let f = c.alloc_qubit();
    c.cx(x[0], f);
    c.x(f);
    c.ccx(f, t256, t257);
    c.cx(f, t256);
    let w = p.fold_w;
    let rm = room(c, p.cap);
    if rm >= 12 {
        mm::csub_k(c, &x[..w], secp_c(), f, rm);
    } else {
        adder::add(c, Some(f), &b[1..w], &x[1..w], None, Some(p.cap));
        c.cx(f, x[0]); // x[0] is 0 when f=1: no carry into bit 1.
    }
    // f = z & !x[257]
    let m = c.alloc_bit();
    c.hmr(f, m);
    c.x(t257);
    c.cz_if(z, t257, m);
    c.x(t257);
    c.free_bit(m);
    c.release_clean(f);
}

/// `a[1] ^= b1 ^ sign(R2) ^ 1` (self-inverse): `isC = !typ & a[1]` afterwards.
fn p_into_a1(c: &mut Builder, cof: &FCof, r2s: Q) {
    c.cx(cof.b[1], cof.a[1]);
    c.cx(r2s, cof.a[1]);
    c.x(cof.a[1]);
}

fn erase_isc(c: &mut Builder, cof: &FCof, tt: Q, isc: Q, rails: &Rails) {
    let r2s = *rails.r2.last().unwrap();
    let m = c.alloc_bit();
    c.hmr(isc, m);
    p_into_a1(c, cof, r2s);
    c.x(tt);
    c.cz_if(tt, cof.a[1], m);
    c.x(tt);
    p_into_a1(c, cof, r2s);
    c.free_bit(m);
    c.release_clean(isc);
}

fn isc_recompute(c: &mut Builder, cof: &FCof, tt: Q, rails: &Rails) -> Q {
    let r2s = *rails.r2.last().unwrap();
    let isc = c.alloc_qubit();
    p_into_a1(c, cof, r2s);
    c.x(tt);
    c.ccx(tt, cof.a[1], isc);
    c.x(tt);
    p_into_a1(c, cof, r2s);
    isc
}

static FPROF: std::sync::Mutex<[f64; 8]> = std::sync::Mutex::new([0.0; 8]);
static FPROF_LAST: std::sync::Mutex<f64> = std::sync::Mutex::new(0.0);
/// Research profile: attribute expected Toffoli since the last mark to bucket k.
pub(crate) fn fprof(c: &Builder, k: usize) {
    if let Some((_, e)) = c.report_totals() {
        let mut l = FPROF_LAST.lock().unwrap();
        if k < 8 { FPROF.lock().unwrap()[k] += e - *l; }
        *l = e;
    }
}
static WSUM: std::sync::Mutex<[usize; 6]> = std::sync::Mutex::new([0; 6]);
pub(crate) fn fprof_dump(tag: &str) {
    { let w = WSUM.lock().unwrap(); if w[0] > 0 { eprintln!("SKYCOF_WSUM rail_sw={} rail_ad={} cof_sw={} cof_ad={} hist={} decwin={}", w[0], w[1], w[2], w[3], w[4], w[5]); } }
    let mut a = FPROF.lock().unwrap();
    eprintln!("SKYCOF_FPROF {tag} rail={:.0} cswap={:.0} dispose={:.0} add={:.0} clamp={:.0} isc={:.0} other={:.0} x={:.0}", a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]);
    *a = [0.0; 8];
}

fn trace_tick(c: &mut Builder, dir: &str, t: usize) {
    if super::pointadd::knob_flag("SKYCOF_TICK_TRACE") {
        let pk = c.take_win_peak();
        eprintln!("SKYCOF_FTICK {dir} {t} live={} peak={pk} ops={} exp={:.1}", c.active_qubits(), c.op_count(), c.report_totals().map_or(0.0, |x| x.1));
    }
}

// ─── the walk ───────────────────────────────────────────────────────────────────────────────────

/// Forward frame walk on `d` (its wires become R2). Returns the parked state with `s = -2^R / d` (lazy).
pub fn forward(c: &mut Builder, p: &WalkParams, env: &Envelope, d: &[Q]) -> FParked {
    let r = p.r;
    adder::defer_active(true);
    let mut rails = walk::seed(c, d);
    // (a, b) = (1, -1) at 2 wires
    let a = c.alloc_qubits(2);
    let b = vec![NO_QUBIT, c.alloc_qubit()];
    c.x(a[0]);
    c.x(b[1]);
    let mut cof = FCof { a, b };
    let mut h = Hreg::new();
    let t0 = first_clamp(env, r);
    // The rail's R2[1..8] is an idle, zero-initialized bank after parking.
    // Before parking, odometer operations have a false gate and the only
    // unconditional read is uncomputed before the next rail step.
    let mut odo = Vec::new();
    let mut prev = Vec::with_capacity(r);
    let mut typ: Option<Q> = None;
    for t in 0..r {
        let w = env.widths(t);
        let fprev = cof.a.len();
        prev.push((rails.r1.len(), rails.r2.len()));
        if t == t0 {
            assert!(rails.r2.len() >= p.odo_bits + 1);
            odo = rails.r2[1..1 + p.odo_bits].to_vec();
        }
        fprof(c, 6);
        let (tt, isc, _) = tick::rail_fwd(c, &mut rails, typ, w.wsw, w.wad, Some(p.cap));
        fprof(c, 0);
        cswap(c, &cof, tt, typ);
        fprof(c, 1);
        let cst = match typ {
            Some(tp) => dispose_fwd(c, p, env, t - 1, tp, tt, isc, &cof, &rails, &mut h, &odo),
            None => None,
        };
        fprof(c, 2);
        let ft = fw(env, t);
        let clamp = t >= 1 && fprev == FCL;
        assert_eq!(clamp, cst.is_some());
        let wt = if clamp { ft + 1 } else { ft };
        if super::pointadd::knob_flag("SKYCOF_FPROF") {
            let mut ws = WSUM.lock().unwrap();
            ws[0] += w.wsw - 1; ws[1] += w.wad; ws[2] += fprev - 1; ws[3] += wt.max(fprev + 1); ws[4] += if t >= 1 { env.h[t - 1] } else { 0 };
            ws[5] += if t >= 1 { let f = fprev; (f - 1) - (f - 1).saturating_sub(p.w_dec).max(1) } else { 0 };
            eprintln!("SKYCOF_TROOM t={t} live={} room={} f={fprev} wadd={} rail={}/{} h={} clamp={clamp}", c.active_qubits(), room(c, p.cap), wt.max(fprev + 1), w.wsw, w.wad, h.len());
        }
        cof_add_fwd(c, &mut cof, isc, &rails, fprev, wt, cst.as_ref().map(|s| s.e), p.cap);
        fprof(c, 3);
        if let Some(ClampSt { zt, nz, e }) = cst {
            let z = zt.z;
            // E = z & !nz
            let m = c.alloc_bit();
            c.hmr(e, m);
            c.x(nz);
            c.cz_if(z, nz, m);
            c.x(nz);
            c.free_bit(m);
            c.release_clean(e);
            let rm = odo_room(c, p.cap);
            mm::odo_nonzero_xor(c, &odo, nz, rm);
            c.release_clean(nz);
            fold(c, &mut cof.a, &cof.b, z, p);
            zt.uncompute(c);
        } else {
            resize_signed(c, &mut cof.a, ft);
        }
        resize_signed(c, &mut cof.b, ft);
        fprof(c, 4);
        erase_isc(c, &cof, tt, isc, &rails);
        fprof(c, 5);
        typ = Some(tt);
        trace_tick(c, "fwd", t);
    }
    // the last letter is a post-park A
    let tl = typ.unwrap();
    c.x(tl);
    c.release_clean(tl);
    // parked rails (0, 1), b = p: classical constants
    assert_eq!(rails.r1.len(), env.rail[r - 1]);
    assert_eq!(rails.r2.len(), env.rail[r - 1]);
    c.x(rails.r2[0]);
    c.free_vec(&rails.r1);
    // Keep the aliased odometer lanes live through the arithmetic shell.
    let mut clear_r2 = vec![rails.r2[0]];
    clear_r2.extend_from_slice(&rails.r2[1 + p.odo_bits..]);
    c.free_vec(&clear_r2);
    assert_eq!(cof.a.len(), FCL);
    assert_eq!(cof.b.len(), FCL);
    let pv = crate::point_add::SECP256K1_P;
    for i in 1..N {
        if pv.bit(i) {
            c.x(cof.b[i]);
        }
    }
    c.free_vec(&cof.b[1..]);
    // s = x + p = (x - c) + 2^256 ; top wire 0
    let mut a = cof.a;
    let cc = U256::from(secp_c());
    c.x_all(&a);
    crate::point_add::const_arith::add_const(c, &a, cc);
    c.x_all(&a);
    c.x(a[N]);
    let top = a.pop().unwrap();
    c.free(top);
    fprof(c, 6);
    fprof_dump("fwd");
    adder::defer_active(false);
    FParked { s: a, h, odo, prev }
}

/// Exact walk back from [`forward`]'s parked state; returns the wires holding `d`.
pub fn backward(c: &mut Builder, p: &WalkParams, env: &Envelope, pk: FParked) -> Vec<Q> {
    let r = p.r;
    adder::defer_active(true);
    let FParked { s, mut h, mut odo, prev } = pk;
    let t0 = first_clamp(env, r);
    let mut a = s;
    assert_eq!(a.len(), N);
    let top = c.alloc_qubit();
    a.push(top);
    // x = s - 2^256 + c
    c.x(a[N]);
    let cc = U256::from(secp_c());
    crate::point_add::const_arith::add_const(c, &a, cc);
    let mut b = vec![NO_QUBIT];
    b.extend(c.alloc_qubits(FCL - 1));
    let pv = crate::point_add::SECP256K1_P;
    for i in 1..N {
        if pv.bit(i) {
            c.x(b[i]);
        }
    }
    let mut cof = FCof { a, b };
    let wl = env.rail[r - 1];
    let mut r2 = c.alloc_qubits(wl - p.odo_bits);
    let r2_tail = r2.split_off(1);
    r2.extend_from_slice(&odo);
    r2.extend(r2_tail);
    let mut rails = Rails { r1: c.alloc_qubits(wl), r2 };
    c.x(rails.r2[0]);
    let tl = c.alloc_qubit();
    c.x(tl);
    let mut typ = tl;
    for t in (0..r).rev() {
        let w = env.widths(t);
        let ft = fw(env, t);
        let fprev = if t == 0 { 2 } else { fw(env, t - 1) };
        let clamp = t >= 1 && fprev == FCL;
        let wt = if clamp { ft + 1 } else { ft };
        assert_eq!(cof.a.len(), ft);
        let isc = isc_recompute(c, &cof, typ, &rails);
        resize_signed(c, &mut cof.b, fprev);
        let cst = if clamp {
            let zt = FPark::compute(c, &cof.b, p.park_j);
            let z = zt.z;
            unfold(c, &mut cof.a, &cof.b, z, p);
            let nz = c.alloc_qubit();
            let rm = odo_room(c, p.cap);
            mm::odo_nonzero_xor(c, &odo, nz, rm);
            let e = c.alloc_qubit();
            c.x(nz);
            c.ccx(z, nz, e);
            c.x(nz);
            Some(ClampSt { zt, nz, e })
        } else {
            resize_signed(c, &mut cof.a, wt.max(fprev + 1));
            None
        };
        cof_add_rev(c, &mut cof, isc, &rails, fprev, wt, cst.as_ref().map(|s| s.e), p.cap);
        let tprev = if t >= 1 { Some(dispose_rev(c, p, env, t - 1, typ, isc, &cof, &rails, &mut h, &odo, cst)) } else { None };
        cswap(c, &cof, typ, tprev);
        tick::rail_rev(c, &mut rails, typ, isc, tprev, w.wsw, prev[t], Some(p.cap));
        trace_tick(c, "rev", t);
        if t == t0 {
            // The lane IDs remain in R2 and walk back to the input; they are
            // no longer an odometer after this tick.
            odo = Vec::new();
        }
        if let Some(tq) = tprev {
            typ = tq;
        }
    }
    // cofactors back at (1, -1), width 2; history and odometer empty
    assert_eq!(cof.a.len(), 2);
    c.x(cof.a[0]);
    c.x(cof.b[1]);
    c.free_vec(&cof.a);
    c.free_vec(&cof.b[1..]);
    h.shrink_to(c, 0);
    assert!(odo.is_empty());
    adder::defer_active(false);
    assert_eq!(adder::defer_stack_len(), 0, "frame walk: deferred debts left over");
    walk::unseed(c, rails)
}
