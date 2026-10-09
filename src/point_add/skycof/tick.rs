//! SKY-COF walk tick: Skywalk signed rails (the `heo` rail tick) + Kaliski-frame integer cofactors,
//! public per-tick field widths, forward and exact reverse. Research code, inert in the default build.
//!
//! # State
//! * rails `(R1, R2)`: two's complement, LSB first, = an orientation of `(+-u, +-(u+v))` (Skywalk seed
//!   `(d + p, d)`); `v` odd.
//! * cofactors `(s, r)`: unsigned, LSB first, `s.len() == r.len()` at entry; Kaliski invariant
//!   `u s + v r = p` with `s` even and `r` odd before park (start `s = 0, r = 1`).
//!
//! # Forward tick (`fwd_tick`)
//! 1. Rail tick, gate for gate `heo::fwd_tick` (only the rail add is room-aware): `c = R1[0]`,
//!    Fredkin on `c`, `H = R1 >> 1` (relabel), `R2 -/+= H` (subtract when the signs agree). The freed
//!    rail LSB becomes `typ_t = typ_{t-1} xor c`; the add's sign wire ends as
//!    `isC = sign(R2_new) xor sign(R2_old)` (the Skywalk tape bit `s_t`).
//!    Letters: `typ = [A]` (u even), `isC = [C]` (u odd, u < v), B otherwise. At the park step
//!    (`u = v = 1`) the rails label the step C when `R2_old < 0` and B otherwise; both give `u = 0`,
//!    `r = p`; C gives `s_park = 2 r_old = -2 s_old (mod p)`, so the sign wire must count C as labelled.
//!    After park `typ = 1` and `isC = 0` on every tick.
//! 2. Cofactors: `Fredkin(isC; s, r)` (bit 0 by two CNOTs: `s0 = 0, r0 = 1` whenever `isC = 1`),
//!    `r += s` controlled on `not typ` (B or C), then `s <- 2s` by relabel (a fresh zero LSB).
//! 3. `isC` is erased by HMR with the phase repair `CZ(s_new[1], not typ)` (`isC = s_new[1] and not typ`).
//!
//! Widths: rails `wsw` at the swap, `wad` at the add (post-tick). Cofactors: `r` ends at
//! `ecof` wires; `s` ends at `ecof` wires, except when `ecof == clamp` and the entry width is already
//! `>= clamp`: then `s` ends at `clamp + 1` wires, the top wire being `2s >> clamp` (the park fold
//! flag; 0 on every pre-park tick). The caller folds it (`s <- 2s mod p`) or frees it before the next
//! tick. Trimmed wires must be zero (rails: sign copies) -- the envelope's promise.
//!
//! # Reverse tick (`rev_tick`)
//! Given `typ_t` (from the decoder) and `typ_{t-1}`: `isC = s[1] and not typ` (1 CCX), undo the
//! relabel, `r -= s` controlled on `not typ`, un-Fredkin, then the Skywalk reverse rail tick with
//! `c_t = typ_t xor typ_{t-1}`; `typ_t` becomes the rail LSB again and `isC` is uncomputed from the rails.
use super::adder::{self, Plan};
use crate::circuit::QubitId as Q;
use crate::point_add::builder::Builder;
use crate::point_add::heo::Rails;

pub struct Cof {
    pub s: Vec<Q>,
    pub r: Vec<Q>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TickWidths {
    /// rail width at the swap (two's complement incl. sign)
    pub wsw: usize,
    /// rail width at the add = post-tick rail width
    pub wad: usize,
    /// post-tick cofactor field width (unsigned), `<= clamp`
    pub ecof: usize,
    /// cofactor clamp (256 in production)
    pub clamp: usize,
}

/// Entry widths, needed by the reverse tick.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrevWidths {
    pub r1: usize,
    pub r2: usize,
    pub cof: usize,
}

/// Plans used by the two adds (for reports).
#[derive(Clone, Debug, PartialEq)]
pub struct TickPlans {
    pub rail: Plan,
    pub cof: Plan,
}

fn fredkin(c: &mut Builder, ctrl: Q, a: Q, b: Q) {
    c.cx(b, a);
    c.ccx(ctrl, a, b);
    c.cx(b, a);
}

/// Two's-complement resize (`heo`): grow = sign-extend, trim = CX from the new top + free.
pub fn resize_signed(c: &mut Builder, reg: &mut Vec<Q>, w: usize) {
    while reg.len() < w {
        let q = c.alloc_qubit();
        c.cx(*reg.last().unwrap(), q);
        reg.push(q);
    }
    while reg.len() > w {
        let top = reg.pop().unwrap();
        c.cx(*reg.last().unwrap(), top);
        c.free(top);
    }
}

/// Unsigned resize: grow = fresh zero wires, trim = free (the trimmed wires must be zero).
pub fn resize_unsigned(c: &mut Builder, reg: &mut Vec<Q>, w: usize) {
    while reg.len() < w {
        let q = c.alloc_qubit();
        reg.push(q);
    }
    while reg.len() > w {
        let top = reg.pop().unwrap();
        c.free(top);
    }
}

/// Forward rail tick (`heo::fwd_tick` with a room-aware add). Returns `(typ_t, isC, plan)`.
pub fn rail_fwd(c: &mut Builder, rails: &mut Rails, typ_prev: Option<Q>, wsw: usize, wad: usize, cap: Option<usize>)
                -> (Q, Q, Plan) {
    assert!(wsw >= 3 && wad >= 2, "rail widths {wsw}/{wad}");
    resize_signed(c, &mut rails.r1, wsw);
    resize_signed(c, &mut rails.r2, wsw);
    let (r1, r2) = (&rails.r1, &rails.r2);
    let ctl = r1[0];
    for i in 1..wsw {
        fredkin(c, ctl, r1[i], r2[i]);
    }
    c.cx(ctl, r2[0]);
    let mut e2 = r1[1..].to_vec();
    resize_signed(c, &mut e2, wad);
    resize_signed(c, &mut rails.r2, wad);
    let r2 = &rails.r2;
    let tau = c.alloc_qubit();
    c.cx(e2[wad - 1], tau);
    c.cx(r2[wad - 1], tau);
    c.x(tau);
    c.cx_all(tau, &e2);
    let plan = adder::add(c, None, &e2, r2, Some(tau), cap);
    c.cx_all(tau, &e2);
    c.x(tau);
    c.cx(e2[wad - 1], tau);
    c.cx(r2[wad - 1], tau);
    if let Some(tp) = typ_prev {
        c.cx(tp, ctl);
    }
    rails.r1 = e2;
    (ctl, tau, plan)
}

/// Exact inverse of [`rail_fwd`] (`heo::rev_tick` with a room-aware subtract); consumes `typ` (it
/// becomes the rail LSB) and `isc` (uncomputed and freed).
#[allow(clippy::too_many_arguments)]
pub fn rail_rev(c: &mut Builder, rails: &mut Rails, typ: Q, isc: Q, typ_prev: Option<Q>, wsw: usize,
                prev: (usize, usize), cap: Option<usize>) -> Plan {
    let wad = rails.r1.len();
    assert_eq!(rails.r2.len(), wad, "rail_rev: rails must both be at the add width");
    let tau = isc;
    c.cx(rails.r1[wad - 1], tau);
    c.cx(rails.r2[wad - 1], tau);
    c.x(tau);
    c.cx_all(tau, &rails.r1);
    let plan = adder::sub(c, None, &rails.r1, &rails.r2, Some(tau), cap);
    c.cx_all(tau, &rails.r1);
    c.x(tau);
    c.cx(rails.r1[wad - 1], tau);
    c.cx(rails.r2[wad - 1], tau);
    c.free(tau);
    let ctl = typ;
    if let Some(tp) = typ_prev {
        c.cx(tp, ctl);
    }
    resize_signed(c, &mut rails.r1, wsw - 1);
    resize_signed(c, &mut rails.r2, wsw);
    rails.r1.insert(0, ctl);
    c.cx(ctl, rails.r2[0]);
    for i in 1..wsw {
        fredkin(c, ctl, rails.r1[i], rails.r2[i]);
    }
    resize_signed(c, &mut rails.r1, prev.0);
    resize_signed(c, &mut rails.r2, prev.1);
    plan
}

/// Operand length of the cofactor add (`s` before the relabel).
fn add_operand_len(w: &TickWidths, e_prev: usize) -> usize {
    if w.ecof == w.clamp && e_prev >= w.clamp { w.ecof } else { w.ecof - 1 }
}

/// Cofactor update of one forward tick; `typ`, `isc` from [`rail_fwd`]. Leaves `isc` live.
pub fn cof_fwd(c: &mut Builder, cof: &mut Cof, typ: Q, isc: Q, w: &TickWidths, cap: Option<usize>) -> Plan {
    let e_prev = cof.s.len();
    assert_eq!(cof.r.len(), e_prev, "cof_fwd: s and r must enter at one width (fold the park flag first)");
    assert!(e_prev >= 2 && w.ecof >= 2 && w.ecof <= w.clamp, "cof widths {e_prev} -> {}", w.ecof);
    for i in 1..e_prev {
        fredkin(c, isc, cof.s[i], cof.r[i]);
    }
    c.cx(isc, cof.s[0]);
    c.cx(isc, cof.r[0]);
    let n = w.ecof;
    let k = add_operand_len(w, e_prev);
    resize_unsigned(c, &mut cof.r, n);
    resize_unsigned(c, &mut cof.s, k);
    c.x(typ);
    let plan = adder::add(c, Some(typ), &cof.s, &cof.r, None, cap);
    c.x(typ);
    let z = c.alloc_qubit();
    cof.s.insert(0, z);
    plan
}

/// Erase `isC = s[1] and not typ` by measurement (0 Toffoli). Valid right after [`cof_fwd`].
pub fn erase_isc(c: &mut Builder, cof: &Cof, typ: Q, isc: Q) {
    let m = c.alloc_bit();
    c.hmr(isc, m);
    c.x(typ);
    c.cz_if(cof.s[1], typ, m);
    c.x(typ);
    c.free_bit(m);
    c.release_clean(isc);
}

/// Forward tick that leaves `isC` live (e.g. for the C-parity sign wire); the caller must
/// [`erase_isc`] it before the cofactors change again. Returns `(typ_t, isC, entry widths, plans)`.
pub fn fwd_tick_open(c: &mut Builder, rails: &mut Rails, cof: &mut Cof, typ_prev: Option<Q>, w: &TickWidths,
                     cap: Option<usize>) -> (Q, Q, PrevWidths, TickPlans) {
    let prev = PrevWidths { r1: rails.r1.len(), r2: rails.r2.len(), cof: cof.s.len() };
    let (typ, isc, rail) = rail_fwd(c, rails, typ_prev, w.wsw, w.wad, cap);
    let cofp = cof_fwd(c, cof, typ, isc, w, cap);
    (typ, isc, prev, TickPlans { rail, cof: cofp })
}

/// One forward SKY-COF tick. Returns `typ_t` (a live wire the caller owns), the entry widths and the
/// add plans.
pub fn fwd_tick(c: &mut Builder, rails: &mut Rails, cof: &mut Cof, typ_prev: Option<Q>, w: &TickWidths,
                cap: Option<usize>) -> (Q, PrevWidths, TickPlans) {
    let (typ, isc, prev, plans) = fwd_tick_open(c, rails, cof, typ_prev, w, cap);
    erase_isc(c, cof, typ, isc);
    (typ, prev, plans)
}

/// Recompute `isC = s[1] and not typ` into a fresh wire (1 CCX), on a post-tick state.
pub fn isc_recompute(c: &mut Builder, cof: &Cof, typ: Q) -> Q {
    let isc = c.alloc_qubit();
    c.x(typ);
    c.ccx(typ, cof.s[1], isc);
    c.x(typ);
    isc
}

/// Reverse cofactor update given the recomputed `isC` (see [`isc_recompute`]).
pub fn cof_rev(c: &mut Builder, cof: &mut Cof, typ: Q, isc: Q, e_prev: usize, cap: Option<usize>) -> Plan {
    let n = cof.r.len();
    let z = cof.s.remove(0);
    c.free(z);
    assert!(cof.s.len() == n || cof.s.len() + 1 == n, "cof_rev: s {} vs r {n}", cof.s.len());
    c.x(typ);
    let plan = adder::sub(c, Some(typ), &cof.s, &cof.r, None, cap);
    c.x(typ);
    resize_unsigned(c, &mut cof.r, e_prev);
    resize_unsigned(c, &mut cof.s, e_prev);
    for i in 1..e_prev {
        fredkin(c, isc, cof.s[i], cof.r[i]);
    }
    c.cx(isc, cof.s[0]);
    c.cx(isc, cof.r[0]);
    plan
}

/// Exact inverse of [`fwd_tick_open`]: consumes `typ` (`typ_t`) and `isc` (a live `isC`, e.g. from
/// [`isc_recompute`]).
#[allow(clippy::too_many_arguments)]
pub fn rev_tick_with_isc(c: &mut Builder, rails: &mut Rails, cof: &mut Cof, typ: Q, isc: Q, typ_prev: Option<Q>,
                         w: &TickWidths, prev: &PrevWidths, cap: Option<usize>) -> TickPlans {
    let cofp = cof_rev(c, cof, typ, isc, prev.cof, cap);
    let rail = rail_rev(c, rails, typ, isc, typ_prev, w.wsw, (prev.r1, prev.r2), cap);
    TickPlans { rail, cof: cofp }
}

/// Exact inverse of [`fwd_tick`]: consumes `typ` (`typ_t`, as the forward tick left it).
#[allow(clippy::too_many_arguments)]
pub fn rev_tick(c: &mut Builder, rails: &mut Rails, cof: &mut Cof, typ: Q, typ_prev: Option<Q>, w: &TickWidths,
                prev: &PrevWidths, cap: Option<usize>) -> TickPlans {
    let isc = isc_recompute(c, cof, typ);
    rev_tick_with_isc(c, rails, cof, typ, isc, typ_prev, w, prev, cap)
}
