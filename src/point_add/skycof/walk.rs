//! SKY-COF walk: seed the rails from `d`, R forward ticks (rail tick, decoder/history disposal of the
//! previous letter, cofactor update, post-park fold), park bookkeeping (rail zero test + odometer),
//! and the exact walk back. Research code; used only by `skycof::pointadd`.
//!
//! # Per-tick schedule (forward, tick t >= 1)
//! 1. `rail_fwd_t(typ_{t-1})` -> `typ_t`, `isC_t` (rails now post(t)).
//! 2. Dispose `typ_{t-1}` against the cofactor post-state of tick t-1 (still untouched):
//!    * t-1 = 0: `first_tick` (A or C only).
//!    * cofactor field below the clamp: decoder push without `en` (a walk parks only once `r = p` fits, i.e.
//!      on ticks whose field is at the clamp; an earlier park is an envelope miss).
//!    * field at the clamp: park test `z = [top park_j bits of r all one]` (= [r == p] = [t-1 >= park]: before
//!      park `r <= p/v < 2^255` for `v >= 2`, and for `v = 1` `p - r = u s` was never below 2^247 in
//!      0.24M walks); odometer step (`g = z & typ`, `odo += g`, `typ ^= g`, `g` erased against
//!      `z & [odo != 0]`); decoder push with `en = !z`. Post-park letters are A (`typ = 1`) and the park
//!      tick's letter is B or C (`typ = 0`), so the odometer ends at the number of post-park ticks.
//! 3. `cof_fwd_t(typ_t, isC_t)`, `isC` erased by measurement.
//! 4. If the cofactor came out at clamp+1 wires: fold `s <- s - p` when the top wire is set (constant add
//!    over the low `fold_w` bits; the top wire is 0 before park).
//!
//! `typ_{R-1}` is disposed the same way after the last tick. The parked rails (0, 1) and `r = p` are then
//! classical constants and are freed; the walk back re-creates them and runs the exact inverse of every step
//! in reverse order.
use super::decoder::{self as dec, DecCfg, Hreg, TickIo};
use super::tick::{self, Cof, PrevWidths, TickWidths};
use super::adder;
use crate::circuit::QubitId as Q;
use crate::point_add::builder::Builder;
use crate::point_add::heo::Rails;
use crate::point_add::skycof_mm as mm;
use crate::point_add::N;

pub const SEED_W: usize = N + 2;
pub const CLAMP: usize = N;

/// Walk parameters (source defaults; research overrides in `pointadd::params`).
#[derive(Clone, Copy, Debug)]
pub struct WalkParams {
    pub r: usize,
    /// bits of the park test on the top of `r`
    pub park_j: usize,
    pub w_dec: usize,
    pub fold_w: usize,
    pub odo_bits: usize,
    pub cap: usize,
}

/// Per-tick public widths: rail (post-tick), cofactor field (post-tick), history envelope.
pub struct Envelope {
    pub rail: Vec<usize>,
    pub cof: Vec<usize>,
    pub h: Vec<usize>,
}

impl Envelope {
    /// The design's public k=0 w=64 eps=1e-4 widths (rails srail+8, cofactors min(kcof+8, 256),
    /// history H_k0w64+10), extended to `r` ticks by repeating the last row.
    pub fn design(r: usize) -> Self {
        let txt = include_str!("design_widths_k0w64_1e-4.tsv");
        let (mut rail, mut cof, mut h) = (Vec::new(), Vec::new(), Vec::new());
        for l in txt.lines() {
            if l.starts_with('#') || l.starts_with('t') || l.trim().is_empty() {
                continue;
            }
            let f: Vec<usize> = l.split('\t').take(4).map(|x| x.trim().parse().unwrap()).collect();
            assert_eq!(f[0], rail.len(), "envelope rows out of order");
            rail.push(f[1]);
            cof.push(f[2]);
            h.push(f[3]);
        }
        assert!(!rail.is_empty());
        rail.truncate(r);
        cof.truncate(r);
        h.truncate(r);
        while rail.len() < r {
            rail.push(*rail.last().unwrap());
            cof.push(*cof.last().unwrap());
            h.push(*h.last().unwrap());
        }
        for t in 1..r {
            h[t] = h[t].max(h[t - 1]);
            cof[t] = cof[t].max(cof[t - 1]).min(CLAMP);
        }
        Envelope { rail, cof, h }
    }
    pub fn widths(&self, t: usize) -> TickWidths {
        TickWidths { wsw: if t == 0 { SEED_W } else { self.rail[t - 1] }, wad: self.rail[t], ecof: self.cof[t], clamp: CLAMP }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TopFate {
    None,
    Freed,
    Folded,
}

/// State after the forward walk: `s` (256 wires, = -2^R / d mod p, lazily reduced), the history, the
/// odometer, and the book-keeping the walk back needs. Rails and `r` are freed (classical constants).
pub struct Parked {
    pub s: Vec<Q>,
    pub h: Hreg,
    pub odo: Vec<Q>,
    prev: Vec<PrevWidths>,
    tops: Vec<TopFate>,
}

fn room(c: &Builder, cap: usize) -> usize {
    cap.saturating_sub(c.active_qubits() as usize)
}

fn secp_c() -> u128 {
    mm::Field::secp().c
}

/// Rails `(d + p, d)` at width `SEED_W`; `R2` takes over `d`'s wires.
pub fn seed(c: &mut Builder, d: &[Q]) -> Rails {
    use crate::point_add::const_arith::add_const;
    use crate::point_add::modular::f;
    let r1 = c.alloc_qubits(SEED_W);
    c.cx_pairs(&d[..N], &r1[..N]);
    c.x(r1[N]); // d + 2^256
    c.x_all(&r1[..N + 1]); // r - f = NOT(NOT r + f)  (mod 2^257)
    add_const(c, &r1[..N + 1], f());
    c.x_all(&r1[..N + 1]);
    let mut r2 = d.to_vec();
    r2.extend(c.alloc_qubits(SEED_W - N));
    Rails { r1, r2 }
}

/// Inverse of [`seed`]; returns the wires now holding `d`.
pub fn unseed(c: &mut Builder, rails: Rails) -> Vec<Q> {
    use crate::point_add::const_arith::add_const;
    use crate::point_add::modular::f;
    let Rails { r1, r2 } = rails;
    assert_eq!(r1.len(), SEED_W);
    assert_eq!(r2.len(), SEED_W);
    add_const(c, &r1[..N + 1], f()); // d + 2^256
    c.x(r1[N]);
    c.cx_pairs(&r2[..N], &r1[..N]);
    c.free_vec(&r1);
    c.free_vec(&r2[N..]);
    r2[..N].to_vec()
}

// ─── park test ──────────────────────────────────────────────────────────────────────────────────

/// AND tree over `lits` with every internal node live. Returns (root, nodes bottom-up). `len - 1` Toffoli.
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

/// Erase tree nodes top-down by measurement (each node's children are still live): 0 Toffoli.
fn erase_nodes(c: &mut Builder, nodes: &[(Q, Q, Q)]) {
    for &(n, a, b) in nodes.iter().rev() {
        let m = c.alloc_bit();
        c.hmr(n, m);
        c.cz_if(a, b, m);
        c.free_bit(m);
        c.release_clean(n);
    }
}

/// A fresh wire holding AND(lits) with no other wire kept (`len - 1` Toffoli, `len - 1` wires transient).
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

/// Multi-controlled Z on `lits` (under the caller's condition): `len - 2` Toffoli.
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

/// Erase a wire holding AND(lits) whose tree is gone: HMR, then MCZ under the outcome.
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

/// Bits per part of the park test (each part's AND is a frozen wire; its tree is `PARK_PART - 1` wires).
const PARK_PART: usize = 5;

/// `z = AND(top j bits of r)`: frozen part ANDs `a_i` (parts of `PARK_PART` bits), `z = AND(a_i)` frozen,
/// then the parts are erased (frozen erasure) so only `z` is held while the odometer and the decoder run.
/// `j - 1` Toffoli plus `(len - 2)/2` expected per part; at most `PARK_PART + 1` wires transient. The
/// uncompute measures `z` and, under the outcome, recomputes the parts to apply `MCZ(a_i)` and erases
/// them again.
pub struct ParkTest {
    pub z: Q,
    parts: Vec<Vec<Q>>,
}

impl ParkTest {
    pub fn compute(c: &mut Builder, r: &[Q], j: usize) -> Self {
        assert_eq!(r.len(), CLAMP);
        assert!(j > PARK_PART && j <= CLAMP);
        let bits = &r[CLAMP - j..];
        let parts: Vec<Vec<Q>> = bits.chunks(PARK_PART).map(|p| p.to_vec()).collect();
        let a: Vec<Q> = parts.iter().map(|p| and_frozen(c, p)).collect();
        let z = and_frozen(c, &a);
        for (ai, p) in a.iter().zip(&parts).rev() {
            erase_frozen(c, *ai, p);
        }
        ParkTest { z, parts }
    }
    pub fn uncompute(self, c: &mut Builder) {
        let m = c.alloc_bit();
        c.hmr(self.z, m);
        c.release_clean(self.z);
        c.push_condition(m);
        let a: Vec<Q> = self.parts.iter().map(|p| and_frozen(c, p)).collect();
        mcz(c, &a);
        for (ai, p) in a.iter().zip(&self.parts).rev() {
            erase_frozen(c, *ai, p);
        }
        c.pop_condition();
        c.free_bit(m);
    }
}

// ─── odometer step ──────────────────────────────────────────────────────────────────────────────

fn odo_room(c: &Builder, cap: usize) -> usize {
    room(c, cap).max(4)
}

/// `g = z & typ; odo += g; typ ^= g; g ^= z & [odo != 0]` (g ends 0).
fn odo_fwd(c: &mut Builder, z: Q, typ: Q, odo: &[Q], cap: usize) {
    let g = c.alloc_qubit();
    c.ccx(z, typ, g);
    let rm = odo_room(c, cap);
    mm::odo_inc(c, odo, g, rm);
    c.cx(g, typ);
    let nz = c.alloc_qubit();
    let rm = odo_room(c, cap);
    mm::odo_nonzero_xor(c, odo, nz, rm);
    c.ccx(z, nz, g);
    let rm = odo_room(c, cap);
    mm::odo_nonzero_xor(c, odo, nz, rm);
    c.release_clean(nz);
    c.release_clean(g);
}

/// Exact inverse of [`odo_fwd`].
fn odo_rev(c: &mut Builder, z: Q, typ: Q, odo: &[Q], cap: usize) {
    let g = c.alloc_qubit();
    let nz = c.alloc_qubit();
    let rm = odo_room(c, cap);
    mm::odo_nonzero_xor(c, odo, nz, rm);
    c.ccx(z, nz, g);
    let rm = odo_room(c, cap);
    mm::odo_nonzero_xor(c, odo, nz, rm);
    c.release_clean(nz);
    c.cx(g, typ);
    let rm = odo_room(c, cap);
    mm::odo_dec(c, odo, g, rm);
    c.ccx(z, typ, g);
    c.release_clean(g);
}

// ─── post-park fold ─────────────────────────────────────────────────────────────────────────────

/// `s` at clamp+1 wires: when the top wire is set, `s <- s - p` (= low bits + c, window `fold_w`);
/// the top wire is then `s[0]` (s even before, odd after) and is cleared and freed.
fn fold(c: &mut Builder, cof: &mut Cof, p: &WalkParams) {
    assert_eq!(cof.s.len(), CLAMP + 1);
    let top = cof.s.pop().unwrap();
    let w = p.fold_w;
    let rm = room(c, p.cap);
    if rm >= 12 {
        mm::cadd_k(c, &cof.s[..w], secp_c(), top, rm);
    } else {
        // r == p whenever the top wire can be set (park tick and after): s -= top * (p mod 2^w)
        adder::sub(c, Some(top), &cof.r[..w], &cof.s[..w], None, Some(p.cap));
    }
    c.cx(cof.s[0], top);
    c.release_clean(top);
}

/// Exact inverse of [`fold`].
fn unfold(c: &mut Builder, cof: &mut Cof, p: &WalkParams) {
    assert_eq!(cof.s.len(), CLAMP);
    let top = c.alloc_qubit();
    c.cx(cof.s[0], top);
    let w = p.fold_w;
    let rm = room(c, p.cap);
    if rm >= 12 {
        mm::csub_k(c, &cof.s[..w], secp_c(), top, rm);
    } else {
        adder::add(c, Some(top), &cof.r[..w], &cof.s[..w], None, Some(p.cap));
    }
    cof.s.push(top);
}

// ─── letter disposal ────────────────────────────────────────────────────────────────────────────

fn dec_cfg(c: &Builder, p: &WalkParams, e: usize, en: bool) -> DecCfg {
    let n = dec::Window::new(e, p.w_dec).n();
    let floor = dec::min_room(en);
    let rm = room(c, p.cap).clamp(floor, n + floor);
    DecCfg { w: p.w_dec, room: rm }
}

/// Forward: erase `typ` (letter of tick `t1`) against the cofactor post-state of tick `t1`;
/// rails are post(t1 + 1).
#[allow(clippy::too_many_arguments)]
fn dispose_fwd(c: &mut Builder, p: &WalkParams, env: &Envelope, t1: usize, typ: Q, cof: &Cof, h: &mut Hreg, odo: &[Q]) {
    h.grow_to(c, env.h[t1]);
    if t1 == 0 {
        dec::first_tick(c, &cof.s, typ, None);
    } else if env.cof[t1] == CLAMP {
        trace_step(c, "pre-park");
        let zt = ParkTest::compute(c, &cof.r, p.park_j);
        trace_step(c, "parktest");
        odo_fwd(c, zt.z, typ, odo, p.cap);
        trace_step(c, "odo");
        c.x(zt.z);
        let cfg = dec_cfg(c, p, env.cof[t1], true);
        let io = TickIo { s: &cof.s, r: &cof.r, e: env.cof[t1], en: Some(zt.z), typ, cflag: None, park: None };
        dec::push(c, &io, h, cfg);
        trace_step(c, "dec");
        c.x(zt.z);
        zt.uncompute(c);
        trace_step(c, "unpark");
    } else {
        let cfg = dec_cfg(c, p, env.cof[t1], false);
        let io = TickIo { s: &cof.s, r: &cof.r, e: env.cof[t1], en: None, typ, cflag: None, park: None };
        dec::push(c, &io, h, cfg);
    }
    c.release_clean(typ);
}

/// Reverse: re-create the letter of tick `t1` (exact inverse of [`dispose_fwd`]).
#[allow(clippy::too_many_arguments)]
fn dispose_rev(c: &mut Builder, p: &WalkParams, env: &Envelope, t1: usize, cof: &Cof, h: &mut Hreg, odo: &[Q]) -> Q {
    h.shrink_to(c, env.h[t1]);
    let typ = c.alloc_qubit();
    if t1 == 0 {
        dec::first_tick(c, &cof.s, typ, None);
    } else if env.cof[t1] == CLAMP {
        let zt = ParkTest::compute(c, &cof.r, p.park_j);
        c.x(zt.z);
        let cfg = dec_cfg(c, p, env.cof[t1], true);
        let io = TickIo { s: &cof.s, r: &cof.r, e: env.cof[t1], en: Some(zt.z), typ, cflag: None, park: None };
        dec::pop(c, &io, h, cfg);
        c.x(zt.z);
        odo_rev(c, zt.z, typ, odo, p.cap);
        zt.uncompute(c);
    } else {
        let cfg = dec_cfg(c, p, env.cof[t1], false);
        let io = TickIo { s: &cof.s, r: &cof.r, e: env.cof[t1], en: None, typ, cflag: None, park: None };
        dec::pop(c, &io, h, cfg);
    }
    typ
}

/// Research: tick-boundary snapshots (the ops so far plus the walk registers), recorded only when a probe
/// enables the recorder. Order: rails r1, r2, cof s, r, history, odometer, typ.
pub type Snap = (String, Vec<crate::circuit::Op>, Vec<Vec<Q>>);
thread_local! {
    pub static SNAPS: std::cell::RefCell<Option<Vec<Snap>>> = const { std::cell::RefCell::new(None) };
}

fn snap(c: &mut Builder, tag: String, rails: &Rails, cof: &Cof, h: &Hreg, odo: &[Q], typ: Option<Q>) {
    SNAPS.with(|s| {
        if let Some(v) = s.borrow_mut().as_mut() {
            let ops = c.take_ops();
            v.push((tag, ops, vec![rails.r1.clone(), rails.r2.clone(), cof.s.clone(), cof.r.clone(), h.wires.clone(), odo.to_vec(), typ.into_iter().collect()]));
        }
    });
}

fn trace_step(c: &mut Builder, what: &str) {
    if super::pointadd::knob_flag("SKYCOF_STEP_TRACE") {
        let pk = c.take_win_peak();
        eprintln!("SKYCOF_STEP {what} live={} peak={pk}", c.active_qubits());
    }
}

/// Phase label hook: per-tick trace under `SKYCOF_TICK_TRACE` (research).
fn trace_tick(c: &mut Builder, dir: &str, t: usize) {
    if super::pointadd::knob_flag("SKYCOF_TICK_TRACE") {
        let pk = c.take_win_peak();
        eprintln!("SKYCOF_TICK {dir} {t} live={} peak={pk} ops={}", c.active_qubits(), c.op_count());
    }
}

// ─── the walk ───────────────────────────────────────────────────────────────────────────────────

/// Forward walk on `d` (its wires become R2). Returns the parked state.
pub fn forward(c: &mut Builder, p: &WalkParams, env: &Envelope, d: &[Q]) -> Parked {
    let r = p.r;
    let mut rails = seed(c, d);
    let mut cof = Cof { s: c.alloc_qubits(2), r: c.alloc_qubits(2) };
    c.x(cof.r[0]);
    let mut h = Hreg::new();
    let odo = c.alloc_qubits(p.odo_bits);
    let mut prev = Vec::with_capacity(r);
    let mut tops = Vec::with_capacity(r);
    let mut typ: Option<Q> = None;
    for t in 0..r {
        let w = env.widths(t);
        prev.push(PrevWidths { r1: rails.r1.len(), r2: rails.r2.len(), cof: cof.s.len() });
        trace_step(c, "tick-start");
        let (typ_t, isc, _) = tick::rail_fwd(c, &mut rails, typ, w.wsw, w.wad, Some(p.cap));
        trace_step(c, "rail");
        if let Some(tp) = typ {
            dispose_fwd(c, p, env, t - 1, tp, &cof, &mut h, &odo);
        }
        trace_step(c, "dispose");
        tick::cof_fwd(c, &mut cof, typ_t, isc, &w, Some(p.cap));
        trace_step(c, "cof");
        tick::erase_isc(c, &cof, typ_t, isc);
        let fate = if cof.s.len() > cof.r.len() {
            fold(c, &mut cof, p);
            TopFate::Folded
        } else {
            TopFate::None
        };
        tops.push(fate);
        typ = Some(typ_t);
        trace_tick(c, "fwd", t);
        snap(c, format!("F{t}"), &rails, &cof, &h, &odo, typ);
    }
    dispose_fwd(c, p, env, r - 1, typ.unwrap(), &cof, &mut h, &odo);
    // parked rails (R1, R2) = (0, 1) and r = p: classical constants
    assert_eq!(rails.r1.len(), env.rail[r - 1]);
    assert_eq!(rails.r2.len(), env.rail[r - 1]);
    c.x(rails.r2[0]);
    c.free_vec(&rails.r1);
    c.free_vec(&rails.r2);
    assert_eq!(cof.r.len(), N);
    assert_eq!(cof.s.len(), N);
    let pv = crate::point_add::SECP256K1_P;
    for i in 0..N {
        if pv.bit(i) {
            c.x(cof.r[i]);
        }
    }
    c.free_vec(&cof.r);
    Parked { s: cof.s, h, odo, prev, tops }
}

/// Exact walk back from [`forward`]'s parked state; returns the wires holding `d`.
pub fn backward(c: &mut Builder, p: &WalkParams, env: &Envelope, pk: Parked) -> Vec<Q> {
    let r = p.r;
    let Parked { s, mut h, odo, prev, tops } = pk;
    let wl = env.rail[r - 1];
    let mut rails = Rails { r1: c.alloc_qubits(wl), r2: c.alloc_qubits(wl) };
    c.x(rails.r2[0]);
    let rr = c.alloc_qubits(N);
    let pv = crate::point_add::SECP256K1_P;
    for i in 0..N {
        if pv.bit(i) {
            c.x(rr[i]);
        }
    }
    let mut cof = Cof { s, r: rr };
    let mut typ = dispose_rev(c, p, env, r - 1, &cof, &mut h, &odo);
    for t in (0..r).rev() {
        let w = env.widths(t);
        match tops[t] {
            TopFate::Folded => unfold(c, &mut cof, p),
            TopFate::Freed => {
                let q = c.alloc_qubit();
                cof.s.push(q);
            }
            TopFate::None => {}
        }
        let isc = tick::isc_recompute(c, &cof, typ);
        tick::cof_rev(c, &mut cof, typ, isc, prev[t].cof, Some(p.cap));
        let tprev = if t >= 1 { Some(dispose_rev(c, p, env, t - 1, &cof, &mut h, &odo)) } else { None };
        tick::rail_rev(c, &mut rails, typ, isc, tprev, w.wsw, (prev[t].r1, prev[t].r2), Some(p.cap));
        trace_tick(c, "rev", t);
        if let Some(tq) = tprev {
            typ = tq;
        }
        if t >= 1 {
            snap(c, format!("B{}", t - 1), &rails, &cof, &h, &odo, Some(typ));
        }
    }
    // cofactors back at (s, r) = (0, 1), width 2; history and odometer empty
    assert_eq!(cof.s.len(), 2);
    c.x(cof.r[0]);
    c.free_vec(&cof.s);
    c.free_vec(&cof.r);
    h.shrink_to(c, 0);
    c.free_vec(&odo);
    unseed(c, rails)
}
