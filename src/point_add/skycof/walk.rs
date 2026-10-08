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
use super::adder;
use super::decoder::{self as dec, DecCfg, Hreg, TickIo};
use super::tick::{self, Cof, PrevWidths, TickWidths};
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
#[derive(Clone)]
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
            let f: Vec<usize> = l
                .split('\t')
                .take(4)
                .map(|x| x.trim().parse().unwrap())
                .collect();
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
        // GCD-only research builds have substantially more room than the
        // embedded point-addition walk.  Let the probe spend that room on a
        // wider public envelope instead of relying on a nonce-selected tail.
        // The knob is captured only when SKYCOF_RESEARCH=1.
        if let Some(raw) = super::pointadd::knob("SKYCOF_ENVELOPE_EXTRA") {
            let extra: usize = raw.parse().expect("SKYCOF_ENVELOPE_EXTRA integer");
            for x in &mut rail {
                *x += extra;
            }
            for x in &mut cof {
                *x = (*x + extra).min(CLAMP);
            }
            for x in &mut h {
                *x += extra;
            }
        }
        Envelope { rail, cof, h }
    }
    pub fn widths(&self, t: usize) -> TickWidths {
        TickWidths {
            wsw: if t == 0 { SEED_W } else { self.rail[t - 1] },
            wad: self.rail[t],
            ecof: self.cof[t],
            clamp: CLAMP,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TopFate {
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

const GHOST_ODO_START: usize = 64;

fn ghost_odo() -> bool {
    super::pointadd::knob("SKYCOF_GHOST_ODO")
        .map(|v| v != "0" && !v.is_empty())
        .unwrap_or(true)
}

fn check_ghost_odo(p: &WalkParams, env: &Envelope) {
    if !ghost_odo() {
        return;
    }
    let end = GHOST_ODO_START + p.odo_bits;
    assert!(p.odo_bits > 0 && end < CLAMP);
    assert!(dec::Window::new(CLAMP, p.w_dec).lo >= end,
        "embedded counter overlaps decoder field reads");
    assert!(p.fold_w <= GHOST_ODO_START,
        "embedded counter overlaps the folded constant window");
    assert!(CLAMP - p.park_j >= end,
        "embedded counter overlaps the park predicate");
    let first_clamp = env.cof.iter().position(|&e| e == CLAMP)
        .expect("embedded counter needs a clamped endpoint");
    assert!(p.r - first_clamp < (1usize << p.odo_bits),
        "embedded counter can overflow the public parked horizon");
    assert!(env.rail[p.r - 1] > 0);
}

/// At clamp the middle R bits are ordinary cofactor data before park and the
/// odometer afterwards. The other R consumers exclude this interval while
/// parked. It is an alias, never independently allocated or freed.
fn odo_view<'a>(p: &WalkParams, cof: &'a Cof, owned: &'a [Q]) -> &'a [Q] {
    if ghost_odo() {
        assert_eq!(cof.r.len(), CLAMP);
        &cof.r[GHOST_ODO_START..GHOST_ODO_START + p.odo_bits]
    } else {
        owned
    }
}

/// Toggle the prime padding on the unique park-B/C event. In the forward
/// direction this turns known prime bits into zero counter storage. In the
/// inverse direction it restores the full prime before the park cofactor
/// update is undone. Erase g while typ is still unchanged.
fn ghost_odo_prime_xor(c: &mut Builder, p: &WalkParams, cof: &Cof, z: Q, typ: Q) {
    if !ghost_odo() {
        return;
    }
    let g = c.alloc_qubit();
    c.x(typ);
    c.ccx(z, typ, g);
    c.x(typ);
    let prime = crate::point_add::SECP256K1_P;
    for i in 0..p.odo_bits {
        if prime.bit(GHOST_ODO_START + i) {
            c.cx(g, cof.r[GHOST_ODO_START + i]);
        }
    }
    let m = c.alloc_bit();
    c.hmr(g, m);
    c.z_if(z, m);
    c.cz_if(z, typ, m);
    c.free_bit(m);
    c.release_clean(g);
}

fn secp_c() -> u128 {
    mm::Field::secp().c
}

/// Add a public constant while respecting the walk cap.  The ordinary
/// constant ladder is cheapest when all carries fit.  In low room, a single
/// prepared |1> turns the same constant into a controlled-constant add, which
/// lets `const_arith` use its exact chunked/HMR backend.
fn add_const_capped(c: &mut Builder, acc: &[Q], k: alloy_primitives::U256, cap: usize) {
    use crate::point_add::const_arith::{add_const, cadd_const_trunc};
    let carries = acc.len().saturating_sub(2);
    let room = cap.saturating_sub(c.active_qubits() as usize);
    if room >= carries {
        add_const(c, acc, k);
    } else {
        let one = c.alloc_qubit();
        c.x(one);
        cadd_const_trunc(c, acc, k, one, false);
        c.x(one);
        c.free(one);
    }
}

/// Rails `(d + p, d)` at width `SEED_W`; `R2` takes over `d`'s wires.
pub fn seed(c: &mut Builder, d: &[Q], cap: usize) -> Rails {
    use crate::point_add::modular::f;
    let r1 = c.alloc_qubits(SEED_W);
    c.cx_pairs(&d[..N], &r1[..N]);
    c.x(r1[N]); // d + 2^256
    c.x_all(&r1[..N + 1]); // r - f = NOT(NOT r + f)  (mod 2^257)
    add_const_capped(c, &r1[..N + 1], f(), cap);
    c.x_all(&r1[..N + 1]);
    let mut r2 = d.to_vec();
    r2.extend(c.alloc_qubits(SEED_W - N));
    Rails { r1, r2 }
}

/// Inverse of [`seed`]; returns the wires now holding `d`.
pub fn unseed(c: &mut Builder, rails: Rails, cap: usize) -> Vec<Q> {
    use crate::point_add::modular::f;
    let Rails { r1, r2 } = rails;
    assert_eq!(r1.len(), SEED_W);
    assert_eq!(r2.len(), SEED_W);
    add_const_capped(c, &r1[..N + 1], f(), cap); // d + 2^256
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
    DecCfg {
        w: p.w_dec,
        room: rm,
    }
}

/// Forward: erase `typ` (letter of tick `t1`) against the cofactor post-state of tick `t1`;
/// rails are post(t1 + 1).
#[allow(clippy::too_many_arguments)]
fn dispose_fwd(
    c: &mut Builder,
    p: &WalkParams,
    env: &Envelope,
    t1: usize,
    typ: Q,
    cof: &Cof,
    h: &mut Hreg,
    odo: &[Q],
) {
    h.grow_to(c, env.h[t1]);
    if t1 == 0 {
        dec::first_tick(c, &cof.s, typ, None);
    } else if env.cof[t1] == CLAMP {
        trace_step(c, "pre-park");
        let zt = ParkTest::compute(c, &cof.r, p.park_j);
        trace_step(c, "parktest");
        ghost_odo_prime_xor(c, p, cof, zt.z, typ);
        odo_fwd(c, zt.z, typ, odo_view(p, cof, odo), p.cap);
        trace_step(c, "odo");
        c.x(zt.z);
        let cfg = dec_cfg(c, p, env.cof[t1], true);
        let io = TickIo {
            s: &cof.s,
            r: &cof.r,
            e: env.cof[t1],
            en: Some(zt.z),
            typ,
            cflag: None,
            park: None,
        };
        dec::push(c, &io, h, cfg);
        trace_step(c, "dec");
        c.x(zt.z);
        zt.uncompute(c);
        trace_step(c, "unpark");
    } else {
        let cfg = dec_cfg(c, p, env.cof[t1], false);
        let io = TickIo {
            s: &cof.s,
            r: &cof.r,
            e: env.cof[t1],
            en: None,
            typ,
            cflag: None,
            park: None,
        };
        dec::push(c, &io, h, cfg);
    }
    c.release_clean(typ);
}

/// Reverse: re-create the letter of tick `t1` (exact inverse of [`dispose_fwd`]).
#[allow(clippy::too_many_arguments)]
fn dispose_rev(
    c: &mut Builder,
    p: &WalkParams,
    env: &Envelope,
    t1: usize,
    cof: &Cof,
    h: &mut Hreg,
    odo: &[Q],
) -> Q {
    h.shrink_to(c, env.h[t1]);
    let typ = c.alloc_qubit();
    if t1 == 0 {
        dec::first_tick(c, &cof.s, typ, None);
    } else if env.cof[t1] == CLAMP {
        let zt = ParkTest::compute(c, &cof.r, p.park_j);
        c.x(zt.z);
        let cfg = dec_cfg(c, p, env.cof[t1], true);
        let io = TickIo {
            s: &cof.s,
            r: &cof.r,
            e: env.cof[t1],
            en: Some(zt.z),
            typ,
            cflag: None,
            park: None,
        };
        dec::pop(c, &io, h, cfg);
        c.x(zt.z);
        odo_rev(c, zt.z, typ, odo_view(p, cof, odo), p.cap);
        ghost_odo_prime_xor(c, p, cof, zt.z, typ);
        zt.uncompute(c);
    } else {
        let cfg = dec_cfg(c, p, env.cof[t1], false);
        let io = TickIo {
            s: &cof.s,
            r: &cof.r,
            e: env.cof[t1],
            en: None,
            typ,
            cflag: None,
            park: None,
        };
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

fn snap(
    c: &mut Builder,
    tag: String,
    rails: &Rails,
    cof: &Cof,
    h: &Hreg,
    odo: &[Q],
    typ: Option<Q>,
) {
    SNAPS.with(|s| {
        if let Some(v) = s.borrow_mut().as_mut() {
            let ops = c.take_ops();
            v.push((
                tag,
                ops,
                vec![
                    rails.r1.clone(),
                    rails.r2.clone(),
                    cof.s.clone(),
                    cof.r.clone(),
                    h.wires.clone(),
                    odo.to_vec(),
                    typ.into_iter().collect(),
                ],
            ));
        }
    });
}

fn trace_step(c: &mut Builder, what: &str) {
    if super::pointadd::knob_flag("SKYCOF_STEP_TRACE") {
        let pk = c.take_win_peak();
        eprintln!("SKYCOF_STEP {what} live={} peak={pk}", c.active_qubits());
    }
}

/// Research-only per-component expected-Toffoli delta. This observes the
/// phase-report counters and therefore cannot alter the emitted operation
/// stream.
fn trace_cost(c: &Builder, dir: &str, t: usize, what: &str, before: f64) {
    if super::pointadd::knob_flag("SKYCOF_PART_COST_TRACE") {
        let after = c.report_totals().map_or(before, |x| x.1);
        eprintln!("SKYCOF_PART_COST {dir} {t} {what} {:.3}", after - before);
    }
}

/// Phase label hook: per-tick trace under `SKYCOF_TICK_TRACE` (research).
fn trace_tick(c: &mut Builder, dir: &str, t: usize) {
    if super::pointadd::knob_flag("SKYCOF_TICK_TRACE") {
        let pk = c.take_win_peak();
        eprintln!(
            "SKYCOF_TICK {dir} {t} live={} peak={pk} ops={}",
            c.active_qubits(),
            c.op_count()
        );
    }
}

// ─── the walk ───────────────────────────────────────────────────────────────────────────────────

/// Live state at a public forward cut.  This is the integration seam for a
/// packed tail: every quantum owner needed by the exact reverse is explicit,
/// while the caller-owned numerator remains outside this object and live.
pub struct ActiveWalk {
    pub rails: Rails,
    pub cof: Cof,
    pub h: Hreg,
    pub odo: Vec<Q>,
    pub typ: Option<Q>,
    pub next_t: usize,
    pub(crate) prev: Vec<PrevWidths>,
    pub(crate) tops: Vec<TopFate>,
}

impl ActiveWalk {
    /// Persistent GCD state at the cut, excluding caller-owned passengers.
    pub fn live_width(&self) -> usize {
        self.rails.r1.len()
            + self.rails.r2.len()
            + self.cof.s.len()
            + self.cof.r.len()
            + self.h.wires.len()
            + self.odo.len()
            + usize::from(self.typ.is_some())
    }
}

fn forward_ticks(c: &mut Builder, p: &WalkParams, env: &Envelope, st: &mut ActiveWalk, end: usize) {
    assert!(st.next_t <= end && end <= p.r);
    for t in st.next_t..end {
        let w = env.widths(t);
        st.prev.push(PrevWidths {
            r1: st.rails.r1.len(),
            r2: st.rails.r2.len(),
            cof: st.cof.s.len(),
        });
        trace_step(c, "tick-start");
        let t0 = c.report_totals().map_or(0.0, |x| x.1);
        let (typ_t, isc, _) = tick::rail_fwd(c, &mut st.rails, st.typ, w.wsw, w.wad, Some(p.cap));
        trace_cost(c, "fwd", t, "rail", t0);
        trace_step(c, "rail");
        let t0 = c.report_totals().map_or(0.0, |x| x.1);
        if let Some(tp) = st.typ {
            dispose_fwd(c, p, env, t - 1, tp, &st.cof, &mut st.h, &st.odo);
        }
        trace_cost(c, "fwd", t, "decoder", t0);
        trace_step(c, "dispose");
        let t0 = c.report_totals().map_or(0.0, |x| x.1);
        tick::cof_fwd(c, &mut st.cof, typ_t, isc, &w, Some(p.cap));
        trace_cost(c, "fwd", t, "cofactor", t0);
        trace_step(c, "cof");
        let t0 = c.report_totals().map_or(0.0, |x| x.1);
        tick::erase_isc(c, &st.cof, typ_t, isc);
        let fate = if st.cof.s.len() > st.cof.r.len() {
            fold(c, &mut st.cof, p);
            TopFate::Folded
        } else {
            TopFate::None
        };
        trace_cost(c, "fwd", t, "erase_fold", t0);
        st.tops.push(fate);
        st.typ = Some(typ_t);
        st.next_t = t + 1;
        trace_tick(c, "fwd", t);
        snap(
            c,
            format!("F{t}"),
            &st.rails,
            &st.cof,
            &st.h,
            &st.odo,
            st.typ,
        );
    }
}

/// Execute the exact public-layout prefix and stop at `cut` before tick
/// `cut`.  No caller-owned passenger is allocated or released here.
pub fn forward_to(
    c: &mut Builder,
    p: &WalkParams,
    env: &Envelope,
    d: &[Q],
    cut: usize,
) -> ActiveWalk {
    assert!(cut <= p.r);
    check_ghost_odo(p, env);
    let rails = seed(c, d, p.cap);
    let cof = Cof {
        s: c.alloc_qubits(2),
        r: c.alloc_qubits(2),
    };
    c.x(cof.r[0]);
    let mut st = ActiveWalk {
        rails,
        cof,
        h: Hreg::new(),
        odo: c.alloc_qubits(if ghost_odo() { 0 } else { p.odo_bits }),
        typ: None,
        next_t: 0,
        prev: Vec::with_capacity(p.r),
        tops: Vec::with_capacity(p.r),
    };
    forward_ticks(c, p, env, &mut st, cut);
    st
}

/// Resume an [`ActiveWalk`] through the endpoint using the original layout.
/// A packed backend will implement the same input/output contract.
pub fn forward_from(c: &mut Builder, p: &WalkParams, env: &Envelope, mut st: ActiveWalk) -> Parked {
    let r = p.r;
    forward_ticks(c, p, env, &mut st, r);
    let ActiveWalk {
        rails,
        cof,
        mut h,
        mut odo,
        typ,
        prev,
        tops,
        ..
    } = st;
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
    if ghost_odo() {
        assert!(odo.is_empty());
        odo = cof.r[GHOST_ODO_START..GHOST_ODO_START + p.odo_bits].to_vec();
    }
    for i in 0..N {
        if ghost_odo() && (GHOST_ODO_START..GHOST_ODO_START + p.odo_bits).contains(&i) {
            // These owners contain the endpoint counter, not prime padding.
            continue;
        }
        if pv.bit(i) {
            c.x(cof.r[i]);
        }
        if ghost_odo() {
            c.free(cof.r[i]);
        }
    }
    if !ghost_odo() {
        c.free_vec(&cof.r);
    }
    Parked {
        s: cof.s,
        h,
        odo,
        prev,
        tops,
    }
}

/// Forward walk on `d` (its wires become R2). Returns the parked state.
pub fn forward(c: &mut Builder, p: &WalkParams, env: &Envelope, d: &[Q]) -> Parked {
    let st = forward_to(c, p, env, d, 0);
    forward_from(c, p, env, st)
}

/// Exact inverse of [`forward_to`].  This is the integration counterpart of a
/// packed suffix seam: after that suffix is undone, the public prefix can be
/// reversed directly without constructing the parked endpoint.
pub fn backward_from_active(
    c: &mut Builder,
    p: &WalkParams,
    env: &Envelope,
    st: ActiveWalk,
) -> Vec<Q> {
    let ActiveWalk {
        mut rails,
        mut cof,
        mut h,
        odo,
        typ,
        next_t,
        prev,
        tops,
    } = st;
    assert!(next_t > 0 && next_t <= p.r);
    assert_eq!(prev.len(), next_t);
    assert_eq!(tops.len(), next_t);
    let mut typ = typ.expect("nonempty prefix has a current type bit");
    for t in (0..next_t).rev() {
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
        let tprev = if t >= 1 {
            Some(dispose_rev(c, p, env, t - 1, &cof, &mut h, &odo))
        } else {
            None
        };
        tick::rail_rev(
            c,
            &mut rails,
            typ,
            isc,
            tprev,
            w.wsw,
            (prev[t].r1, prev[t].r2),
            Some(p.cap),
        );
        if let Some(tq) = tprev {
            typ = tq;
        }
    }
    assert_eq!(cof.s.len(), 2);
    c.x(cof.r[0]);
    c.free_vec(&cof.s);
    c.free_vec(&cof.r);
    h.shrink_to(c, 0);
    c.free_vec(&odo);
    unseed(c, rails, p.cap)
}

/// Exact walk back from [`forward`]'s parked state; returns the wires holding `d`.
pub fn backward(c: &mut Builder, p: &WalkParams, env: &Envelope, pk: Parked) -> Vec<Q> {
    let r = p.r;
    let Parked {
        s,
        mut h,
        mut odo,
        prev,
        tops,
    } = pk;
    let wl = env.rail[r - 1];
    let mut rails = Rails {
        r1: c.alloc_qubits(wl),
        r2: c.alloc_qubits(wl),
    };
    c.x(rails.r2[0]);
    let rr = if ghost_odo() {
        assert_eq!(odo.len(), p.odo_bits);
        (0..N).map(|i| {
            if (GHOST_ODO_START..GHOST_ODO_START + p.odo_bits).contains(&i) {
                odo[i - GHOST_ODO_START]
            } else {
                c.alloc_qubit()
            }
        }).collect::<Vec<_>>()
    } else {
        c.alloc_qubits(N)
    };
    let pv = crate::point_add::SECP256K1_P;
    for i in 0..N {
        if pv.bit(i) && !(ghost_odo() && (GHOST_ODO_START..GHOST_ODO_START + p.odo_bits).contains(&i)) {
            c.x(rr[i]);
        }
    }
    if ghost_odo() {
        // Ownership has returned to R. Do not free these aliased IDs twice.
        odo.clear();
    }
    let mut cof = Cof { s, r: rr };
    let mut typ = dispose_rev(c, p, env, r - 1, &cof, &mut h, &odo);
    for t in (0..r).rev() {
        let w = env.widths(t);
        let t0 = c.report_totals().map_or(0.0, |x| x.1);
        match tops[t] {
            TopFate::Folded => unfold(c, &mut cof, p),
            TopFate::Freed => {
                let q = c.alloc_qubit();
                cof.s.push(q);
            }
            TopFate::None => {}
        }
        trace_cost(c, "rev", t, "unfold", t0);
        let t0 = c.report_totals().map_or(0.0, |x| x.1);
        let isc = tick::isc_recompute(c, &cof, typ);
        tick::cof_rev(c, &mut cof, typ, isc, prev[t].cof, Some(p.cap));
        trace_cost(c, "rev", t, "cofactor", t0);
        let t0 = c.report_totals().map_or(0.0, |x| x.1);
        let tprev = if t >= 1 {
            Some(dispose_rev(c, p, env, t - 1, &cof, &mut h, &odo))
        } else {
            None
        };
        trace_cost(c, "rev", t, "decoder", t0);
        let t0 = c.report_totals().map_or(0.0, |x| x.1);
        tick::rail_rev(
            c,
            &mut rails,
            typ,
            isc,
            tprev,
            w.wsw,
            (prev[t].r1, prev[t].r2),
            Some(p.cap),
        );
        trace_cost(c, "rev", t, "rail", t0);
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
    unseed(c, rails, p.cap)
}
