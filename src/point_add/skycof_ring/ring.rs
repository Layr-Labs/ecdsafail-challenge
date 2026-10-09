//! SKY-COF masked ring: Kaliski rails and integer cofactors sharing two registers (research code).
//!
//! # Layout (register width `N`, `N = 257` for secp256k1)
//! * `A = [u | s]`: value `u` at logical positions `0..` (LSB first); cofactor `s` stored reversed,
//!   cofactor index `j` at position `N-1-j`. `B = [v | r]` the same way.
//! * Theorem (`u s + v r = p`, all positive): `bits(u) + bits(s) <= N`, `bits(v) + bits(r) <= N`, so the
//!   fields never collide. Cross pairs (`u` vs `r`, `v` vs `s`) can overlap (measured up to 284/285).
//! * Boundary registers (canonical, `KB = bitlen(N)` bits each):
//!   - `KA = bits(s)` for `A` (cofactor side: `s` doubles every tick, so the boundary moves by exactly
//!     one position per tick and needs no arithmetic);
//!   - `VB = bits(v)` for `B` (value side: `v` is untouched by the B step, so `r += s` needs no
//!     boundary update; the cofactor-side `bits(r)` is NOT invertible from boundary registers after
//!     `r += s` -- `max(bits r, bits s) + carry` forgets `bits(r)` whenever `bits(r) < bits(s)`).
//!   Both are functions of the register contents, so the reverse tick recomputes them.
//!
//! # Forward tick (pre-park entry, `u >= 1`), Kaliski in swap-first form (C = swap, then B)
//! 0. `c = u[0]` (fresh copy; the letter bit `c = [B or C]`, live output of the tick).
//! 1. conversion 1: `UA = bits(u)` (transient, `ua_width` bits), `KA -> 0`. One gap-indicator chain
//!    (`lod::convert`) when the room allows, else two chunked leading-one deposits (`lod_deposit`):
//!    `UA ^= bits(u)` below the cut `N - KA`, then `KA ^= bits(s)` below the cut `N - UA`.
//! 2. `isC = c AND [u < v]`: `[u < v] = [UA < VB] OR ([UA == VB] AND [u mod 2^VB < v mod 2^VB])`
//!    (two small compares give `<` and `==`; one value-cell borrow cascade captured at the leaf `VB`).
//! 3. controlled on `isC`: swap `A <-> B` (N Fredkins) and `UA <-> VB` (`ua_width` Fredkins).
//! 4. conversion 2: `KA = post(bits(s'))`, `post(b) = b + [b > 0] = bits(2 s')`, `UA -> 0` (same two
//!    forms). `KA` is in post convention from here to the end of the tick.
//! 5. cofactor update `r' += c * s'` (masked Cuccaro, op1 + op2):
//!    op1 `B_cof[0..N-VB) += A_cof[0..N-VB)` (mod 2^(N-VB); `A`'s value bits that intrude below the cut
//!    are added too); op2 `B_cof[bits(s')..N-VB) -= A_cof[bits(s')..N-VB)` in the two-flag form (removes
//!    exactly the intruding value bits; an empty region when `bits(s') > N - VB`).
//! 6. rail update `u' -= c * v'` (masked Cuccaro, op1 + op2):
//!    op1 `A_val[0..E) -= B_val[0..E)`, `E = N - bits(s')`; op2 `A_val[VB..E) += B_val[VB..E)` (adds back
//!    the cofactor bits of `B` that intrude below `E`). Exact: `0 <= u' - v' < 2^E`.
//! 7. halve `u` / double `s`: rotate `A` by one position (relabel, 0 gates).
//! `isC` ends equal to cofactor bit 1 of the new `s` (`isC = s'[0]`), so [`isc_erase`] / [`isc_recompute`]
//! are single CNOTs.
//!
//! # Reverse tick: the exact inverse, step by step (consumes `c` and `isC`).
//!
//! # Windows and room
//! Every step takes the per-tick support of the boundary values ([`TickZ`]): cells that every
//! supported value leaves active are plain, cells beyond every cut are skipped, the rest are masked.
//! `Ring::cap` (absolute live-wire cap) bounds the conversion chains (merged form only when the whole
//! chain fits; chunked deposits otherwise). The masked adds and the compare have fixed scratch
//! (carry, flags, temp, engines).
use super::engine::{and_clear, and_into, Lit};
use super::lod::{convert_gated, lod_deposit, Room};
use super::mc::{cmp_capture, cmp_phase, mc_add, mc_add_ex, McShape, Thr};
use crate::circuit::QubitId as Q;
use crate::point_add::builder::Builder;

/// Inclusive range of a boundary value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rng {
    pub lo: usize,
    pub hi: usize,
}

impl Rng {
    pub fn new(lo: usize, hi: usize) -> Rng {
        assert!(lo <= hi);
        Rng { lo, hi }
    }
    pub fn vals(&self) -> std::ops::RangeInclusive<usize> {
        self.lo..=self.hi
    }
}

/// Per-tick support of the boundary values (bit lengths).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TickZ {
    /// bits(s), bits(u), bits(v) at entry
    pub ka: Rng,
    pub ua: Rng,
    pub vb: Rng,
    /// bits(s'), bits(u'), bits(v') after the swap
    pub kap: Rng,
    pub uap: Rng,
    pub vbp: Rng,
}

/// Ring state: the two shared registers (logical position order) and the boundary registers.
pub struct Ring {
    pub n: usize,
    /// live-wire cap for the room-aware steps (the leading-one chains); None = unbounded
    pub cap: Option<usize>,
    pub a: Vec<Q>,
    pub b: Vec<Q>,
    pub ka: Vec<Q>,
    pub vb: Vec<Q>,
    /// Optional gate of the two boundary conversions (walk integration: `NOT parked`). With the gate at 0
    /// the conversions leave `KA` and the transient `UA` untouched; every other step of a tick from a
    /// parked state (`u = 0`, so `c = 0`) is the identity, so the tick reduces to the rotation.
    pub gate: Option<Q>,
}

/// Boundary register width for registers of `n` wires.
pub fn kbits(n: usize) -> usize {
    (usize::BITS - n.leading_zeros()) as usize
}

pub fn post(b: usize) -> usize {
    b + usize::from(b > 0)
}

impl Ring {
    pub fn aval(&self) -> Vec<Q> {
        self.a.clone()
    }
    pub fn acof(&self) -> Vec<Q> {
        self.a.iter().rev().copied().collect()
    }
    pub fn bval(&self) -> Vec<Q> {
        self.b.clone()
    }
    pub fn bcof(&self) -> Vec<Q> {
        self.b.iter().rev().copied().collect()
    }
}

/// Per-step Toffoli/shape record (filled by the forward / reverse tick for reports).
#[derive(Clone, Debug, Default)]
pub struct StepLog {
    pub marks: Vec<(&'static str, usize)>,
    /// live-wire peak inside each step (absolute; the caller subtracts its entry count)
    pub peaks: Vec<(&'static str, usize)>,
    pub cof: [McShape; 2],
    pub rail: [McShape; 2],
    pub lod_cells: [usize; 4],
}

fn fredkin(c: &mut Builder, ctl: Q, a: Q, b: Q) {
    c.cx(b, a);
    c.ccx(ctl, a, b);
    c.cx(b, a);
}

fn thr_ka_rest<'a>(r: &'a Ring, z: &TickZ) -> Thr<'a> {
    Thr { reg: &r.ka, pairs: z.ka.vals().map(|b| (b, r.n - b)).collect() }
}
fn thr_ka_post<'a>(r: &'a Ring, z: &TickZ) -> Thr<'a> {
    Thr { reg: &r.ka, pairs: z.kap.vals().map(|b| (post(b), r.n - b)).collect() }
}
fn thr_ua_cof<'a>(ua: &'a [Q], n: usize, rg: Rng) -> Thr<'a> {
    Thr { reg: ua, pairs: rg.vals().map(|b| (b, n - b)).collect() }
}

/// Step 2: `isc ^= c AND [u < v]` (self-inverse given the same `UA`, `VB`, `A`, `B`).
/// `[u < v] = [UA < VB] OR ([UA == VB] AND [u mod 2^VB < v mod 2^VB])`; `[UA == VB]` comes from the two
/// 9-bit compares (`NOT lt AND NOT gt`), so no equality ladder is needed.
pub fn compare(cb: &mut Builder, r: &Ring, ua: &[Q], c: Q, isc: Q, z: &TickZ) {
    let w = ua.len();
    let vbw = &r.vb[..w];
    let lt = cb.alloc_qubit();
    cmp_capture(cb, ua, vbw, lt, None, None);
    let gt = cb.alloc_qubit();
    cmp_capture(cb, vbw, ua, gt, None, None);
    let lits = [Lit { q: c, pol: true }, Lit { q: lt, pol: false }, Lit { q: gt, pol: false }];
    let g = and_into(cb, &lits).unwrap();
    let nc = z.vb.hi.min(r.n);
    let th = Thr { reg: &r.vb, pairs: z.vb.vals().map(|b| (b, b)).collect() };
    cmp_capture(cb, &r.a[..nc], &r.b[..nc], isc, Some(&th), Some(g));
    cb.ccx(c, lt, isc);
    and_clear(cb, &lits, Some(g));
    for (q, a, b) in [(gt, vbw, ua), (lt, ua, vbw)] {
        let m = cb.alloc_bit();
        cb.hmr(q, m);
        cmp_phase(cb, a, b, m);
        cb.free_bit(m);
        cb.release_clean(q);
    }
}

/// Step 3: controlled swap of the registers and of `UA <-> VB`.
pub fn swap(cb: &mut Builder, r: &Ring, ua: &[Q], isc: Q) {
    for i in 0..r.n {
        fredkin(cb, isc, r.a[i], r.b[i]);
    }
    for j in 0..ua.len() {
        fredkin(cb, isc, ua[j], r.vb[j]);
    }
    // VB's bits above UA's width are zero on the support (both bit lengths < 2^width)
}

/// Step 4 (forward when `inverse = false`): `r' += c * s'` on the cofactor fields (KA in post convention).
/// op1 `B_cof[0..N-VB) += A_cof[0..N-VB)`; op2 `B_cof[bits(s')..N-VB) -= A_cof[bits(s')..N-VB)` in the
/// two-flag form (the region is empty when `bits(s') > N - VB`, i.e. when nothing of `u'` intrudes).
pub fn cof_update(cb: &mut Builder, r: &Ring, c: Q, z: &TickZ, inverse: bool, log: &mut StepLog) {
    let (t, o) = (r.bcof(), r.acof());
    let up = Thr { reg: &r.vb, pairs: z.vbp.vals().map(|b| (b, r.n - b)).collect() };
    let lowt = Thr { reg: &r.ka, pairs: z.kap.vals().map(|b| (post(b), b)).collect() };
    if !inverse {
        log.cof[0] = mc_add(cb, &t, &o, Some(c), false, Some(&up), None);
        log.cof[1] = mc_add_ex(cb, &t, &o, Some(c), true, Some(&up), Some(&lowt), true);
    } else {
        log.cof[1] = mc_add_ex(cb, &t, &o, Some(c), false, Some(&up), Some(&lowt), true);
        log.cof[0] = mc_add(cb, &t, &o, Some(c), true, Some(&up), None);
    }
}

/// Step 5 (forward when `inverse = false`): `u' -= c * v'` on the value fields.
pub fn rail_update(cb: &mut Builder, r: &Ring, c: Q, z: &TickZ, inverse: bool, log: &mut StepLog) {
    let (t, o) = (r.aval(), r.bval());
    let up = thr_ka_post(r, z);
    let lowt = Thr { reg: &r.vb, pairs: z.vbp.vals().map(|b| (b, b)).collect() };
    if !inverse {
        log.rail[0] = mc_add(cb, &t, &o, Some(c), true, Some(&up), None);
        log.rail[1] = mc_add(cb, &t, &o, Some(c), false, Some(&up), Some(&lowt));
    } else {
        log.rail[1] = mc_add(cb, &t, &o, Some(c), true, Some(&up), Some(&lowt));
        log.rail[0] = mc_add(cb, &t, &o, Some(c), false, Some(&up), None);
    }
}

/// Step 1a / 3b(inverse) deposit: `UA ^= bits(u)` with `KA` in rest convention (`post = false`) or
/// post convention (`post = true`).
pub fn dep_ua(cb: &mut Builder, r: &Ring, ua: &[Q], z: &TickZ, post_conv: bool) -> usize {
    let x = r.aval();
    if post_conv {
        lod_deposit(cb, &x, &thr_ka_post(r, z), z.uap.lo, ua, &|b| b, r.gate, room(r))
    } else {
        lod_deposit(cb, &x, &thr_ka_rest(r, z), z.ua.lo, ua, &|b| b, r.gate, room(r))
    }
}

/// Step 1b / 3a deposit: `KA ^= bits(s)` (`post = false`, entry zones) or `KA ^= post(bits(s'))`
/// (`post = true`, post-swap zones).
pub fn dep_ka(cb: &mut Builder, r: &Ring, ua: &[Q], z: &TickZ, post_conv: bool) -> usize {
    let x = r.acof();
    if post_conv {
        lod_deposit(cb, &x, &thr_ua_cof(ua, r.n, z.uap), z.kap.lo, &r.ka, &post, r.gate, room(r))
    } else {
        lod_deposit(cb, &x, &thr_ua_cof(ua, r.n, z.ua), z.ka.lo, &r.ka, &|b| b, r.gate, room(r))
    }
}

fn room(r: &Ring) -> Room {
    r.cap.map_or(Room::Unbounded, Room::Cap)
}

fn mark(cb: &mut Builder, log: &mut StepLog, name: &'static str) {
    log.marks.push((name, cb.op_count()));
    let pk = cb.take_win_peak() as usize;
    log.peaks.push((name, pk));
}

/// Width of the transient `UA` register at this tick: enough for every supported `bits(u)`, `bits(v)`
/// (before and after the swap), so `UA <-> VB` only exchanges VB's low bits.
pub fn ua_width(r: &Ring, z: &TickZ) -> usize {
    let hi = z.ua.hi.max(z.uap.hi).max(z.vb.hi).max(z.vbp.hi);
    kbits(hi).max(1).min(r.ka.len())
}

/// Merged (one-chain) conversions when the room allows; `SKYCOF_RING_CONVERT` = `merged` / `split` /
/// `auto` (default).
fn use_merged(cb: &Builder, r: &Ring, chain: usize) -> bool {
    static MODE: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    let mode = MODE.get_or_init(|| std::env::var("SKYCOF_RING_CONVERT").unwrap_or_else(|_| "auto".into()));
    match mode.as_str() {
        "merged" => true,
        "split" => false,
        _ => r.cap.is_none_or(|k| k >= cb.active_qubits() as usize + chain + 10),
    }
}

/// Conversion 1 (`KA = bits(s)` -> `UA = bits(u)`, KA -> 0) or its inverse (`inverse = true`).
fn conv1(cb: &mut Builder, r: &Ring, ua: &[Q], z: &TickZ, inverse: bool, log: &mut StepLog) {
    let x = r.aval();
    let top = thr_ka_rest(r, z);
    let bot = Thr { reg: ua, pairs: z.ua.vals().map(|b| (b, b)).collect() };
    let chain = top.range().1.saturating_sub(z.ua.lo);
    let n = r.n;
    if use_merged(cb, r, chain) {
        log.lod_cells[0] = convert_gated(cb, &x, &top, &bot, !inverse, &|e| n - e, &|b| b, r.gate);
        log.lod_cells[1] = 0;
    } else if !inverse {
        log.lod_cells[0] = dep_ua(cb, r, ua, z, false);
        log.lod_cells[1] = dep_ka(cb, r, ua, z, false);
    } else {
        log.lod_cells[1] = dep_ka(cb, r, ua, z, false);
        log.lod_cells[0] = dep_ua(cb, r, ua, z, false);
    }
}

/// Conversion 2 (`UA = bits(u')` -> `KA = post(bits(s'))`, UA -> 0) or its inverse.
fn conv2(cb: &mut Builder, r: &Ring, ua: &[Q], z: &TickZ, inverse: bool, log: &mut StepLog) {
    let x = r.aval();
    let top = thr_ka_post(r, z);
    let bot = Thr { reg: ua, pairs: z.uap.vals().map(|b| (b, b)).collect() };
    let chain = top.range().1.saturating_sub(z.uap.lo);
    let n = r.n;
    if use_merged(cb, r, chain) {
        log.lod_cells[2] = convert_gated(cb, &x, &top, &bot, inverse, &|e| post(n - e), &|b| b, r.gate);
        log.lod_cells[3] = 0;
    } else if !inverse {
        log.lod_cells[2] = dep_ka(cb, r, ua, z, true);
        log.lod_cells[3] = dep_ua(cb, r, ua, z, true);
    } else {
        log.lod_cells[3] = dep_ua(cb, r, ua, z, true);
        log.lod_cells[2] = dep_ka(cb, r, ua, z, true);
    }
}

/// Forward tick (module doc). Returns `(c, isC)`, both live.
pub fn tick_fwd(cb: &mut Builder, r: &mut Ring, z: &TickZ, log: &mut StepLog) -> (Q, Q) {
    mark(cb, log, "start");
    let c = cb.alloc_qubit();
    cb.cx(r.a[0], c);
    let ua = cb.alloc_qubits(ua_width(r, z));
    conv1(cb, r, &ua, z, false, log);
    mark(cb, log, "conv1");
    let isc = cb.alloc_qubit();
    compare(cb, r, &ua, c, isc, z);
    mark(cb, log, "cmp");
    swap(cb, r, &ua, isc);
    mark(cb, log, "swap");
    conv2(cb, r, &ua, z, false, log);
    for &q in &ua {
        cb.free(q);
    }
    mark(cb, log, "conv2");
    cof_update(cb, r, c, z, false, log);
    mark(cb, log, "cof");
    rail_update(cb, r, c, z, false, log);
    mark(cb, log, "rail");
    r.a.rotate_left(1);
    (c, isc)
}

/// `isC` equals cofactor bit 1 of `A` after the tick: clear it (0 Toffoli).
pub fn isc_erase(cb: &mut Builder, r: &Ring, isc: Q) {
    cb.cx(r.a[r.n - 2], isc);
    cb.free(isc);
}

/// Recompute `isC` from a post-tick state (0 Toffoli).
pub fn isc_recompute(cb: &mut Builder, r: &Ring) -> Q {
    let isc = cb.alloc_qubit();
    cb.cx(r.a[r.n - 2], isc);
    isc
}

/// Exact inverse of [`tick_fwd`]: consumes `c` and `isc`.
pub fn tick_rev(cb: &mut Builder, r: &mut Ring, z: &TickZ, c: Q, isc: Q, log: &mut StepLog) {
    mark(cb, log, "start");
    r.a.rotate_right(1);
    rail_update(cb, r, c, z, true, log);
    mark(cb, log, "rail");
    cof_update(cb, r, c, z, true, log);
    mark(cb, log, "cof");
    let ua = cb.alloc_qubits(ua_width(r, z));
    conv2(cb, r, &ua, z, true, log);
    mark(cb, log, "conv2");
    swap(cb, r, &ua, isc);
    mark(cb, log, "swap");
    compare(cb, r, &ua, c, isc, z);
    cb.free(isc);
    mark(cb, log, "cmp");
    conv1(cb, r, &ua, z, true, log);
    for &q in &ua {
        cb.free(q);
    }
    mark(cb, log, "conv1");
    cb.cx(r.a[0], c);
    cb.free(c);
}
