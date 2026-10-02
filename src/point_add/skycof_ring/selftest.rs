//! Gate-level selftests of the SKY-COF masked ring: `SKYCOF_RING_SELFTEST=1 build_circuit`
//! (`=cost` runs only the cost report, `=unit` only the primitive tests). Knobs: `SKYCOF_RING_KMAX`
//! (largest small modulus bit length, register width `K+1`, default 8), `SKYCOF_RING_TRAIN` (training
//! walks for the full-width windows, default 20000), `SKYCOF_RING_HELD` (held-out walks for the window
//! exceedance, default 20000), `SKYCOF_RING_MARGIN` (window margin, default 2), `SKYCOF_RING_FULL`
//! (64-walk batches per tick at full width, default 2), `SKYCOF_RING_CHAIN` (ticks of the chained
//! full-width walk, default 400), `SKYCOF_RING_COST_TSV` (per-tick cost table path).
//!
//! 1. engine: every window of 1..5-bit registers (5-bit subsampled), gated / ungated, ascending,
//!    descending and jumping orders, every register value: leaf = gate AND [reg == v].
//! 2. masked add / subtract: n <= 5 cells, every target, operand, lower cut, upper cut (L <= E),
//!    control, both cut maps (increasing / decreasing in the register value), full and inner zones.
//! 3. capture compare: n <= 5, every a, b, cut, gate; and the fixed cut.
//! 4. leading-one deposit: n <= 6 cells, every x, cut, scan floor, gate, two deposit maps.
//! 5. tick, small registers: every reachable pre-park Kaliski state for every odd modulus P with
//!    K bits (K = 4..KMAX, register width K+1), every d in [1, P): one forward tick against the classical
//!    step (registers, boundaries, letter bit, isC), then the reverse tick back; loose windows (every
//!    boundary value 0..N allowed, every cell masked) and tight per-tick windows.
//! 6. tick, full width (N = 257, secp256k1 p): random walks, every tick, windows from training walks.
//! 7. chained full-width walk: 64 walks forward tick by tick and back with live letter bits.
//! 8. cost per call at the design's windows (expected Toffoli, measured scratch above the ring).
//! Every gate-level check: values exact, zero phase, no dirty release, every non-register wire zero.
use super::engine::Engine;
use super::lod::{lod_deposit, Room};
use super::mc::{cmp_capture, mc_add_ex, Thr};
use super::ring::*;
use crate::circuit::{Op, OperationType as K, QubitId as Q, NO_BIT};
use crate::point_add::builder::Builder;
use ruint::Uint;

type U = Uint<512, 8>;

fn env_usize(k: &str, d: usize) -> usize {
    std::env::var(k).ok().and_then(|v| v.trim().parse().ok()).unwrap_or(d)
}

// ─── simulator (bitsliced, 64 lanes; dirty-release detection) ─────────────────

pub(crate) struct Sim {
    q: Vec<u64>,
    b: Vec<u64>,
    pub(crate) phase: u64,
    pub(crate) dirty: u64,
    rng: u64,
}

impl Sim {
    pub(crate) fn new(nq: usize, nb: usize, seed: u64) -> Self {
        Sim { q: vec![0; nq], b: vec![0; nb.max(1)], phase: 0, dirty: 0, rng: seed ^ 0x5EED_5C0F }
    }
    fn next(&mut self) -> u64 {
        self.rng = self.rng.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.rng;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn clear(&mut self) {
        self.q.iter_mut().for_each(|x| *x = 0);
        self.b.iter_mut().for_each(|x| *x = 0);
        self.phase = 0;
        self.dirty = 0;
    }
    pub(crate) fn run(&mut self, ops: &[Op]) {
        let mut stack: Vec<u64> = Vec::new();
        let mut base = u64::MAX;
        for o in ops {
            let mut co = base;
            if o.c_condition != NO_BIT && o.kind != K::PushCondition {
                co &= self.b[o.c_condition.0 as usize];
            }
            let t = o.q_target.0 as usize;
            match o.kind {
                K::X => self.q[t] ^= co,
                K::CX => self.q[t] ^= co & self.q[o.q_control1.0 as usize],
                K::CCX => {
                    let v = co & self.q[o.q_control1.0 as usize] & self.q[o.q_control2.0 as usize];
                    self.q[t] ^= v;
                }
                K::Z => self.phase ^= co & self.q[t],
                K::CZ => self.phase ^= co & self.q[t] & self.q[o.q_control1.0 as usize],
                K::CCZ => {
                    self.phase ^= co & self.q[t] & self.q[o.q_control1.0 as usize] & self.q[o.q_control2.0 as usize];
                }
                K::Swap => {
                    let a = o.q_control1.0 as usize;
                    let d = (self.q[a] ^ self.q[t]) & co;
                    self.q[a] ^= d;
                    self.q[t] ^= d;
                }
                K::Neg => self.phase ^= co,
                K::Hmr => {
                    let r = self.next();
                    let ct = o.c_target.0 as usize;
                    self.b[ct] = (self.b[ct] & !co) | (r & co);
                    self.phase ^= self.q[t] & r & co;
                    self.q[t] &= !co;
                }
                K::R => {
                    self.dirty |= co & self.q[t];
                    self.q[t] &= !co;
                }
                K::BitInvert => self.b[o.c_target.0 as usize] ^= co,
                K::BitStore0 => self.b[o.c_target.0 as usize] &= !co,
                K::BitStore1 => self.b[o.c_target.0 as usize] |= co,
                K::PushCondition => {
                    stack.push(base);
                    base &= self.b[o.c_condition.0 as usize];
                }
                K::PopCondition => base = stack.pop().expect("condition stack underflow"),
                K::Register | K::AppendToRegister | K::DebugPrint => {}
            }
        }
        assert!(stack.is_empty(), "unbalanced conditions");
    }
    pub(crate) fn set(&mut self, reg: &[Q], v: U, lane: usize) {
        for (i, w) in reg.iter().enumerate() {
            let q = &mut self.q[w.0 as usize];
            if v.bit(i) { *q |= 1 << lane } else { *q &= !(1 << lane) }
        }
    }
    pub(crate) fn setu(&mut self, reg: &[Q], v: usize, lane: usize) {
        self.set(reg, U::from(v as u64), lane)
    }
    pub(crate) fn get(&self, reg: &[Q], lane: usize) -> U {
        let mut v = U::ZERO;
        for (i, w) in reg.iter().enumerate() {
            if (self.q[w.0 as usize] >> lane) & 1 == 1 {
                v.set_bit(i, true);
            }
        }
        v
    }
    pub(crate) fn getu(&self, reg: &[Q], lane: usize) -> usize {
        self.get(reg, lane).as_limbs()[0] as usize
    }
    /// OR over all qubits outside `keep`.
    pub(crate) fn residue(&self, keep: &[Q]) -> u64 {
        let mut m = vec![false; self.q.len()];
        for k in keep {
            m[k.0 as usize] = true;
        }
        self.q.iter().enumerate().filter(|(i, _)| !m[*i]).fold(0, |a, (_, &x)| a | x)
    }
}

fn lane_mask(n: usize) -> u64 {
    if n >= 64 { u64::MAX } else { (1u64 << n) - 1 }
}

/// Expected Toffoli: CCX/CCZ under `d` measured conditions count `2^-d`.
pub(crate) fn expected_ccx(ops: &[Op]) -> f64 {
    let mut depth = 0i32;
    let mut e = 0.0;
    for o in ops {
        match o.kind {
            K::PushCondition => depth += 1,
            K::PopCondition => depth -= 1,
            K::CCX | K::CCZ => {
                let d = depth + i32::from(o.c_condition != NO_BIT);
                e += 0.5f64.powi(d);
            }
            _ => {}
        }
    }
    e
}

fn ccx_count(ops: &[Op]) -> usize {
    ops.iter().filter(|o| matches!(o.kind, K::CCX | K::CCZ)).count()
}

/// Run `ops` on a batch: `init(sim, lane)` sets inputs, `check(sim, lane)` verifies; phase, dirty
/// and residue outside `keep` must be zero.
fn run_batch(ops: &[Op], nq: usize, nb: usize, lanes: usize, seed: u64, keep: &[Q], label: &str,
             init: &mut dyn FnMut(&mut Sim, usize), check: &mut dyn FnMut(&Sim, usize)) {
    let mut sim = Sim::new(nq, nb, seed);
    for l in 0..lanes {
        init(&mut sim, l);
    }
    sim.run(ops);
    let lm = lane_mask(lanes);
    assert_eq!(sim.phase & lm, 0, "{label}: phase {:x}", sim.phase & lm);
    assert_eq!(sim.dirty & lm, 0, "{label}: dirty release {:x}", sim.dirty & lm);
    assert_eq!(sim.residue(keep) & lm, 0, "{label}: garbage {:x}", sim.residue(keep) & lm);
    for l in 0..lanes {
        check(&sim, l);
    }
}

struct Rng64(u64);
impl Rng64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

// ─── 1. engine ───────────────────────────────────────────────────────────────

fn test_engine() {
    let mut rng = Rng64(11);
    let mut circuits = 0usize;
    let (mut tsum, mut steps) = (0usize, 0usize);
    for k in 1..=5usize {
        let max = 1usize << k;
        for lo in 0..max {
            for hi in lo..max {
                if k == 5 && (lo * 7 + hi) % 5 != 0 {
                    continue;
                }
                for gated in [false, true] {
                    for order in 0..3 {
                        let vals: Vec<usize> = match order {
                            0 => (lo..=hi).collect(),
                            1 => (lo..=hi).rev().collect(),
                            _ => (0..(hi - lo + 3)).map(|_| lo + rng.below((hi - lo + 1) as u64) as usize).collect(),
                        };
                        let mut c = Builder::new();
                        let reg = c.alloc_qubits(k);
                        let gate = gated.then(|| c.alloc_qubit());
                        let probes = c.alloc_qubits(vals.len());
                        let mut e = Engine::new(&mut c, &reg, gate, lo, hi);
                        for (i, &v) in vals.iter().enumerate() {
                            e.goto(&mut c, v);
                            match e.leaf() {
                                Some(l) => c.cx(l, probes[i]),
                                None => c.x(probes[i]),
                            }
                        }
                        e.finish(&mut c);
                        let (nq, nb) = c.i13_dims();
                        let ops = c.take_ops();
                        if order == 0 {
                            tsum += ccx_count(&ops);
                            steps += vals.len();
                        }
                        let mut keep: Vec<Q> = reg.clone();
                        keep.extend(gate);
                        keep.extend(probes.iter().copied());
                        let lanes = max * 2;
                        run_batch(&ops, nq, nb, lanes, 3, &keep, "engine", &mut |s, l| {
                            s.setu(&reg, l % max, l);
                            if let Some(g) = gate {
                                s.setu(&[g], l / max, l);
                            }
                        }, &mut |s, l| {
                            let (r, g) = (l % max, if gated { l / max } else { 1 });
                            assert_eq!(s.getu(&reg, l), r, "engine: register changed");
                            for (i, &v) in vals.iter().enumerate() {
                                let want = usize::from(g == 1 && r == v);
                                assert_eq!(s.getu(&[probes[i]], l), want, "engine k={k} [{lo},{hi}] v={v} r={r} g={g}");
                            }
                        });
                        circuits += 1;
                    }
                }
            }
        }
    }
    println!("{{\"kind\":\"skycof-ring-engine\",\"circuits\":{circuits},\"toffoli_per_ascending_step\":{:.3}}}",
             tsum as f64 / steps as f64);
}

// ─── 2. masked add / subtract ────────────────────────────────────────────────

fn mask(n: usize) -> usize {
    (1usize << n) - 1
}

fn test_mc() {
    let kb = 3usize;
    let mut runs = 0usize;
    let mut cases = 0usize;
    for n in 1..=5usize {
        for decreasing in [false, true] {
            // register value -> cut
            let cut = move |v: usize| if decreasing { n - v } else { v };
            // (upper zone, lower zone) of allowed cuts: full, inner, and staggered overlapping zones
            let mut zsets: Vec<(Vec<usize>, Vec<usize>)> = vec![((0..=n).collect(), (0..=n).collect())];
            if n >= 3 {
                zsets.push(((1..n).collect(), (1..n).collect()));
                zsets.push(((1..=n).collect(), (0..n - 1).collect()));
                zsets.push(((2..=n).collect(), (0..=2).collect()));
                zsets.push(((n - 1..=n).collect(), (0..=n - 1).collect()));
            }
            for (zi, (zone_u, zone_l)) in zsets.iter().enumerate() {
                let inner = zi;
                for thr_cfg in 0..4 {
                    // 0 upper only, 1 lower only, 2 both (one flag, L <= E), 3 both (two flags, any L, E)
                    for ctrl in [false, true] {
                        for sub in [false, true] {
                            let mut c = Builder::new();
                            let t = c.alloc_qubits(n);
                            let o = c.alloc_qubits(n);
                            let re = c.alloc_qubits(kb);
                            let rl = c.alloc_qubits(kb);
                            let g = ctrl.then(|| c.alloc_qubit());
                            let up = Thr { reg: &re, pairs: zone_u.iter().map(|&k| (cut(k), k)).collect() };
                            let lo = Thr { reg: &rl, pairs: zone_l.iter().map(|&k| (cut(k), k)).collect() };
                            let uo = (thr_cfg != 1).then_some(&up);
                            let lw = (thr_cfg != 0).then_some(&lo);
                            mc_add_ex(&mut c, &t, &o, g, sub, uo, lw, thr_cfg == 3);
                            let (nq, nb) = c.i13_dims();
                            let ops = c.take_ops();
                            let mut keep: Vec<Q> = t.iter().chain(&o).chain(&re).chain(&rl).copied().collect();
                            keep.extend(g);
                            // enumerate inputs
                            let mut inputs: Vec<(usize, usize, usize, usize, usize)> = Vec::new();
                            let ecuts: Vec<usize> = if thr_cfg != 1 { zone_u.clone() } else { vec![n] };
                            let lcuts: Vec<usize> = if thr_cfg != 0 { zone_l.clone() } else { vec![0] };
                            for &ek in &ecuts {
                                for &lk in &lcuts {
                                    if lk > ek && thr_cfg != 3 {
                                        continue;
                                    }
                                    for gv in 0..=usize::from(ctrl) {
                                        for tv in 0..=mask(n) {
                                            for ov in 0..=mask(n) {
                                                inputs.push((tv, ov, ek, lk, gv));
                                            }
                                        }
                                    }
                                }
                            }
                            for (bi, chunk) in inputs.chunks(64).enumerate() {
                                run_batch(&ops, nq, nb, chunk.len(), bi as u64, &keep, "mc", &mut |s, l| {
                                    let (tv, ov, ek, lk, gv) = chunk[l];
                                    s.setu(&t, tv, l);
                                    s.setu(&o, ov, l);
                                    s.setu(&re, cut(ek), l);
                                    s.setu(&rl, cut(lk), l);
                                    if let Some(gq) = g {
                                        s.setu(&[gq], gv, l);
                                    }
                                }, &mut |s, l| {
                                    let (tv, ov, ek, lk, gv) = chunk[l];
                                    let gv = if ctrl { gv } else { 1 };
                                    let (ek, lk) = if lk > ek { (lk, lk) } else { (ek, lk) };
                                    let w = ek - lk;
                                    let seg = (tv >> lk) & mask(w);
                                    let oseg = (ov >> lk) & mask(w);
                                    let nseg = if sub { seg.wrapping_sub(gv * oseg) } else { seg + gv * oseg } & mask(w);
                                    let want = (tv & !(mask(w) << lk)) | (nseg << lk);
                                    assert_eq!(s.getu(&t, l), want,
                                               "mc n={n} dec={decreasing} inner={inner} cfg={thr_cfg} ctrl={ctrl} sub={sub} t={tv} o={ov} E={ek} L={lk} g={gv}");
                                    assert_eq!(s.getu(&o, l), ov, "mc: operand changed");
                                });
                                runs += 1;
                            }
                            cases += inputs.len();
                        }
                    }
                }
            }
        }
    }
    println!("{{\"kind\":\"skycof-ring-mc\",\"cases\":{cases},\"runs\":{runs}}}");
}

// ─── 3. capture compare ──────────────────────────────────────────────────────

fn test_cmp() {
    let kb = 3usize;
    let mut cases = 0usize;
    for n in 1..=5usize {
        for mode in 0..3 {
            // 0 fixed cut n, 1 increasing cut map, 2 decreasing
            for gated in [false, true] {
                let mut c = Builder::new();
                let a = c.alloc_qubits(n);
                let b = c.alloc_qubits(n);
                let reg = c.alloc_qubits(kb);
                let out = c.alloc_qubit();
                let gate = gated.then(|| c.alloc_qubit());
                let cut = move |v: usize| if mode == 2 { n - v } else { v };
                let th = Thr { reg: &reg, pairs: (0..=n).map(|k| (cut(k), k)).collect() };
                cmp_capture(&mut c, &a, &b, out, (mode != 0).then_some(&th), gate);
                let (nq, nb) = c.i13_dims();
                let ops = c.take_ops();
                let mut keep: Vec<Q> = a.iter().chain(&b).chain(&reg).copied().collect();
                keep.push(out);
                keep.extend(gate);
                let mut inputs = Vec::new();
                for k in 0..=n {
                    if mode == 0 && k != n {
                        continue;
                    }
                    for gv in 0..=usize::from(gated) {
                        for ov in 0..2 {
                            for av in 0..=mask(n) {
                                for bv in 0..=mask(n) {
                                    inputs.push((av, bv, k, gv, ov));
                                }
                            }
                        }
                    }
                }
                for (bi, chunk) in inputs.chunks(64).enumerate() {
                    run_batch(&ops, nq, nb, chunk.len(), bi as u64, &keep, "cmp", &mut |s, l| {
                        let (av, bv, k, gv, ov) = chunk[l];
                        s.setu(&a, av, l);
                        s.setu(&b, bv, l);
                        s.setu(&reg, cut(k), l);
                        s.setu(&[out], ov, l);
                        if let Some(gq) = gate {
                            s.setu(&[gq], gv, l);
                        }
                    }, &mut |s, l| {
                        let (av, bv, k, gv, ov) = chunk[l];
                        let gv = if gated { gv } else { 1 };
                        let lt = usize::from((av & mask(k)) < (bv & mask(k)));
                        assert_eq!(s.getu(&[out], l), ov ^ (gv & lt), "cmp n={n} mode={mode} a={av} b={bv} k={k} g={gv}");
                        assert_eq!((s.getu(&a, l), s.getu(&b, l)), (av, bv));
                    });
                }
                cases += inputs.len();
            }
        }
    }
    println!("{{\"kind\":\"skycof-ring-cmp\",\"cases\":{cases}}}");
}

// ─── 4. leading-one deposit ──────────────────────────────────────────────────

fn test_lod() {
    let kb = 3usize;
    let mut cases = 0usize;
    let mut rng = Rng64(5);
    for n in 1..=6usize {
        for decreasing in [false, true] {
            for rlo in 0..=2usize.min(n) {
              for room in [None, Some(3usize), Some(4), Some(5)] {
                for gated in [false, true] {
                    for fsel in 0..2 {
                        let f = move |r: usize| if fsel == 1 { post(r) } else { r };
                        // cuts allowed: [rlo, n]
                        let cuts: Vec<usize> = (rlo..=n).collect();
                        let vmap = move |k: usize| if decreasing { 7 - k } else { k };
                        let mut c = Builder::new();
                        let x = c.alloc_qubits(n);
                        let reg = c.alloc_qubits(kb);
                        let out = c.alloc_qubits(kb);
                        let gate = gated.then(|| c.alloc_qubit());
                        let th = Thr { reg: &reg, pairs: cuts.iter().map(|&k| (vmap(k), k)).collect() };
                        lod_deposit(&mut c, &x, &th, rlo, &out, &f, gate, room.map_or(Room::Unbounded, Room::Chain));
                        let (nq, nb) = c.i13_dims();
                        let ops = c.take_ops();
                        let mut keep: Vec<Q> = x.iter().chain(&reg).chain(&out).copied().collect();
                        keep.extend(gate);
                        let mut inputs = Vec::new();
                        for &k in &cuts {
                            for xv in 0..=mask(n) {
                                let top = (0..k).rev().find(|&i| (xv >> i) & 1 == 1).map_or(0, |i| i + 1);
                                if top < rlo {
                                    continue;
                                }
                                for gv in 0..=usize::from(gated) {
                                    inputs.push((xv, k, gv, rng.below(8) as usize, top));
                                }
                            }
                        }
                        for (bi, chunk) in inputs.chunks(64).enumerate() {
                            run_batch(&ops, nq, nb, chunk.len(), bi as u64, &keep, "lod", &mut |s, l| {
                                let (xv, k, gv, ov, _) = chunk[l];
                                s.setu(&x, xv, l);
                                s.setu(&reg, vmap(k), l);
                                s.setu(&out, ov, l);
                                if let Some(gq) = gate {
                                    s.setu(&[gq], gv, l);
                                }
                            }, &mut |s, l| {
                                let (xv, k, gv, ov, top) = chunk[l];
                                let gv = if gated { gv } else { 1 };
                                let want = ov ^ if gv == 1 { f(top) } else { 0 };
                                assert_eq!(s.getu(&out, l), want, "lod n={n} dec={decreasing} rlo={rlo} room={room:?} x={xv} E={k} g={gv} f={fsel}");
                                assert_eq!(s.getu(&x, l), xv);
                            });
                        }
                        cases += inputs.len();
                    }
                }
            }
          }
        }
    }
    println!("{{\"kind\":\"skycof-ring-lod\",\"cases\":{cases}}}");
}

// ─── classical Kaliski model ─────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct KSt {
    u: U,
    v: U,
    s: U,
    r: U,
}

fn bits(x: U) -> usize {
    512 - x.leading_zeros()
}

/// Classical swap-first Kaliski step: (post state, c = u odd, isC).
fn kal(st: &KSt) -> (KSt, bool, bool) {
    let KSt { u, v, s, r } = *st;
    if !u.bit(0) {
        (KSt { u: u >> 1usize, v, s: s << 1usize, r }, false, false)
    } else if u >= v {
        (KSt { u: (u - v) >> 1usize, v, s: s << 1usize, r: r + s }, true, false)
    } else {
        (KSt { u: (v - u) >> 1usize, v: u, s: r << 1usize, r: r + s }, true, true)
    }
}

/// bits(s'), bits(u'), bits(v') after the swap of the step from `st`.
fn post_bits(st: &KSt) -> (usize, usize, usize) {
    let swap = st.u.bit(0) && st.u < st.v;
    if swap { (bits(st.r), bits(st.v), bits(st.u)) } else { (bits(st.s), bits(st.u), bits(st.v)) }
}

fn enc(val: U, cof: U, n: usize) -> U {
    let mut x = val;
    for j in 0..bits(cof) {
        if cof.bit(j) {
            x.set_bit(n - 1 - j, true);
        }
    }
    x
}

fn layout_ok(st: &KSt, n: usize) -> bool {
    bits(st.u) + bits(st.s) <= n && bits(st.v) + bits(st.r) <= n
}

/// All pre-park states of the walk from d (u >= 1), with their tick index.
fn walk(d: U, p: U, max_ticks: usize) -> Vec<KSt> {
    let mut st = KSt { u: d, v: p, s: U::ZERO, r: U::from(1u64) };
    let mut out = Vec::new();
    while !st.u.is_zero() && out.len() < max_ticks {
        out.push(st);
        st = kal(&st).0;
    }
    out
}

#[derive(Clone, Copy)]
struct ZAcc {
    lo: [usize; 6],
    hi: [usize; 6],
}

impl ZAcc {
    fn new() -> Self {
        ZAcc { lo: [usize::MAX; 6], hi: [0; 6] }
    }
    fn add(&mut self, st: &KSt) {
        let (sp, up, vp) = post_bits(st);
        let v = [bits(st.s), bits(st.u), bits(st.v), sp, up, vp];
        for i in 0..6 {
            self.lo[i] = self.lo[i].min(v[i]);
            self.hi[i] = self.hi[i].max(v[i]);
        }
    }
    fn zones(&self, margin: usize, n: usize) -> TickZ {
        let r = |i: usize| Rng::new(self.lo[i].saturating_sub(margin), (self.hi[i] + margin).min(n));
        TickZ { ka: r(0), ua: r(1), vb: r(2), kap: r(3), uap: r(4), vbp: r(5) }
    }
    fn contains(z: &TickZ, st: &KSt) -> bool {
        let (sp, up, vp) = post_bits(st);
        let inn = |r: Rng, x: usize| x >= r.lo && x <= r.hi;
        inn(z.ka, bits(st.s)) && inn(z.ua, bits(st.u)) && inn(z.vb, bits(st.v)) && inn(z.kap, sp) && inn(z.uap, up)
            && inn(z.vbp, vp)
    }
}

fn loose(n: usize) -> TickZ {
    // KA after step 3a holds bits(2 s') <= N, so bits(s') <= N - 1
    let r = Rng::new(0, n);
    TickZ { ka: r, ua: r, vb: r, kap: Rng::new(0, n - 1), uap: r, vbp: r }
}

// ─── 5/6. tick tests ─────────────────────────────────────────────────────────

struct TickC {
    ops: Vec<Op>,
    mid: usize,
    nq: usize,
    nb: usize,
    a0: Vec<Q>,
    b0: Vec<Q>,
    ka0: Vec<Q>,
    vb0: Vec<Q>,
    a1: Vec<Q>,
    b1: Vec<Q>,
    ka1: Vec<Q>,
    vb1: Vec<Q>,
    cq: Q,
    a2: Vec<Q>,
    b2: Vec<Q>,
    peak_fwd: usize,
    peak_rev: usize,
    entry: usize,
    log_f: StepLog,
    log_r: StepLog,
}

fn build_tick(n: usize, z: &TickZ, budget: Option<usize>) -> TickC {
    let mut cb = Builder::new();
    let kb = kbits(n);
    let a0 = cb.alloc_qubits(n);
    let b0 = cb.alloc_qubits(n);
    let ka0 = cb.alloc_qubits(kb);
    let vb0 = cb.alloc_qubits(kb);
    let entry = 2 * n + 2 * kb;
    let mut r = Ring { n, cap: budget.map(|b| entry + b), a: a0.clone(), b: b0.clone(), ka: ka0.clone(), vb: vb0.clone(), gate: None };
    assert_eq!(cb.active_qubits() as usize, entry);
    let mut log_f = StepLog::default();
    let mut log_r = StepLog::default();
    let _ = cb.take_win_peak();
    let (cq, isc) = tick_fwd(&mut cb, &mut r, z, &mut log_f);
    let pf = log_f.peaks.iter().map(|x| x.1).max().unwrap();
    isc_erase(&mut cb, &r, isc);
    let mid = cb.op_count();
    let (a1, b1, ka1, vb1) = (r.a.clone(), r.b.clone(), r.ka.clone(), r.vb.clone());
    let _ = cb.take_win_peak();
    let isc = isc_recompute(&mut cb, &r);
    tick_rev(&mut cb, &mut r, z, cq, isc, &mut log_r);
    let pr = log_r.peaks.iter().map(|x| x.1).max().unwrap();
    assert_eq!(cb.active_qubits() as usize, entry, "tick leaks wires");
    let (nq, nb) = cb.i13_dims();
    let ops = cb.take_ops();
    TickC { ops, mid, nq, nb, a0, b0, ka0, vb0, a1, b1, ka1, vb1, cq, a2: r.a, b2: r.b, peak_fwd: pf - entry,
            peak_rev: pr - entry, entry, log_f, log_r }
}

fn run_tick(tc: &TickC, n: usize, states: &[KSt], seed: u64, label: &str) {
    let mut keep_mid: Vec<Q> = tc.a1.iter().chain(&tc.b1).chain(&tc.ka1).chain(&tc.vb1).copied().collect();
    keep_mid.push(tc.cq);
    let keep_end: Vec<Q> = tc.a2.iter().chain(&tc.b2).chain(&tc.ka0).chain(&tc.vb0).copied().collect();
    assert_eq!(tc.a2, tc.a0);
    assert_eq!(tc.b2, tc.b0);
    for (bi, chunk) in states.chunks(64).enumerate() {
        let mut sim = Sim::new(tc.nq, tc.nb, seed ^ bi as u64);
        let lm = lane_mask(chunk.len());
        for (l, st) in chunk.iter().enumerate() {
            sim.set(&tc.a0, enc(st.u, st.s, n), l);
            sim.set(&tc.b0, enc(st.v, st.r, n), l);
            sim.setu(&tc.ka0, bits(st.s), l);
            sim.setu(&tc.vb0, bits(st.v), l);
        }
        sim.run(&tc.ops[..tc.mid]);
        if sim.dirty & lm != 0 {
            let l = (sim.dirty & lm).trailing_zeros() as usize;
            let st = chunk[l];
            for (i, o) in tc.ops[..tc.mid].iter().enumerate() {
                if o.kind != K::R {
                    continue;
                }
                let mut s2 = Sim::new(tc.nq, tc.nb, 1);
                s2.set(&tc.a0, enc(st.u, st.s, n), 0);
                s2.set(&tc.b0, enc(st.v, st.r, n), 0);
                s2.setu(&tc.ka0, bits(st.s), 0);
                s2.setu(&tc.vb0, bits(st.v), 0);
                s2.run(&tc.ops[..=i]);
                if s2.dirty & 1 != 0 {
                    let marks: Vec<String> = tc.log_f.marks.iter().map(|(a, b)| format!("{a}@{b}")).collect();
                    eprintln!("first dirty release at op {i}: {o:?}; marks {marks:?}; z {:?}", ());
                    break;
                }
            }
            let (p, cbit, isc) = kal(&st);
            panic!("{label} fwd dirty; state {st:?}; want {p:?} c {cbit} isc {isc} A {:x} B {:x}; got A {:x} B {:x} KA {} VB {} c {}",
                   enc(p.u, p.s, n), enc(p.v, p.r, n), sim.get(&tc.a1, l), sim.get(&tc.b1, l), sim.getu(&tc.ka1, l),
                   sim.getu(&tc.vb1, l), sim.getu(&[tc.cq], l));
        }
        assert_eq!(sim.phase & lm, 0, "{label} fwd phase {:x}", sim.phase & lm);
        assert_eq!(sim.dirty & lm, 0, "{label} fwd dirty {:x}", sim.dirty & lm);
        let res = sim.residue(&keep_mid) & lm;
        assert_eq!(res, 0, "{label} fwd garbage {res:x}");
        for (l, st) in chunk.iter().enumerate() {
            let (p, cbit, _) = kal(st);
            let ok = sim.get(&tc.a1, l) == enc(p.u, p.s, n) && sim.get(&tc.b1, l) == enc(p.v, p.r, n)
                && sim.getu(&tc.ka1, l) == bits(p.s) && sim.getu(&tc.vb1, l) == bits(p.v)
                && sim.getu(&[tc.cq], l) == usize::from(cbit);
            assert!(ok, "{label} fwd value: pre {st:?} want {p:?}; got A {:x} B {:x} KA {} VB {} c {}", sim.get(&tc.a1, l),
                    sim.get(&tc.b1, l), sim.getu(&tc.ka1, l), sim.getu(&tc.vb1, l), sim.getu(&[tc.cq], l));
        }
        sim.run(&tc.ops[tc.mid..]);
        assert_eq!(sim.phase & lm, 0, "{label} rev phase");
        assert_eq!(sim.dirty & lm, 0, "{label} rev dirty");
        assert_eq!(sim.residue(&keep_end) & lm, 0, "{label} rev garbage");
        for (l, st) in chunk.iter().enumerate() {
            let ok = sim.get(&tc.a2, l) == enc(st.u, st.s, n) && sim.get(&tc.b2, l) == enc(st.v, st.r, n)
                && sim.getu(&tc.ka0, l) == bits(st.s) && sim.getu(&tc.vb0, l) == bits(st.v);
            assert!(ok, "{label} rev value: pre {st:?}");
        }
    }
}

fn test_ticks_small(kmax: usize) {
    for kbit in 4..=kmax {
        let n = kbit + 1;
        let mut by_t: Vec<Vec<KSt>> = Vec::new();
        let mut all: Vec<KSt> = Vec::new();
        let (mut moduli, mut cswaps) = (0usize, 0usize);
        for p in ((1usize << (kbit - 1)) + 1..(1usize << kbit)).step_by(2) {
            moduli += 1;
            let pu = U::from(p as u64);
            for d in 1..p {
                for (t, st) in walk(U::from(d as u64), pu, 4 * n).into_iter().enumerate() {
                    assert!(layout_ok(&st, n), "layout theorem violated: {st:?}");
                    if by_t.len() <= t {
                        by_t.push(Vec::new());
                    }
                    cswaps += usize::from(kal(&st).2);
                    by_t[t].push(st);
                    all.push(st);
                }
            }
        }
        // loose windows: one circuit for every state
        let tc = build_tick(n, &loose(n), None);
        run_tick(&tc, n, &all, 7, &format!("tick K={kbit} loose"));
        let tcb = build_tick(n, &loose(n), Some(16));
        run_tick(&tcb, n, &all, 8, &format!("tick K={kbit} loose budget"));
        // tight per-tick windows
        let mut tight_circuits = 0;
        for (t, sts) in by_t.iter().enumerate() {
            let mut za = ZAcc::new();
            sts.iter().for_each(|s| za.add(s));
            let z = za.zones(0, n);
            let tc2 = build_tick(n, &z, if t % 2 == 0 { None } else { Some(14) });
            run_tick(&tc2, n, sts, 9 + t as u64, &format!("tick K={kbit} t={t} tight"));
            tight_circuits += 1;
        }
        println!("{{\"kind\":\"skycof-ring-tick-small\",\"K\":{kbit},\"N\":{n},\"moduli\":{moduli},\"states\":{},\"c_swaps\":{cswaps},\"tight_circuits\":{tight_circuits},\"loose_fwd_ccx\":{},\"loose_scratch\":{}}}",
                 all.len(), ccx_count(&tc.ops[..tc.mid]), tc.peak_fwd.max(tc.peak_rev));
    }
}

// ─── full width ──────────────────────────────────────────────────────────────

const NFULL: usize = 257;
const RTICKS: usize = 400;

fn secp_p() -> U {
    (U::from(1u64) << 256usize) - (U::from(1u64) << 32usize) - U::from(977u64)
}

fn rand_scalar(rng: &mut Rng64, p: U) -> U {
    loop {
        let mut d = U::ZERO;
        for i in 0..256 {
            if rng.next() & 1 == 1 {
                d.set_bit(i, true);
            }
        }
        if !d.is_zero() && d < p {
            return d;
        }
    }
}

/// Per-tick windows from training walks (min/max over pre-park states, widened by the margin).
fn train_zones(ntrain: usize, margin: usize, seed: u64) -> Vec<TickZ> {
    let p = secp_p();
    let mut rng = Rng64(seed);
    let mut acc = vec![ZAcc::new(); RTICKS];
    for _ in 0..ntrain {
        let d = rand_scalar(&mut rng, p);
        for (t, st) in walk(d, p, RTICKS).iter().enumerate() {
            acc[t].add(st);
        }
    }
    let mut last = acc[0];
    acc.iter()
        .map(|a| {
            let a = if a.lo[0] == usize::MAX { last } else { *a };
            last = a;
            a.zones(margin, NFULL)
        })
        .collect()
}

fn heldout_exceed(z: &[TickZ], nheld: usize, seed: u64) -> (usize, usize) {
    let p = secp_p();
    let mut rng = Rng64(seed);
    let mut bad = 0;
    for _ in 0..nheld {
        let d = rand_scalar(&mut rng, p);
        if walk(d, p, RTICKS).iter().enumerate().any(|(t, st)| !ZAcc::contains(&z[t], st)) {
            bad += 1;
        }
    }
    (bad, nheld)
}

fn test_full(z: &[TickZ], batches: usize) {
    let p = secp_p();
    let mut rng = Rng64(20261001);
    let mut walks: Vec<Vec<KSt>> = Vec::new();
    while walks.len() < 64 * batches {
        let w = walk(rand_scalar(&mut rng, p), p, RTICKS);
        if w.iter().enumerate().all(|(t, st)| ZAcc::contains(&z[t], st)) {
            walks.push(w);
        }
    }
    let mut ticks = 0usize;
    let mut states = 0usize;
    for t in 0..RTICKS {
        let sts: Vec<KSt> = walks.iter().filter_map(|w| w.get(t).copied()).collect();
        if sts.is_empty() {
            continue;
        }
        let tc = build_tick(NFULL, &z[t], if t % 2 == 0 { None } else { Some(18) });
        run_tick(&tc, NFULL, &sts, 100 + t as u64, &format!("full t={t}"));
        ticks += 1;
        states += sts.len();
    }
    println!("{{\"kind\":\"skycof-ring-tick-full\",\"walks\":{},\"ticks\":{ticks},\"states\":{states}}}", walks.len());
}

/// 64 walks chained tick by tick at full width (forward to `nt` ticks, then all the way back).
fn test_chain(z: &[TickZ], nt_req: usize) {
    let p = secp_p();
    let mut rng = Rng64(777);
    let mut walks: Vec<Vec<KSt>> = Vec::new();
    while walks.len() < 64 {
        let w = walk(rand_scalar(&mut rng, p), p, RTICKS);
        if w.iter().enumerate().all(|(t, st)| ZAcc::contains(&z[t], st)) {
            walks.push(w);
        }
    }
    let nt = walks.iter().map(|w| w.len()).min().unwrap().min(nt_req);
    let mut cb = Builder::new();
    let kb = kbits(NFULL);
    let a0 = cb.alloc_qubits(NFULL);
    let b0 = cb.alloc_qubits(NFULL);
    let ka0 = cb.alloc_qubits(kb);
    let vb0 = cb.alloc_qubits(kb);
    let mut r = Ring { n: NFULL, cap: None, a: a0.clone(), b: b0.clone(), ka: ka0.clone(), vb: vb0.clone(), gate: None };
    let mut cs: Vec<Q> = Vec::new();
    let mut log = StepLog::default();
    for t in 0..nt {
        let (cq, isc) = tick_fwd(&mut cb, &mut r, &z[t], &mut log);
        isc_erase(&mut cb, &r, isc);
        cs.push(cq);
    }
    let mid = cb.op_count();
    let (a1, b1, ka1, vb1) = (r.a.clone(), r.b.clone(), r.ka.clone(), r.vb.clone());
    for t in (0..nt).rev() {
        let isc = isc_recompute(&mut cb, &r);
        tick_rev(&mut cb, &mut r, &z[t], cs[t], isc, &mut log);
    }
    let (nq, nb) = cb.i13_dims();
    let ops = cb.take_ops();
    let mut sim = Sim::new(nq, nb, 4242);
    for (l, w) in walks.iter().enumerate() {
        let st = w[0];
        sim.set(&a0, enc(st.u, st.s, NFULL), l);
        sim.set(&b0, enc(st.v, st.r, NFULL), l);
        sim.setu(&ka0, bits(st.s), l);
        sim.setu(&vb0, bits(st.v), l);
    }
    sim.run(&ops[..mid]);
    assert_eq!(sim.phase | sim.dirty, 0, "chain fwd phase/dirty");
    let mut keep: Vec<Q> = a1.iter().chain(&b1).chain(&ka1).chain(&vb1).copied().collect();
    keep.extend(cs.iter().copied());
    assert_eq!(sim.residue(&keep), 0, "chain fwd garbage");
    for (l, w) in walks.iter().enumerate() {
        let end = if nt < w.len() { w[nt] } else { kal(&w[nt - 1]).0 };
        assert_eq!(sim.get(&a1, l), enc(end.u, end.s, NFULL), "chain fwd A lane {l}");
        assert_eq!(sim.get(&b1, l), enc(end.v, end.r, NFULL), "chain fwd B lane {l}");
        assert_eq!((sim.getu(&ka1, l), sim.getu(&vb1, l)), (bits(end.s), bits(end.v)));
        for t in 0..nt {
            assert_eq!(sim.getu(&[cs[t]], l) == 1, w[t].u.bit(0), "chain letter bit t={t}");
        }
    }
    sim.run(&ops[mid..]);
    assert_eq!(sim.phase | sim.dirty, 0, "chain rev phase/dirty");
    let keep0: Vec<Q> = r.a.iter().chain(&r.b).chain(&ka0).chain(&vb0).copied().collect();
    assert_eq!(sim.residue(&keep0), 0, "chain rev garbage");
    for (l, w) in walks.iter().enumerate() {
        let st = w[0];
        assert_eq!(sim.get(&r.a, l), enc(st.u, st.s, NFULL), "chain rev A");
        assert_eq!(sim.get(&r.b, l), enc(st.v, st.r, NFULL), "chain rev B");
    }
    println!("{{\"kind\":\"skycof-ring-chain\",\"walks\":64,\"ticks\":{nt},\"ops\":{}}}", ops.len());
}

// ─── 8. cost ─────────────────────────────────────────────────────────────────

fn seg(tc: &TickC, log: &StepLog, base: usize, end: usize) -> Vec<(&'static str, f64)> {
    let mut out = Vec::new();
    let mut prev = base;
    for &(name, at) in &log.marks[1..] {
        out.push((name, expected_ccx(&tc.ops[prev..at])));
        prev = at;
    }
    out.push(("tail", expected_ccx(&tc.ops[prev..end])));
    out
}

/// Per-tick budgets from a live profile: `SKYCOF_RING_LIVE_TSV` (lines `t<TAB>live`, live counted with
/// the ring and both boundary registers) and `SKYCOF_RING_CAP`: budget(t) = cap - live(t).
fn live_budgets() -> Option<(usize, Vec<usize>)> {
    let cap: usize = std::env::var("SKYCOF_RING_CAP").ok()?.trim().parse().ok()?;
    let text = std::fs::read_to_string(std::env::var("SKYCOF_RING_LIVE_TSV").ok()?).ok()?;
    let live: Vec<usize> = text.lines().filter_map(|l| l.split(char::from(9u8)).nth(1)?.trim().parse().ok()).collect();
    Some((cap, live))
}

pub fn cost_report(z: &[TickZ], budget: Option<usize>) {
    let lb = live_budgets();
    let tag = match &lb {
        Some((cap, _)) => format!("cap{cap}"),
        None => budget.map_or("inf".to_string(), |b| b.to_string()),
    };
    let path = std::env::var("SKYCOF_RING_COST_TSV").ok().map(|p| p.replace(".tsv", &format!("_b{tag}.tsv")));
    let mut tsv = String::from("t\tka\tua\tvb\tkap\tuap\tvbp\tfwd\trev\tscratch_fwd\tscratch_rev\tconv1\tcmp\tswap\tconv2\tcof\trail\tcof_plain\tcof_masked\tcof2_masked\trail_plain\trail_masked\trail2_masked\tlod_cells\tscratch_steps\n");
    let mut tot_f = 0.0;
    let mut tot_r = 0.0;
    let mut by: std::collections::BTreeMap<&'static str, f64> = Default::default();
    let (mut smax_f, mut smax_r) = (0usize, 0usize);
    let mut smax_step: std::collections::BTreeMap<&'static str, usize> = Default::default();
    for (t, zt) in z.iter().enumerate() {
        let b = match &lb {
            Some((cap, live)) => Some(cap.saturating_sub(live[t.min(live.len() - 1)])),
            None => budget,
        };
        let tc = build_tick(NFULL, zt, b);
        let f = expected_ccx(&tc.ops[..tc.mid]);
        let r = expected_ccx(&tc.ops[tc.mid..]);
        tot_f += f;
        tot_r += r;
        let parts = seg(&tc, &tc.log_f, 0, tc.mid);
        for &(nm, v) in &parts {
            *by.entry(nm).or_default() += v;
        }
        smax_f = smax_f.max(tc.peak_fwd);
        smax_r = smax_r.max(tc.peak_rev);
        let pv = |nm: &str| parts.iter().find(|x| x.0 == nm).map_or(0.0, |x| x.1);
        let rg = |x: Rng| format!("{}-{}", x.lo, x.hi);
        tsv += &format!("{t}\t{}\t{}\t{}\t{}\t{}\t{}\t{f:.1}\t{r:.1}\t{}\t{}\t{:.1}\t{:.1}\t{:.1}\t{:.1}\t{:.1}\t{:.1}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                        rg(zt.ka), rg(zt.ua), rg(zt.vb), rg(zt.kap), rg(zt.uap), rg(zt.vbp), tc.peak_fwd, tc.peak_rev,
                        pv("conv1"), pv("cmp"), pv("swap"), pv("conv2"), pv("cof"), pv("rail"),
                        tc.log_f.cof[0].plain, tc.log_f.cof[0].masked, tc.log_f.cof[1].masked, tc.log_f.rail[0].plain,
                        tc.log_f.rail[0].masked, tc.log_f.rail[1].masked,
                        tc.log_f.lod_cells.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","),
                        tc.log_f.peaks.iter().skip(1).map(|(nm, p)| format!("{nm}:{}", p.saturating_sub(tc.entry))).collect::<Vec<_>>().join(","));
        for (nm, p) in tc.log_f.peaks.iter().skip(1) {
            let e = smax_step.entry(*nm).or_insert(0usize);
            *e = (*e).max(p.saturating_sub(tc.entry));
        }
    }
    if let Some(p) = path {
        std::fs::write(&p, &tsv).expect("write cost tsv");
    }
    let parts: Vec<String> = by.iter().map(|(k, v)| format!("\"{k}\":{v:.0}")).collect();
    println!("{{\"kind\":\"skycof-ring-cost\",\"budget\":\"{tag}\",\"ticks\":{},\"fwd_ccx\":{tot_f:.0},\"rev_ccx\":{tot_r:.0},\"fwd_parts\":{{{}}},\"max_scratch_fwd\":{smax_f},\"max_scratch_rev\":{smax_r},\"max_scratch_by_step\":{{{}}}}}",
             z.len(), parts.join(","), smax_step.iter().map(|(k, v)| format!("\"{k}\":{v}")).collect::<Vec<_>>().join(","));
}

pub fn run() {
    let mode = std::env::var("SKYCOF_RING_SELFTEST").unwrap_or_default();
    let mode = mode.trim();
    let t0 = std::time::Instant::now();
    let unit = || {
        test_engine();
        test_mc();
        test_cmp();
        test_lod();
    };
    if mode == "unit" {
        unit();
        println!("{{\"kind\":\"skycof-ring-selftest\",\"result\":\"PASS\",\"mode\":\"unit\",\"secs\":{:.1}}}", t0.elapsed().as_secs_f64());
        return;
    }
    let margin = env_usize("SKYCOF_RING_MARGIN", 2);
    let ntrain = env_usize("SKYCOF_RING_TRAIN", 20000);
    if mode != "cost" {
        unit();
        test_ticks_small(env_usize("SKYCOF_RING_KMAX", 8));
    }
    let z = train_zones(ntrain, margin, 1234567);
    let (bad, held) = heldout_exceed(&z, env_usize("SKYCOF_RING_HELD", 20000), 99);
    println!("{{\"kind\":\"skycof-ring-windows\",\"train\":{ntrain},\"margin\":{margin},\"heldout\":{held},\"walks_outside\":{bad}}}");
    if mode != "cost" {
        test_full(&z, env_usize("SKYCOF_RING_FULL", 2));
        test_chain(&z, env_usize("SKYCOF_RING_CHAIN", 400));
    }
    let budgets: Vec<Option<usize>> = std::env::var("SKYCOF_RING_BUDGETS").ok()
        .map(|v| v.split(',').map(|x| x.trim().parse::<usize>().ok()).collect())
        .unwrap_or_else(|| vec![None, Some(24), Some(18)]);
    for b in budgets {
        cost_report(&z, b);
    }
    println!("{{\"kind\":\"skycof-ring-selftest\",\"result\":\"PASS\",\"mode\":\"{mode}\",\"secs\":{:.1}}}", t0.elapsed().as_secs_f64());
}
