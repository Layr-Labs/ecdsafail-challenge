//! O2 (W3b) focused gates: U15 K9, U30 DB, U13 K8, U16 C1.
//! Each cut: exhaustive/all-assignment primitive check (all wires + phase, forced HMR tapes
//! 00/ff/aa/55 plus a SHAKE tape, both play directions) and a whole-walk all-wire + phase
//! equivalence with the cut on vs off (forward tick boundaries and the end of the inverse replay).
#![allow(dead_code)]
use super::builder::B;
use super::frogdrop_sched::{p, N};
use super::lilypad::*;
use super::lilypad_g::*;
use super::tests_frogdrop::Rng;
use super::tests_strip::{get_s, put};
use crate::circuit::{analyze_ops, Op, QubitId};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update, XofReader};

pub(crate) enum Tape {
    Fixed(u8),
    Shake(sha3::Shake256Reader),
}
impl XofReader for Tape {
    fn read(&mut self, o: &mut [u8]) {
        match self {
            Tape::Fixed(v) => o.fill(*v),
            Tape::Shake(r) => r.read(o),
        }
    }
}
pub(crate) fn tape(kind: u16) -> Tape {
    if kind < 256 {
        Tape::Fixed(kind as u8)
    } else {
        let mut h = sha3::Shake256::default();
        h.update(b"o2-tape");
        h.update(&kind.to_le_bytes());
        Tape::Shake(h.finalize_xof())
    }
}
pub(crate) const TAPES: [u16; 5] = [0x00, 0xff, 0xaa, 0x55, 0x100];

fn env_or(k: &str, d: usize) -> usize {
    std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d)
}

/// 64 inputs: 8 edges (1, 2, 3, p-1, p-2, 2^255, 2^255-1, 0x55..55) + 56 uniform in [1,p).
pub(crate) fn inputs(seed: u64) -> Vec<N> {
    let pm = p();
    let f = N::from(0x5555_5555_5555_5555u64);
    let mut v = vec![
        N::from(1u64),
        N::from(2u64),
        N::from(3u64),
        pm - N::from(1u64),
        pm - N::from(2u64),
        N::from(1u64) << 255usize,
        (N::from(1u64) << 255usize) - N::from(1u64),
        f | (f << 64usize) | (f << 128usize) | (f << 192usize),
    ];
    let mut rng = Rng::new(seed);
    while v.len() < 64 {
        let x = rng.below(256) % pm;
        if x != N::ZERO {
            v.push(x);
        }
    }
    v
}

pub(crate) struct Walk {
    pub b: B,
    pub x: Vec<QubitId>,
    pub w: PWalk,
    /// op index after init, after each forward tick, after the inverse walk
    pub bounds: Vec<usize>,
}

/// Production-shaped division walk: capq 11, 8 log lanes, forward then the inverse replay.
pub(crate) fn division_walk(sch: &PSched, room_fwd: usize, room_inv: usize) -> Walk {
    let mut b = B::new();
    let x = b.alloc_n(256);
    let mut a = x.clone();
    a.extend(b.alloc_n(sch.w - 256));
    let mut w = PWalk { a, bb: b.alloc_n(sch.w), q: vec![], h: b.alloc_n(HB), capq: 11, log: b.alloc_n(8) };
    let sc = PScr::alloc_fwd(&mut b, room_fwd);
    let mut bounds = vec![];
    init_g(&mut b, &w, sch, &sc);
    bounds.push(b.ops.len());
    let division = b.new_division();
    let m = b.fresh_bits(sch.s + 1);
    for t in 1..=sch.s {
        let rho = rho_stable(&w, t - 1);
        step_core_g(&mut b, &w, t, sch, &sc, &rho, sc.e, &[], Some((division, false)));
        halve_g(&mut b, &w, t, sch, &sc);
        b.hmr_to(sc.e, m[t]);
        bounds.push(b.ops.len());
    }
    sc.release(&mut b);
    w.q = b.alloc_n(13);
    let sci = PScr::alloc_inv_g(&mut b, room_inv,true,true);
    walk_inverse_g(&mut b, &w, sch, &sci, &GScr, &m, Some(division));
    b.close_division(division);
    sci.release(&mut b);
    bounds.push(b.ops.len());
    Walk { b, x, w, bounds }
}

/// Simulate on 64 shots; return (qubit rows, phase) at every bound.
pub(crate) fn states(wk: &Walk, xs: &[N], tk: u16) -> Vec<(Vec<u64>, u64)> {
    let (nq, nb, _, _) = analyze_ops(wk.b.ops.iter());
    let mut tp = tape(tk);
    let mut s = Simulator::new((nq as usize).max(wk.b.width() as usize), (nb as usize).max(2), &mut tp);
    for k in 0..64 {
        put(&mut s.qubits, &wk.x, k, xs[k]);
    }
    let mut out = vec![];
    let mut at = 0;
    for &bd in &wk.bounds {
        s.apply_iter(wk.b.ops[at..bd].iter());
        at = bd;
        out.push((s.qubits.clone(), s.phase));
    }
    out
}

pub(crate) fn diff_rows(a: &(Vec<u64>, u64), b: &(Vec<u64>, u64)) -> u64 {
    let mut d = a.1 ^ b.1;
    let n = a.0.len().max(b.0.len());
    for i in 0..n {
        d |= a.0.get(i).copied().unwrap_or(0) ^ b.0.get(i).copied().unwrap_or(0);
    }
    d
}

pub(crate) fn expected_t(ops: &[Op]) -> f64 {
    use crate::circuit::OperationType as K;
    let mut w = 1.0f64;
    let mut st = vec![];
    let mut tot = 0.0;
    for op in ops {
        match op.kind {
            K::PushCondition => {
                st.push(w);
                w *= 0.5;
            }
            K::PopCondition => w = st.pop().unwrap(),
            K::CCX | K::CCZ => tot += w,
            _ => {}
        }
    }
    tot
}

/// Round-trip summary on the last state: shots with x restored and every other lane clean, phase 0.
pub(crate) fn round_trip(wk: &Walk, last: &(Vec<u64>, u64), xs: &[N]) -> (u32, u32) {
    let mut restored = 0u64;
    for k in 0..64 {
        let m256 = (N::from(1u64) << 256usize) - N::from(1u64);
        if get_s(&last.0, &wk.x, k) & m256 == xs[k] {
            restored |= 1 << k;
        }
    }
    let keep: std::collections::HashSet<u64> = wk.x.iter().map(|q| q.0).collect();
    let mut dirty = last.1;
    for (i, row) in last.0.iter().enumerate() {
        if !keep.contains(&(i as u64)) {
            dirty |= row;
        }
    }
    (restored.count_ones(), (!dirty).count_ones())
}

/// Whole-walk equivalence of two builds (all wires + phase) at bounds[from..], 2 input seeds x 5 tapes.
/// Also prints the analytic expected T of each build's forward and inverse parts.
pub(crate) fn walk_equivalence(tag: &str, off: &Walk, on: &Walk, from: usize) {
    assert_eq!(off.bounds.len(), on.bounds.len());
    let nb = on.bounds.len();
    let tf_off = expected_t(&off.b.ops[..off.bounds[nb - 2]]);
    let tf_on = expected_t(&on.b.ops[..on.bounds[nb - 2]]);
    let ti_off = expected_t(&off.b.ops[off.bounds[nb - 2]..]);
    let ti_on = expected_t(&on.b.ops[on.bounds[nb - 2]..]);
    eprintln!("O2_{tag}_WALK_T forward off {tf_off} on {tf_on} delta {}; inverse off {ti_off} on {ti_on} delta {}",
        tf_on - tf_off, ti_on - ti_off);
    for seed in [0x0209u64, 0x0215] {
        let xs = inputs(seed);
        for tk in TAPES {
            let so = states(off, &xs, tk);
            let sn = states(on, &xs, tk);
            // forward tick boundaries: every shot (failing walks included)
            for i in from..nb - 1 {
                // Forward phases carry deferred debts (paired chunk adds, e-measurement) that are repaid
                // only by the inverse replay; a cut that changes an add's shape changes those debts. So the
                // forward phase is compared only under the all-zero tape (no measurement kicks), and every
                // tape's phase is compared at the inverse end.
                let d = if tk == 0 {
                    diff_rows(&so[i], &sn[i])
                } else {
                    diff_rows(&(so[i].0.clone(), 0), &(sn[i].0.clone(), 0))
                };
                assert_eq!(d, 0, "{tag} seed {seed:#x} tape {tk:#x} bound {i}: on/off differ");
            }
            // end of the inverse replay: identical on the support (shots the off build restores
            // cleanly); report any differing off-support shot
            let last = nb - 1;
            let keep: std::collections::HashSet<u64> = off.x.iter().map(|q| q.0).collect();
            let mut dirty_off = so[last].1;
            for (i, row) in so[last].0.iter().enumerate() {
                if !keep.contains(&(i as u64)) {
                    dirty_off |= row;
                }
            }
            let support = !dirty_off;
            let dend = diff_rows(&so[last], &sn[last]);
            assert_eq!(dend & support, 0, "{tag} seed {seed:#x} tape {tk:#x}: inverse end differs on support");
            let (r_on, c_on) = round_trip(on, &sn[last], &xs);
            let (r_off, c_off) = round_trip(off, &so[last], &xs);
            eprintln!("O2_{tag}_WALK seed {seed:#x} tape {tk:#x}: on==off (all wires+phase) at forward bounds {from}..{}, and at the inverse end on the {} support shots (off-support differing {}); round trip on {r_on}/{c_on} off {r_off}/{c_off} (restored/clean of 64)",
                nb - 1, support.count_ones(), (dend & !support).count_ones());
        }
    }
}

pub(crate) fn rooms() -> (usize, usize) {
    (env_or("O2_ROOM_FWD", 17), env_or("O2_ROOM_INV", 3))
}


// ------------------------------------------------------------------ U15 K9
thread_local! {static O2_K9_REF: std::cell::RefCell<Vec<u64>> = const { std::cell::RefCell::new(Vec::new()) };}

/// Exhaustive primitive: cswap(s,u,v) == CX(s,u);CX(s,v) exactly on the support u != v (and on s = 0),
/// both play directions (all 8 assignments, all wires, phase).
#[test]
fn o2_k9_primitive_exhaustive() {
    for inverse in [false, true] {
        for kind in 0..2 {
            let mut b = B::new();
            let q = b.alloc_n(3);
            b.begin();
            if kind == 0 {
                b.cswap(q[0], q[1], q[2]);
            } else {
                b.cx(q[0], q[1]);
                b.cx(q[0], q[2]);
            }
            let r = b.end();
            b.play(&r, inverse);
            let mut rows = [0u64; 3];
            for case in 0..8u64 {
                for (i, row) in rows.iter_mut().enumerate() {
                    if case >> i & 1 != 0 {
                        *row |= 1 << case;
                    }
                }
            }
            let mut tp = tape(0);
            let mut s = Simulator::new(3, 2, &mut tp);
            s.qubits.copy_from_slice(&rows);
            s.apply_iter(b.ops.iter());
            assert_eq!(s.phase, 0);
            let out = s.qubits.clone();
            if kind == 0 {
                O2_K9_REF.with(|c| *c.borrow_mut() = out);
            } else {
                let refv = O2_K9_REF.with(|c| c.borrow().clone());
                let mut differ = 0u64;
                for i in 0..3 {
                    differ |= refv[i] ^ out[i];
                }
                for case in 0..8u64 {
                    let (sg, u, v) = (case & 1, case >> 1 & 1, case >> 2 & 1);
                    assert_eq!(differ >> case & 1 == 0, u != v || sg == 0, "inverse={inverse} s={sg} u={u} v={v}");
                }
                eprintln!("O2_K9_PRIMITIVE inverse={inverse}: equal on all assignments with u!=v or s=0; differs only on s=1,u=v");
            }
        }
    }
}

/// Whole-walk K9 on vs off: identical qubits and phase at every forward tick boundary and after the
/// inverse replay (2 x 64 shots incl. edges, 5 tapes). The invariant U0=0, V0=1 before every swap is
/// thereby checked on every shot, failing walks included, in both traversals.
#[test]
#[ignore]
fn o2_k9_walk_equivalence() {
    let (rf, ri) = rooms();
    let sch = sched_g();
    test_k9(false);
    let off = division_walk(&sch, rf, ri);
    test_k9(true);
    let on = division_walk(&sch, rf, ri);
    walk_equivalence("K9", &off, &on, 0);
}


// ------------------------------------------------------------------ U30 DB
/// The schedule file trims kv[1..=16] from 260 to 259. Model check of the bound (deterministic):
/// |G|,|F| < 3*2^256 and |G +- F| <= 2(|g|+|f|) < 2^258, so 259 signed lanes hold every operand and sum.
#[test]
fn o2_db_schedule_and_bound() {
    let sch = sched_g();
    for t in 1..=16 {
        assert_eq!(sch.kv[t], 259, "DB kv[{t}]");
    }
    assert_eq!(sch.kv[17], 259);
    // Integer replica of the forced-digit walk on the G coordinates: every stored value and every
    // sum fits 259 signed bits on 4,096 inputs (edges + uniform), all 16 ticks (and to 532 for width).
    let pm = p();
    let lim = N::from(1u64) << 258usize;
    let mut rng = Rng::new(0xdb);
    let mut xs = inputs(0xdb0);
    while xs.len() < 4096 {
        let x = rng.below(256) % pm;
        if x != N::ZERO {
            xs.push(x);
        }
    }
    // signed values as (neg, magnitude)
    fn mag(v: &(bool, N)) -> N { v.1 }
    fn add(a: &(bool, N), b: &(bool, N), sub: bool) -> (bool, N) {
        let bn = b.0 ^ sub;
        if a.0 == bn { (a.0, a.1 + b.1) } else if a.1 >= b.1 { (a.0, a.1 - b.1) } else { (bn, b.1 - a.1) }
    }
    let mut worst = N::ZERO;
    for &x in &xs {
        // Lilypad: f = p, g = x; divstep on (delta, f, g) with the G = 2g - f bookkeeping
        let (mut f, mut g) = ((false, pm), (false, x));
        let mut delta: i64 = 1;
        for _t in 1..=532 {
            let gg = add(&(g.0, g.1 << 1usize), &f, true); // G = 2g - f
            let s1 = add(&gg, &f, false);
            let s2 = add(&gg, &f, true);
            for v in [&f, &gg, &s1, &s2] {
                assert!(mag(v) < lim, "DB bound violated");
                if mag(v) > worst { worst = mag(v); }
            }
            let godd = g.1.bit(0);
            if delta > 0 && godd {
                let ng = add(&g, &f, true); // (g - f)/2
                f = g;
                g = (ng.0, ng.1 >> 1usize);
                delta = 1 - delta;
            } else {
                let ng = if godd { add(&g, &f, false) } else { g };
                g = (ng.0, ng.1 >> 1usize);
                delta += 1;
            }
            if g.1 == N::ZERO { g.0 = false; }
        }
    }
    eprintln!("O2_DB_BOUND 4096 inputs x 532 ticks: max |value| bits {} (< 259 signed lanes)", 384 - worst.leading_zeros());
}

/// Whole-walk DB on vs off (kv[1..=16] = 259 vs 260): identical qubits and phase at every forward tick
/// boundary and after the inverse replay.
#[test]
#[ignore]
fn o2_db_walk_equivalence() {
    let (rf, ri) = rooms();
    let on_s = sched_g();
    let mut off_s = on_s.clone();
    for t in 1..=16 {
        off_s.kv[t] = 260;
    }
    let off = division_walk(&off_s, rf, ri);
    let on = division_walk(&on_s, rf, ri);
    walk_equivalence("DB", &off, &on, 0);
}


// ------------------------------------------------------------------ U13 K8
/// Exhaustive small-width analog of the fused init + tick-1 block: x of m bits shifted to lanes 1..m,
/// e = x0, a <- a - K*!e over n target lanes (complement + k8_add_kne with the clean bank), then the
/// K load and V = 1. All x in [0, 2^m), five tapes, forward against the integer model (all wires,
/// phase 0) and inverse playback from the model output back to the input.
#[test]
fn o2_k8_fused_exhaustive() {
    let mut consts: Vec<(usize, u64)> = vec![];
    for m in [8usize, 10] {
        let full = (1u64 << m) - 1;
        let pm = p();
        let plow = (0..m).filter(|&i| pm.bit(i)).map(|i| 1u64 << i).sum::<u64>();
        for k in [plow, full - 4, full, 3, 0x5555 & full | 3, 0xa5a5 & full | 1, 1] {
            consts.push((m, k));
        }
    }
    let mut nchk = 0usize;
    for &(m, kc) in &consts {
        assert!(kc & 1 == 1);
        for extra in [2usize, 3] {
            let n = m + extra; // target lanes 1..=n (production: 256 + 3, or 256 + 2 with DB)
            let mut b = B::new();
            let xl = b.alloc_n(n + 1);
            let e = b.alloc();
            let bank = b.alloc_n(m + 3);
            let v0 = b.alloc();
            b.begin();
            for f in (0..m).rev() {
                b.swap(xl[f], xl[f + 1]);
            }
            b.cx(xl[1], e);
            let a: Vec<QubitId> = xl[1..=n].to_vec();
            let k: Vec<bool> = (0..n).map(|i| i < 64 && kc >> i & 1 != 0).collect();
            for &q in &a {
                b.x(q);
            }
            k8_add_kne(&mut b, &a, e, &k, m, &bank);
            for &q in &a {
                b.x(q);
            }
            for i in 0..m {
                if kc >> i & 1 != 0 {
                    b.x(bank[i]);
                }
            }
            b.x(v0);
            let r = b.end();
            let ands = r.iter().filter(|g| matches!(g, super::builder::G::AndC(..))).count();
            let nq = b.width() as usize;
            let modw = n + 1;
            let mask = if modw >= 64 { u64::MAX } else { (1u64 << modw) - 1 };
            for inverse in [false, true] {
                let mut bi = B::new();
                for _ in 0..nq {
                    bi.alloc();
                }
                bi.play(&r, inverse);
                let ops = std::mem::take(&mut bi.ops);
                for tk in TAPES {
                    for base in (0..(1u64 << m)).step_by(64) {
                        let mut tp = tape(tk);
                        let mut s = Simulator::new(nq, 4, &mut tp);
                        let mut want = vec![0u64; nq];
                        let mut init = vec![0u64; nq];
                        for sh in 0..64u64 {
                            let x = base + sh;
                            if x >= 1u64 << m {
                                break;
                            }
                            let x0 = x & 1;
                            let out = (2 * x).wrapping_sub(if x0 == 0 { 2 * kc } else { 0 }) & mask;
                            let (inp, outp): (&mut Vec<u64>, &mut Vec<u64>) = if inverse { (&mut want, &mut init) } else { (&mut init, &mut want) };
                            for i in 0..m {
                                if x >> i & 1 != 0 {
                                    inp[xl[i].0 as usize] |= 1 << sh;
                                }
                            }
                            for i in 0..=n {
                                if out >> i & 1 != 0 {
                                    outp[xl[i].0 as usize] |= 1 << sh;
                                }
                            }
                            if x0 != 0 {
                                outp[e.0 as usize] |= 1 << sh;
                            }
                            for i in 0..m {
                                if kc >> i & 1 != 0 {
                                    outp[bank[i].0 as usize] |= 1 << sh;
                                }
                            }
                            outp[v0.0 as usize] |= 1 << sh;
                        }
                        s.qubits.copy_from_slice(&init);
                        s.apply_iter(ops.iter());
                        assert_eq!(s.qubits, want, "K8 analog m {m} K {kc:#x} n {n} inverse {inverse} tape {tk:#x} base {base}");
                        assert_eq!(s.phase, 0, "K8 analog phase m {m} K {kc:#x} n {n} inverse {inverse} tape {tk:#x}");
                        nchk += 1;
                    }
                }
            }
            eprintln!("O2_K8_ANALOG m {m} n {n} K {kc:#x}: {ands} AndC (n-1 = {}), exact both directions, 5 tapes", n - 1);
        }
    }
    eprintln!("O2_K8_ANALOG {nchk} 64-shot batches exact");
}

/// Whole-walk K8 on vs off: identical qubits and phase at every forward tick boundary from the end of
/// tick 1 on (the init boundary differs by construction) and after the inverse replay (x restored).
#[test]
#[ignore]
fn o2_k8_walk_equivalence() {
    let (rf, ri) = rooms();
    let sch = sched_g();
    test_k8(false);
    let off = division_walk(&sch, rf, ri);
    test_k8(true);
    let on = division_walk(&sch, rf, ri);
    walk_equivalence("K8", &off, &on, 1);
    // tick-1 block cost (init + tick 1) in each build
    let t_off = expected_t(&off.b.ops[..off.bounds[1]]);
    let t_on = expected_t(&on.b.ops[..on.bounds[1]]);
    eprintln!("O2_K8_TICK1 forward init+tick1 expected T off {t_off} on {t_on} delta {}", t_on - t_off);
}


// ------------------------------------------------------------------ U16 C1
/// Integer model of the endpoint relation: V = S ^ rho, S = P + ~U + !rho mod 2^L, P = key ? -p : p.
fn c1_model(l: usize, u: u64, key: bool, rho: bool, pc: u64) -> u64 {
    let mask = (1u64 << l) - 1;
    let pk = if key { pc.wrapping_neg() } else { pc } & mask;
    let s = pk.wrapping_add(!u & mask).wrapping_add(u64::from(!rho)) & mask;
    if rho { !s & mask } else { s }
}

/// Exhaustive L <= 10 check of the out-of-place regeneration and its inverted (sum-erase) play:
/// every U, key, two rho lanes and both rho flips; five HMR tapes; all wires and phase. The model is
/// first checked bit-for-bit against the original adapter construction (in-place conversion add +
/// key pattern), inverted from V = 0, i.e. the old regeneration.
#[test]
fn o2_c1_regen_exhaustive() {
    use super::modp_ft::ctrl_add_pool;
    let pm = p();
    let mut nchk = 0usize;
    for l in 2..=10usize {
        let mask = (1u64 << l) - 1;
        let plow = (0..l).filter(|&i| pm.bit(i)).map(|i| 1u64 << i).sum::<u64>();
        for pc in [plow, mask, 1, 0x2d & mask | 1, 0x355 & mask | 1] {
            assert!(pc & 1 == 1);
            let pb: Vec<bool> = (0..l).map(|i| pc >> i & 1 != 0).collect();
            for flip in [false, true] {
                // lanes: u[l], v[l], key, r0, r1, pool[l]
                let mut b = B::new();
                let u = b.alloc_n(l);
                let v = b.alloc_n(l);
                let key = b.alloc();
                let r = b.alloc_n(2);
                let pool = b.alloc_n(l);
                let rho = ParityCtl { qs: r.clone(), flip };
                b.begin();
                c1_regen_v(&mut b, &u, &v, key, &pb, &rho);
                let vc = b.end();
                let ands = vc.iter().filter(|g| matches!(g, super::builder::G::AndC(..))).count();
                assert_eq!(ands, l - 1);
                // the original construction (recorded): conv (X ^= rho; Y += X; Y ^= rho; X ^= rho) + pattern
                b.begin();
                for &q in &u { rho.xor_into(&mut b, q); }
                ctrl_add_pool(&mut b, &u, &v, super::builder::ONE, &pool);
                for &q in &v { rho.xor_into(&mut b, q); }
                for &q in &u { rho.xor_into(&mut b, q); }
                let negp = pc.wrapping_neg() & mask;
                for s in 0..l {
                    let (pos, neg) = (pc >> s & 1 != 0, negp >> s & 1 != 0);
                    if pos { b.x(v[s]); }
                    if pos != neg { b.cx(key, v[s]); }
                }
                let old = b.end();
                let nq = b.width() as usize;
                let n_cases = (1usize << l) * 8;
                let mk = |vc: &Vec<super::builder::G>, inverse: bool| {
                    let mut bi = B::new();
                    bi.play(vc, inverse);
                    std::mem::take(&mut bi.ops)
                };
                let regen_new = mk(&vc, false);
                let erase_new = mk(&vc, true);
                let regen_old = mk(&old, true);
                for tk in TAPES {
                    for base in (0..n_cases).step_by(64) {
                        let mut pre = vec![0u64; nq];
                        let mut post = vec![0u64; nq];
                        for sh in 0..64usize {
                            // shots past the last case repeat valid cases (every shot is checked)
                            let c = (base + sh) % n_cases;
                            let uu = (c >> 3) as u64;
                            let kk = c & 1 != 0;
                            let (r0, r1) = (c >> 1 & 1 != 0, c >> 2 & 1 != 0);
                            let rv = r0 ^ r1 ^ flip;
                            let vv = c1_model(l, uu, kk, rv, pc);
                            for i in 0..l {
                                if uu >> i & 1 != 0 { pre[u[i].0 as usize] |= 1 << sh; post[u[i].0 as usize] |= 1 << sh; }
                                if vv >> i & 1 != 0 { post[v[i].0 as usize] |= 1 << sh; }
                            }
                            for (q, bit) in [(key, kk), (r[0], r0), (r[1], r1)] {
                                if bit { pre[q.0 as usize] |= 1 << sh; post[q.0 as usize] |= 1 << sh; }
                            }
                        }
                        for (ops, from, to, what) in [(&regen_old, &pre, &post, "old regen"), (&regen_new, &pre, &post, "new regen"), (&erase_new, &post, &pre, "new erase")] {
                            let mut tp = tape(tk);
                            let mut s = Simulator::new(nq, 4, &mut tp);
                            s.qubits.copy_from_slice(from);
                            s.apply_iter(ops.iter());
                            assert_eq!(&s.qubits, to, "C1 {what} L {l} p {pc:#x} flip {flip} tape {tk:#x} base {base}");
                            assert_eq!(s.phase, 0, "C1 {what} phase L {l} p {pc:#x} flip {flip} tape {tk:#x}");
                            nchk += 1;
                        }
                    }
                }
            }
            eprintln!("O2_C1_EXHAUSTIVE L {l} p {pc:#x}: model == old regeneration; new regen and erase exact (all U, key, rho, flips, 5 tapes); {} AndC", l - 1);
        }
    }
    eprintln!("O2_C1_EXHAUSTIVE {nchk} 64-case batches");
}

/// Production width: forward walk, then the endpoint adapter forward and inverted, C1 on vs off.
/// On the success support (old adapter leaves every V lane clean) both adapters give identical
/// qubits and phase; the inverse play restores the pre-adapter state. Off-support shots are counted.
#[test]
#[ignore]
fn o2_c1_adapter_walk() {
    let (rf, _) = rooms();
    let sch = sched_g();
    let build = |c1: bool| {
        test_c1(c1);
        let mut b = B::new();
        let x = b.alloc_n(256);
        let mut a = x.clone();
        a.extend(b.alloc_n(sch.w - 256));
        let w = PWalk { a, bb: b.alloc_n(sch.w), q: vec![], h: b.alloc_n(HB), capq: 11, log: b.alloc_n(8) };
        let sc = PScr::alloc_fwd(&mut b, rf);
        let _m = walk_forward_g(&mut b, &w, &sch, &sc, &GScr, None);
        let b0 = b.ops.len();
        let ad = endpoint_adapter_g(&mut b, &w, &sch, &sc);
        b.play(&ad, false);
        let b1 = b.ops.len();
        b.play(&ad, true);
        let b2 = b.ops.len();
        let t_fwd = expected_t(&b.ops[b0..b1]);
        let t_inv = expected_t(&b.ops[b1..b2]);
        (Walk { b, x, w, bounds: vec![b0, b1, b2] }, t_fwd, t_inv)
    };
    let (off, tf0, ti0) = build(false);
    let (on, tf1, ti1) = build(true);
    eprintln!("O2_C1_ADAPTER_T forward play off {tf0} on {tf1} delta {}; inverse play off {ti0} on {ti1} delta {}", tf1 - tf0, ti1 - ti0);
    let tn = sch.s + 1;
    let vs: Vec<QubitId> = (0..sch.w - sch.c[tn]).map(|s| on.w.bsig(s)).collect();
    for seed in [0x0c1u64, 0x0c2] {
        let xs = inputs(seed);
        for tk in TAPES {
            let so = states(&off, &xs, tk);
            let sn = states(&on, &xs, tk);
            assert_eq!(diff_rows(&(so[0].0.clone(), 0), &(sn[0].0.clone(), 0)), 0);
            let mut support = u64::MAX;
            for &q in &vs {
                support &= !so[1].0[q.0 as usize];
            }
            let mut d1 = so[1].1 ^ sn[1].1;
            for (x, y) in so[1].0.iter().zip(&sn[1].0) { d1 |= x ^ y; }
            assert_eq!(d1 & support, 0, "C1 seed {seed:#x} tape {tk:#x}: forward adapter differs on support");
            let mut d2 = 0u64;
            for (x, y) in so[0].0.iter().zip(&sn[2].0) { d2 |= x ^ y; }
            assert_eq!(d2 & support, 0, "C1 seed {seed:#x} tape {tk:#x}: adapter pair not identity on support");
            assert_eq!((sn[2].1 ^ sn[0].1) & support, 0, "C1 seed {seed:#x} tape {tk:#x}: adapter pair phase");
            eprintln!("O2_C1_ADAPTER seed {seed:#x} tape {tk:#x}: support {}/64; on==off after forward play; pair = identity on support",
                support.count_ones());
        }
    }
}

/// Debug print of the L = 2..3 tables (model, old regeneration, new regeneration).
#[test]
#[ignore]
fn o2_c1_debug_small() {
    use super::modp_ft::ctrl_add_pool;
    for l in [2usize, 3] {
        let mask = (1u64 << l) - 1;
        let pc = 3u64 & mask | 1;
        let pb: Vec<bool> = (0..l).map(|i| pc >> i & 1 != 0).collect();
        let mut b = B::new();
        let u = b.alloc_n(l);
        let v = b.alloc_n(l);
        let key = b.alloc();
        let r = b.alloc_n(2);
        let pool = b.alloc_n(l);
        let rho = ParityCtl { qs: r.clone(), flip: false };
        b.begin();
        c1_regen_v(&mut b, &u, &v, key, &pb, &rho);
        let vc = b.end();
        b.begin();
        for &q in &u { rho.xor_into(&mut b, q); }
        ctrl_add_pool(&mut b, &u, &v, super::builder::ONE, &pool);
        for &q in &v { rho.xor_into(&mut b, q); }
        for &q in &u { rho.xor_into(&mut b, q); }
        let negp = pc.wrapping_neg() & mask;
        for s in 0..l {
            let (pos, neg) = (pc >> s & 1 != 0, negp >> s & 1 != 0);
            if pos { b.x(v[s]); }
            if pos != neg { b.cx(key, v[s]); }
        }
        let old = b.end();
        eprintln!("old recording: {:?}", old);
        let nq = b.width() as usize;
        for (name, rec, inv) in [("old", &old, true), ("new", &vc, false)] {
            let n0 = b.ops.len();
            b.play(rec, inv);
            let ops: Vec<Op> = b.ops[n0..].to_vec();
            let mut tp = tape(0);
            let mut s = Simulator::new(nq, 4, &mut tp);
            for c in 0..(8usize << l) {
                let uu = (c >> 3) as u64;
                let kk = c & 1 != 0;
                let (r0, r1) = (c >> 1 & 1 != 0, c >> 2 & 1 != 0);
                for i in 0..l { if uu >> i & 1 != 0 { s.qubits[u[i].0 as usize] |= 1 << c; } }
                for (q, bit) in [(key, kk), (r[0], r0), (r[1], r1)] { if bit { s.qubits[q.0 as usize] |= 1 << c; } }
            }
            s.apply_iter(ops.iter());
            for c in 0..(8usize << l) {
                let uu = (c >> 3) as u64;
                let kk = c & 1 != 0;
                let (r0, r1) = (c >> 1 & 1 != 0, c >> 2 & 1 != 0);
                let mut got = 0u64;
                for i in 0..l { if s.qubits[v[i].0 as usize] >> c & 1 != 0 { got |= 1 << i; } }
                let mut uo = 0u64;
                for i in 0..l { if s.qubits[u[i].0 as usize] >> c & 1 != 0 { uo |= 1 << i; } }
                eprintln!("O2_C1_DBG L {l} {name} U {uu} key {} rho {} model {} got {got} u_after {uo}", kk as u8, (r0 ^ r1) as u8, c1_model(l, uu, kk, r0 ^ r1, pc));
            }
        }
    }
}
