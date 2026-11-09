//! O1 (R21 W3a) focused primitive checks: all wires, phase, forced X-measurement tapes, both directions.

use super::builder::B;
use super::frogdrop_sched::N;
use super::tests_frogdrop::Rng;
use crate::circuit::{analyze_ops, QubitId};
use crate::sim::Simulator;
use sha3::digest::XofReader;

pub(crate) struct Fixed(pub u8);
impl XofReader for Fixed {
    fn read(&mut self, out: &mut [u8]) {
        out.fill(self.0);
    }
}

/// Forced or pseudo-random X-measurement tape.
pub(crate) enum Tape {
    Fixed(u8),
    Shake(sha3::Shake256Reader),
}
impl XofReader for Tape {
    fn read(&mut self, out: &mut [u8]) {
        match self {
            Tape::Fixed(b) => out.fill(*b),
            Tape::Shake(r) => r.read(out),
        }
    }
}

pub(crate) const TAPES: [u8; 4] = [0x00, 0xff, 0xaa, 0x55];

pub(crate) fn put(w: &mut [u64], qs: &[QubitId], shot: usize, v: N) {
    for (i, q) in qs.iter().enumerate() {
        if v.bit(i) {
            w[q.0 as usize] |= 1 << shot;
        }
    }
}
pub(crate) fn get(w: &[u64], qs: &[QubitId], shot: usize) -> N {
    let mut v = N::ZERO;
    for (i, q) in qs.iter().enumerate() {
        if (w[q.0 as usize] >> shot) & 1 == 1 {
            v |= N::from(1u64) << i;
        }
    }
    v
}
pub(crate) fn mask(n: usize) -> N {
    (N::from(1u64) << n) - N::from(1u64)
}
/// two's complement value of an n-lane register as (negative, magnitude)
fn sext_to(v: N, from: usize, to: usize) -> N {
    if v.bit(from - 1) { (v | (mask(to) ^ mask(from))) & mask(to) } else { v & mask(to) }
}



/// U14 primitive 1: tq <- sext(hi) c mod 2^64, exhaustive over hi for hi widths 3..=8 (w977 = h + 10), recorded build
/// played forward then inverted, every tape (the build has AND erasures only), all wires and phase.
#[test]
fn o1_u14_tq_build_exhaustive() {
    use super::pointadd_lilypad::reduce_tq_build;
    let c = N::from((1u64 << 32) + 977);
    for h in 3..=8usize {
        let mut b = B::new();
        let hi = b.alloc_n(h);
        let tq = b.alloc_n(64);
        let pool = b.alloc_n(64);
        b.begin();
        reduce_tq_build(&mut b, &hi, &tq, &pool);
        let r = b.end();
        let t0 = b.tof;
        b.play(&r, false);
        let tf = b.tof - t0;
        let mid = b.ops.len();
        b.play(&r, true);
        let (_, nb, _, _) = analyze_ops(b.ops.iter());
        for tape in TAPES {
            for batch in 0..(1usize << h).div_ceil(64) {
                let mut xof = Fixed(tape);
                let mut sim = Simulator::new(b.width() as usize, (nb as usize).max(1), &mut xof);
                let vals: Vec<N> = (0..64).map(|s| N::from(((batch * 64 + s) % (1 << h)) as u64)).collect();
                for s in 0..64 {
                    put(&mut sim.qubits, &hi, s, vals[s]);
                }
                let init = sim.qubits.clone();
                sim.apply_iter(b.ops[..mid].iter());
                assert_eq!(sim.phase, 0, "h={h} tape={tape:x}");
                for s in 0..64 {
                    let hv = sext_to(vals[s], h, 64);
                    let want = hv.wrapping_mul(c) & mask(64);
                    assert_eq!(get(&sim.qubits, &tq, s), want, "h={h} hi={} tape={tape:x}", vals[s]);
                    assert_eq!(get(&sim.qubits, &hi, s), vals[s]);
                    assert_eq!(get(&sim.qubits, &pool, s), N::ZERO);
                }
                sim.apply_iter(b.ops[mid..].iter());
                assert_eq!(sim.qubits, init, "h={h} reverse restores");
                assert_eq!(sim.phase, 0);
            }
        }
        eprintln!("O1 U14 tq build h={h}: {tf} T forward, exhaustive over 2^{h} hi x 4 tapes ok");
    }
}

/// U14 primitive 2: lo +=/-= sext(tq) mod 2^n with repeated sign source lanes, exhaustive over (lo, tq) at n = 8, 10 and
/// tq widths 3, 4, full pool and recycled-loan pools, forward and inverted recording, every tape.
#[test]
fn o1_u14_sext_add_exhaustive() {
    use super::pointadd_lilypad::reduce_tq_add;
    for n in [8usize, 10] {
        for k in [3usize, 4] {
            for pool_len in [n - 1, n - 3, n - 4] {
                for sub in [false, true] {
                    let mut b = B::new();
                    let lo = b.alloc_n(n);
                    let tq = b.alloc_n(k);
                    let pool = b.alloc_n(pool_len);
                    b.begin();
                    reduce_tq_add(&mut b, &lo, &tq, &pool, sub);
                    let r = b.end();
                    let t0 = b.tof;
                    b.play(&r, false);
                    let tf = b.tof - t0;
                    let mid = b.ops.len();
                    b.play(&r, true);
                    let (_, nb, _, _) = analyze_ops(b.ops.iter());
                    let total = 1usize << (n + k);
                    for tape in TAPES {
                        for batch in 0..total.div_ceil(64) {
                            let mut xof = Fixed(tape);
                            let mut sim = Simulator::new(b.width() as usize, (nb as usize).max(1), &mut xof);
                            let ins: Vec<(N, N)> = (0..64)
                                .map(|s| {
                                    let v = (batch * 64 + s) % total;
                                    (N::from((v & ((1 << n) - 1)) as u64), N::from((v >> n) as u64))
                                })
                                .collect();
                            for s in 0..64 {
                                put(&mut sim.qubits, &lo, s, ins[s].0);
                                put(&mut sim.qubits, &tq, s, ins[s].1);
                            }
                            let init = sim.qubits.clone();
                            sim.apply_iter(b.ops[..mid].iter());
                            assert_eq!(sim.phase, 0, "n={n} k={k} pool={pool_len} sub={sub} tape={tape:x}");
                            for s in 0..64 {
                                let a = sext_to(ins[s].1, k, n);
                                let m = N::from(1u64) << n;
                                let want = if sub { (ins[s].0 + m - a) & mask(n) } else { (ins[s].0 + a) & mask(n) };
                                assert_eq!(get(&sim.qubits, &lo, s), want);
                                assert_eq!(get(&sim.qubits, &tq, s), ins[s].1);
                                assert_eq!(get(&sim.qubits, &pool, s), N::ZERO);
                            }
                            sim.apply_iter(b.ops[mid..].iter());
                            assert_eq!(sim.qubits, init);
                            assert_eq!(sim.phase, 0);
                        }
                    }
                    eprintln!("O1 U14 sext add n={n} k={k} pool={pool_len} sub={sub}: {tf} T, exhaustive ok");
                }
            }
        }
    }
}

/// U14 production: reduce_ct_fwd then reduce_ct_undo on the 287-lane C' at the live width of the shell (558 owners),
/// caps 872 / 875 / 885 (pools 248 / 251 / 256), edge and random (lo, hi), all four tapes: lo' = lo + hi c mod 2^256,
/// hi and every other wire restored, scratch clean, the undo repays the forward's measurement phase exactly.
#[test]
fn o1_u14_reduce_round_trip() {
    use super::pointadd_lilypad::{reduce_ct_fwd, reduce_ct_undo, test_peak};
    let c = N::from((1u64 << 32) + 977);
    let mut rng = Rng::new(1414);
    for cap in [872u64, 875, 885] {
        let mut b = B::new();
        let other = b.alloc_n(558 - 287);
        let inv = b.alloc_n(287);
        test_peak(Some(cap));
        let t0 = b.tof;
        let m = reduce_ct_fwd(&mut b, &inv);
        let tf = b.tof - t0;
        let peak_fwd = b.peak;
        let mid = b.ops.len();
        let t1 = b.tof;
        reduce_ct_undo(&mut b, &inv, &m);
        let tu = b.tof - t1;
        test_peak(None);
        assert!(b.peak <= cap, "peak {} over cap {cap}", b.peak);
        assert_eq!(b.live, 558);
        let (_, nb, _, _) = analyze_ops(b.ops.iter());
        let edges_hi: [i64; 7] = [-(1 << 30), -1, 0, 1, (1 << 30) - 1, -12345678, 987654321];
        let lo_edges = [N::ZERO, mask(256), mask(256) - N::from(5u64), N::from(1u64) << 255, mask(64)];
        for tape in TAPES {
            for round in 0..4 {
                let mut xof = Fixed(tape);
                let mut sim = Simulator::new(b.width() as usize, (nb as usize).max(1), &mut xof);
                let mut ins = vec![];
                for s in 0..64 {
                    let hv: i64 = if s < 35 && round == 0 { edges_hi[s % 7] } else { (rng.next() as i64) >> 33 };
                    let lv = if s < 35 && round == 0 { lo_edges[s / 7] } else { rng.below(256) };
                    let hn = if hv < 0 { (N::from(1u64) << 31) - N::from((-hv) as u64) } else { N::from(hv as u64) };
                    ins.push((lv, hn));
                    put(&mut sim.qubits, &inv[..256], s, lv);
                    put(&mut sim.qubits, &inv[256..], s, hn);
                    put(&mut sim.qubits, &other, s, rng.below(other.len()));
                }
                let init = sim.qubits.clone();
                sim.apply_iter(b.ops[..mid].iter());
                for s in 0..64 {
                    let (lv, hn) = ins[s];
                    let want = (lv + sext_to(hn, 31, 256).wrapping_mul(c)) & mask(256);
                    assert_eq!(get(&sim.qubits, &inv[..256], s), want, "cap {cap} tape {tape:x} shot {s}");
                    assert_eq!(get(&sim.qubits, &inv[256..], s), hn);
                }
                for q in 0..sim.qubits.len() {
                    let owned = other.iter().chain(&inv).any(|x| x.0 as usize == q);
                    if !owned {
                        assert_eq!(sim.qubits[q], 0, "scratch q{q} dirty after forward");
                    }
                }
                sim.apply_iter(b.ops[mid..].iter());
                assert_eq!(sim.qubits, init, "cap {cap} tape {tape:x}: undo restores every wire");
                assert_eq!(sim.phase, 0, "cap {cap} tape {tape:x}: undo repays the receipts");
            }
        }
        eprintln!("O1 U14 reduce cap {cap}: forward {tf} T, undo {tu} T (base five-add 1224 each way), peak {peak_fwd}");
    }
}

/// Price of the alternatives at the production widths (builder T, no simulation): base five sext adds, RHI (reduce_hi
/// with a 41-lane tq), and this build (C3 + C3b).
#[test]
fn o1_u14_price() {
    use super::modp_ft::{add_sext, reduce_hi, sub_sext};
    for pool_len in [248usize, 251, 256] {
        let mut b = B::new();
        let inv = b.alloc_n(287);
        let pool = b.alloc_n(pool_len.max(255));
        let (lo, hi) = (&inv[..256], &inv[256..]);
        let t0 = b.tof;
        add_sext(&mut b, hi, &lo[32..], &pool);
        add_sext(&mut b, hi, &lo[10..], &pool);
        sub_sext(&mut b, hi, &lo[5..], &pool);
        sub_sext(&mut b, hi, &lo[4..], &pool);
        add_sext(&mut b, hi, lo, &pool);
        let base = b.tof - t0;
        let tq = b.alloc_n(41);
        let t1 = b.tof;
        reduce_hi(&mut b, &inv, &tq, &pool);
        let rhi = b.tof - t1;
        eprintln!("O1 U14 price pool {pool_len}: base {base} RHI {rhi}");
    }
}


fn modp() -> N {
    super::frogdrop_sched::p()
}

/// U22 classical replica: K' = (3 ox + c - 1) mod p from the in-circuit classical ops, against integer arithmetic,
/// over boundary values (every crossing of p, 2p, 3p by 3 ox + c - 1, and 0, 1, p - 1, 2^255) plus 1,000,000 uniform
/// ox < p. Classical ops only (no qubit is touched, 0 T).
#[test]
fn o1_u22_classical_k_replica() {
    let pm = modp();
    let c = N::from((1u64 << 32) + 977);
    let mut b = B::new();
    let ox = b.declare_bits(2, 256);
    let n0 = b.ops.len();
    let kq = super::pointadd_lilypad::classical_3ox_plus_cm1(&mut b, &ox);
    assert_eq!(b.tof, 0);
    // no condition stack: every PushCondition in the stream keeps following its measurement
    assert!(b.ops[n0..].iter().all(|op| !matches!(op.kind, crate::circuit::OperationType::PushCondition | crate::circuit::OperationType::PopCondition)));
    let nops = b.ops.len() - n0;
    let (_, nb, _, _) = analyze_ops(b.ops.iter());
    let three = N::from(3u64);
    let mut edges = vec![N::ZERO, N::from(1u64), N::from(2u64), pm - N::from(1u64), pm - N::from(2u64), N::from(1u64) << 255];
    for k in 1..=3u64 {
        // 3 ox + c - 1 crosses k p
        let t = N::from(k) * pm - c + N::from(1u64);
        let base = t / three;
        for d in 0..4u64 {
            for v in [base + N::from(d), if base >= N::from(d) { base - N::from(d) } else { N::ZERO }] {
                if v < pm {
                    edges.push(v);
                }
            }
        }
    }
    let mut rng = Rng::new(2222);
    let total = 1_000_000usize;
    let mut checked = 0usize;
    let batches = (edges.len() + total).div_ceil(64);
    for batch in 0..batches {
        let mut xof = Fixed(0);
        let mut sim = Simulator::new(b.width().max(1) as usize, (nb as usize).max(1), &mut xof);
        let mut vals = vec![];
        for s in 0..64 {
            let idx = batch * 64 + s;
            let v = if idx < edges.len() {
                edges[idx]
            } else {
                loop {
                    let r = rng.below(256);
                    if r < pm {
                        break r;
                    }
                }
            };
            vals.push(v);
            for i in 0..256 {
                if v.bit(i) {
                    sim.bits[ox[i].0 as usize] |= 1 << s;
                }
            }
        }
        sim.apply_iter(b.ops.iter());
        assert_eq!(sim.phase, 0);
        for s in 0..64 {
            let mut got = N::ZERO;
            for i in 0..256 {
                if (sim.bits[kq[i].0 as usize] >> s) & 1 == 1 {
                    got |= N::from(1u64) << i;
                }
            }
            let want = (three * vals[s] + c - N::from(1u64)) % pm;
            assert_eq!(got, want, "ox = {:x}", vals[s]);
            checked += 1;
        }
    }
    eprintln!("O1 U22 classical K' replica: {checked} ox values ({} boundary) exact; {nops} classical ops, 0 T", edges.len());
}

/// U22 slot equivalence: x <- -x - 3 ox mod p by (X all; modsub of the classical K') against the base (ctrl_neg;
/// three classical modsubs of ox) and integer arithmetic, all wires, phase and scratch, four forced tapes.
#[test]
fn o1_u22_slot_equivalence() {
    use super::modp_ft::{ctrl_neg, modadd_classical, Ms};
    let pm = modp();
    let c = N::from((1u64 << 32) + 977);
    let mut rng = Rng::new(2323);
    for variant in 0..2 {
        let mut b = B::new();
        let x = b.alloc_n(256);
        let ox = b.declare_bits(2, 256);
        let t0 = b.tof;
        if variant == 0 {
            let ms = Ms::alloc_room(&mut b, 875);
            ctrl_neg(&mut b, &ms, &x, None);
            ms.release(&mut b);
            let ms = Ms::alloc_room(&mut b, 875);
            for _ in 0..3 {
                modadd_classical(&mut b, &ms, &x, &ox, true);
            }
            ms.release(&mut b);
        } else {
            let kq = super::pointadd_lilypad::classical_3ox_plus_cm1(&mut b, &ox);
            for &q in &x {
                b.x(q);
            }
            let ms = Ms::alloc_room(&mut b, 875);
            modadd_classical(&mut b, &ms, &x, &kq, true);
            ms.release(&mut b);
        }
        let native = b.tof - t0;
        let expected = b.tof as f64 - b.tof_cond as f64 / 2.0;
        let (nq, nb, _, _) = analyze_ops(b.ops.iter());
        let mut edge_fail = vec![];
        for tape in TAPES {
            for round in 0..8 {
                let mut xof = Fixed(tape);
                let mut sim = Simulator::new((nq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
                let mut ins = vec![];
                for s in 0..64 {
                    let xv = if round == 0 && s < 8 {
                        [N::ZERO, N::from(1u64), c - N::from(2u64), c - N::from(1u64), c, pm - N::from(1u64), N::from(1u64) << 255, c + c][s]
                    } else {
                        rng.below(256) % pm
                    };
                    let ov = if round == 1 && s < 4 { [N::ZERO, N::from(1u64), pm - N::from(1u64), (pm - N::from(1u64)) / N::from(3u64)][s] } else { rng.below(256) % pm };
                    put(&mut sim.qubits, &x, s, xv);
                    for i in 0..256 {
                        if ov.bit(i) {
                            sim.bits[ox[i].0 as usize] |= 1 << s;
                        }
                    }
                    ins.push((xv, ov));
                }
                sim.apply_iter(b.ops.iter());
                for s in 0..64 {
                    let (xv, ov) = ins[s];
                    let want = (pm * N::from(4u64) - xv - N::from(3u64) * ov) % pm;
                    let got = get(&sim.qubits, &x, s);
                    if round == 0 && s < 8 {
                        if got != want {
                            edge_fail.push(s);
                        }
                    } else {
                        assert_eq!(got, want, "variant {variant} tape {tape:x} x {xv:x} ox {ov:x}");
                    }
                }
                let live_mask = if round == 0 { !0xffu64 } else { u64::MAX };
                assert_eq!(sim.phase & live_mask, 0, "variant {variant} tape {tape:x} round {round} phase");
                for q in 0..sim.qubits.len() {
                    if !x.iter().any(|v| v.0 as usize == q) {
                        let dirty = sim.qubits[q] & if round == 0 { !0xffu64 } else { u64::MAX };
                        assert_eq!(dirty, 0, "variant {variant} scratch q{q}");
                    }
                }
            }
        }
        edge_fail.sort();
        edge_fail.dedup();
        eprintln!("O1 U22 slot variant {variant} ({}): native {native} T, expected {expected:.1} T; edge x in [0,1,c-2,c-1,c,p-1,2^255,2c] mismatching at {:?}",
            if variant == 0 { "base" } else { "K' modsub" }, edge_fail);
    }
}



/// Simulate a z-only circuit on 64 shots; returns (z values, phase, all non-z wires clean).
fn run_z(b: &B, z_in: &[QubitId], z_out: &[QubitId], vals: &[N], tape: u8, keep: &[QubitId]) -> (Vec<N>, u64, bool) {
    let (nq, nb, _, _) = analyze_ops(b.ops.iter());
    let mut xof = Fixed(tape);
    let mut sim = Simulator::new((nq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
    for s in 0..64 {
        put(&mut sim.qubits, z_in, s, vals[s % vals.len()]);
    }
    for &q in keep {
        sim.qubits[q.0 as usize] = u64::MAX;
    }
    sim.apply_iter(b.ops.iter());
    let out: Vec<N> = (0..64).map(|s| get(&sim.qubits, z_out, s)).collect();
    let clean = (0..sim.qubits.len()).all(|q| {
        z_out.iter().any(|v| v.0 as usize == q) || keep.iter().any(|v| v.0 as usize == q) || sim.qubits[q] == 0
    });
    (out, sim.phase, clean)
}

/// U11 blocks: every k-bit Montgomery halving and doubling block (k = 5..=22) at the exact pool it needs, against
/// integer z 2^-+k mod p, on edge values (0, 2^200, p - 1, 2^255, p - 2^k, 12345 2^60, every z_low pattern for k <= 8)
/// and random z (z < S c, ~2^-200, is the inherited fold4 class and is not an edge here),
/// four forced tapes; halve-then-double restores z exactly (both directions); scratch clean and phase 0. Prints each
/// block's T against the priced cost.
#[test]
fn o1_u11_mont_blocks() {
    use super::modp_ft::{mont_cost, mont_double_k, mont_halve_k, mont_pool};
    let pm = modp();
    let mut rng = Rng::new(1111);
    for k in 5..=22usize {
        let inv2k = N::from(2u64).pow_mod(pm - N::from(2u64), pm).pow_mod(N::from(k as u64), pm);
        let two_k = N::from(1u64) << k;
        let mut b = B::new();
        let z = b.alloc_n(256);
        let pool = b.alloc_n(mont_pool(k));
        let mut zz = z.clone();
        let t0 = b.tof;
        mont_halve_k(&mut b, &pool, &mut zz, k);
        let th = b.tof - t0;
        let z_half = zz.clone();
        let t1 = b.tof;
        mont_double_k(&mut b, &pool, &mut zz, k);
        let td = b.tof - t1;
        assert_eq!(th as usize, mont_cost(k, false), "k={k} halving cost");
        assert_eq!(td as usize, mont_cost(k, true), "k={k} doubling cost");
        // circuit with only the halving, to read the midpoint
        let mut bh = B::new();
        let zh = bh.alloc_n(256);
        let poolh = bh.alloc_n(mont_pool(k));
        let mut zhh = zh.clone();
        mont_halve_k(&mut bh, &poolh, &mut zhh, k);
        let lows = if k <= 8 { 1usize << k } else { 0 };
        let rounds = (lows.div_ceil(64)).max(2) + 2;
        for tape in TAPES {
            for round in 0..rounds {
                let vals: Vec<N> = (0..64)
                    .map(|s| {
                        let idx = round * 64 + s;
                        if idx < lows {
                            ((rng.below(256) % pm) & !mask(k)) | N::from(idx as u64)
                        } else if round == rounds - 1 && s < 6 {
                            [N::ZERO, N::from(1u64) << 200, pm - N::from(1u64), N::from(1u64) << 255, pm - two_k, N::from(12345u64) << 60][s]
                        } else {
                            rng.below(256) % pm
                        }
                    })
                    .map(|v| if v >= pm { v - pm } else { v })
                    .collect();
                let (half, ph, clean) = run_z(&bh, &zh, &zhh, &vals, tape, &[]);
                assert_eq!(ph, 0, "k={k} halve phase");
                assert!(clean, "k={k} halve scratch");
                for s in 0..64 {
                    assert_eq!(half[s], vals[s].mul_mod(inv2k, pm), "k={k} tape {tape:x} z={:x}", vals[s]);
                }
                let (back, ph2, clean2) = run_z(&b, &z, &zz, &vals, tape, &[]);
                assert_eq!(ph2, 0, "k={k} round trip phase");
                assert!(clean2, "k={k} round trip scratch");
                assert_eq!(zz, z, "k={k} lane order restored");
                for s in 0..64 {
                    assert_eq!(back[s], vals[s], "k={k} round trip z={:x}", vals[s]);
                }
            }
        }
        // doubling alone against integer arithmetic
        let mut bd = B::new();
        let zd = bd.alloc_n(256);
        let poold = bd.alloc_n(mont_pool(k));
        let mut zdd = zd.clone();
        mont_double_k(&mut bd, &poold, &mut zdd, k);
        for tape in TAPES {
            let vals: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
            let (dbl, ph, clean) = run_z(&bd, &zd, &zdd, &vals, tape, &[]);
            assert_eq!(ph, 0);
            assert!(clean);
            for s in 0..64 {
                assert_eq!(dbl[s] % pm, vals[s].mul_mod(two_k % pm, pm), "k={k} double z={:x}", vals[s]);
            }
        }
        let _ = z_half;
        eprintln!("O1 U11 block k={k}: halving {th} T, doubling {td} T (fold4 {} per {k}), pool {}", 74 * k / 4, mont_pool(k));
    }
}

/// U11 source probe: mod_halve_n / mod_double_n by 275 and 19 with the planned Montgomery blocks against integer
/// arithmetic and against the inherited fold4 route (pool 81 forces it), 4 tapes x 64 random z; prints the T of both.
#[test]
fn o1_u11_scale_n_probe() {
    use super::modp_ft::{mod_double_n, mod_halve_n, mont_plan, Ms};
    let pm = modp();
    let mut rng = Rng::new(1112);
    let inv2 = N::from(2u64).pow_mod(pm - N::from(2u64), pm);
    for (n, double) in [(275usize, false), (275, true), (19, false)] {
        let mut tees = vec![];
        for pool_len in [256usize, 81] {
            let mut b = B::new();
            let z = b.alloc_n(256);
            let k = b.alloc();
            let r = b.alloc_n(pool_len);
            let one = b.alloc();
            b.x(one);
            let ms = Ms { k, r, one };
            let mut zz = z.clone();
            let t0 = b.tof;
            if double {
                mod_double_n(&mut b, &ms, &mut zz, n);
            } else {
                mod_halve_n(&mut b, &ms, &mut zz, n);
            }
            let t = b.tof - t0;
            b.x(one);
            let f = if double { N::from(2u64).pow_mod(N::from(n as u64), pm) } else { inv2.pow_mod(N::from(n as u64), pm) };
            for tape in TAPES {
                let vals: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
                let (out, ph, clean) = run_z(&b, &z, &zz, &vals, tape, &[]);
                assert_eq!(ph, 0);
                assert!(clean, "n={n} double={double} pool={pool_len} scratch");
                for s in 0..64 {
                    assert_eq!(out[s] % pm, vals[s].mul_mod(f, pm), "n={n} double={double} pool={pool_len}");
                }
            }
            tees.push((pool_len, t, mont_plan(n, pool_len, double)));
        }
        eprintln!("O1 U11 scale n={n} double={double}: {:?}", tees);
    }
}

/// U11 window census: inputs that force a k = 17 halving block's borrow past its window (z lanes 48..79 zero below a
/// borrow) and the fold4 route on the same inputs: reports which route mis-reduces (both drop at <= 2^-31 per window).
#[test]
fn o1_u11_window_census() {
    use super::modp_ft::{mod_halve_n, mont_halve_k, mont_pool, Ms};
    let pm = modp();
    let mut rng = Rng::new(1113);
    let k = 17usize;
    let inv2k = N::from(2u64).pow_mod(pm - N::from(2u64), pm).pow_mod(N::from(k as u64), pm);
    let mut bm = B::new();
    let zm = bm.alloc_n(256);
    let poolm = bm.alloc_n(mont_pool(k));
    let mut zmm = zm.clone();
    mont_halve_k(&mut bm, &poolm, &mut zmm, k);
    let mut bf = B::new();
    let zf = bf.alloc_n(256);
    let kq = bf.alloc();
    let r = bf.alloc_n(90);
    let one = bf.alloc();
    bf.x(one);
    let ms = Ms { k: kq, r, one };
    let mut zff = zf.clone();
    for _ in 0..4 {
        super::modp_ft::mod_halve4(&mut bf, &ms, &mut zff);
    }
    let _ = mod_halve_n;
    bf.x(one);
    // z with lanes 32..80 zero: the block's subtrahend Y >= 2^32 borrows through the window's top
    let vals: Vec<N> = (0..64).map(|_| (rng.below(256) % pm) & !(mask(80) ^ mask(32))).collect();
    let (outm, _, _) = run_z(&bm, &zm, &zmm, &vals, 0xaa, &[]);
    let (outf, _, _) = run_z(&bf, &zf, &zff, &vals, 0xaa, &[]);
    let want: Vec<N> = vals.iter().map(|v| v.mul_mod(inv2k, pm)).collect();
    let bad_m = (0..64).filter(|&s| outm[s] != want[s]).count();
    let want4: Vec<N> = vals.iter().map(|v| v.mul_mod(N::from(2u64).pow_mod(pm - N::from(2u64), pm).pow_mod(N::from(16u64), pm), pm)).collect();
    let bad_f = (0..64).filter(|&s| outf[s] != want4[s]).count();
    eprintln!("O1 U11 window census (z lanes 32..80 zero): k=17 block mis-reduces {bad_m}/64, 4 x fold4 mis-reduces {bad_f}/64");
}



/// U20 primitive: const_add_pool / const_add_recycled with h = ONE (sentinel) against the same fold with h = a |1>
/// lane, exhaustive over t at n = 6, 8, 10 for sparse constants (every lowest-set-bit position class, odd and even, top
/// bit set or not) and every carry route (full pool, topless, multi-topless shortages 2..5); recorded and played
/// forward then inverted; four forced tapes; all wires and phase.
#[test]
fn o1_u20_const_add_one_exhaustive() {
    use super::builder::ONE;
    use super::modp_ft::const_add_pool;
    let mut checked = 0usize;
    for n in [6usize, 8, 10] {
        let ks: Vec<u64> = vec![1, 3, (1u64 << (n - 1)) | 1, 0b1010_0101 & ((1u64 << n) - 1), 2, 4 | 16, (1u64 << n) - 1, (1u64 << (n - 1)) + 2, 0b110];
        for &k in &ks {
            if k == 0 || k >= (1u64 << n) {
                continue;
            }
            let i0 = k.trailing_zeros() as usize;
            let need = n - 1 - i0;
            for short in 0..=5usize {
                if short > need || need - short == 0 {
                    continue;
                }
                let pool_len = need - short;
                if short >= 2 {
                    let tail_len = short + 1;
                    if n < tail_len + 1 || i0 >= n - tail_len || (n - tail_len) - i0 < tail_len.saturating_sub(2) {
                        continue;
                    }
                }
                let mut outs = vec![];
                for use_one in [true, false] {
                    let mut b = B::new();
                    let t = b.alloc_n(n);
                    let pool = b.alloc_n(pool_len);
                    let lane = b.alloc();
                    let h = if use_one { ONE } else { lane };
                    b.begin();
                    const_add_pool(&mut b, &t, h, k, &pool);
                    let r = b.end();
                    let t0 = b.tof;
                    b.play(&r, false);
                    let tf = b.tof - t0;
                    let mid = b.ops.len();
                    b.play(&r, true);
                    let (_, nb, _, _) = analyze_ops(b.ops.iter());
                    for tape in TAPES {
                        for batch in 0..(1usize << n).div_ceil(64) {
                            let mut xof = Fixed(tape);
                            let mut sim = Simulator::new(b.width() as usize, (nb as usize).max(1), &mut xof);
                            let vals: Vec<u64> = (0..64).map(|s| ((batch * 64 + s) % (1 << n)) as u64).collect();
                            for s in 0..64 {
                                put(&mut sim.qubits, &t, s, N::from(vals[s]));
                            }
                            if !use_one {
                                sim.qubits[lane.0 as usize] = u64::MAX;
                            }
                            let init = sim.qubits.clone();
                            sim.apply_iter(b.ops[..mid].iter());
                            assert_eq!(sim.phase, 0, "n={n} k={k} short={short} one={use_one} tape={tape:x}");
                            for s in 0..64 {
                                assert_eq!(get(&sim.qubits, &t, s), N::from((vals[s] + k) & ((1 << n) - 1)), "n={n} k={k} short={short} one={use_one}");
                                assert_eq!(get(&sim.qubits, &pool, s), N::ZERO);
                            }
                            sim.apply_iter(b.ops[mid..].iter());
                            assert_eq!(sim.qubits, init);
                            assert_eq!(sim.phase, 0);
                            checked += 64;
                        }
                    }
                    outs.push(tf);
                }
                assert!(outs[0] <= outs[1], "ONE lowering must not cost more: n={n} k={k} short={short} {outs:?}");
            }
        }
    }
    eprintln!("O1 U20 const_add_pool ONE vs |1> lane: {checked} cases exact (both directions, 4 tapes)");
}

/// U20 production-width folds and compares with the sentinel: the 64-lane constant folds at the binder pools 57 / 60
/// (recycled carry prefix) with h = ONE; carry_erase_cin with cin = ONE (n = 1..6 exhaustive); every check against
/// the |1>-lane form, four tapes, both directions.
#[test]
fn o1_u20_fold_compare_one() {
    use super::builder::ONE;
    use super::modp_ft::{const_add_pool, C};
    let mut rng = Rng::new(2020);
    for pool_len in [57usize, 58, 60, 63] {
        for k in [C, (C - 1) >> 1, 0x9E37_79B9u64.wrapping_neg(), 0x9E37_79B9u64] {
            let mut b = B::new();
            let t = b.alloc_n(64);
            let pool = b.alloc_n(pool_len);
            b.begin();
            const_add_pool(&mut b, &t, ONE, k, &pool);
            let r = b.end();
            let t0 = b.tof;
            b.play(&r, false);
            let tf = b.tof - t0;
            let mid = b.ops.len();
            b.play(&r, true);
            let (_, nb, _, _) = analyze_ops(b.ops.iter());
            for tape in TAPES {
                let mut xof = Fixed(tape);
                let mut sim = Simulator::new(b.width() as usize, (nb as usize).max(1), &mut xof);
                let vals: Vec<N> = (0..64).map(|s| if s < 3 { [N::ZERO, mask(64), mask(64) - N::from(k)][s] } else { rng.below(64) }).collect();
                for s in 0..64 {
                    put(&mut sim.qubits, &t, s, vals[s]);
                }
                let init = sim.qubits.clone();
                sim.apply_iter(b.ops[..mid].iter());
                assert_eq!(sim.phase, 0);
                for s in 0..64 {
                    assert_eq!(get(&sim.qubits, &t, s), (vals[s] + N::from(k)) & mask(64), "pool {pool_len} k {k:x}");
                    assert_eq!(get(&sim.qubits, &pool, s), N::ZERO);
                }
                sim.apply_iter(b.ops[mid..].iter());
                assert_eq!(sim.qubits, init);
                assert_eq!(sim.phase, 0);
            }
            eprintln!("O1 U20 64-lane fold h=ONE pool {pool_len} k {k:#x}: {tf} T");
        }
    }
    for n in 1..=6usize {
        for ctl_one in [true, false] {
            let mut b = B::new();
            let a = b.alloc_n(n);
            let t = b.alloc_n(n);
            let flag = b.alloc();
            let pool = b.alloc_n(n);
            let cq = b.alloc();
            b.begin();
            b.carry_erase_cin(&a, &t, if ctl_one { ONE } else { cq }, flag, &pool, Some(ONE));
            let r = b.end();
            b.play(&r, false);
            let mid = b.ops.len();
            b.play(&r, true);
            let (_, nb, _, _) = analyze_ops(b.ops.iter());
            let m = (1u64 << n) - 1;
            for tape in TAPES {
                for batch in 0..(1usize << (2 * n)).div_ceil(64) {
                    let mut xof = Fixed(tape);
                    let mut sim = Simulator::new(b.width() as usize, (nb as usize).max(1), &mut xof);
                    let mut ins = vec![];
                    for s in 0..64 {
                        let v = ((batch * 64 + s) % (1 << (2 * n))) as u64;
                        let (av, tv) = (v & m, v >> n);
                        let ctl = if ctl_one { 1 } else { (s as u64 / 3) & 1 };
                        let f = ctl & ((av + tv + 1) >> n);
                        sim.qubits[cq.0 as usize] |= ctl << s;
                        put(&mut sim.qubits, &a, s, N::from(av));
                        put(&mut sim.qubits, &t, s, N::from(tv));
                        sim.qubits[flag.0 as usize] |= f << s;
                        ins.push((av, tv));
                    }
                    let init = sim.qubits.clone();
                    sim.apply_iter(b.ops[..mid].iter());
                    assert_eq!(sim.phase, 0, "carry_erase cin=ONE n={n} ctl_one={ctl_one} tape={tape:x}");
                    assert_eq!(sim.qubits[flag.0 as usize], 0);
                    for q in &pool {
                        assert_eq!(sim.qubits[q.0 as usize], 0);
                    }
                    sim.apply_iter(b.ops[mid..].iter());
                    assert_eq!(sim.qubits, init);
                    assert_eq!(sim.phase, 0);
                }
            }
        }
    }
    eprintln!("O1 U20 carry_erase_cin(cin = ONE) exhaustive n = 1..6, both controls, 4 tapes ok");
}

/// U20 modular ops with the sentinel Ms (no |1> lane): modsub (signed_modadd s = ONE), the fused signed halve/double
/// tables with a constant sign, ctrl_neg(None), and the classical modsub, at pools 57 / 60 / 75 / 256, against integer
/// arithmetic, four tapes; scratch clean and phase 0.
#[test]
fn o1_u20_modular_ops_one() {
    use super::builder::ONE;
    use super::modp_ft::{ctrl_neg, modadd_classical, modsub, signed_modadd_double, signed_modadd_halve, Ms};
    let pm = modp();
    let inv2 = N::from(2u64).pow_mod(pm - N::from(2u64), pm);
    let mut rng = Rng::new(2021);
    for pool_len in [57usize, 60, 64, 65, 75, 256] {
        for op in 0..5 {
            let mut b = B::new();
            let z = b.alloc_n(256);
            let y = b.alloc_n(256);
            let ox = b.declare_bits(2, 256);
            let k = b.alloc();
            let r = b.alloc_n(pool_len);
            let ms = Ms { k, r: r.clone(), one: ONE };
            let mut zz = z.clone();
            let t0 = b.tof;
            match op {
                0 => modsub(&mut b, &ms, &z, &y, k),
                1 => signed_modadd_halve(&mut b, &ms, &mut zz, &y, Some(ONE)),
                2 => signed_modadd_double(&mut b, &ms, &mut zz, &y, Some(ONE)),
                3 => ctrl_neg(&mut b, &ms, &z, None),
                _ => {
                    if pool_len < 256 {
                        continue;
                    }
                    modadd_classical(&mut b, &ms, &z, &ox, true)
                }
            }
            let e = (b.tof - t0) as f64;
            let (nq, nb, _, _) = analyze_ops(b.ops.iter());
            for tape in TAPES {
                let mut xof = Fixed(tape);
                let mut sim = Simulator::new((nq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
                let mut ins = vec![];
                for s in 0..64 {
                    let zv = rng.below(256) % pm;
                    let zv = if zv.is_zero() { N::from(5u64) } else { zv };
                    let yv = rng.below(256) % pm;
                    put(&mut sim.qubits, &z, s, zv);
                    put(&mut sim.qubits, &y, s, yv);
                    for i in 0..256 {
                        if yv.bit(i) {
                            sim.bits[ox[i].0 as usize] |= 1 << s;
                        }
                    }
                    ins.push((zv, yv));
                }
                sim.apply_iter(b.ops.iter());
                assert_eq!(sim.phase, 0, "pool {pool_len} op {op} tape {tape:x}");
                for s in 0..64 {
                    let (zv, yv) = ins[s];
                    let d = (zv + pm - yv) % pm;
                    let want = match op {
                        0 | 4 => d,
                        1 => d.mul_mod(inv2, pm),
                        2 => d.mul_mod(N::from(2u64), pm),
                        _ => pm - zv,
                    };
                    let got = get(&sim.qubits, &zz, s);
                    assert_eq!(got, want, "pool {pool_len} op {op} tape {tape:x} shot {s}");
                    assert_eq!(get(&sim.qubits, &y, s), yv);
                }
                for q in r.iter().chain([&k]) {
                    assert_eq!(sim.qubits[q.0 as usize], 0, "pool {pool_len} op {op}: scratch");
                }
            }
            eprintln!("O1 U20 op {op} (0 modsub, 1 halve s=ONE, 2 double s=ONE, 3 ctrl_neg None, 4 classical modsub) pool {pool_len}: {e} T emitted");
        }
    }
}



/// U21 (exact) primitive: offset_start_exact then offset_end_exact at the slot-6 pools (56 / 57 / 59 / 60) and a full
/// pool: after the start z = ([c0 = 0] y + K) mod 2^256 exactly, with the carry run through every high lane (y = p - 1,
/// y = 2^256 - 1, y lanes 64..96 all ones, y = 2^64 - K, ...) as edges; the end restores every wire, phase 0, four tapes.
#[test]
fn o1_u21x_offset_exact_primitive() {
    use super::modp_ft::{test_offset_exact, Ms};
    let k = test_offset_exact(None);
    let pm = super::frogdrop_sched::p();
    let mut rng = Rng::new(2122);
    for pool_len in [56usize, 57, 59, 60, 70] {
        let mut b = B::new();
        let z = b.alloc_n(256);
        let y = b.alloc_n(256);
        let c0 = b.alloc();
        let flag = b.alloc();
        let pool = b.alloc_n(pool_len);
        let one = b.alloc();
        b.x(one);
        let ms = Ms { k: flag, r: pool.clone(), one };
        let t0 = b.tof;
        test_offset_exact(Some((&mut b, &ms, &z, &y, c0, false)));
        let ts = b.tof - t0;
        let mid = b.ops.len();
        let t1 = b.tof;
        test_offset_exact(Some((&mut b, &ms, &z, &y, c0, true)));
        let te = b.tof - t1;
        b.x(one);
        let (_, nb, _, _) = analyze_ops(b.ops.iter());
        for tape in TAPES {
            for round in 0..4 {
                let mut xof = Fixed(tape);
                let mut sim = Simulator::new(b.width() as usize, (nb as usize).max(1), &mut xof);
                let mut ins = vec![];
                for s in 0..64 {
                    let yv = match (round, s % 8) {
                        (0, 0) => pm - N::from(1u64),
                        (0, 1) => mask(256),
                        (0, 2) => mask(96) ^ mask(64) | rng.below(64),
                        (0, 3) => (N::from(1u64) << 64) - N::from(k),
                        (0, 4) => mask(256) - N::from(k) + N::from(1u64),
                        (0, 5) => N::ZERO,
                        _ => rng.below(256),
                    };
                    let cv = (s / 8 + round) as u64 & 1;
                    put(&mut sim.qubits, &y, s, yv);
                    sim.qubits[c0.0 as usize] |= cv << s;
                    ins.push((yv, cv));
                }
                let init = sim.qubits.clone();
                sim.apply_iter(b.ops[..mid].iter());
                assert_eq!(sim.phase, 0, "pool {pool_len} tape {tape:x}");
                for s in 0..64 {
                    let (yv, cv) = ins[s];
                    let a = if cv == 0 { yv } else { N::ZERO };
                    assert_eq!(get(&sim.qubits, &z, s), (a + N::from(k)) & mask(256), "pool {pool_len} tape {tape:x} y {yv:x} c0 {cv}");
                    assert_eq!(get(&sim.qubits, &pool, s), N::ZERO);
                }
                assert_eq!(sim.qubits[flag.0 as usize], 0);
                sim.apply_iter(b.ops[mid..].iter());
                assert_eq!(sim.qubits, init, "pool {pool_len} tape {tape:x}: end restores");
                assert_eq!(sim.phase, 0);
            }
        }
        eprintln!("O1 U21x exact offset start/end pool {pool_len}: start {ts} T, end {te} T, K = {k:#x}");
    }
}

/// U21 (exact) tail, differential: product_tail_neg_s_offset + paired uncompute with the exact start/end against the
/// same functions routed through the inherited xor + ctrl_modadd start (test switch), at the slot-6 pools 56 / 59 / 75,
/// four forced and four SHAKE tapes, both c0 values, edges y = p - 1, p - K, p - K - 1, 2^256 - K, 2^256 - K - 1, 2 and
/// random y: outside the declared class {c0 = 0, y in [2^256 - K, p)} (where the base folds an overflow that the exact
/// start wraps, ~2^-192.7 per shot) every shot must be correct (z_mid, phase, all wires) or one the base also fails.
/// Prints the expected T of both forms, inherited failures, and base-only failures the exact start does not have.
#[test]
fn o1_u21x_offset_tail() {
    use super::frogdrop_sched::p;
    use super::modp_ft::{
        fix_pair_begin_repay, fix_pair_begin_save, fix_pair_end_repay, fix_pair_end_save, fix_pair_test_reset,
        product_tail_neg_s_offset, product_tail_neg_s_offset_uncompute, test_offset_base_start, test_offset_exact, Ms,
    };
    use sha3::digest::{ExtendableOutput, Update};
    let pm = p();
    let kk = N::from(test_offset_exact(None));
    let two256 = N::from(1u64) << 256;
    let inv2_256 = N::from(2u64).pow_mod(pm - N::from(2u64), pm).pow_mod(N::from(256u64), pm);
    for pool_len in [56usize, 59, 75] {
        let mut circuits = vec![];
        for base in [true, false] {
            fix_pair_test_reset();
            test_offset_base_start(base);
            let mut b = B::new();
            let (a, y) = (b.alloc_n(256), b.alloc_n(256));
            let flag = b.alloc();
            let pool = b.alloc_n(pool_len);
            let one = b.alloc();
            b.x(one);
            let ms = Ms { k: flag, r: pool.clone(), one };
            let z = b.alloc_n(256);
            let mut zz = z.clone();
            let (t0, c0) = (b.tof, b.tof_cond);
            fix_pair_begin_save(0);
            product_tail_neg_s_offset(&mut b, &ms, &mut zz, &a, &y, 256);
            fix_pair_end_save();
            let e_fwd = (b.tof - t0) as f64 - (b.tof_cond - c0) as f64 / 2.0;
            let mid = b.ops.len();
            let z_mid = zz.clone();
            let (t1, c1) = (b.tof, b.tof_cond);
            fix_pair_begin_repay();
            product_tail_neg_s_offset_uncompute(&mut b, &ms, &mut zz, &a, &y, 256);
            fix_pair_end_repay();
            let e_unc = (b.tof - t1) as f64 - (b.tof_cond - c1) as f64 / 2.0;
            assert_eq!(zz, z);
            b.x(one);
            test_offset_base_start(false);
            circuits.push((b, a, y, z_mid, mid, e_fwd, e_unc));
        }
        let mut rng = Rng::new(0x2122 ^ pool_len as u64);
        let (mut shots, mut in_class, mut both_wrong, mut base_only) = (0, 0, 0, 0);
        for tape in 0..8usize {
            let mut ins = vec![];
            for s in 0..64 {
                let mut av = rng.below(256) % pm;
                let mut yv = rng.below(256) % pm;
                if yv <= N::from(1u64) {
                    yv = N::from(3u64);
                }
                if tape <= 1 && s < 24 {
                    let e = [pm - N::from(1u64), N::from(2u64), pm - kk, pm - kk - N::from(1u64), two256 - kk, two256 - kk - N::from(1u64)];
                    yv = e[s % 6];
                    av = (av & !N::from(1u64)) | N::from((s / 6) as u64 & 1);
                }
                ins.push((av, yv));
            }
            let class = |s: usize| !ins[s].0.bit(0) && ins[s].1 >= two256 - kk;
            let mut outs = vec![];
            for (b, a, y, z_mid, mid, _, _) in &circuits {
                let (nq, nb, _, _) = analyze_ops(b.ops.iter());
                let mut xof = if tape < 4 {
                    Tape::Fixed(TAPES[tape])
                } else {
                    let mut h = sha3::Shake256::default();
                    h.update(b"o1-u21x-offset-tail");
                    h.update(&[tape as u8, pool_len as u8]);
                    Tape::Shake(h.finalize_xof())
                };
                let mut sim = Simulator::new((nq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
                for s in 0..64 {
                    put(&mut sim.qubits, a, s, ins[s].0);
                    put(&mut sim.qubits, y, s, ins[s].1);
                }
                sim.apply_iter(b.ops[..*mid].iter());
                let zm: Vec<N> = (0..64).map(|s| get(&sim.qubits, z_mid, s)).collect();
                sim.apply_iter(b.ops[*mid..].iter());
                outs.push((zm, sim.qubits.clone(), sim.phase));
            }
            // per shot: correct = z_mid right, phase 0, every non-input wire clean, inputs restored
            let ok = |o: &(Vec<N>, Vec<u64>, u64), s: usize, a: &[QubitId], y: &[QubitId]| -> bool {
                let (av, yv) = ins[s];
                let want = (pm - av.mul_mod(yv, pm).mul_mod(inv2_256, pm)) % pm;
                if o.0[s] % pm != want || (o.2 >> s) & 1 == 1 {
                    return false;
                }
                if get(&o.1, a, s) != av || get(&o.1, y, s) != yv {
                    return false;
                }
                (0..o.1.len()).all(|q| a.iter().chain(y).any(|v| v.0 as usize == q) || (o.1[q] >> s) & 1 == 0)
            };
            let (a, y) = (&circuits[1].1, &circuits[1].2);
            for s in 0..64 {
                if class(s) {
                    in_class += 1;
                    continue;
                }
                shots += 1;
                let (bo, mo) = (ok(&outs[0], s, a, y), ok(&outs[1], s, a, y));
                if mo {
                    if !bo {
                        base_only += 1;
                    }
                    continue;
                }
                // the exact start may fail only where the base also fails (failure-set inclusion)
                assert!(!bo, "pool {pool_len} tape {tape} shot {s}: exact start fails where the base succeeds");
                both_wrong += 1;
            }
        }
        eprintln!(
            "O1 U21x offset tail pool {pool_len}: {shots} shots outside the declared class: exact start correct or failing only where the base fails ({both_wrong} inherited failures; {base_only} base-only failures fixed), {in_class} declared-class edge shots; compute T base {:.1} -> {:.1}, uncompute {:.1} -> {:.1}",
            circuits[0].5, circuits[1].5, circuits[0].6, circuits[1].6
        );
    }
}



/// U33: ctrl_neg_phase against the replaced ctrl_neg(z, key); z_if(z, m) x256; ctrl_neg(z, key) at the slot-6 pools
/// (56 / 57 / 59 / 60 / 64), both key values, m random / all ones / zero, z random in [1, p) plus edges, four forced
/// tapes: identical per-shot phase, z unchanged, scratch clean. Prints both T counts.
#[test]
fn o1_u33_neg_phase_oracle() {
    use super::modp_ft::{ctrl_neg, ctrl_neg_phase, Ms};
    let pm = super::frogdrop_sched::p();
    let mut rng = Rng::new(3333);
    for pool_len in [56usize, 57, 59, 60, 64] {
        let mut tees = vec![];
        let mut circuits = vec![];
        for variant in 0..2 {
            let mut b = B::new();
            let z = b.alloc_n(256);
            let key = b.alloc();
            let m = b.fresh_bits(256);
            let flag = b.alloc();
            let pool = b.alloc_n(pool_len);
            let one = b.alloc();
            b.x(one);
            let ms = Ms { k: flag, r: pool.clone(), one };
            let t0 = b.tof;
            let c0 = b.tof_cond;
            if variant == 0 {
                ctrl_neg(&mut b, &ms, &z, Some(key));
                for i in 0..256 {
                    b.z_if(z[i], m[i]);
                }
                ctrl_neg(&mut b, &ms, &z, Some(key));
            } else {
                ctrl_neg_phase(&mut b, &ms, &z, key, &m);
            }
            b.x(one);
            tees.push((b.tof - t0) as f64 - (b.tof_cond - c0) as f64 / 2.0);
            circuits.push((b, z, key, m, pool));
        }
        for tape in TAPES {
            for round in 0..6 {
                let zs: Vec<N> = (0..64)
                    .map(|s| match (round, s % 8) {
                        (0, 0) => N::from(1u64),
                        (0, 1) => pm - N::from(1u64),
                        (0, 2) => mask(65) ^ N::from(1u64),
                        (0, 3) => N::from(1u64) << 65,
                        _ => {
                            let v = rng.below(256) % pm;
                            if v.is_zero() { N::from(7u64) } else { v }
                        }
                    })
                    .collect();
                let keys: Vec<u64> = (0..64).map(|s| ((s / 2 + round) % 2) as u64).collect();
                let ms_: Vec<N> = (0..64).map(|s| match (round, s % 3) { (1, 0) => mask(256), (1, 1) => N::ZERO, _ => rng.below(256) }).collect();
                let mut phases = vec![];
                for (b, z, key, m, pool) in &circuits {
                    let (nq, nb, _, _) = analyze_ops(b.ops.iter());
                    let mut xof = Fixed(tape);
                    let mut sim = Simulator::new((nq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
                    for s in 0..64 {
                        put(&mut sim.qubits, z, s, zs[s]);
                        sim.qubits[key.0 as usize] |= keys[s] << s;
                        for i in 0..256 {
                            if ms_[s].bit(i) {
                                sim.bits[m[i].0 as usize] |= 1 << s;
                            }
                        }
                    }
                    sim.apply_iter(b.ops.iter());
                    for s in 0..64 {
                        assert_eq!(get(&sim.qubits, z, s), zs[s], "pool {pool_len}: z restored");
                        assert_eq!(get(&sim.qubits, pool, s), N::ZERO);
                    }
                    phases.push(sim.phase);
                }
                assert_eq!(phases[0], phases[1], "pool {pool_len} tape {tape:x} round {round}: phase differs");
            }
        }
        eprintln!("O1 U33 pool {pool_len}: replaced pair {:.1} T, phase oracle {:.1} T", tees[0], tees[1]);
    }
}
