//! Actual generated-op tests for the XOR kernel and its retained boundaries.
use super::*;
use crate::circuit::{analyze_ops, Op, OperationType as K};
use crate::sim::Simulator;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

struct Guard(Vec<(&'static str, Option<String>)>);
impl Guard {
    fn new() -> Self {
        Self(
            [
                "MIDQ_DIRECT_CTZ",
                "MIDQ_PREFIX_QCAP",
                "MIDQ_CHUNKED_PREFIX",
                "MIDQ_VARIABLE_CHUNKS",
                "LOWQ_HYBRID_CACHE_CTZ",
                "LOWQ_HYBRID_INPLACE_CTZ",
                "LOWQ_ONE_A_ELIM",
                "LOWQ_CLZ_DIFF_CONST_FOLD",
                "LOWQ_BORROW_PASSENGER_CARRY",
                "LOWQ_COMPACT_KGANC",
                "TRAILMIX_Q_TARGET",
                "MIDQ_MEASURE_GATE_AND",
            ]
            .into_iter()
            .map(|key| (key, std::env::var(key).ok()))
            .collect(),
        )
    }
}
impl Drop for Guard {
    fn drop(&mut self) {
        for (key, value) in &self.0 {
            if let Some(value) = value {
                std::env::set_var(key, value);
            } else {
                std::env::remove_var(key);
            }
        }
    }
}

struct Measurements {
    forced: Option<u8>,
    random: sha3::Shake256Reader,
}
impl XofReader for Measurements {
    fn read(&mut self, bytes: &mut [u8]) {
        if let Some(value) = self.forced {
            bytes.fill(value);
        } else {
            self.random.read(bytes);
        }
    }
}

struct Built {
    ops: Vec<Op>,
    ids: Vec<QubitId>,
    peak: usize,
    cap: usize,
}

fn build(n: usize, width: usize, available: usize, hybrid: bool, original: Option<bool>) -> Built {
    let mut c = Circuit::new();
    let q = c.alloc_qreg_bits("test.q", n);
    let shift = c.alloc_qreg_bits("test.shift", width);
    let active = c.alloc_qreg("test.active");
    let role = c.alloc_qreg("test.role");
    let witness = c.alloc_qreg("test.witness");
    let carry = c.alloc_qreg("test.carry");
    let ids = q
        .iter()
        .chain(&shift)
        .chain([&active, &role, &witness])
        .map(|q| QubitId(q.id().into()))
        .collect();
    c.flush_pending_frees();
    // A Hybrid AND takes one wire before the prefix planner gets its allowance.
    let cap = c.b.active_qubits as usize + available + usize::from(hybrid);
    std::env::set_var("MIDQ_PREFIX_QCAP", cap.to_string());
    std::env::set_var(
        "MIDQ_DIRECT_CTZ",
        if original.is_some() { "0" } else { "1" },
    );
    let control = HybridGateControl::new(&active, &role);
    let gate = if hybrid {
        GateControl::Hybrid(&control)
    } else {
        GateControl::Direct(&active)
    };
    if let Some(inverse) = original {
        super::super::ctz_shift(&mut c, &q, &shift, gate, Some(&carry), inverse);
    } else {
        assert!(try_apply(&mut c, &q, &shift, gate));
    }
    control.release(&mut c);
    c.zero_and_free(carry);
    // The output-dependent phase is observed, not erased by a final reset.
    if let Some(bit) = shift.first() {
        c.cz(bit, &witness);
    }
    c.flush_pending_frees();
    Built {
        ops: c.b.ops.clone(),
        ids,
        peak: c.b.peak_qubits as usize,
        cap,
    }
}

fn execute(built: &Built, inputs: &[u128], forced: Option<u8>) -> (Vec<u128>, Vec<bool>) {
    let (nq, nb, _, _) = analyze_ops(built.ops.iter());
    let mut hash = Shake256::default();
    hash.update(b"direct-ctz-selftest-v1");
    let mut measurements = Measurements {
        forced,
        random: hash.finalize_xof(),
    };
    let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut measurements);
    for (bit, &id) in built.ids.iter().enumerate() {
        for (shot, &value) in inputs.iter().enumerate() {
            *sim.qubit_mut(id) |= (((value >> bit) & 1) as u64) << shot;
        }
    }
    let mask = u64::MAX >> (64 - inputs.len());
    // A fixed nonzero incoming phase checks preservation rather than only zero.
    sim.phase = 0xa55a_9669_3cc3_5aa5 & mask;
    predicate_clear_selftest::checked_apply(&mut sim, &built.ops, mask);
    let values = (0..inputs.len())
        .map(|shot| {
            built
                .ids
                .iter()
                .enumerate()
                .fold(0u128, |value, (bit, &id)| {
                    value | (((sim.qubit(id) >> shot) & 1) as u128) << bit
                })
        })
        .collect();
    let phases = (0..inputs.len())
        .map(|shot| sim.phase >> shot & 1 != 0)
        .collect();
    for &id in &built.ids {
        *sim.qubit_mut(id) = 0;
    }
    assert!(
        sim.qubits.iter().all(|word| word & mask == 0),
        "dirty prefix scratch"
    );
    (values, phases)
}

fn sentinel(q: u128, n: usize) -> usize {
    if n == 0 {
        0
    } else {
        (q.trailing_zeros() as usize).min(n - 1)
    }
}

fn weighted_t(ops: &[Op]) -> f64 {
    let mut depth = 0;
    let mut total = 0.0;
    for op in ops {
        match op.kind {
            K::PushCondition => depth += 1,
            K::PopCondition => depth -= 1,
            K::CCX | K::CCZ => total += 2.0f64.powi(-depth),
            _ => {}
        }
    }
    assert_eq!(depth, 0);
    total
}

pub(super) fn run() {
    let _guard = Guard::new();
    for key in [
        "MIDQ_CHUNKED_PREFIX",
        "MIDQ_VARIABLE_CHUNKS",
        "LOWQ_HYBRID_CACHE_CTZ",
        "LOWQ_HYBRID_INPLACE_CTZ",
        "LOWQ_ONE_A_ELIM",
        "LOWQ_CLZ_DIFF_CONST_FOLD",
        "LOWQ_BORROW_PASSENGER_CARRY",
        "LOWQ_COMPACT_KGANC",
        "MIDQ_MEASURE_GATE_AND",
    ] {
        std::env::set_var(key, "1");
    }
    std::env::set_var("TRAILMIX_Q_TARGET", "684");
    let width = 5;
    let mut checked = 0;
    for n in 1usize..=8 {
        for available in 1usize..=n {
            if crate::point_add::clean_chunk_plan::plan(n - 1, available).is_none() {
                continue;
            }
            for hybrid in [false, true] {
                let kernel = build(n, width, available, hybrid, None);
                assert!(kernel.peak <= kernel.cap);
                let chunks = crate::point_add::clean_chunk_plan::plan(n - 1, available).unwrap();
                let replay: usize = chunks
                    .iter()
                    .take(chunks.len().saturating_sub(1))
                    .map(|k| k - 1)
                    .sum();
                let expected_t =
                    (n - 1) as f64 + 0.5 * replay as f64 + if hybrid && n > 1 { 1.0 } else { 0.0 };
                assert_eq!(
                    weighted_t(&kernel.ops),
                    expected_t,
                    "kernel count n={n} A={available} hybrid={hybrid}"
                );
                // Every small quotient, arbitrary XOR target, both quantum
                // controls and an independent phase witness, including q=0.
                let inputs: Vec<_> = (0..1u128 << (n + width + 3)).collect();
                for batch in inputs.chunks(64) {
                    for mode in [Some(0), Some(255), Some(0x55), None] {
                        let (got, phases) = execute(&kernel, batch, mode);
                        for (shot, &input) in batch.iter().enumerate() {
                            let q = input & ((1u128 << n) - 1);
                            let enabled = input >> (n + width) & 1 != 0
                                && (!hybrid || input >> (n + width + 1) & 1 != 0);
                            let expected = input
                                ^ if enabled {
                                    (sentinel(q, n) as u128) << n
                                } else {
                                    0
                                };
                            assert_eq!(got[shot], expected);
                            let phase = ((0xa55a_9669_3cc3_5aa5u64 >> shot) & 1 != 0)
                                ^ (expected >> n & 1 != 0 && expected >> (n + width + 2) & 1 != 0);
                            assert_eq!(phases[shot], phase);
                        }
                        checked += batch.len();
                    }
                }
            }
        }
    }
    // Every bit position at the real quotient widths, with dense/zero patterns,
    // old forward clearing and old inverse deposit. Both control strategies.
    for n in [1usize, 2, 5, 9, 18, 26, 31, 32, 33, 64] {
        let safe_width = 5.max((usize::BITS - n.leading_zeros()) as usize + 1);
        let mut widths = vec![safe_width];
        // Production already uses width=5 beyond the old debug-only bound.
        // Release tests also cover its exact modulo-32 metadata semantics.
        if safe_width != 5 && !cfg!(debug_assertions) {
            widths.push(5);
        }
        let count = n - 1;
        let mut qs = vec![0, (1u128 << n) - 1];
        for bit in 0..n {
            qs.extend([1u128 << bit, ((1u128 << n) - 1) ^ ((1u128 << bit) - 1)]);
        }
        for width in widths {
            for available in [4usize, 8, 16, 32, 64] {
                if crate::point_add::clean_chunk_plan::plan(count, available).is_none() {
                    continue;
                }
                for hybrid in [false, true] {
                    let kernel = build(n, width, available, hybrid, None);
                    assert!(kernel.peak <= kernel.cap);
                    for inverse in [false, true] {
                        let reference = build(n, width, available, hybrid, Some(inverse));
                        let mut inputs = Vec::new();
                        for &q in &qs {
                            for controls in 0..8u128 {
                                let enabled = controls & 1 != 0 && (!hybrid || controls & 2 != 0);
                                let shift = if !inverse && enabled {
                                    sentinel(q, n) & ((1usize << width) - 1)
                                } else {
                                    0
                                };
                                inputs.push(q | ((shift as u128) << n) | (controls << (n + width)));
                            }
                        }
                        for batch in inputs.chunks(64) {
                            for mode in [Some(0), Some(255), Some(0x55), None] {
                                assert_eq!(
                                execute(&kernel, batch, mode),
                                execute(&reference, batch, mode),
                                "boundary n={n} A={available} hybrid={hybrid} inverse={inverse}"
                            );
                                checked += batch.len();
                            }
                        }
                        eprintln!("DIRECT_CTZ_RESOURCE n={n} width={width} A={available} hybrid={hybrid} inverse={inverse} oldQ={} newQ={} old_weightedT={} new_weightedT={}",
                        reference.peak, kernel.peak, weighted_t(&reference.ops), weighted_t(&kernel.ops));
                    }
                }
            }
        }
    }
    // No admission at an impossible prefix cap; the caller keeps the old route.
    std::env::set_var("MIDQ_DIRECT_CTZ", "1");
    let mut c = Circuit::new();
    let q = c.alloc_qreg_bits("fallback.q", 18);
    let shift = c.alloc_qreg_bits("fallback.shift", 5);
    let active = c.alloc_qreg("fallback.active");
    c.flush_pending_frees();
    std::env::set_var("MIDQ_PREFIX_QCAP", c.b.active_qubits.to_string());
    let before = c.b.ops.clone();
    assert!(!try_apply(&mut c, &q, &shift, GateControl::Direct(&active)));
    assert_eq!(before, c.b.ops);
    let role = c.alloc_qreg("fallback.role");
    let control = HybridGateControl::new(&active, &role);
    c.flush_pending_frees();
    std::env::set_var("MIDQ_PREFIX_QCAP", c.b.active_qubits.to_string());
    let before = c.b.ops.clone();
    let peak = c.b.peak_qubits;
    assert!(!try_apply(
        &mut c,
        &q,
        &shift,
        GateControl::Hybrid(&control)
    ));
    assert!(control.held.borrow().is_none());
    assert_eq!(before, c.b.ops);
    assert_eq!(peak, c.b.peak_qubits);
    eprintln!("DIRECT_CTZ_SELFTEST PASS: {checked} actual-op basis/measurement cases; arbitrary XOR targets, preserved N-1 zero sentinel, direct/hybrid controls, exact shift boundaries, phase witness, pre-reset scratch, cap and weighted count");
}
