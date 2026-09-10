//! Native full word/phase/dirty/scratch comparison and small count-only probe.
use super::*;
use crate::circuit::{analyze_ops, BitId, Op, OperationType as K, QubitId};
use crate::point_add::B;
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
                "MIDQ_CHECKPOINT_CAP_AWARE",
                "MIDQ_CHECKPOINT_QCAP",
                "MIDQ_CHECKPOINT_CAP_TRACE",
                "MIDQ_DIRTY_CONST",
                "MIDQ_COMPACT_CONST_CARRY",
                "MIDQ_ALL_CONST_FOLDS",
                "MIDQ_CHUNKED_CONTROLLED_ADD",
                "MIDQ_CONTROLLED_ADD_RECURSIVE",
                "MIDQ_CONTROLLED_ADD_QCAP",
                "POINT_ADD_COUNT_ONLY",
            ]
            .into_iter()
            .map(|k| (k, std::env::var(k).ok()))
            .collect(),
        )
    }
}
impl Drop for Guard {
    fn drop(&mut self) {
        for (k, v) in &self.0 {
            if let Some(v) = v {
                std::env::set_var(k, v)
            } else {
                std::env::remove_var(k)
            }
        }
    }
}
struct Measurements(Option<u8>, sha3::Shake256Reader);
impl Measurements {
    fn new(mode: usize) -> Self {
        let mut h = Shake256::default();
        h.update(b"checkpoint-cap-aware-native-v1");
        Self(
            [Some(0), Some(255), Some(0x55), None][mode],
            h.finalize_xof(),
        )
    }
}
impl XofReader for Measurements {
    fn read(&mut self, out: &mut [u8]) {
        if let Some(v) = self.0 {
            out.fill(v)
        } else {
            self.1.read(out)
        }
    }
}
fn condition(c: &mut Circuit, on: Option<bool>, body: impl FnOnce(&mut Circuit)) {
    if let Some(on) = on {
        let outer = c.alloc_bit();
        let inner = c.alloc_bit();
        for (bit, value) in [(outer, on), (inner, true)] {
            let mut op = Op::empty();
            op.kind = if value { K::BitStore1 } else { K::BitStore0 };
            op.c_target = BitId(bit.raw() as u64);
            c.b.push_op(op);
        }
        c.with_conditions(&[outer, inner], body);
        c.free_bit(inner);
        c.free_bit(outer);
    } else {
        body(c);
    }
}
fn setup() {
    for (k, v) in [
        ("MIDQ_DIRTY_CONST", "1"),
        ("MIDQ_COMPACT_CONST_CARRY", "1"),
        ("MIDQ_ALL_CONST_FOLDS", "0"),
        ("MIDQ_CHUNKED_CONTROLLED_ADD", "1"),
        ("MIDQ_CONTROLLED_ADD_RECURSIVE", "1"),
    ] {
        std::env::set_var(k, v);
    }
}
fn build(
    n: usize,
    value: u64,
    subtract: bool,
    aware: bool,
    live: usize,
    limit: usize,
    on: Option<bool>,
    scoped: bool,
) -> B {
    std::env::set_var("MIDQ_CHECKPOINT_CAP_AWARE", if aware { "1" } else { "0" });
    std::env::set_var("MIDQ_CHECKPOINT_QCAP", limit.to_string());
    std::env::set_var("MIDQ_CONTROLLED_ADD_QCAP", limit.to_string());
    let mut c = Circuit::new();
    let target = c.alloc_qreg_bits("probe.target", n);
    let donor = c.alloc_qreg_bits("probe.donor", n);
    let control = c.alloc_qreg("probe.control");
    assert!(live >= 2 * n + 1);
    let _spectator = c.alloc_qreg_bits("probe.spectator", live - 2 * n - 1);
    c.set_section("probe/midq.tail.backward.checkpoint");
    condition(&mut c, on, |c| {
        let scope = if scoped { enter(c) } else { None };
        super::super::midq_constant_update(
            c,
            &control,
            &target,
            &value.to_le_bytes(),
            &donor,
            subtract,
        );
        leave(c, scope);
    });
    c.flush_pending_frees();
    assert_eq!(c.b.active_qubits as usize, live);
    c.into_builder()
}
fn execute(b: &B, input: &[u64], mode: usize) -> (Vec<u64>, u64) {
    let (nq, nb, _, _) = analyze_ops(b.ops.iter());
    let mut rng = Measurements::new(mode);
    let mut sim = Simulator::new(
        (nq as usize).max(input.len()).max(b.next_qubit as usize),
        nb as usize + 1,
        &mut rng,
    );
    sim.qubits[..input.len()].copy_from_slice(input);
    sim.phase = 0xa53c_09f0_1278_ee11;
    super::super::predicate_clear_selftest::checked_apply(&mut sim, &b.ops, u64::MAX);
    for &v in &sim.qubits[input.len()..] {
        assert_eq!(v, 0, "fresh scratch dirty");
    }
    (sim.qubits[..input.len()].to_vec(), sim.phase)
}
fn scalar_expected(input: &[u64], n: usize, value: u64, subtract: bool, on: bool) -> Vec<u64> {
    let mut out = input.to_vec();
    let control = if on { input[2 * n] } else { 0 };
    let mut carry = 0u64;
    for i in 0..n {
        let a = if subtract { !input[i] } else { input[i] };
        let b = if i < 64 && (value >> i) & 1 != 0 {
            control
        } else {
            0
        };
        let sum = a ^ b ^ carry;
        carry = (a & b) | (a & carry) | (b & carry);
        out[i] = if subtract { !sum } else { sum };
    }
    out
}

pub(crate) fn run() {
    let _guard = Guard::new();
    setup();
    std::env::remove_var("POINT_ADD_COUNT_ONLY");
    let mut checked = 0;
    for n in 2usize..=6 {
        for value in [0u64, 1, 3, 5, 9, 17, 39, 0x1000003d1] {
            for subtract in [false, true] {
                let live = 2 * n + 1;
                let old = build(n, value, subtract, false, live, live, None, true);
                let new = build(n, value, subtract, true, live, live, None, true);
                assert_eq!(
                    new.peak_qubits as usize, live,
                    "fallback must allocate zero clean wires"
                );
                let states = 1usize << (2 * n + 1);
                for first in (0..states).step_by(64) {
                    let mut input = vec![0u64; live];
                    for lane in 0..64 {
                        let v = (first + lane) % states;
                        for i in 0..live {
                            input[i] |= ((v >> i & 1) as u64) << lane;
                        }
                    }
                    let expected = scalar_expected(&input, n, value, subtract, true);
                    for mode in 0..4 {
                        assert_eq!(
                            execute(&old, &input, mode),
                            (expected.clone(), 0xa53c_09f0_1278_ee11)
                        );
                        assert_eq!(
                            execute(&new, &input, mode),
                            (expected.clone(), 0xa53c_09f0_1278_ee11)
                        );
                        checked += 64;
                    }
                }
            }
        }
    }
    // Actual255/256-bit primitives with arbitrary dirty words and nonzero
    // spectators, at the scout's exact1009-wire pre-adder live count.
    for (n, value) in [(255usize, 0x800001e8u64), (256, 0x1000003d1)] {
        for subtract in [false, true] {
            let old = build(n, value, subtract, false, 1009, 1009, None, true);
            let new = build(n, value, subtract, true, 1009, 1009, None, true);
            assert_eq!(old.peak_qubits, 1011);
            assert_eq!(new.peak_qubits, 1009);
            let mut seed = Shake256::default();
            seed.update(b"checkpoint-cap-full-word-inputs");
            seed.update(&(n as u64).to_le_bytes());
            let mut rng = seed.finalize_xof();
            let input: Vec<_> = (0..1009)
                .map(|_| {
                    let mut bytes = [0u8; 8];
                    rng.read(&mut bytes);
                    u64::from_le_bytes(bytes)
                })
                .collect();
            let expected = scalar_expected(&input, n, value, subtract, true);
            for mode in 0..4 {
                assert_eq!(
                    execute(&old, &input, mode),
                    (expected.clone(), 0xa53c_09f0_1278_ee11)
                );
                assert_eq!(
                    execute(&new, &input, mode),
                    (expected.clone(), 0xa53c_09f0_1278_ee11)
                );
                checked += 64;
            }
        }
    }
    // Non-executing/executing nested classical conditions, and exact unchanged
    // operation streams when disabled, outside checkpoint scope, or roomy.
    for on in [false, true] {
        let old = build(6, 977, true, false, 19, 19, Some(on), true);
        let new = build(6, 977, true, true, 19, 19, Some(on), true);
        let input: Vec<_> = (0..19)
            .map(|i| (i as u64).wrapping_mul(0x9e3779b97f4a7c15) ^ 0xa55ac33c96695aa5)
            .collect();
        let expected = scalar_expected(&input, 6, 977, true, on);
        for mode in 0..4 {
            assert_eq!(
                execute(&old, &input, mode),
                (expected.clone(), 0xa53c_09f0_1278_ee11)
            );
            assert_eq!(
                execute(&new, &input, mode),
                (expected.clone(), 0xa53c_09f0_1278_ee11)
            );
            checked += 64;
        }
    }
    for scoped in [false, true] {
        let old = build(17, 977, false, false, 35, 37, None, scoped);
        let new = build(17, 977, false, true, 35, 37, None, scoped);
        assert_eq!(old.ops, new.ops, "normal headroom preserves original gates");
    }
    let old = build(17, 977, false, false, 35, 35, None, false);
    let new = build(17, 977, false, true, 35, 35, None, false);
    assert_eq!(old.ops, new.ops, "non-checkpoint unchanged");
    // The legacy three-clean variant must not be admitted with only two slots.
    std::env::set_var("MIDQ_COMPACT_CONST_CARRY", "0");
    let old = build(6, 39, false, false, 13, 15, None, true);
    let new = build(6, 39, false, true, 13, 15, None, true);
    assert_eq!(old.peak_qubits, 16);
    assert_eq!(new.peak_qubits, 13);
    eprintln!("CHECKPOINT_CAP_SELFTEST PASS cases={checked}; exact modulo words including noncanonical/wrapping values, both directions/controls, arbitrary dirty donors, phase and pre-reset scratch, four measurement streams, conditions, flag/scope/headroom fallbacks; whole-checkpoint/circuit tests remain separate");
}
pub(crate) fn profile() {
    let _guard = Guard::new();
    setup();
    std::env::set_var("POINT_ADD_COUNT_ONLY", "1");
    for (n, value) in [(256usize, 0x1000003d1u64), (255, 0x800001e8)] {
        for live in [1008usize, 1009] {
            for limit in [1000usize, 1009, 1010, 1011] {
                for aware in [false, true] {
                    let b = build(n, value, false, aware, live, limit, None, true);
                    let t =
                        b.counted_kind_ops[K::CCX as usize] + b.counted_kind_ops[K::CCZ as usize];
                    eprintln!("CHECKPOINT_CAP_PROFILE n={n} constant={value} aware={aware} live={live} cap={limit} actual_peak={} raw_T={t} ops={} live_floor_above_cap={} added_clean={}",b.peak_qubits,b.counted_ops,live>limit,b.peak_qubits as usize-live);
                }
            }
        }
    }
}
