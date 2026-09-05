//! Opt-in emitted-op tests; the port's in-Circuit simulator is a stub.

use super::*;
use crate::circuit::{analyze_ops, BitId, Op, NO_BIT};
use crate::point_add::trailmix_port::arith::khattar_gidney::phase_and_of_khattar_gidney_refs;
use crate::sim::Simulator;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

struct Measurements {
    forced: Option<u8>,
    random: sha3::Shake256Reader,
}

impl Measurements {
    fn new(mode: usize) -> Self {
        let mut hash = Shake256::default();
        hash.update(b"midq-predicate-components-v1");
        hash.update(&(mode as u64).to_le_bytes());
        Self {
            forced: [Some(0), Some(255), Some(0x55), None, None, None, None][mode],
            random: hash.finalize_xof(),
        }
    }
}

impl XofReader for Measurements {
    fn read(&mut self, out: &mut [u8]) {
        if let Some(byte) = self.forced {
            out.fill(byte);
        } else {
            self.random.read(out);
        }
    }
}

fn emitted_t(ops: &[Op]) -> usize {
    ops.iter()
        .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ))
        .count()
}

fn ids(reg: &[QReg]) -> Vec<QubitId> {
    reg.iter().map(|q| QubitId(q.id().into())).collect()
}

// Check every reset BEFORE it can hide a dirty scratch bit. Keep the original
// simulator for every gate, wrapping each in the saved outer condition mask.
fn checked_apply<R: XofReader>(sim: &mut Simulator<'_, R>, ops: &[Op], live: u64) {
    let scratch_bit = BitId((sim.num_bits - 1) as u64);
    let mut push = Op::empty();
    push.kind = OperationType::PushCondition;
    push.c_condition = scratch_bit;
    let mut pop = Op::empty();
    pop.kind = OperationType::PopCondition;
    let mut stack = Vec::new();
    let mut mask = u64::MAX;
    for op in ops {
        match op.kind {
            OperationType::PushCondition => {
                stack.push(mask);
                mask &= sim.bit(op.c_condition);
            }
            OperationType::PopCondition => mask = stack.pop().expect("balanced condition"),
            _ => {
                let cond = mask
                    & if op.c_condition == NO_BIT {
                        u64::MAX
                    } else {
                        sim.bit(op.c_condition)
                    };
                if op.kind == OperationType::R {
                    assert_eq!(
                        sim.qubit(op.q_target) & cond & live,
                        0,
                        "dirty reset at {op:?}"
                    );
                }
                *sim.bit_mut(scratch_bit) = mask;
                sim.apply_iter([&push, op, &pop].into_iter());
            }
        }
    }
    assert!(stack.is_empty());
}

fn check_outputs<R: XofReader>(
    sim: &Simulator<'_, R>,
    data: &[QubitId],
    want: &[u64],
    phase: u64,
    live: u64,
) {
    assert_eq!(sim.phase & live, phase & live, "phase mismatch");
    for (i, &id) in data.iter().enumerate() {
        assert_eq!(sim.qubit(id) & live, want[i] & live, "data wire {i}");
    }
    for (i, &value) in sim.qubits.iter().enumerate() {
        if !data.contains(&QubitId(i as u64)) {
            assert_eq!(value & live, 0, "dirty ancilla {i}");
        }
    }
}

fn predicate_case(
    n: usize,
    nonzero: bool,
    phase_only: bool,
    nested: bool,
    measured: bool,
) -> usize {
    std::env::set_var("MIDQ_MEASURE_PREDICATE", if measured { "1" } else { "0" });
    let mut c = Circuit::new();
    let reg = c.alloc_qreg_bits("test.reg", n);
    let witness = c.alloc_qreg("test.witness");
    let data: Vec<_> = reg
        .iter()
        .chain([&witness])
        .map(|q| QubitId(q.id().into()))
        .collect();
    let outer = c.alloc_input_bit();
    let inner = c.alloc_input_bit();
    let body = |c: &mut Circuit| {
        if phase_only {
            let refs: Vec<_> = reg.iter().collect();
            phase_and_of_khattar_gidney_refs(c, &refs);
        } else {
            let flag = c.alloc_qreg("test.flag");
            if nonzero {
                or_nonzero(c, &reg, &flag);
            } else {
                or_is_zero(c, &reg, &flag);
            }
            c.cx(&flag, &witness);
            clear_zero_predicate(c, &reg, &flag, nonzero);
            c.zero_and_free(flag);
        }
    };
    if nested {
        c.with_conditions(&[outer, inner], body);
    } else {
        body(&mut c);
    }
    for op in &c.b.ops {
        op.validate();
    }
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let nq = nq.max(data.iter().map(|q| q.0 + 1).max().unwrap_or(0));
    let nb = nb.max(inner.raw() as u64 + 1);
    let total = if n <= 10 {
        1usize << (n + 1 + if nested { 2 } else { 0 })
    } else {
        1024
    };
    let mut checked = 0;
    let mut forced_t = 0;
    for mode in 0..7 {
        let mut rng = Measurements::new(mode);
        let mut inputs = Measurements::new(3 + mode % 4);
        let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        for first in (0..total).step_by(64) {
            sim.clear_for_shot();
            let valid = 64.min(total - first);
            let live = u64::MAX >> (64 - valid);
            let mut initial = Vec::new();
            for (i, &id) in data.iter().enumerate() {
                let value = if n <= 10 {
                    (0..valid).fold(0, |mask, shot| {
                        mask | ((((first + shot) >> i) & 1) as u64) << shot
                    })
                } else {
                    let mut buf = [0; 8];
                    inputs.read(&mut buf);
                    // Keep all-zero, all-one, and walking one/zero lanes in
                    // every wide batch, where a random AND would almost never fire.
                    let mut v = u64::from_le_bytes(buf) & !15;
                    v |= 2;
                    if i == (first / 64) % n {
                        v |= 4;
                    } else {
                        v |= 8;
                    }
                    v
                };
                *sim.qubit_mut(id) = value;
                initial.push(value);
            }
            let condition_mask = |index: usize, wide: u64| {
                if !nested {
                    u64::MAX
                } else if n <= 10 {
                    (0..valid).fold(0, |mask, shot| {
                        mask | ((((first + shot) >> index) & 1) as u64) << shot
                    })
                } else {
                    wide.rotate_left(mode as u32)
                }
            };
            let outer_mask = condition_mask(n + 1, 0x3333333333333333);
            let inner_mask = condition_mask(n + 2, 0x5555555555555555);
            *sim.bit_mut(BitId(outer.raw().into())) = outer_mask;
            *sim.bit_mut(BitId(inner.raw().into())) = inner_mask;
            let cond = sim.bit(BitId(outer.raw().into())) & sim.bit(BitId(inner.raw().into()));
            let mut buf = [0; 8];
            inputs.read(&mut buf);
            let initial_phase = u64::from_le_bytes(buf);
            sim.phase = initial_phase;
            let mut want = initial.clone();
            let expected_phase = if phase_only {
                initial_phase ^ (initial[..n].iter().fold(u64::MAX, |a, b| a & b) & cond)
            } else {
                let nz = initial[..n].iter().fold(0, |a, b| a | b);
                want[n] ^= (if nonzero { nz } else { !nz }) & cond;
                initial_phase
            };
            checked_apply(&mut sim, &c.b.ops, live);
            check_outputs(&sim, &data, &want, expected_phase, live);
            checked += valid;
        }
        if mode < 2 {
            forced_t += sim.stats.toffoli_gates;
        }
    }
    if n == 256 && !nested {
        let average = forced_t as f64 / (2 * total) as f64;
        assert_eq!(
            average,
            if phase_only {
                524.0
            } else if measured {
                787.0
            } else {
                1050.0
            }
        );
        eprintln!("predicate component n={n} nonzero={nonzero} phase_only={phase_only} measured={measured} emittedT={} exactAvgT={average} Q={nq}", emitted_t(&c.b.ops));
    }
    checked
}

fn hybrid_cases(measured: bool) -> usize {
    std::env::set_var("MIDQ_MEASURE_GATE_AND", if measured { "1" } else { "0" });
    let mut c = Circuit::new();
    let reg = c.alloc_qreg_bits("test.hybrid", 3);
    let data = ids(&reg);
    let control = HybridGateControl::new(&reg[0], &reg[1]);
    control.with(&mut c, |c, g| c.cx(g, &reg[2]));
    control.with(&mut c, |c, g| c.cx(g, &reg[2]));
    control.release(&mut c);
    control.release(&mut c);
    control.with(&mut c, |c, g| c.cx(g, &reg[2]));
    control.with_ephemeral(&mut c, |c, g| c.cx(g, &reg[2]));
    control.with(&mut c, |c, g| c.cx(g, &reg[2]));
    control.release(&mut c);
    for op in &c.b.ops {
        op.validate();
    }
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    for mode in 0..7 {
        let mut rng = Measurements::new(mode);
        let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        let initial = [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0];
        for (id, value) in data.iter().zip(initial) {
            *sim.qubit_mut(*id) = value;
        }
        sim.phase = 0xabcddcba01234567;
        checked_apply(&mut sim, &c.b.ops, u64::MAX);
        check_outputs(
            &sim,
            &data,
            &[
                initial[0],
                initial[1],
                initial[2] ^ (initial[0] & initial[1]),
            ],
            0xabcddcba01234567,
            u64::MAX,
        );
    }
    7 * 64
}

fn swap_cases(measured: bool) -> usize {
    std::env::set_var("MIDQ_MEASURE_PREDICATE", if measured { "1" } else { "0" });
    let mut c = Circuit::new();
    let aa = c.alloc_qreg_bits("test.aa", 2);
    let bb = c.alloc_qreg_bits("test.bb", 2);
    let ca = c.alloc_qreg_bits("test.ca", 2);
    let cb = c.alloc_qreg_bits("test.cb", 2);
    let qq = c.alloc_qreg_bits("test.qq", 2);
    let counter = c.alloc_qreg_bits("test.counter", 2);
    let parity = c.alloc_qreg("test.parity");
    let data: Vec<_> = aa
        .iter()
        .chain(&bb)
        .chain(&ca)
        .chain(&cb)
        .chain(&qq)
        .chain(&counter)
        .chain([&parity])
        .map(|q| QubitId(q.id().into()))
        .collect();
    let active = compute_active(&mut c, &counter);
    swap_and_done_forward(&mut c, &aa, &bb, &ca, &cb, &qq, &counter, &parity, active);
    let split = c.b.ops.len();
    let active = undo_done_and_swap(&mut c, &aa, &bb, &ca, &cb, &qq, &counter, &parity);
    uncompute_active(&mut c, &counter, &active);
    c.zero_and_free(active);
    for op in &c.b.ops {
        op.validate();
    }
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let inputs: Vec<_> = (0..1usize << data.len())
        .filter(|v| {
            // Exactly the existing swap predicate invariant, without imposing
            // coprimality or restricting the unrelated cofactor/counter values.
            !(v & 3 != 0 && (v >> 2) & 3 == 0 && (v >> 8) & 3 == 0 && (v >> 10) & 3 == 0)
        })
        .collect();
    for mode in 0..7 {
        let mut rng = Measurements::new(mode);
        let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        for batch in inputs.chunks(64) {
            sim.clear_for_shot();
            let live = u64::MAX >> (64 - batch.len());
            let initial: Vec<_> = (0..data.len())
                .map(|i| {
                    batch
                        .iter()
                        .enumerate()
                        .fold(0, |m, (j, v)| m | (((v >> i) & 1) as u64) << j)
                })
                .collect();
            let expected: Vec<_> = batch
                .iter()
                .map(|&v| {
                    let mut v = v;
                    let swap = v & 3 != 0 && (v >> 8) & 15 == 0;
                    if swap {
                        let t = (v ^ (v >> 2)) & 0x33;
                        v ^= t ^ (t << 2) ^ (1 << 12);
                    }
                    if v & 3 == 0 && (v >> 8) & 3 == 0 {
                        v = (v & !(3 << 10)) | (((((v >> 10) & 3) + 1) & 3) << 10);
                    }
                    v
                })
                .collect();
            let want: Vec<_> = (0..data.len())
                .map(|i| {
                    expected
                        .iter()
                        .enumerate()
                        .fold(0, |m, (j, v)| m | (((v >> i) & 1) as u64) << j)
                })
                .collect();
            for (id, &value) in data.iter().zip(&initial) {
                *sim.qubit_mut(*id) = value;
            }
            sim.phase = 0xfedcba9876543210;
            checked_apply(&mut sim, &c.b.ops[..split], live);
            check_outputs(&sim, &data, &want, 0xfedcba9876543210, live);
            checked_apply(&mut sim, &c.b.ops[split..], live);
            check_outputs(&sim, &data, &initial, 0xfedcba9876543210, live);
        }
    }
    inputs.len() * 7
}

fn done_counter_cases(measured: bool, width: usize) -> usize {
    std::env::set_var("MIDQ_MEASURE_PREDICATE", if measured { "1" } else { "0" });
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("test.a", 2);
    let q = c.alloc_qreg_bits("test.q", 2);
    let counter = c.alloc_qreg_bits("test.counter", width);
    let witness = c.alloc_qreg("test.witness");
    let data: Vec<_> = a
        .iter()
        .chain(&q)
        .chain(&counter)
        .chain([&witness])
        .map(|q| QubitId(q.id().into()))
        .collect();
    // Also exercise the empty-counter compute/uncompute_active specialization.
    let active = compute_active(&mut c, &counter);
    c.cx(&active, &witness);
    uncompute_active(&mut c, &counter, &active);
    c.zero_and_free(active);
    done_counter_fn(&mut c, &a, &q, &counter, false);
    let split = c.b.ops.len();
    done_counter_fn(&mut c, &a, &q, &counter, true);
    let active = compute_active(&mut c, &counter);
    c.cx(&active, &witness);
    uncompute_active(&mut c, &counter, &active);
    c.zero_and_free(active);
    for op in &c.b.ops {
        op.validate();
    }
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let max = (1 << width) - 1;
    let inputs: Vec<_> = (0..1usize << data.len())
        .filter(|&v| {
            let conv = v & 15 == 0;
            let count = (v >> 4) & max;
            // Legacy done_counter_fn uses counter!=0 to erase convergence. Its
            // valid domain requires a terminated state for positive counters and
            // enough counter width to avoid wraparound.
            width == 0 || ((count == 0 || conv) && (!conv || count < max))
        })
        .collect();
    for mode in 0..7 {
        let mut rng = Measurements::new(mode);
        let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        for batch in inputs.chunks(64) {
            sim.clear_for_shot();
            let live = u64::MAX >> (64 - batch.len());
            let masks = |values: &[usize]| -> Vec<u64> {
                (0..data.len())
                    .map(|i| {
                        values
                            .iter()
                            .enumerate()
                            .fold(0, |m, (j, v)| m | (((v >> i) & 1) as u64) << j)
                    })
                    .collect()
            };
            let initial = masks(batch);
            let expected: Vec<_> = batch
                .iter()
                .map(|&v| {
                    let mut out = v;
                    if (v >> 4) & max == 0 {
                        out ^= 1 << (4 + width);
                    }
                    if width > 0 && v & 15 == 0 {
                        out += 1 << 4;
                    }
                    out
                })
                .collect();
            for (id, &value) in data.iter().zip(&initial) {
                *sim.qubit_mut(*id) = value;
            }
            sim.phase = 0x123456789abcdef0;
            checked_apply(&mut sim, &c.b.ops[..split], live);
            check_outputs(&sim, &data, &masks(&expected), 0x123456789abcdef0, live);
            checked_apply(&mut sim, &c.b.ops[split..], live);
            check_outputs(&sim, &data, &initial, 0x123456789abcdef0, live);
        }
    }
    inputs.len() * 7
}

pub(crate) fn run() {
    assert_ne!(
        std::env::var("POINT_ADD_COUNT_ONLY").ok().as_deref(),
        Some("1")
    );
    let mut checked = 0;
    for n in (0..=10).chain([16, 31, 32, 63, 64, 65, 127, 128, 255, 256, 257, 512]) {
        for nested in [false, true] {
            checked += predicate_case(n, false, true, nested, true);
            for nonzero in [false, true] {
                for measured in [false, true] {
                    checked += predicate_case(n, nonzero, false, nested, measured);
                }
            }
        }
    }
    for measured in [false, true] {
        checked += hybrid_cases(measured);
        checked += swap_cases(measured);
        checked += done_counter_cases(measured, 0);
        checked += done_counter_cases(measured, 2);
    }
    eprintln!("MIDQ_PREDICATE_CLEAR_SELFTEST PASS: {checked} input/measurement cases; values, exact phase, every reset and final ancilla checked");
}
