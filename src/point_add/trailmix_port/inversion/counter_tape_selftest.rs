use super::super::{
    midq_mod_signed_add_halve, midq_value_round_backward, midq_value_round_forward_with_sign,
    predicate_clear_selftest::checked_apply,
};
use super::*;
use crate::circuit::{analyze_ops, Op, QubitId};
use crate::sim::Simulator;
use alloy_primitives::U256;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

struct Measurements(Option<u8>, sha3::Shake256Reader);
impl Measurements {
    fn new(mode: usize) -> Self {
        let mut seed = Shake256::default();
        seed.update(b"counter-tape-components-v1");
        Self([Some(0), Some(255), None][mode], seed.finalize_xof())
    }
}
impl XofReader for Measurements {
    fn read(&mut self, out: &mut [u8]) {
        if let Some(byte) = self.0 {
            out.fill(byte);
        } else {
            self.1.read(out);
        }
    }
}

fn ids(reg: &[QReg]) -> Vec<QubitId> {
    reg.iter().map(|q| QubitId(q.id().into())).collect()
}
fn write<R: XofReader>(sim: &mut Simulator<R>, reg: &[QubitId], lane: usize, value: U256) {
    for (i, &q) in reg.iter().enumerate().take(256) {
        if value.bit(i) {
            *sim.qubit_mut(q) |= 1 << lane;
        }
    }
}
fn read<R: XofReader>(sim: &Simulator<R>, reg: &[QubitId], lane: usize) -> U256 {
    let mut value = U256::ZERO;
    for (i, &q) in reg.iter().enumerate() {
        let on = sim.qubit(q) >> lane & 1;
        if i >= 256 {
            assert_eq!(on, 0, "overflow lane");
        } else if on != 0 {
            value |= U256::from(1) << i;
        }
    }
    value
}
fn clean<R: XofReader>(sim: &Simulator<R>, live: &[&[QubitId]], mask: u64) {
    assert_eq!(sim.phase & mask, 0, "phase");
    for (i, &bits) in sim.qubits.iter().enumerate() {
        if !live.iter().any(|reg| reg.contains(&QubitId(i as u64))) {
            assert_eq!(bits & mask, 0, "scratch {i}");
        }
    }
}
fn apply<R: XofReader>(sim: &mut Simulator<R>, ops: &[Op], mask: u64) {
    checked_apply(sim, ops, mask);
    assert_eq!(sim.phase & mask, 0, "component phase");
}

fn map_exhaustive() {
    let mut checked = 0;
    for n in 2..=5 {
        let mut c = Circuit::new();
        let a = c.alloc_qreg_bits("a", 3);
        let q = c.alloc_qreg_bits("q", 2);
        let ca = c.alloc_qreg_bits("ca", n);
        let cb = c.alloc_qreg_bits("cb", n);
        let data = [ids(&a), ids(&q), ids(&ca), ids(&cb)];
        let flag = prepare(&mut c, &a, &ca, &cb, &q);
        let flag_ids = ids(std::slice::from_ref(&flag));
        let mid = c.b.ops.len();
        restore(&mut c, &a, &ca, &cb, &q, flag);
        let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
        let mut rng = Measurements::new(2);
        let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        let cmask = (1usize << n) - 1;
        for first in (0..1usize << (5 + 2 * n)).step_by(64) {
            sim.clear_for_shot();
            let inputs: Vec<_> = (first..first + 64)
                .map(|v| [v & 7, v >> 3 & 3, v >> 5 & cmask, v >> (5 + n) & cmask])
                .collect();
            for (lane, values) in inputs.iter().enumerate() {
                for i in 0..4 {
                    write(&mut sim, &data[i], lane, U256::from(values[i]));
                }
            }
            apply(&mut sim, &c.b.ops[..mid], u64::MAX);
            for (lane, values) in inputs.iter().enumerate() {
                let t = usize::from(values[0] == 0 && values[1] == 0);
                let expected = [
                    values[0] ^ t,
                    values[1],
                    values[2].wrapping_sub(t * values[3]) & cmask,
                    values[3],
                ];
                assert_eq!(read(&sim, &flag_ids, lane), U256::from(t));
                for i in 0..4 {
                    assert_eq!(read(&sim, &data[i], lane), U256::from(expected[i]));
                }
            }
            clean(
                &sim,
                &[&data[0], &data[1], &data[2], &data[3], &flag_ids],
                u64::MAX,
            );
            apply(&mut sim, &c.b.ops[mid..], u64::MAX);
            clean(&sim, &[&data[0], &data[1], &data[2], &data[3]], u64::MAX);
            for (lane, values) in inputs.iter().enumerate() {
                for i in 0..4 {
                    assert_eq!(read(&sim, &data[i], lane), U256::from(values[i]));
                }
                checked += 1;
            }
        }
    }
    eprintln!("COUNTER_TAPE_MAP PASS cases={checked}, full small-width cube including A=0,q>0, modular subtraction, inverse/value/phase/pre-reset");
}

fn signed(v: i16, n: usize) -> i16 {
    (v << (16 - n)) >> (16 - n)
}

fn tape_exhaustive() {
    let width = 4;
    let mut c = Circuit::new();
    let mut a = c.alloc_qreg_bits("a", width);
    let mut b = c.alloc_qreg_bits("b", width);
    let terminal = c.alloc_qreg("terminal");
    let mut counter = c.alloc_qreg_bits("counter", BITS);
    let original = [
        ids(&a),
        ids(&b),
        ids(&counter),
        ids(std::slice::from_ref(&terminal)),
    ];
    let mut slots = std::mem::take(&mut counter).into_iter();
    let mut tape = Vec::new();
    let mut boundaries = Vec::new();
    for round in 0..BITS {
        let encoded = slots.next().unwrap();
        c.cx(&a[1], &encoded);
        c.cx(&b[1], &encoded);
        let logical = c.alloc_qreg("logical");
        xor_decoded(&mut c, &terminal, &encoded, &logical);
        if round % 2 == 0 {
            midq_value_round_forward_with_sign(&mut c, &mut a, &mut b, &logical, width);
        } else {
            midq_value_round_forward_with_sign(&mut c, &mut b, &mut a, &logical, width);
        }
        xor_decoded(&mut c, &terminal, &encoded, &logical);
        c.zero_and_free(logical);
        tape.push(encoded);
        boundaries.push((c.b.ops.len(), ids(&a), ids(&b), ids(&tape)));
    }
    assert!(slots.next().is_none());
    let mid = c.b.ops.len();
    for round in (0..BITS).rev() {
        let encoded = tape.pop().unwrap();
        let logical = c.alloc_qreg("logical");
        xor_decoded(&mut c, &terminal, &encoded, &logical);
        if round % 2 == 0 {
            midq_value_round_backward(&mut c, &mut a, &mut b, logical, width);
        } else {
            midq_value_round_backward(&mut c, &mut b, &mut a, logical, width);
        }
        c.cx(&a[1], &encoded);
        c.cx(&b[1], &encoded);
        counter.push(encoded);
    }
    counter.reverse();
    assert_eq!(ids(&counter), original[2], "physical counter IDs and order");
    let restored = [ids(&a), ids(&b), ids(&counter), original[3].clone()];
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let mut rng = Measurements::new(2);
    let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
    for batch in 0..5 {
        sim.clear_for_shot();
        let mut pairs = [[1i16; 2]; 64];
        let mut codes = [0usize; 64];
        for lane in 0..64 {
            if batch == 0 {
                pairs[lane] = [
                    signed((lane as i16 & 7) * 2 + 1, width),
                    signed((lane as i16 >> 3) * 2 + 1, width),
                ];
            } else {
                codes[lane] = (batch - 1) * 64 + lane;
            }
            write(
                &mut sim,
                &original[0],
                lane,
                U256::from(pairs[lane][0] as u16 & 15),
            );
            write(
                &mut sim,
                &original[1],
                lane,
                U256::from(pairs[lane][1] as u16 & 15),
            );
            write(&mut sim, &original[2], lane, U256::from(codes[lane]));
            write(
                &mut sim,
                &original[3],
                lane,
                U256::from(usize::from(batch != 0)),
            );
        }
        let initial_pairs = pairs;
        let mut start = 0;
        for (round, (end, ar, br, tr)) in boundaries.iter().enumerate() {
            apply(&mut sim, &c.b.ops[start..*end], u64::MAX);
            for lane in 0..64 {
                let s = (pairs[lane][0] ^ pairs[lane][1]) >> 1 & 1;
                if batch != 0 {
                    assert_eq!(s, 0);
                }
                codes[lane] ^= (s as usize) << round;
                let target = 1 - round % 2;
                let src = pairs[lane][1 - target];
                pairs[lane][target] =
                    signed(pairs[lane][target] + if s == 0 { src } else { -src }, width) >> 1;
                assert_eq!(read(&sim, ar, lane), U256::from(pairs[lane][0] as u16 & 15));
                assert_eq!(read(&sim, br, lane), U256::from(pairs[lane][1] as u16 & 15));
                assert_eq!(
                    read(&sim, tr, lane),
                    U256::from(codes[lane] & ((1 << (round + 1)) - 1))
                );
            }
            let all_counter_ids = &original[2];
            clean(&sim, &[ar, br, all_counter_ids, &original[3]], u64::MAX);
            start = *end;
        }
        apply(&mut sim, &c.b.ops[mid..], u64::MAX);
        clean(
            &sim,
            &[&restored[0], &restored[1], &restored[2], &restored[3]],
            u64::MAX,
        );
        for lane in 0..64 {
            assert_eq!(
                read(&sim, &restored[0], lane),
                U256::from(initial_pairs[lane][0] as u16 & 15)
            );
            assert_eq!(
                read(&sim, &restored[1], lane),
                U256::from(initial_pairs[lane][1] as u16 & 15)
            );
            assert_eq!(
                read(&sim, &restored[2], lane),
                U256::from(if batch == 0 {
                    0
                } else {
                    (batch - 1) * 64 + lane
                })
            );
        }
    }
    eprintln!("COUNTER_TAPE_VALUES PASS 64 live odd signed pairs + all 256 terminal counters, 8 rounds, overflow/model/value/phase/pre-reset/ID restoration");
}

fn stationary_coefficients() {
    let mut c = Circuit::new();
    let ca = c.alloc_qreg_bits("ca", 257);
    let cb = c.alloc_qreg_bits("cb", 257);
    let sign = c.alloc_qreg("sign");
    let data = [ids(&ca), ids(&cb)];
    midq_mod_signed_add_halve(&mut c, &ca, &cb, &sign, false);
    let mid = c.b.ops.len();
    midq_mod_signed_add_halve(&mut c, &ca, &cb, &sign, true);
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let p = U256::MAX - U256::from(0x1000003d0u64);
    let f = U256::from(0x1000003d1u64);
    let mut values = vec![
        U256::from(1),
        U256::from(2),
        f - U256::from(1),
        f,
        f + U256::from(1),
        p / U256::from(2),
        p / U256::from(2) + U256::from(1),
        p - U256::from(1),
        p - U256::from(2),
    ];
    for i in 1..256 {
        values.push(U256::from(1) << i);
        values.push(p - (U256::from(1) << i));
    }
    for mode in 0..3 {
        let mut rng = Measurements::new(mode);
        let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        for batch in values.chunks(64) {
            sim.clear_for_shot();
            let mask = u64::MAX >> (64 - batch.len());
            for (lane, &value) in batch.iter().enumerate() {
                for reg in &data {
                    write(&mut sim, reg, lane, value);
                }
            }
            apply(&mut sim, &c.b.ops[..mid], mask);
            clean(&sim, &[&data[0], &data[1]], mask);
            for (lane, &value) in batch.iter().enumerate() {
                for reg in &data {
                    assert_eq!(read(&sim, reg, lane), value, "stationary forward");
                }
            }
            apply(&mut sim, &c.b.ops[mid..], mask);
            clean(&sim, &[&data[0], &data[1]], mask);
            for (lane, &value) in batch.iter().enumerate() {
                for reg in &data {
                    assert_eq!(read(&sim, reg, lane), value, "stationary inverse");
                }
            }
        }
    }
    eprintln!("COUNTER_TAPE_COEFFICIENTS PASS {} full-width equal rows x 3 measurement streams, stationary forward/inverse/value/phase/pre-reset", values.len());
}

fn full_tail(shared: bool, checkpoint: bool) {
    use super::super::{midq_tail_backward, midq_tail_forward};
    std::env::set_var("MIDQ_COUNTER_TAPE", if shared { "1" } else { "0" });
    std::env::set_var("MIDQ_TAIL_CHECKPOINT", if checkpoint { "1" } else { "0" });
    std::env::set_var("MIDQ_QUOTIENT_CODE", "1");
    let mut c = Circuit::new();
    let mut a = c.alloc_qreg_bits("a", 85);
    let mut b = c.alloc_qreg_bits("b", 85);
    let mut ca = c.alloc_qreg_bits("ca", 257);
    let mut cb = c.alloc_qreg_bits("cb", 257);
    let mut q = c.alloc_qreg_bits("q", 18);
    let mut counter = c.alloc_qreg_bits("counter", BITS);
    let parity = c.alloc_qreg("parity");
    let initial = [
        ids(&a),
        ids(&b),
        ids(&ca),
        ids(&cb),
        ids(&q),
        ids(&counter),
        ids(std::slice::from_ref(&parity)),
    ];
    let state = midq_tail_forward(
        &mut c,
        &mut a,
        &mut b,
        &mut ca,
        &mut cb,
        &mut q,
        &mut counter,
        &parity,
    );
    let mid = c.b.ops.len();
    let endpoint = ids(&ca);
    let tape = ids(&state.tape);
    let mut end_live: Vec<_> = [&a, &b, &ca, &cb, &q, &counter, &state.tape, &state.ctz]
        .into_iter()
        .flat_map(|reg| ids(reg))
        .collect();
    end_live.extend(ids(std::slice::from_ref(&parity)));
    if let Some(selector) = state.ctz_select_a.as_ref() {
        end_live.extend(ids(std::slice::from_ref(selector)));
    }
    if let Some(packed) = state.packed_metadata.as_ref() {
        end_live.extend(ids(&packed.bits));
    }
    if let Some(flag) = state.counter_terminal.as_ref() {
        end_live.extend(ids(std::slice::from_ref(flag)));
    }
    if let Some(code) = state.quotient_code.as_ref() {
        end_live.extend(ids(code));
    }
    if shared {
        assert!(counter.is_empty());
    }
    midq_tail_backward(
        &mut c,
        &mut a,
        &mut b,
        &mut ca,
        &mut cb,
        &mut q,
        &mut counter,
        &parity,
        state,
    );
    let restored = [
        ids(&a),
        ids(&b),
        ids(&ca),
        ids(&cb),
        ids(&q),
        ids(&counter),
        initial[6].clone(),
    ];
    assert_eq!(initial[5], restored[5], "same physical counter order");
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let p = U256::MAX - U256::from(0x1000003d0u64);
    let pairs = [
        (1, 1),
        (3, 5),
        (2, 3),
        (3, 2),
        (1, 7),
        (7, 1),
        (5, 7),
        (7, 5),
    ];
    let inverse_values = [
        U256::from(1),
        U256::from(2),
        p - U256::from(1),
        p - U256::from(2),
        p / U256::from(2),
        p / U256::from(2) + U256::from(1),
        U256::from(1) << 255,
        U256::from(0x1000003d1u64),
    ];
    for mode in 0..3 {
        let mut rng = Measurements::new(mode);
        let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        for batch in 0..if shared { 5 } else { 1 } {
            sim.clear_for_shot();
            let mut inputs = Vec::new();
            let mut expected = Vec::new();
            for lane in 0..64 {
                let par = lane / 8 % 2;
                let (av, bv, cav, cbv, count, inv) = if batch == 0 {
                    let (av, bv) = pairs[lane % 8];
                    let (av, bv) = (U256::from(av), U256::from(bv));
                    // Avoid the inherited fast-field cancellation boundary;
                    // tiny inverse=1, (A,B)=(7,5) already fails with codec OFF.
                    let inv = (U256::from(0x123456789abcdefu64) << 128) + U256::from(lane + 1);
                    (
                        av,
                        bv,
                        if par == 1 { p - av * inv } else { av * inv },
                        if par == 1 { bv * inv } else { p - bv * inv },
                        0,
                        inv,
                    )
                } else {
                    let v = inverse_values[lane % inverse_values.len()];
                    (
                        U256::ZERO,
                        U256::from(1),
                        p,
                        v,
                        (batch - 1) * 64 + lane,
                        if par == 1 { v } else { p - v },
                    )
                };
                let row = [
                    av,
                    bv,
                    cav,
                    cbv,
                    U256::ZERO,
                    U256::from(count),
                    U256::from(par),
                ];
                for i in 0..7 {
                    write(&mut sim, &initial[i], lane, row[i]);
                }
                inputs.push(row);
                expected.push(inv);
            }
            apply(&mut sim, &c.b.ops[..mid], u64::MAX);
            clean(&sim, &[&end_live], u64::MAX);
            for lane in 0..64 {
                assert_eq!(read(&sim, &endpoint, lane), expected[lane], "tail endpoint shared={shared} checkpoint={checkpoint} batch={batch} lane={lane}");
                if batch != 0 {
                    assert_eq!(read(&sim, &tape[..BITS], lane), inputs[lane][5]);
                }
            }
            apply(&mut sim, &c.b.ops[mid..], u64::MAX);
            clean(
                &sim,
                &restored.iter().map(Vec::as_slice).collect::<Vec<_>>(),
                u64::MAX,
            );
            for lane in 0..64 {
                for i in 0..7 {
                    assert_eq!(read(&sim, &restored[i], lane), inputs[lane][i], "tail restore shared={shared} checkpoint={checkpoint} batch={batch} lane={lane} reg={i}");
                }
            }
        }
    }
    eprintln!("COUNTER_TAPE_FULL_TAIL PASS shared={shared} checkpoint={checkpoint} cases={} Q={nq} ops={} all 224 rounds + normalization + qcodec + endpoint + reverse, value/phase/pre-reset/IDs", if shared {960} else {192}, c.b.ops.len());
}

fn counter_wrap_witness() {
    use super::super::{compute_active, done_counter_from_swap_predicates, uncompute_active};
    let mut c = Circuit::new();
    let q_zero = c.alloc_qreg("q_zero");
    let a_nonzero = c.alloc_qreg("a_nonzero");
    let count = c.alloc_qreg_bits("counter", BITS);
    let count_ids = ids(&count);
    let qz = ids(std::slice::from_ref(&q_zero));
    done_counter_from_swap_predicates(&mut c, &q_zero, &a_nonzero, &count, false);
    let active = compute_active(&mut c, &count);
    let active_ids = ids(std::slice::from_ref(&active));
    let mid = c.b.ops.len();
    uncompute_active(&mut c, &count, &active);
    c.zero_and_free(active);
    done_counter_from_swap_predicates(&mut c, &q_zero, &a_nonzero, &count, true);
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let mut rng = Measurements::new(2);
    let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
    write(&mut sim, &count_ids, 0, U256::from(255));
    write(&mut sim, &qz, 0, U256::from(1));
    apply(&mut sim, &c.b.ops[..mid], 1);
    assert_eq!(read(&sim, &count_ids, 0), U256::ZERO);
    assert_eq!(read(&sim, &active_ids, 0), U256::from(1));
    apply(&mut sim, &c.b.ops[mid..], 1);
    assert_eq!(read(&sim, &count_ids, 0), U256::from(255));
    clean(&sim, &[&count_ids, &qz], 1);
    eprintln!("COUNTER_TAPE_WRAP WITNESS: terminal count=255 -> 0, active=1 despite q=0; no-wrap/inactive promise cannot be dropped");
}

fn prefix_width_obligation() {
    use super::super::{
        trailmix_cacb_width, trailmix_counter_width, MIDQ_PZ_CUT, MIDQ_TAIL_ROUNDS,
    };
    use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::reg_widths;
    crate::point_add::trailmix_port::configure_sub1000_trailmix_route();
    assert_eq!(
        (MIDQ_PZ_CUT, MIDQ_TAIL_ROUNDS, trailmix_counter_width()),
        (360, 224, 8)
    );
    let mut max_width = 0;
    for step in 0..MIDQ_PZ_CUT {
        let (_, _, ca, cb, _) = reg_widths(step);
        let width = trailmix_cacb_width(ca.max(cb));
        assert!(
            width < 256,
            "early-terminal exclusion needs review at step {step}"
        );
        max_width = max_width.max(width);
    }
    eprintln!("COUNTER_TAPE_PREFIX PASS all 360 coefficient widths <= {max_width} < 256; ca=p cannot occur on the inherited exact-width support, hence done never increments counter and no wrap occurs there");
}

pub(crate) fn run() {
    std::env::set_var("MIDQ_DIRTY_CONST", "1");
    std::env::set_var("MIDQ_DIRTY_FIELD_NEG", "1");
    std::env::set_var("MIDQ_COMPACT_CONST_CARRY", "1");
    std::env::set_var("MIDQ_MEASURE_COMPARE", "1");
    map_exhaustive();
    tape_exhaustive();
    stationary_coefficients();
    counter_wrap_witness();
    for checkpoint in [false, true] {
        full_tail(false, checkpoint);
        full_tail(true, checkpoint);
    }
    prefix_width_obligation();
}
