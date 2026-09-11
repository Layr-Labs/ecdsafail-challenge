//! Actual emitted operations; the port's in-Circuit simulator is not used.
use super::*;
use crate::circuit::{analyze_ops, BitId, Op};
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
        let mut h = Shake256::default();
        h.update(b"d-alignment-prep-v1");
        h.update(&(mode as u64).to_le_bytes());
        Self {
            forced: [Some(0), Some(255), Some(0x55), None][mode],
            random: h.finalize_xof(),
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

fn circuit(n: usize, direction: usize, nested: bool) -> (Vec<Op>, Vec<QubitId>, [BitId; 2], usize) {
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("test.a", n);
    let b = c.alloc_qreg_bits("test.b", n);
    let ca = c.alloc_qreg_bits("test.ca", n);
    let cb = c.alloc_qreg_bits("test.cb", n);
    let q = c.alloc_qreg_bits("test.q", n.min(32));
    let phi = c.alloc_qreg_bits("test.phi", 5);
    let role = c.alloc_qreg("test.role");
    let ids = a
        .iter()
        .chain(&b)
        .chain(&ca)
        .chain(&cb)
        .chain(&q)
        .chain(&phi)
        .chain([&role])
        .map(|q| QubitId(q.id().into()))
        .collect::<Vec<_>>();
    let srot = c.alloc_qreg_bits("test.srot", 5);
    let offset = c.alloc_qreg("test.offset");
    let outer = c.alloc_input_bit();
    let inner = c.alloc_input_bit();
    let emit = |c: &mut Circuit| {
        if direction != 1 {
            apply(c, &a, &b, &ca, &cb, &q, &phi, &role, &srot, &offset, false);
        }
        if direction != 0 {
            apply(c, &a, &b, &ca, &cb, &q, &phi, &role, &srot, &offset, true);
        }
    };
    if nested {
        c.with_conditions(&[outer, inner], emit);
    } else {
        emit(&mut c);
    }
    for bit in srot {
        c.zero_and_free(bit);
    }
    c.zero_and_free(offset);
    c.flush_pending_frees();
    for op in &c.b.ops {
        op.validate();
    }
    (
        c.b.ops.clone(),
        ids,
        [BitId(outer.raw() as u64), BitId(inner.raw() as u64)],
        c.b.peak_qubits as usize,
    )
}

fn run_case(n: usize, cases: &[(u64, u64)], direction: usize, nested: bool) -> usize {
    let (ops, data, conditions, peak) = circuit(n, direction, nested);
    let (nq, nb, _, _) = analyze_ops(ops.iter());
    let nq = nq.max(data.iter().map(|q| q.0 + 1).max().unwrap());
    let nb = nb.max(conditions[1].0 + 1);
    let mut checked = 0;
    for mode in 0..4 {
        let mut rng = Measurements::new(mode);
        let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        for batch in cases.chunks(64) {
            sim.clear_for_shot();
            let live = u64::MAX >> (64 - batch.len());
            let outer = if nested { 0xeeeeeeeeeeeeeeee } else { u64::MAX };
            let inner = if nested { 0xbbbbbbbbbbbbbbbb } else { u64::MAX };
            *sim.bit_mut(conditions[0]) = outer;
            *sim.bit_mut(conditions[1]) = inner;
            for (j, &id) in data.iter().enumerate() {
                *sim.qubit_mut(id) = batch.iter().enumerate().fold(0, |word, (shot, &(a, b))| {
                    word | ((((if direction == 1 { b } else { a }) >> j) & 1) << shot)
                });
            }
            super::super::predicate_clear_selftest::checked_apply(&mut sim, &ops, live);
            assert_eq!(
                sim.phase & live,
                0,
                "phase n={n} direction={direction} mode={mode} nested={nested}"
            );
            for (shot, &(a, b)) in batch.iter().enumerate() {
                let input = if direction == 1 { b } else { a };
                let expected = if direction == 0 { b } else { a };
                let expected = if (outer & inner) >> shot & 1 == 0 {
                    input
                } else {
                    expected
                };
                let got = data
                    .iter()
                    .enumerate()
                    .fold(0u64, |v, (j, &id)| v | (((sim.qubit(id) >> shot) & 1) << j));
                assert_eq!(
                    got, expected,
                    "value n={n} direction={direction} input={input}"
                );
            }
            for (i, &value) in sim.qubits.iter().enumerate() {
                if !data.contains(&QubitId(i as u64)) {
                    assert_eq!(value & live, 0, "scratch {i}");
                }
            }
            checked += batch.len();
        }
    }
    let raw: usize = ops
        .iter()
        .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ))
        .count();
    eprintln!("D_ALIGN_PREP component n={n} direction={direction} nested={nested} raw_phase_toffoli={raw} peak={peak} checked={checked}");
    checked
}

fn rotate_cases() -> usize {
    let mut checked = 0;
    for n in 2..=9 {
        let mut c = Circuit::new();
        let word = c.alloc_qreg_bits("test.rotate", n);
        let delta = c.alloc_qreg_bits("test.delta", 6);
        let data: Vec<_> = word
            .iter()
            .chain(&delta)
            .map(|q| QubitId(q.id().into()))
            .collect();
        rotate_delta(&mut c, &word, &delta, false);
        let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
        let nq = nq.max(data.iter().map(|q| q.0 + 1).max().unwrap());
        let mut rng = Measurements::new(0);
        let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        let total = 1usize << (n + 6);
        for first in (0..total).step_by(64) {
            sim.clear_for_shot();
            for (j, &id) in data.iter().enumerate() {
                *sim.qubit_mut(id) =
                    (0..64).fold(0, |v, s| v | ((((first + s) >> j) & 1) as u64) << s);
            }
            super::super::predicate_clear_selftest::checked_apply(&mut sim, &c.b.ops, u64::MAX);
            for shot in 0..64 {
                let input = first + shot;
                let mask = (1usize << n) - 1;
                let a = input & mask;
                let d = ((input >> n) as isize - 32).rem_euclid(n as isize) as usize;
                let expected = ((a << d) | (a >> ((n - d) % n))) & mask;
                let actual = word.iter().enumerate().fold(0usize, |v, (j, q)| {
                    v | (((sim.qubit(QubitId(q.id().into())) >> shot) & 1) as usize) << j
                });
                assert_eq!(actual, expected, "cyclic n={n} a={a} delta={}", input >> n);
                for (j, q) in delta.iter().enumerate() {
                    assert_eq!(
                        (sim.qubit(QubitId(q.id().into())) >> shot) & 1,
                        ((input >> (n + j)) & 1) as u64
                    );
                }
            }
            assert_eq!(sim.phase, 0);
        }
        checked += total;
    }
    checked
}

fn frame_cases() -> usize {
    let mut c = Circuit::new();
    let q = c.alloc_qreg_bits("test.frame.q", 32);
    let out = c.alloc_qreg_bits("test.frame.out", 5);
    let role = c.alloc_qreg("test.frame.role");
    let data: Vec<_> = q
        .iter()
        .chain(&out)
        .chain([&role])
        .map(|q| QubitId(q.id().into()))
        .collect();
    frame_xor(&mut c, &q, &role, &out);
    c.flush_pending_frees();
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let words: Vec<u64> = std::iter::once(0)
        .chain((0..32).flat_map(|i| [1u64 << i, (1u64 << i) | (1u64 << 31)]))
        .collect();
    let inputs: Vec<_> = words
        .iter()
        .flat_map(|&q| {
            (0..32u64).flat_map(move |out| (0..2u64).map(move |r| q | (out << 32) | (r << 37)))
        })
        .collect();
    let mut checked = 0;
    for mode in 0..4 {
        let mut rng = Measurements::new(mode);
        let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        for batch in inputs.chunks(64) {
            sim.clear_for_shot();
            let live = u64::MAX >> (64 - batch.len());
            for (i, &id) in data.iter().enumerate() {
                *sim.qubit_mut(id) = batch
                    .iter()
                    .enumerate()
                    .fold(0, |v, (s, &x)| v | (((x >> i) & 1) << s));
            }
            super::super::predicate_clear_selftest::checked_apply(&mut sim, &c.b.ops, live);
            assert_eq!(sim.phase & live, 0);
            for (s, &x) in batch.iter().enumerate() {
                let q = x as u32;
                let toggle = if q != 0 && x >> 37 != 0 {
                    q.trailing_zeros() as u64
                } else {
                    0
                };
                let expected = x ^ (toggle << 32);
                let got = data
                    .iter()
                    .enumerate()
                    .fold(0u64, |v, (i, &id)| v | (((sim.qubit(id) >> s) & 1) << i));
                assert_eq!(got, expected, "q32 frame input={x}");
            }
            for (i, &v) in sim.qubits.iter().enumerate() {
                if !data.contains(&QubitId(i as u64)) {
                    assert_eq!(v & live, 0);
                }
            }
            checked += batch.len();
        }
    }
    checked
}

fn wide_cases() -> usize {
    type Word = ruint::Uint<256, 4>;
    let rows: Vec<_> = include_str!("d_alignment_prep_wide_cases.txt")
        .lines()
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(|line| {
            let v: Vec<_> = line.split_whitespace().collect();
            assert_eq!(v.len(), 11);
            let n: usize = v[0].parse().unwrap();
            let words: Vec<Word> = v[1..]
                .iter()
                .map(|s| Word::from_str_radix(s, 16).unwrap())
                .collect();
            let before = words[..7].to_vec();
            let mut after = before.clone();
            after[1] = words[7];
            after[5] = words[8];
            after[6] = words[9];
            (n, before, after)
        })
        .collect();
    assert_eq!(rows.len(), 5766);
    let mut checked = 0;
    for n in [40, 85, 97, 109, 137, 256] {
        let widths = [n, n, n, n, 32, 5, 1];
        let bit = |words: &[Word], mut i: usize| -> u64 {
            for (word, &width) in words.iter().zip(&widths) {
                if i < width {
                    return (word.as_limbs()[i / 64] >> (i % 64)) & 1;
                }
                i -= width;
            }
            unreachable!()
        };
        let cases: Vec<_> = rows.iter().filter(|r| r.0 == n).collect();
        for direction in 0..3 {
            for nested in [false, true] {
                let (ops, data, conditions, peak) = circuit(n, direction, nested);
                assert_eq!(data.len(), widths.iter().sum::<usize>());
                let (nq, nb, _, _) = analyze_ops(ops.iter());
                let nq = nq.max(data.iter().map(|q| q.0 + 1).max().unwrap());
                let nb = nb.max(conditions[1].0 + 1);
                for mode in 0..4 {
                    let mut rng = Measurements::new(mode);
                    let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
                    for batch in cases.chunks(64) {
                        sim.clear_for_shot();
                        let live = u64::MAX >> (64 - batch.len());
                        let outer = if nested { 0xeeeeeeeeeeeeeeee } else { u64::MAX };
                        let inner = if nested { 0xbbbbbbbbbbbbbbbb } else { u64::MAX };
                        *sim.bit_mut(conditions[0]) = outer;
                        *sim.bit_mut(conditions[1]) = inner;
                        for (i, &id) in data.iter().enumerate() {
                            *sim.qubit_mut(id) = batch.iter().enumerate().fold(0, |v, (s, row)| {
                                v | (bit(if direction == 1 { &row.2 } else { &row.1 }, i) << s)
                            });
                        }
                        super::super::predicate_clear_selftest::checked_apply(&mut sim, &ops, live);
                        assert_eq!(
                            sim.phase & live,
                            0,
                            "wide phase n={n} direction={direction} mode={mode}"
                        );
                        for (i, &id) in data.iter().enumerate() {
                            let expected = batch.iter().enumerate().fold(0, |v, (s, row)| {
                                let input = if direction == 1 { &row.2 } else { &row.1 };
                                let output = if direction == 0 { &row.2 } else { &row.1 };
                                v | (bit(
                                    if ((outer & inner) >> s) & 1 == 0 {
                                        input
                                    } else {
                                        output
                                    },
                                    i,
                                ) << s)
                            });
                            assert_eq!(
                                sim.qubit(id) & live,
                                expected,
                                "wide data n={n} direction={direction} bit={i}"
                            );
                        }
                        for (i, &v) in sim.qubits.iter().enumerate() {
                            if !data.contains(&QubitId(i as u64)) {
                                assert_eq!(v & live, 0, "wide scratch n={n} wire={i}");
                            }
                        }
                        checked += batch.len();
                    }
                }
                let raw: usize = ops.iter().filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ)).count();
                eprintln!("D_ALIGN_PREP synthetic_local_wide n={n} direction={direction} nested={nested} raw_phase_toffoli={raw} peak={peak}; not_reachability_evidence=true");
            }
        }
    }
    checked
}

pub(super) fn run() {
    let fixtures = include_str!("d_alignment_prep_cases.txt")
        .lines()
        .filter(|l| !l.starts_with('#') && !l.is_empty())
        .map(|l| {
            let v: Vec<u64> = l.split_whitespace().map(|s| s.parse().unwrap()).collect();
            assert_eq!(v.len(), 3);
            (v[0] as usize, v[1], v[2])
        })
        .collect::<Vec<_>>();
    let cyclic = rotate_cases();
    let q32_frame = frame_cases();
    let mut checked = 0;
    let mut wide_checked = 0;
    for measured in [false, true] {
        std::env::set_var("MIDQ_MEASURE_COMPARE", if measured { "1" } else { "0" });
        wide_checked += wide_cases();
        for n in 2..=9 {
            let cases: Vec<_> = fixtures
                .iter()
                .filter(|v| v.0 == n)
                .map(|v| (v.1, v.2))
                .collect();
            assert!(!cases.is_empty());
            for direction in 0..3 {
                for nested in [false, true] {
                    checked += run_case(n, &cases, direction, nested);
                }
            }
        }
    }
    eprintln!("D_ALIGN_PREP_SELFTEST PASS cyclic={cyclic} q32_frame={q32_frame} prepared={checked} synthetic_wide={wide_checked}; component_only=true full_positions=true zero_quotient=true inverse_on_forward_image=true no_production_dispatch=true");
}
