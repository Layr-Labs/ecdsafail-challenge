//! Release-native equivalence on the exact common-floor PREP contract.
use super::*;
use crate::circuit::{analyze_ops, BitId, Op};
use crate::sim::Simulator;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};
use std::collections::BTreeMap;
type Word = ruint::Uint<256, 4>;
type Key = (usize, usize, usize, bool);

struct Random {
    fixed: Option<u8>,
    reader: sha3::Shake256Reader,
}
impl Random {
    fn new(mode: usize) -> Self {
        let mut h = Shake256::default();
        h.update(b"d-alignment-common-floor-v1");
        h.update(&(mode as u64).to_le_bytes());
        Self {
            fixed: [Some(0), Some(255), Some(0x55), None][mode],
            reader: h.finalize_xof(),
        }
    }
}
impl XofReader for Random {
    fn read(&mut self, out: &mut [u8]) {
        if let Some(v) = self.fixed {
            out.fill(v);
        } else {
            self.reader.read(out);
        }
    }
}

fn circuit(
    key: Key,
    direction: usize,
    nested: bool,
    variant: usize,
) -> (Vec<Op>, Vec<QubitId>, [BitId; 2], u32) {
    let (n, m, lo, automatic) = key;
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("common.A", n);
    let b = c.alloc_qreg_bits("common.B", n);
    let ca = c.alloc_qreg_bits("common.ca", m);
    let cb = c.alloc_qreg_bits("common.cb", m);
    let q = c.alloc_qreg_bits("common.q", 32);
    let phi = c.alloc_qreg_bits("common.phi", 5);
    let role = c.alloc_qreg("common.R");
    let data: Vec<_> = a
        .iter()
        .chain(&b)
        .chain(&ca)
        .chain(&cb)
        .chain(&q)
        .chain(&phi)
        .chain([&role])
        .map(|q| QubitId(q.id().into()))
        .collect();
    let srot = c.alloc_qreg_bits("common.srot", 5);
    let offset = c.alloc_qreg("common.offset");
    let outer = c.alloc_input_bit();
    let inner = c.alloc_input_bit();
    std::env::set_var(
        "MIDQ_D_ALIGN_COMMON_WINDOW",
        if variant == 1 { "1" } else { "0" },
    );
    let body = |c: &mut Circuit| {
        let one = |c: &mut Circuit, inverse| {
            if variant == 0 {
                apply(
                    c, &a, &b, &ca, &cb, &q, &phi, &role, &srot, &offset, inverse,
                );
            } else if automatic || variant == 2 {
                apply_profile(
                    c, &a, &b, &ca, &cb, &q, &phi, &role, &srot, &offset, inverse,
                );
            } else {
                apply_with_floor(
                    c, &a, &b, &ca, &cb, &q, &phi, &role, &srot, &offset, inverse, lo,
                );
            }
        };
        if direction != 1 {
            one(c, false);
        }
        if direction != 0 {
            one(c, true);
        }
    };
    if nested {
        c.with_conditions(&[outer, inner], body);
    } else {
        body(&mut c);
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
        data,
        [BitId(outer.raw() as u64), BitId(inner.raw() as u64)],
        c.b.peak_qubits,
    )
}

fn check(
    key: Key,
    cases: &[(Vec<Word>, Vec<Word>)],
    direction: usize,
    nested: bool,
    variant: usize,
) -> usize {
    let (n, m, lo, _) = key;
    let widths = [n, n, m, m, 32, 5, 1];
    let bit = |words: &[Word], mut i: usize| -> u64 {
        for (word, &width) in words.iter().zip(&widths) {
            if i < width {
                return (word.as_limbs()[i / 64] >> (i % 64)) & 1;
            }
            i -= width;
        }
        unreachable!()
    };
    let (ops, data, conditions, peak) = circuit(key, direction, nested, variant);
    let (nq, nb, _, _) = analyze_ops(ops.iter());
    let nq = nq.max(data.iter().map(|q| q.0 + 1).max().unwrap());
    let nb = nb.max(conditions[1].0 + 1);
    let mut checked = 0;
    for mode in 0..4 {
        let mut rng = Random::new(mode);
        let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        for batch in cases.chunks(64) {
            sim.clear_for_shot();
            let live = u64::MAX >> (64 - batch.len());
            let outer = if nested { 0xeeeeeeeeeeeeeeee } else { u64::MAX };
            let inner = if nested { 0xbbbbbbbbbbbbbbbb } else { u64::MAX };
            *sim.bit_mut(conditions[0]) = outer;
            *sim.bit_mut(conditions[1]) = inner;
            for (i, &id) in data.iter().enumerate() {
                *sim.qubit_mut(id) = batch.iter().enumerate().fold(0, |v, (s, (a, b))| {
                    v | (bit(if direction == 1 { b } else { a }, i) << s)
                });
            }
            super::super::predicate_clear_selftest::checked_apply(&mut sim, &ops, live);
            assert_eq!(
                sim.phase & live,
                0,
                "common phase key={key:?} dir={direction} variant={variant} mode={mode}"
            );
            for (i, &id) in data.iter().enumerate() {
                let expected = batch.iter().enumerate().fold(0, |v, (s, (a, b))| {
                    let input = if direction == 1 { b } else { a };
                    let output = if direction == 0 { b } else { a };
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
                    "common value key={key:?} dir={direction} variant={variant} bit={i}"
                );
            }
            for (i, &value) in sim.qubits.iter().enumerate() {
                if !data.contains(&QubitId(i as u64)) {
                    assert_eq!(
                        value & live,
                        0,
                        "common scratch n={n} m={m} lo={lo} wire={i}"
                    );
                }
            }
            checked += batch.len();
        }
    }
    if !nested && variant == 1 {
        let raw = ops
            .iter()
            .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ))
            .count();
        eprintln!("D_ALIGN_COMMON_WINDOW component n={n} m={m} lo={lo} direction={direction} raw_T={raw} peak={peak} checked={checked}");
    }
    checked
}

pub(super) fn run() {
    assert_eq!(profile_floor(256, 1), 222);
    assert_eq!(profile_floor(203, 102), 121);
    assert_eq!(profile_floor(94, 235), 0);
    assert_eq!(profile_floor(16, 1), 0);
    assert_eq!(profile_floor(256, 0), 0);
    let mut groups: BTreeMap<Key, Vec<(Vec<Word>, Vec<Word>)>> = BTreeMap::new();
    for line in include_str!("d_alignment_common_window_cases.txt")
        .lines()
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
    {
        let fields: Vec<_> = line.split_whitespace().collect();
        assert_eq!(fields.len(), 14);
        let key: Key = (
            fields[0].parse().unwrap(),
            fields[1].parse().unwrap(),
            fields[2].parse().unwrap(),
            fields[3] == "1",
        );
        let words: Vec<Word> = fields[4..]
            .iter()
            .map(|s| Word::from_str_radix(s, 16).unwrap())
            .collect();
        let before = words[..7].to_vec();
        let mut after = before.clone();
        after[1] = words[7];
        after[5] = words[8];
        after[6] = words[9];
        let phi = before[5].as_limbs()[0] as usize;
        let divisor = before[1] >> phi;
        assert!(divisor >= (Word::from(1) << key.2));
        if key.3 {
            assert_eq!(profile_floor(key.0, key.1), key.2);
        }
        groups.entry(key).or_default().push((before, after));
    }
    assert_eq!(groups.values().map(Vec::len).sum::<usize>(), 5860);
    let mut checked = 0;
    let mut flag_off = 0;
    for measured in [false, true] {
        std::env::set_var("MIDQ_MEASURE_COMPARE", if measured { "1" } else { "0" });
        for (&key, cases) in &groups {
            for direction in 0..3 {
                for nested in [false, true] {
                    let full = circuit(key, direction, nested, 0);
                    let off = circuit(key, direction, nested, 2);
                    assert_eq!(full.0, off.0, "flag-off operation identity");
                    assert_eq!(full.3, off.3);
                    flag_off += 1;
                    for variant in 0..2 {
                        checked += check(key, cases, direction, nested, variant);
                    }
                }
            }
        }
    }
    eprintln!("D_ALIGN_COMMON_WINDOW_SELFTEST PASS cases={checked} flag_off_streams={flag_off} common_floor_contract=true arbitrary_A_below_floor=true inverse_on_forward_image=true local_fixtures_not_field_reachability=true");
}
