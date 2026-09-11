//! Actual full-iteration operation streams, independent exact PZ fixtures.
use super::*;
use crate::circuit::{analyze_ops, BitId, Op};
use crate::sim::Simulator;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};
use std::collections::BTreeMap;
type Word = ruint::Uint<256, 4>;
struct Case {
    before: Vec<Word>,
    after: Vec<Word>,
    input: usize,
}
struct Random {
    fixed: Option<u8>,
    reader: sha3::Shake256Reader,
}
impl Random {
    fn new(mode: usize) -> Self {
        let mut s = Shake256::default();
        s.update(b"d-align-whole-iteration-v1");
        s.update(&(mode as u64).to_le_bytes());
        Self {
            fixed: [Some(0), Some(255), Some(0x55), None][mode],
            reader: s.finalize_xof(),
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
struct Built {
    ops: Vec<Op>,
    split: Option<usize>,
    data: Vec<Vec<QubitId>>,
    conditions: [BitId; 2],
    nq: usize,
    nb: usize,
    peak: u32,
}
fn ids(v: &[QReg]) -> Vec<QubitId> {
    v.iter().map(|q| QubitId(q.id().into())).collect()
}

#[allow(clippy::too_many_arguments)]
fn raw_step(
    c: &mut Circuit,
    a: &mut Vec<QReg>,
    b: &mut Vec<QReg>,
    ca: &[QReg],
    cb: &[QReg],
    q: &[QReg],
    counter: &[QReg],
    parity: &QReg,
    srot: &[QReg],
    offset: &QReg,
    carry: &QReg,
    i: usize,
    inverse: bool,
    framed: bool,
) {
    use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::reg_widths;
    let n = a.len();
    if !framed {
        shrunken_pz_pass_step(
            c,
            a,
            b,
            ca,
            cb,
            q,
            counter,
            parity,
            srot,
            offset,
            Some(carry),
            i,
            inverse,
        );
        return;
    }
    let phi = c.alloc_qreg_bits("iteration.phi", 5);
    let role = c.alloc_qreg("iteration.R");
    if !inverse {
        let (pa, pb, _, _, _) = reg_widths(i.saturating_sub(1));
        let v = n.max(trailmix_ab_width(pa.max(pb)));
        shrunken_pz_resize(c, a, v, "A");
        shrunken_pz_resize(c, b, v, "B");
    }
    enter(c, b, ca, cb, q, &phi, &role);
    step(
        c,
        a,
        b,
        ca,
        cb,
        q,
        counter,
        parity,
        srot,
        offset,
        Some(carry),
        &phi,
        &role,
        i,
        inverse,
    );
    exit(c, b, ca, cb, q, &phi, &role);
    // This wrapper compares raw i-width interfaces; the shared helper itself
    // returns the previous framed width on inverse for the real driver.
    shrunken_pz_resize(c, a, n, "A");
    shrunken_pz_resize(c, b, n, "B");
    for bit in phi {
        c.zero_and_free(bit);
    }
    c.zero_and_free(role);
}

fn build(i: usize, direction: usize, nested: bool, framed: bool) -> Built {
    use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::reg_widths;
    let (wa, wb, wca, wcb, _) = reg_widths(i);
    let n = trailmix_ab_width(wa.max(wb));
    let m = trailmix_cacb_width(wca.max(wcb));
    let mut c = Circuit::new();
    let passenger = c.alloc_qreg_bits("iteration.passenger", 256);
    let sign = c.alloc_qreg("iteration.sgn");
    let carry = c.alloc_qreg("iteration.borrowed_carry");
    let mut a = c.alloc_qreg_bits("iteration.A", n);
    let mut b = c.alloc_qreg_bits("iteration.B", n);
    let ca = c.alloc_qreg_bits("iteration.ca", m);
    let cb = c.alloc_qreg_bits("iteration.cb", m);
    let q = c.alloc_qreg_bits("iteration.q", 32);
    let counter = c.alloc_qreg_bits("iteration.counter", 8);
    let parity = c.alloc_qreg("iteration.parity");
    let srot = c.alloc_qreg_bits("iteration.srot", 5);
    let offset = c.alloc_qreg("iteration.offset");
    let data = vec![
        ids(&a),
        ids(&b),
        ids(&ca),
        ids(&cb),
        ids(&q),
        ids(&counter),
        vec![QubitId(parity.id().into())],
        vec![QubitId(sign.id().into())],
        ids(&passenger),
    ];
    let outer = c.alloc_input_bit();
    let inner = c.alloc_input_bit();
    let mut split = None;
    let mut part = |c: &mut Circuit, inverse| {
        raw_step(
            c, &mut a, &mut b, &ca, &cb, &q, &counter, &parity, &srot, &offset, &carry, i, inverse,
            framed,
        )
    };
    if direction != 1 {
        if nested {
            c.with_conditions(&[outer, inner], |c| part(c, false));
        } else {
            part(&mut c, false);
        }
        c.flush_pending_frees();
        if direction == 2 {
            split = Some(c.b.ops.len());
        }
    }
    if direction != 0 {
        if nested {
            c.with_conditions(&[outer, inner], |c| part(c, true));
        } else {
            part(&mut c, true);
        }
    }
    for bit in srot {
        c.zero_and_free(bit);
    }
    c.zero_and_free(offset);
    c.flush_pending_frees();
    for op in &c.b.ops {
        op.validate();
    }
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let nq = nq.max(data.iter().flatten().map(|q| q.0 + 1).max().unwrap());
    let nb = nb.max(inner.raw() as u64 + 1);
    assert!(
        c.b.peak_qubits <= 1100,
        "whole iteration peak={} step={i} framed={framed}",
        c.b.peak_qubits
    );
    Built {
        ops: c.b.ops.clone(),
        split,
        data,
        conditions: [BitId(outer.raw() as u64), BitId(inner.raw() as u64)],
        nq: nq as usize,
        nb: nb as usize,
        peak: c.b.peak_qubits,
    }
}

fn words(state: &[Word], input: usize) -> Vec<Word> {
    let count = state[4]
        .as_limbs()
        .iter()
        .map(|x| x.count_ones() as u64)
        .sum::<u64>();
    let mut out = state[..5].to_vec();
    out.push(Word::from(count));
    out.push(state[5]);
    out.push(Word::from((input & 1) as u64));
    let z = 0x9e3779b97f4a7c15u64.wrapping_mul(input as u64 + 1);
    out.push(Word::from_limbs([
        z,
        z.rotate_left(13),
        !z,
        z.rotate_right(9) ^ 0xa5a5a5a5a5a5a5a5,
    ]));
    out
}

fn verify<R: XofReader>(
    sim: &Simulator<'_, R>,
    data: &[Vec<QubitId>],
    cases: &[Case],
    direction: usize,
    applied: u64,
    live: u64,
    phase: u64,
) {
    assert_eq!(sim.phase & live, phase & live, "whole-iteration phase");
    let expected_words: Vec<_> = cases
        .iter()
        .enumerate()
        .map(|(shot, case)| {
            let input = if direction == 1 {
                &case.after
            } else {
                &case.before
            };
            let output = if direction == 0 {
                &case.after
            } else {
                &case.before
            };
            words(
                if applied >> shot & 1 == 0 {
                    input
                } else {
                    output
                },
                case.input,
            )
        })
        .collect();
    let mut is_data = vec![false; sim.qubits.len()];
    for (g, group) in data.iter().enumerate() {
        for (j, &id) in group.iter().enumerate() {
            is_data[id.0 as usize] = true;
            let expected = expected_words
                .iter()
                .enumerate()
                .fold(0, |mask, (shot, w)| {
                    mask | (((w[g].as_limbs()[j / 64] >> (j % 64)) & 1) << shot)
                });
            assert_eq!(sim.qubit(id) & live, expected, "data group={g} bit={j}");
        }
    }
    for (i, &value) in sim.qubits.iter().enumerate() {
        if !is_data[i] {
            assert_eq!(value & live, 0, "whole-iteration scratch wire={i}");
        }
    }
}

fn check(i: usize, cases: &[Case], direction: usize, nested: bool, framed: bool) -> usize {
    let b = build(i, direction, nested, framed);
    let mut checked = 0;
    for mode in 0..4 {
        let mut rng = Random::new(mode);
        let mut sim = Simulator::new(b.nq, b.nb + 1, &mut rng);
        for batch in cases.chunks(64) {
            sim.clear_for_shot();
            let live = u64::MAX >> (64 - batch.len());
            let outer = if nested { 0xeeeeeeeeeeeeeeee } else { u64::MAX };
            let inner = if nested { 0xbbbbbbbbbbbbbbbb } else { u64::MAX };
            let applied = outer & inner;
            *sim.bit_mut(b.conditions[0]) = outer;
            *sim.bit_mut(b.conditions[1]) = inner;
            let phase = 0x9696696996966969;
            sim.phase = phase;
            let input_words: Vec<_> = batch
                .iter()
                .map(|row| {
                    words(
                        if direction == 1 {
                            &row.after
                        } else {
                            &row.before
                        },
                        row.input,
                    )
                })
                .collect();
            for (g, group) in b.data.iter().enumerate() {
                for (j, &id) in group.iter().enumerate() {
                    *sim.qubit_mut(id) =
                        input_words.iter().enumerate().fold(0, |mask, (shot, w)| {
                            mask | (((w[g].as_limbs()[j / 64] >> (j % 64)) & 1) << shot)
                        });
                }
            }
            if let Some(split) = b.split {
                super::super::predicate_clear_selftest::checked_apply(
                    &mut sim,
                    &b.ops[..split],
                    live,
                );
                verify(&sim, &b.data, batch, 0, applied, live, phase);
                super::super::predicate_clear_selftest::checked_apply(
                    &mut sim,
                    &b.ops[split..],
                    live,
                );
            } else {
                super::super::predicate_clear_selftest::checked_apply(&mut sim, &b.ops, live);
            }
            verify(&sim, &b.data, batch, direction, applied, live, phase);
            checked += batch.len();
        }
    }
    if i % 32 == 0 || i + 1 == MIDQ_PZ_CUT {
        eprintln!("D_ALIGN_ITERATION step={i} dir={direction} nested={nested} framed={framed} peak={} checked={checked}",b.peak);
    }
    checked
}

pub(super) fn run() {
    use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::reg_widths;
    assert_eq!(
        MIDQ_PZ_CUT, 340,
        "native fixtures are for the cut340 prefix"
    );
    assert_eq!(qretain::fixed_width(), Some(32));
    assert_eq!(env_usize("HYBRID_QCAP", 0), 1100);
    assert_eq!(
        std::env::var("MIDQ_D_ALIGN_COMMON_WINDOW").ok().as_deref(),
        Some("1")
    );
    assert_eq!(
        std::env::var("MIDQ_RETAIN_MUL_LENGTHS").ok().as_deref(),
        Some("1")
    );
    std::env::set_var("POINT_ADD_COUNT_ONLY", "0");
    let mut groups: BTreeMap<usize, Vec<Case>> = BTreeMap::new();
    for line in include_str!("d_alignment_iteration_cases.txt")
        .lines()
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
    {
        let f: Vec<_> = line.split_whitespace().collect();
        assert_eq!(f.len(), 16);
        let i: usize = f[0].parse().unwrap();
        let n: usize = f[1].parse().unwrap();
        let m: usize = f[2].parse().unwrap();
        let input = f[3].parse().unwrap();
        let (wa, wb, wca, wcb, _) = reg_widths(i);
        assert_eq!(
            (n, m),
            (
                trailmix_ab_width(wa.max(wb)),
                trailmix_cacb_width(wca.max(wcb))
            )
        );
        let v: Vec<Word> = f[4..]
            .iter()
            .map(|s| Word::from_str_radix(s, 16).unwrap())
            .collect();
        groups.entry(i).or_default().push(Case {
            before: v[..6].to_vec(),
            after: v[6..].to_vec(),
            input,
        });
    }
    assert_eq!(groups.len(), 340);
    assert_eq!(groups.values().map(Vec::len).sum::<usize>(), 11664);
    let mut checked = 0;
    for (&i, cases) in &groups {
        for direction in 0..3 {
            for nested in [false, true] {
                for framed in [false, true] {
                    checked += check(i, cases, direction, nested, framed);
                }
            }
        }
    }
    eprintln!("D_ALIGN_ITERATION_SELFTEST PASS cases={checked} original_and_shared_framed=true raw_frame_raw_interfaces=true forward_inverse_roundtrip=true midpoint_phase_checks=true every_reset_checked=true passenger256_preserved=true actual_PZ_sources=37 qualified_contiguous_prefix_cases=11664");
}
