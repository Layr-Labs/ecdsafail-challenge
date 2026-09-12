use super::super::{expand_node, parse_graph, BitId, Op};
use super::*;
use crate::sim::Simulator;
use sha3::digest::XofReader;
use std::collections::BTreeMap;

fn var(mut n: usize, out: &mut Vec<u8>) {
    loop {
        let b = (n & 127) as u8;
        n >>= 7;
        out.push(b | if n > 0 { 128 } else { 0 });
        if n == 0 {
            break;
        }
    }
}
fn fixture(raw: &[u8], records: usize) -> Vec<u8> {
    let child = vec![2, 1, 1, 4, 0, 1, 2, 0, 1, 0];
    let mut root = Vec::new();
    var(578, &mut root);
    var(1, &mut root);
    var(records, &mut root);
    root.extend_from_slice(raw);
    let mut data = b"P26HIR1\0".to_vec();
    for x in [1, 1, 2] {
        var(x, &mut data);
    }
    for n in [child, root] {
        var(n.len(), &mut data);
        data.extend(n);
    }
    data
}
fn state(enabled: bool, inverse: bool, enclosed: bool, dirty: Option<usize>) -> State {
    let qi: Vec<_> = (1..579)
        .filter(|q| !(566..574).contains(q) || dirty == Some(*q - 1))
        .collect();
    let mut s = State::new(579, 2, &qi, &[0, 1], true, 0);
    s.qmap = (1..579).map(|q| QubitId(q as u64)).collect();
    s.lengths.enabled = enabled;
    s.lengths.direction = Some(inverse);
    s.retention.enabled = false;
    s.family24_enabled = false;
    s.family36_enabled = false;
    s.family63_enabled = false;
    if enclosed {
        s.raw(K::PushCondition).c_condition = BitId(1);
    }
    s.flush_raw();
    s
}
fn witness(s: &mut State, enclosed: bool) {
    if enclosed {
        s.raw(K::PopCondition);
    }
    // Read the helper's last classical outcome BEFORE overwriting it.
    s.raw(K::PushCondition).c_condition = BitId(0);
    s.raw(K::X).q_target = QubitId(101);
    let op = s.raw(K::CZ);
    op.q_control1 = QubitId(102);
    op.q_target = QubitId(103);
    s.raw(K::PopCondition);
    s.flush_raw();
    assert!(s.proof.balanced());
    for o in &s.out {
        o.validate();
    }
}
fn build(enabled: bool, inverse: bool, enclosed: bool, raw: &[u8], records: usize) -> State {
    let data = fixture(raw, records);
    let g = parse_graph(&data);
    super::super::shared_product::validate_phase_child(&g);
    let mut s = state(enabled, inverse, enclosed, None);
    expand_node(&g, &mut s, 1, 0, 578, 0, 1);
    s.flush_raw();
    s.assert_accounting(g.summaries[g.root].output_ops + usize::from(enclosed), 0);
    witness(&mut s, enclosed);
    s
}
struct Outcomes {
    values: Vec<u8>,
    at: usize,
}
impl XofReader for Outcomes {
    fn read(&mut self, b: &mut [u8]) {
        b.fill(*self.values.get(self.at).expect("unexpected random read"));
        self.at += 1;
    }
}
fn outcomes(ops: &[Op], seed: usize) -> Outcomes {
    let mut counts = BTreeMap::new();
    let mut values = Vec::new();
    for o in ops {
        if matches!(o.kind, K::Hmr | K::R) {
            let key = (o.q_target.0, o.c_target.0);
            let n = counts.entry(key).or_insert(0usize);
            let bit = match seed {
                0 => 0,
                1 => 1,
                _ => {
                    (key.0 as usize * 17 + key.1 as usize * 31 + *n * 13 + seed * 19)
                        .rotate_right((seed % 17) as u32)
                        & 1
                }
            };
            values.push(if bit == 0 { 0 } else { 255 });
            *n += 1;
        }
    }
    Outcomes { values, at: 0 }
}
fn set_word(q: &mut [u64], start: usize, width: usize, word: usize) {
    for i in 0..width {
        q[start + i + 1] = ((word >> i) & 1) as u64;
    }
}
fn compare(old: &State, new: &State, q: &[u64], active: u64, stale: u64, seed: usize) {
    let mut ro = outcomes(&old.out, seed);
    let mut rn = outcomes(&new.out, seed);
    let mut a = Simulator::new(579, 4, &mut ro);
    let mut b = Simulator::new(579, 4, &mut rn);
    a.qubits.copy_from_slice(q);
    b.qubits.copy_from_slice(q);
    a.bits = [stale, active, stale, stale].to_vec();
    b.bits = a.bits.clone();
    a.apply_iter(old.out.iter());
    b.apply_iter(new.out.iter());
    assert_eq!(a.qubits, b.qubits);
    assert_eq!(a.phase, b.phase);
    assert_eq!(a.bits[..2], b.bits[..2]);
}

#[test]
fn stable_length_native_phase_blocks() {
    let mut cases = 0;
    for inverse in [false, true] {
        let raw = if inverse { INVERSE } else { FORWARD };
        for enclosed in [false, true] {
            let old = build(false, inverse, enclosed, raw, 244);
            let new = build(true, inverse, enclosed, raw, 244);
            // Under an unknown outer condition C, the existing bounded Proof
            // retains `(C AND product) AND NOT(C)` after the unchanged shift
            // vchain's HMR. It deliberately does not simplify nested ANDs.
            // Thus the two suffix admissions conservatively fall back; this
            // is checked by the separate actual-native reset regression below.
            let (rewrites, unknown) = if enclosed { (2, 2) } else { (4, 0) };
            assert_eq!(
                (
                    new.lengths.rewrites,
                    new.lengths.unknown_scratch,
                    new.lengths.capture_blocked,
                    new.lengths.boundary_blocked,
                    new.lengths.alias_blocked
                ),
                (rewrites, unknown, 0, 0, 0),
                "inverse={inverse} enclosed={enclosed} guard decisions"
            );
            assert_eq!(new.lengths.windows[usize::from(inverse)], 1);
            assert_eq!(old.input_ops - new.input_ops, 34 * rewrites);
            for sample in 0..1028usize {
                let mut q = vec![0; 579];
                let lq = sample % 257;
                let lrp = (sample * 73 + sample / 257) % 257;
                set_word(&mut q, 531, 9, lq.wrapping_sub(1) & 511);
                set_word(&mut q, 549, 9, lrp.wrapping_sub(1) & 511);
                set_word(&mut q, 540, 9, sample % 512);
                q[560] = ((sample / 512) & 1) as u64;
                for (i, wire) in [0, 1, 3, 560, 561, 562, 563, 564, 100, 101, 102]
                    .into_iter()
                    .enumerate()
                {
                    q[wire + 1] =
                        ((sample.rotate_right(i as u32) ^ sample.wrapping_mul(13)) & 1) as u64;
                }
                for active in [0, 1] {
                    for seed in [0, 1, 2, 7] {
                        compare(&old, &new, &q, active, (sample & 1) as u64, seed);
                        cases += 1;
                    }
                }
            }
        }
    }
    println!("STABLE_LENGTH_PHASE_NATIVE PASS cases={cases}; both source directions, all257 lengths, all512 shift codes, both epochs, arbitrary flags, forced/random HMR outcomes, stale c0 and conditional future c0 read");
}

#[test]
fn stable_length_conditional_reset_proof_is_conservative() {
    let mut s = state(true, false, true, None);
    let (a, b, scratch) = (QubitId(541), QubitId(542), QubitId(566));
    assert!(s.proof.qubit_is_zero(scratch.0 as usize));
    let op = s.raw(K::CCX);
    op.q_control1 = a;
    op.q_control2 = b;
    op.q_target = scratch;
    let op = s.raw(K::Hmr);
    op.q_target = scratch;
    op.c_target = BitId(0);
    s.flush_raw();
    // The symbolic test is intentionally conservative even though the actual
    // conditional computation and reset leave this lane zero on both branches.
    assert!(!s.proof.qubit_is_zero(scratch.0 as usize));
    let op = s.raw(K::CZ);
    op.q_control1 = a;
    op.q_target = b;
    op.c_condition = BitId(0);
    s.raw(K::PopCondition);
    s.flush_raw();
    assert!(s.proof.balanced());
    assert_eq!(s.out.iter().filter(|o| o.kind == K::Hmr).count(), 1);
    for mask in 0..4u64 {
        for active in [0, 1] {
            for outcome in [0, 255] {
                let mut rng = Outcomes {
                    values: vec![outcome],
                    at: 0,
                };
                let mut sim = Simulator::new(579, 4, &mut rng);
                sim.qubits[a.0 as usize] = mask & 1;
                sim.qubits[b.0 as usize] = mask >> 1;
                sim.bits[1] = active;
                let initial = sim.qubits.clone();
                sim.apply_iter(s.out.iter());
                assert_eq!(sim.qubits, initial);
                assert_eq!(sim.phase, 0);
            }
        }
    }
    println!("STABLE_LENGTH_CONDITIONAL_PROOF_NATIVE PASS cases=16; actual clean lane and exact HMR phase correction with conservative symbolic-zero fallback");
}

#[test]
fn stable_length_single_predicate_all_outcomes() {
    let old = build(false, false, true, &FORWARD[..326], 36);
    let mut new = state(true, false, true, None);
    let mut reader = Reader {
        data: FORWARD,
        at: 0,
    };
    let mut window = None;
    assert!(try_apply(
        &mut new,
        &mut reader,
        1,
        0,
        244,
        0,
        578,
        0,
        1,
        &mut window
    ));
    assert_eq!(reader.at, 326);
    witness(&mut new, true);
    let nh = old.out.iter().filter(|o| o.kind == K::Hmr).count();
    assert_eq!(nh, 7);
    let mut cases = 0;
    for ell in 0..257usize {
        for target in [0, 1] {
            for active in [0, 1] {
                for bits in 0..128usize {
                    let mut ro = Outcomes {
                        values: (0..7)
                            .map(|i| if bits >> i & 1 == 1 { 255 } else { 0 })
                            .collect(),
                        at: 0,
                    };
                    let mut rn = Outcomes {
                        values: vec![if bits >> 6 & 1 == 1 { 255 } else { 0 }],
                        at: 0,
                    };
                    let mut a = Simulator::new(579, 4, &mut ro);
                    let mut b = Simulator::new(579, 4, &mut rn);
                    set_word(&mut a.qubits, 531, 9, ell.wrapping_sub(1) & 511);
                    a.qubits[561] = target;
                    a.qubits[102] = 1;
                    a.qubits[103] = 1;
                    a.bits = [(bits & 1) as u64, active, 1, 1].to_vec();
                    b.qubits = a.qubits.clone();
                    b.bits = a.bits.clone();
                    a.apply_iter(old.out.iter());
                    b.apply_iter(new.out.iter());
                    assert_eq!(a.qubits, b.qubits);
                    assert_eq!(a.phase, b.phase);
                    assert_eq!(a.bits[..2], b.bits[..2]);
                    cases += 1;
                }
            }
        }
    }
    println!("STABLE_LENGTH_VCHAIN_NATIVE PASS cases={cases}; all257 codes, both XOR-target states and outer conditions, all128 old HMR outcomes coupled only at final source write, future read");
}

#[test]
fn stable_length_guards_and_off_domain_witness() {
    for ell in 0..257usize {
        let code = ell.wrapping_sub(1) & 511;
        assert_eq!(code >> 8, usize::from(code == 511));
    }
    assert_ne!(256usize >> 8, usize::from(256usize == 511)); // ell257 is outside the promise.
    let digest: [u8; 32] = Sha3_256::digest(super::super::COMPRESSED_HIR).into();
    assert_eq!(digest, ARCHIVE_SHA3);
    for reason in 0..8 {
        let mut s = state(
            true,
            false,
            false,
            if reason == 0 { Some(565) } else { None },
        );
        let mut bytes = FORWARD.to_vec();
        match reason {
            0 => {}
            1 => s.lengths.enabled = false,
            2 => s.lengths.direction = None,
            3 => s.lengths.direction = Some(true),
            4 => bytes[100] ^= 1,
            5 => s.qmap[565] = s.qmap[531],
            6 => s.capture = Some(Vec::new()),
            7 => {
                s.retention.enabled = true;
                s.retention.locations[1] = vec![super::super::RetentionLocation {
                    h: 5,
                    re: 15,
                    end: 20,
                    start_byte: 0,
                    end_byte: 0,
                    t: 565,
                    a: 531,
                    b: 532,
                    c: 0,
                }];
            }
            _ => unreachable!(),
        }
        let mut reader = Reader {
            data: &bytes,
            at: 0,
        };
        let mut window = None;
        assert!(
            !try_apply(&mut s, &mut reader, 1, 0, 244, 0, 578, 0, 1, &mut window),
            "reason {reason}"
        );
        assert_eq!(reader.at, 0);
        assert_eq!(s.lengths.rewrites, 0);
    }
    let a = build(false, false, false, FORWARD, 244);
    let b = build(false, true, false, FORWARD, 244);
    assert_eq!(a.trace, b.trace);
    assert_eq!(a.input_hist, b.input_hist);
    assert_eq!(a.output_hist, b.output_hist);
    assert!(a.out.iter().zip(&b.out).all(|(a, b)| [
        a.kind as u64,
        a.q_control2.0,
        a.q_control1.0,
        a.q_target.0,
        a.c_target.0,
        a.c_condition.0
    ] == [
        b.kind as u64,
        b.q_control2.0,
        b.q_control1.0,
        b.q_target.0,
        b.c_target.0,
        b.c_condition.0
    ]));
    // Direct caller mapping admission and rejected boundaries/conditions.
    let mut s = state(true, false, false, None);
    s.cmap.resize(257, BitId(0));
    s.qmap.extend((0..578).map(|q| QubitId((q + 1) as u64)));
    for &q in &FRAME {
        let parent = match q {
            0 => 518,
            1 => 519,
            3 => 521,
            _ => q,
        };
        s.qmap[578 + q] = s.qmap[parent];
    }
    assert_eq!(
        child_direction(&s, 2261, 146050, 0, 578, 0, 256, 6, 578, 578, 256, 1, 0),
        Some(false)
    );
    assert_eq!(
        child_direction(&s, 2263, 18429, 0, 578, 0, 256, 1132, 578, 578, 256, 1, 0),
        Some(true)
    );
    for (parent, ordinal, child, cond) in [
        (2261, 146049, 6, 0),
        (2261, 147670, 6, 0),
        (2263, 18428, 1132, 0),
        (2263, 20049, 1132, 0),
        (2261, 146050, 6, 1),
        (2262, 146050, 6, 0),
    ] {
        assert_eq!(
            child_direction(&s, parent, ordinal, 0, 578, 0, 256, child, 578, 578, 256, 1, cond),
            None
        );
    }
}

#[test]
#[ignore = "root-owned full-source count only; no artifact or simulation"]
fn stable_length_full_source_census() {
    let data = zstd::stream::decode_all(super::super::COMPRESSED_HIR).unwrap();
    let g = parse_graph(&data);
    super::super::shared_product::validate_phase_child(&g);
    super::super::comparator::validate_helper(&g);
    let mut s = State::new(
        g.root_qubits,
        g.root_bits,
        &(1..=512).collect::<Vec<_>>(),
        &(0..512).collect::<Vec<_>>(),
        false,
        0,
    );
    configure(&mut s, &g, super::super::COMPRESSED_HIR);
    assert!(s.lengths.enabled, "set Q834_STABLE_LENGTH_ZERO=1");
    s.endpoint_enabled = true;
    s.carry_enabled = true;
    s.motif_enabled = true;
    s.motif_exclusions = super::super::motif::exclusions(&g);
    expand_node(&g, &mut s, g.root, 0, g.root_qubits, 0, g.root_bits);
    s.flush_raw();
    s.assert_accounting(g.summaries[g.root].output_ops, 0);
    assert!(
        s.out.is_empty()
            && s.proof.balanced()
            && s.capture.is_none()
            && s.comparator_capture.is_none()
    );
    let t = s.output_hist[K::CCX as usize] + s.output_hist[K::CCZ as usize] - s.outer_lowered;
    let conditional =
        512 * s.predicate_blocks - s.carry_selected - s.endpoint_blocks - s.endpoint_outer;
    println!("STABLE_LENGTH_CENSUS windows={:?} rewrites={} unknown_scratch={} captures={} boundaries={} alias={} prepeephole_ops={} expected_2T={} no_whole_circuit_validation=true",s.lengths.windows,s.lengths.rewrites,s.lengths.unknown_scratch,s.lengths.capture_blocked,s.lengths.boundary_blocked,s.lengths.alias_blocked,s.output_ops+4*257-2,2*t-conditional);
}
