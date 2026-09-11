//! Small profile and actual CTZ boundary tests. Full baseline operation-hash
//! comparison and empirical tail support validation remain separate root jobs.
use super::*;
use crate::circuit::{analyze_ops, QubitId};
use crate::sim::Simulator;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

fn static_contracts() {
    for &profile in PROFILES {
        validate(profile);
        assert_eq!(
            profile.ctz_bits,
            bits_needed(profile.value_widths[0] as usize)
        );
        assert_eq!(profile.checkpoint_start, profile.rounds - 4);
        assert!(profile.value_widths[profile.checkpoint_start..]
            .iter()
            .all(|&w| w == 4));
    }
    let baseline = *PROFILES
        .iter()
        .find(|p| p.id == "cut360")
        .expect("baseline profile present");
    assert!(baseline_layout(baseline));
    assert_eq!(baseline.value_widths, BASELINE_WIDTHS);
    assert_eq!(
        (
            baseline.pz_cut,
            baseline.rounds,
            baseline.ctz_bits,
            baseline.checkpoint_start,
            baseline.payload_replay_start
        ),
        (360, 224, 7, 220, 180)
    );
    let mut changed = baseline;
    changed.pz_cut = 340;
    assert!(!baseline_layout(changed));
    changed = baseline;
    changed.rounds = 228;
    assert!(!baseline_layout(changed));
    changed = baseline;
    changed.baseline_compatible = false;
    assert!(!baseline_layout(changed));
    if SELECTED.baseline_compatible {
        assert_eq!(
            super::super::MIDQ_TAIL_VALUE_WIDTH.as_slice(),
            BASELINE_WIDTHS
                .iter()
                .map(|&w| w as u8)
                .collect::<Vec<_>>()
                .as_slice()
        );
        assert!(legacy_margin_allowed() && legacy_metadata_allowed());
    } else {
        assert!(!legacy_margin_allowed() && !legacy_metadata_allowed());
    }
    assert_eq!(parsed_runtime_cap(None), None);
    for cap in [1000, 1009, 1019, 1040, 1060, 1080, 1100, 1120, 1132] {
        assert_eq!(parsed_runtime_cap(Some(&cap.to_string())), Some(cap));
    }
    if let Some(cap) = runtime_cap() {
        for name in SOFT_CAPS {
            assert_eq!(std::env::var(name).unwrap(), cap.to_string());
        }
        assert_eq!(hard_ceiling(), cap);
    } else {
        assert_eq!(hard_ceiling(), 1019);
    }
    assert_eq!(
        super::super::midq_tail_checkpoint::START,
        SELECTED.rounds - 4
    );
    assert!(super::super::quotient_code::supports_width(18));
    assert!(super::super::quotient_code::supports_width(17));
    assert!(super::super::quotient_code::supports_width(19));
    assert!(!super::super::quotient_code::supports_width(0));
    assert!(!super::super::quotient_code::supports_width(258));
    for n in 1..=257 {
        assert_eq!(super::super::quotient_code::code_bits(n), bits_needed(n));
    }
    assert!(super::super::quotient_code::legacy_rank_width(18));
    assert!(!super::super::quotient_code::legacy_rank_width(17));
}

struct Measurements {
    forced: Option<u8>,
    random: sha3::Shake256Reader,
}
impl XofReader for Measurements {
    fn read(&mut self, b: &mut [u8]) {
        if let Some(v) = self.forced {
            b.fill(v);
        } else {
            self.random.read(b);
        }
    }
}

fn ctz_native() {
    let width = SELECTED.value_widths[0] as usize;
    let mut c = super::super::Circuit::new();
    let value = c.alloc_qreg_bits("profile.ctz.input", width);
    let ids: Vec<_> = value.iter().map(|q| QubitId(q.id().into())).collect();
    let count = super::super::midq_compute_ctz(&mut c, &value, "profile.ctz.count");
    assert_eq!(count.len(), SELECTED.ctz_bits);
    let count_ids: Vec<_> = count.iter().map(|q| QubitId(q.id().into())).collect();
    c.flush_pending_frees();
    let split = c.b.ops.len();
    super::super::midq_uncompute_ctz(&mut c, &value, count);
    c.flush_pending_frees();
    for op in &c.b.ops {
        op.validate();
    }
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let nq = nq.max(ids.iter().chain(&count_ids).map(|q| q.0 + 1).max().unwrap());
    let mut inputs = vec![vec![false; width]];
    for i in 0..width {
        let mut row = vec![false; width];
        row[i] = true;
        inputs.push(row);
    }
    for sample in 0..64usize {
        inputs.push(
            (0..width)
                .map(|i| {
                    sample
                        .wrapping_mul(173)
                        .wrapping_add(i * 137)
                        .rotate_right((i % usize::BITS as usize) as u32)
                        & 1
                        != 0
                })
                .collect(),
        );
    }
    let mut cases = 0;
    for forced in [Some(0), Some(255), Some(0x55), None] {
        let mut hash = Shake256::default();
        hash.update(b"hybrid-profile-ctz-native-v1");
        let mut rng = Measurements {
            forced,
            random: hash.finalize_xof(),
        };
        let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        for batch in inputs.chunks(64) {
            sim.clear_for_shot();
            let live = u64::MAX >> (64 - batch.len());
            for (i, &id) in ids.iter().enumerate() {
                *sim.qubit_mut(id) = batch
                    .iter()
                    .enumerate()
                    .fold(0, |v, (j, row)| v | u64::from(row[i]) << j);
            }
            let before = sim.qubits.clone();
            sim.phase = 0xa53c_09f0_1278_ee11;
            super::super::predicate_clear_selftest::checked_apply(
                &mut sim,
                &c.b.ops[..split],
                live,
            );
            for (j, row) in batch.iter().enumerate() {
                let expected = row.iter().position(|&x| x).unwrap_or(width - 1);
                let got = count_ids.iter().enumerate().fold(0usize, |v, (i, &id)| {
                    v | (((sim.qubit(id) >> j) & 1) as usize) << i
                });
                assert_eq!(
                    got,
                    expected,
                    "CTZ profile={} case={} width={width}",
                    SELECTED.id,
                    cases + j
                );
            }
            for &id in &ids {
                assert_eq!(sim.qubit(id) & live, before[id.0 as usize] & live);
            }
            assert_eq!(sim.phase & live, 0xa53c_09f0_1278_ee11 & live);
            super::super::predicate_clear_selftest::checked_apply(
                &mut sim,
                &c.b.ops[split..],
                live,
            );
            for (i, &value) in sim.qubits.iter().enumerate() {
                assert_eq!(
                    value & live,
                    before[i] & live,
                    "CTZ inverse scratch/data q{i}"
                );
            }
            assert_eq!(sim.phase & live, 0xa53c_09f0_1278_ee11 & live);
            cases += batch.len();
        }
    }
    eprintln!("HYBRID_PROFILE_CTZ_NATIVE PASS profile={} width={width} count_bits={} cases={cases} legacy_zero_sentinel_is_width_minus_one=true every_one_hot=true value_phase_reset_inverse=true",SELECTED.id,SELECTED.ctz_bits);
}

pub(crate) fn run() {
    static_contracts();
    report();
    ctz_native();
    eprintln!("HYBRID_PROFILE_SELFTEST PASS static_profiles={} baseline_table_exact=true no_full_circuit_or_tail_support_claim=true",PROFILES.len());
}

#[cfg(test)]
#[test]
fn hybrid_profile_static_contracts() {
    crate::point_add::trailmix_port::configure_sub1000_trailmix_route();
    static_contracts();
}
