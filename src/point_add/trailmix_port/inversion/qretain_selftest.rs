use super::super::{division_substep_retained_lengths, Circuit, GateControl, QReg};
use super::*;
use crate::circuit::{analyze_ops, Op, QubitId};
use crate::sim::Simulator;
use sha3::digest::XofReader;

struct Guard(Vec<(&'static str, Option<String>)>);
impl Guard {
    fn new() -> Self {
        Self(
            [
                "HYBRID_QRETAIN",
                "TRAILMIX_Q_TARGET",
                "TRAILMIX_Q_CAP",
                "TRAILMIX_SROT_W",
                "MIDQ_PZ_PINGPONG_TAIL",
                "LOWQ_ONE_A_ELIM",
                "LOWQ_CLZ_DIFF_CONST_FOLD",
                "LOWQ_BORROW_PASSENGER_CARRY",
            ]
            .into_iter()
            .map(|n| (n, std::env::var(n).ok()))
            .collect(),
        )
    }
}
impl Drop for Guard {
    fn drop(&mut self) {
        for (n, v) in &self.0 {
            if let Some(v) = v {
                std::env::set_var(n, v);
            } else {
                std::env::remove_var(n);
            }
        }
    }
}
fn enable() {
    for (name, value) in [
        ("HYBRID_QRETAIN", "32"),
        ("TRAILMIX_Q_TARGET", "684"),
        ("TRAILMIX_Q_CAP", "99"),
        ("TRAILMIX_SROT_W", "5"),
        ("MIDQ_PZ_PINGPONG_TAIL", "1"),
    ] {
        std::env::set_var(name, value);
    }
}

fn witness() {
    // Recorded exact steps322..337 from failed control input1465. Actions are
    // the ideal quotient writes/drains; after an old resize fails, that old
    // trajectory is no longer claimed to describe the actual circuit.
    let actions = [21, 17, 16, 13, 10, 5, 3, 0, 0, 3, 5, 10, 13, 16, 17, 21];
    let old_widths = [
        22, 22, 22, 22, 22, 18, 18, 22, 22, 22, 20, 22, 21, 21, 21, 20,
    ];
    let expected = [
        0x200000, 0x220000, 0x230000, 0x232000, 0x232400, 0x232420, 0x232428, 0x232429, 0x232428,
        0x232420, 0x232400, 0x232000, 0x230000, 0x220000, 0x200000, 0,
    ];
    let mut q = 0u64;
    let mut count = 0u32;
    let mut first_old_loss = None;
    for (offset, &bit) in actions.iter().enumerate() {
        let step = 322 + offset;
        let old_discard = q & !((1u64 << old_widths[offset]) - 1);
        if old_discard != 0 && first_old_loss.is_none() {
            first_old_loss = Some((step, q, old_discard));
        }
        assert_eq!(q >> WIDTH, 0);
        if offset > 0 {
            assert_eq!((q >> 21) & 1, 1, "retained high bit at step{step}");
        }
        q ^= 1u64 << bit;
        if offset < 8 {
            count += 1;
        } else {
            count -= 1;
        }
        assert_eq!(q, expected[offset]);
        assert_eq!(q.count_ones(), count);
    }
    assert_eq!(first_old_loss, Some((327, 0x232400, 0x200000)));
    assert_eq!((q, count), (0, 0));
    assert_eq!(super::super::quotient_code::code_bits(WIDTH), 6);
}

fn policy() {
    let _guard = Guard::new();
    enable();
    assert_eq!(fixed_width(), Some(32));
    assert_eq!(initial_width(18), 32);
    let mut rows = [[103, 103, 230, 230, 18], [98, 98, 232, 232, 21]];
    assert!(apply_to_model_rows(&mut rows));
    for row in rows {
        assert_eq!(row[4], 32);
        assert_eq!(
            super::super::trailmix_q_width_step(
                18,
                row[0] as usize,
                row[1] as usize,
                row[2] as usize,
                row[3] as usize
            ),
            32
        );
    }
    for (name, value) in [
        ("TRAILMIX_Q_TARGET", "999"),
        ("TRAILMIX_SROT_W", "6"),
        ("TRAILMIX_Q_CAP", "31"),
        ("MIDQ_PZ_PINGPONG_TAIL", "0"),
    ] {
        enable();
        std::env::set_var(name, value);
        assert!(std::panic::catch_unwind(fixed_width).is_err());
    }
    enable();
    std::env::set_var("HYBRID_QRETAIN", "off");
    assert_eq!(fixed_width(), None);
    assert_eq!(initial_width(22), 22);
    let mut old = [[103, 103, 230, 230, 22]];
    assert!(!apply_to_model_rows(&mut old));
    assert_eq!(old[0][4], 22);
    assert_eq!(
        super::super::trailmix_q_width_step(22, 103, 103, 230, 230),
        18
    );
}

struct Outcomes {
    fixed: Option<u8>,
    state: u64,
}
impl XofReader for Outcomes {
    fn read(&mut self, out: &mut [u8]) {
        if let Some(v) = self.fixed {
            out.fill(v);
        } else {
            for b in out {
                self.state ^= self.state << 13;
                self.state ^= self.state >> 7;
                self.state ^= self.state << 17;
                *b = self.state as u8;
            }
        }
    }
}
struct Built {
    ops: Vec<Op>,
    split: usize,
    ids: Vec<Vec<QubitId>>,
    nq: usize,
    nb: usize,
}
fn ids(v: &[QReg]) -> Vec<QubitId> {
    v.iter().map(|q| QubitId(q.id().into())).collect()
}
fn build(optimized: bool, n: usize) -> Built {
    for key in [
        "LOWQ_ONE_A_ELIM",
        "LOWQ_CLZ_DIFF_CONST_FOLD",
        "LOWQ_BORROW_PASSENGER_CARRY",
    ] {
        std::env::set_var(key, if optimized { "1" } else { "0" });
    }
    assert_eq!(super::super::lowq_one_a_elim_enabled(), optimized);
    assert_eq!(
        super::super::lowq_borrow_passenger_carry_enabled(),
        optimized
    );
    assert_eq!(super::super::lowq_clz_diff_const_fold_enabled(), optimized);
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("qr.test.a", n);
    let b = c.alloc_qreg_bits("qr.test.b", n);
    let q = c.alloc_qreg_bits("qr.test.q", initial_width(22));
    let shift = c.alloc_qreg_bits("qr.test.shift", 5);
    let offset = c.alloc_qreg("qr.test.offset");
    let active = c.alloc_qreg("qr.test.active");
    let carry = c.alloc_qreg("qr.test.borrowed_zero");
    let ids = vec![
        ids(&a),
        ids(&b),
        ids(&q),
        ids(std::slice::from_ref(&active)),
        ids(std::slice::from_ref(&carry)),
    ];
    division_substep_retained_lengths(
        &mut c,
        &a,
        &b,
        &q,
        &shift,
        &offset,
        GateControl::Direct(&active),
        Some(&carry),
        2,
        1,
        5,
        false,
    );
    c.flush_pending_frees();
    let split = c.b.ops.len();
    division_substep_retained_lengths(
        &mut c,
        &a,
        &b,
        &q,
        &shift,
        &offset,
        GateControl::Direct(&active),
        Some(&carry),
        2,
        1,
        5,
        true,
    );
    c.flush_pending_frees();
    let b = c.into_builder();
    let (nq, nb, _, _) = analyze_ops(b.ops.iter());
    let nq = (nq as usize).max(
        ids.iter()
            .flatten()
            .map(|q| q.0 as usize + 1)
            .max()
            .unwrap(),
    );
    Built {
        ops: b.ops,
        split,
        ids,
        nq,
        nb: nb as usize,
    }
}
fn unsupported_alignment(built: &Built) {
    // True pre-offset delta32 / effective j31 is NOT SROT5 support. This
    // coherent finite-word route can round-trip while computing the wrong
    // greedy quotient; retain an explicit native negative witness.
    let a = (3u64 << 32) - 8;
    let b = 3u64;
    let delta = (64 - a.leading_zeros()) - (64 - b.leading_zeros());
    assert_eq!(delta, 32);
    assert!(a < b << delta);
    let input = [a, b, 0, 1, 0];
    for fixed in [Some(0), Some(255), Some(0x55), None] {
        let mut rng = Outcomes {
            fixed,
            state: 0x7385_124e_6783_2321,
        };
        let mut sim = Simulator::new(built.nq, built.nb + 1, &mut rng);
        for (reg, value) in built.ids.iter().zip(input) {
            for (i, q) in reg.iter().enumerate() {
                sim.qubits[q.0 as usize] = (value >> i) & 1;
            }
        }
        let initial = sim.qubits.clone();
        sim.phase = 1;
        super::super::predicate_clear_selftest::checked_apply(
            &mut sim,
            &built.ops[..built.split],
            1,
        );
        let read = |reg: &[QubitId], qubits: &[u64]| {
            reg.iter()
                .enumerate()
                .fold(0u64, |v, (i, q)| v | ((qubits[q.0 as usize] & 1) << i))
        };
        assert_ne!(
            (
                read(&built.ids[0], &sim.qubits),
                read(&built.ids[2], &sim.qubits)
            ),
            (a - (b << 31), 1u64 << 31)
        );
        assert_eq!(sim.phase & 1, 1);
        super::super::predicate_clear_selftest::checked_apply(
            &mut sim,
            &built.ops[built.split..],
            1,
        );
        for (a, b) in sim.qubits.iter().zip(&initial) {
            assert_eq!(a & 1, b & 1);
        }
        assert_eq!(sim.phase & 1, 1);
    }
}
fn native() {
    let _guard = Guard::new();
    enable();
    let mut cases = Vec::new();
    for seed in 0..128usize {
        let b = 2 + (13 * seed) % 126;
        let base = b.max(4);
        let a = base + (seed * 7) % (256 - base);
        let delta = (usize::BITS - a.leading_zeros()) - (usize::BITS - b.leading_zeros());
        let aligned = b << delta;
        let off = usize::from(a < aligned);
        if (a >> 2 < aligned >> 2) != (off != 0) {
            continue;
        }
        let j = delta as usize - off;
        for enabled in [0u64, 1] {
            for prior in [0, 1u64 << 21, 1u64 << 31, (1u64 << 21) | (1u64 << 31)] {
                cases.push((
                    [a as u64, b as u64, prior, enabled, 0],
                    [
                        (a - enabled as usize * (b << j)) as u64,
                        b as u64,
                        prior ^ (enabled << j),
                        enabled,
                        0,
                    ],
                ));
            }
        }
    }
    // Actually create/consume the top q bit on a wide enough operand, not
    // merely retain it while operating on lower positions.
    let mut wide = Vec::new();
    for (a, b, prior) in [
        ((2u64 << 31) + 16, 2u64, 0),
        ((3u64 << 31) - 8, 3, 0),
        ((3u64 << 31) - 8, 3, 1u64 << 31),
        ((2u64 << 30) + 8, 2, 1u64 << 31),
    ] {
        let delta = (64 - a.leading_zeros()) as usize - (64 - b.leading_zeros()) as usize;
        let off = u64::from(a < (b << delta));
        let j = delta - off as usize;
        assert!(delta < 32 && j < 32);
        assert!(prior == 0 || prior.trailing_zeros() as usize > j);
        for enabled in [0u64, 1] {
            wide.push((
                [a, b, prior, enabled, 0],
                [
                    a - enabled * (b << j),
                    b,
                    prior ^ (enabled << j),
                    enabled,
                    0,
                ],
            ));
        }
    }
    let mut checked = 0;
    for optimized in [false, true] {
        for (n, cases) in [(8, &cases), (40, &wide)] {
            let built = build(optimized, n);
            for batch in cases.chunks(64) {
                for fixed in [Some(0), Some(255), Some(0x55), None] {
                    let mut rng = Outcomes {
                        fixed,
                        state: 0x7a08_3485_fa34_abc9,
                    };
                    let mut sim = Simulator::new(built.nq, built.nb + 1, &mut rng);
                    let mut expected = vec![0u64; built.nq];
                    for (lane, (input, output)) in batch.iter().enumerate() {
                        for ((reg, &a), &b) in built.ids.iter().zip(input).zip(output) {
                            for (bit, &q) in reg.iter().enumerate() {
                                sim.qubits[q.0 as usize] |= ((a >> bit) & 1) << lane;
                                expected[q.0 as usize] |= ((b >> bit) & 1) << lane;
                            }
                        }
                    }
                    let initial = sim.qubits.clone();
                    let phase = 0x8127_af35_3301_75bcu64;
                    sim.phase = phase;
                    let mask = u64::MAX >> (64 - batch.len());
                    super::super::predicate_clear_selftest::checked_apply(
                        &mut sim,
                        &built.ops[..built.split],
                        mask,
                    );
                    for (a, b) in sim.qubits.iter().zip(&expected) {
                        assert_eq!(a & mask, b & mask);
                    }
                    assert_eq!(sim.phase & mask, phase & mask);
                    super::super::predicate_clear_selftest::checked_apply(
                        &mut sim,
                        &built.ops[built.split..],
                        mask,
                    );
                    for (a, b) in sim.qubits.iter().zip(&initial) {
                        assert_eq!(a & mask, b & mask);
                    }
                    assert_eq!(sim.phase & mask, phase & mask);
                    checked += batch.len();
                }
            }
        }
        unsupported_alignment(&build(optimized, 40));
    }
    eprintln!("QRETAIN_NATIVE PASS cases={checked} q_bits=32 retained_high_bits=21/31 optimized_and_plain_backends=true value_phase_every_reset_forward_inverse=true; no_whole_profile_membership_claim=true");
}
pub(crate) fn run() {
    witness();
    policy();
    native();
    report();
}
#[cfg(test)]
#[test]
fn qretain_scalar_lifetime_witness() {
    witness();
}
#[cfg(test)]
#[test]
fn qretain_policy_alignment_and_rejections() {
    policy();
}
