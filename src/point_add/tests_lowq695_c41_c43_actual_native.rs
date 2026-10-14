//! Genuine actual5572 HR C41/q2 and C43/q6babca, continuous full columns.
//! Native phase only; masked reciprocal polynomial checks are separate.
use super::*;
use crate::point_add::frogdrop_col::{ColScr, column_pl};

#[test]
#[ignore = "ROOT frozen source, independent admission and fresh complete invoice"]
fn lowq695_actual5572_c41_c43_fullcolumns_continuous_native_phase_v2() {
    use crate::sim::Simulator;
    use sha3::{Shake256, digest::{Update, ExtendableOutput}};
    let (cols, _, _) = crate::point_add::pointadd_frogdrop::col_pars(
        &crate::point_add::frogdrop_sched::from_text(
            crate::point_add::pointadd_frogdrop::SCHED_FROGDROP));
    assert_eq!(cols.len(), 203);
    assert!(crate::point_add::midg::TC >= 25, "no baseline precision reduction");
    let mut records = Vec::new();
    let mut applications = 0u64;
    let mut retained = 0u64;
    for c in [41usize, 43] {
        let cp = &cols[c];
        assert!(cp.hr && cp.ht && cp.dl && !cp.dn);
        assert_eq!(cp.sz, if c == 41 { (116, 224) } else { (116, 221) });
        assert_eq!(cp.sy, if c == 41 { (32, 135) } else { (34, 135) });
        let mut b = default_builder();
        let f = trace_frame(&mut b);
        let mut fd = fd_of(&f);
        let sc = ColScr::carve_col(&f.pool, &fd.sx, &f.dirty,
                                 cp.kp, cp.qb, cp.tail, false);
        let record = rec(&mut b, |b| column_pl(b, &mut fd, cp, &sc, None));
        let forward = default_emitted(&mut b, &record, false);
        let reverse = default_emitted(&mut b, &record, true);
        let n = (forward.len() + reverse.len()) as u64;
        retained = retained.checked_add(n).unwrap();
        applications = applications.checked_add(n.checked_mul(2).unwrap()).unwrap();
        let nb = crate::circuit::analyze_ops(forward.iter().chain(reverse.iter())).1;
        eprintln!("LOWQ695_C41_C43_COLUMN_INVOICE C={c} N_F={} N_I={} classical_bits={nb} TC={} pairs=2 native_only=true fixture_created=false native_started=false",
                  forward.len(), reverse.len(), crate::point_add::midg::TC);
        records.push((c, f, fd, forward, reverse, nb));
    }
    // Sum both complete columns and both orders before model, RNG or Sim.
    eprintln!("LOWQ695_C41_C43_COMPLETE_NATIVE_INVOICE physical_applications={applications} retained_ops={retained} app_cap=100000000 retained_cap=20000000 width=695 allow_booth=true global_cancel=true eager_rows=true payload_hooks=false fixture_created=false native_started=false");
    assert!(applications <= 100_000_000 && retained <= 20_000_000,
            "complete same-binary native invoice before numerical fixtures/simulation");

    let xr = N::from_str_radix(
        "1086eb85872ce639995089f820f41aa32723de5bb56a320d175c954cc4123439", 16).unwrap();
    let p = crate::point_add::frogdrop_sched::p();
    let mut r = vec![p, xr];
    let mut t = vec![N::ZERO, N::from(1u64)];
    while !r.last().unwrap().is_zero() {
        let n = r.len();
        let q = r[n - 2] / r[n - 1];
        r.push(r[n - 2] - q * r[n - 1]);
        t.push(t[n - 2] + q * t[n - 1]);
    }
    let shot = crate::point_add::frogdrop_sched::shot(xr, crate::point_add::frogdrop_sched::L0);
    assert!(shot.recs[..=43].iter().all(|x| x.kind == crate::point_add::frogdrop_sched::Kind::Hr));
    let mut apps = 0u64;
    for (c, f, fd, forward, reverse, nb) in records {
        let j = c + 1;
        let (true_q, sz, sy) = if c == 41 { (2u64, 185usize, 70usize) }
                              else { (0x6babcau64, 163usize, 72usize) };
        assert_eq!(r[j - 1] / r[j], N::from(true_q));
        assert_eq!(r[j].bit_len(), sz);
        assert_eq!(t[j].bit_len(), sy);
        assert_eq!(shot.recs[c].sz, sz);
        assert_eq!(shot.recs[c].sy, sy);
        assert_eq!(p, r[j] * t[j - 1] + r[j - 1] * t[j]);
        assert_eq!(p, r[j] * t[j + 1] + r[j + 1] * t[j]);
        let mut rng = Rng::new(0x695_5572_c41c43 + c as u64);
        let mut input = vec![0u64; 695];
        for &q in &f.dirty { input[q.0 as usize] = rng.next(); }
        let mut want = input.clone();
        let cut_in = 279 - t[j - 1].bit_len().max(t[j].bit_len());
        let cut_out = 279 - t[j].bit_len().max(t[j + 1].bit_len());
        assert!(r[j].bit_len() <= cut_in && r[j + 1].bit_len() <= cut_out);
        for lane in 0..64 {
            put(&mut input, &f.ring[..cut_in], lane, r[j]);
            put(&mut input, &top(&f.ring[cut_in..]), lane, t[j]);
            put(&mut input, &f.q, lane, t[j - 1]);
            put(&mut input, &f.sy, lane, N::from(sy as u64));
            put(&mut want, &f.ring[..cut_out], lane, r[j + 1]);
            put(&mut want, &top(&f.ring[cut_out..]), lane, t[j + 1]);
            put(&mut want, &f.q, lane, t[j]);
            put(&mut want, &fd.sy, lane, N::from(t[j + 1].bit_len() as u64));
        }
        assert_eq!(input[f.ph.0 as usize], 0);
        assert_eq!(want[f.ph.0 as usize], 0);
        eprintln!("LOWQ695_C41_C43_EXACT_MODEL C={c} j={j} true_q={true_q:x} SZ={sz} SY={sy} lanes=64 genuine_Euclid=true dirty259_varied=true fullcolumn=true payload_hooks=false initialized_prefix=false polynomial_phase_claim=false");
        for inverse_first in [false, true] {
            let mut h = Shake256::default();
            h.update(b"lowq695-actual5572-c41-c43-fixed-continuous-native-phase-v2");
            h.update(&[c as u8, u8::from(inverse_first)]);
            let mut xof = h.finalize_xof();
            let mut sim = Simulator::new(695, (nb as usize).max(1), &mut xof);
            sim.qubits = if inverse_first { want.clone() } else { input.clone() };
            let first = if inverse_first { &reverse } else { &forward };
            let second = if inverse_first { &forward } else { &reverse };
            sim.apply_iter(first.iter()); apps += first.len() as u64;
            assert_eq!(sim.phase, 0, "exact native phase at C{c} midpoint");
            let midpoint = if inverse_first { &input } else { &want };
            trace_assert_all(&sim.qubits, midpoint, &f, &fd, "actual5572_C41_C43_native_midpoint");
            sim.apply_iter(second.iter()); apps += second.len() as u64;
            assert_eq!(sim.phase, 0, "exact native phase at C{c} return");
            assert_eq!(sim.qubits, if inverse_first { want.clone() } else { input.clone() },
                       "C{c} continuous return all695 and arbitrary payload259");
        }
    }
    assert_eq!(apps, applications);
    eprintln!("LOWQ695_ACTUAL5572_C41_C43_FULLCOLUMNS_CONTINUOUS_NATIVE_PASS columns=2 packs=4 lanes=256 all695=true dirty259_DATA=true trueq2_and_q6babca=true native_phase0=true FI=true IF=true no_interpass_classical_phase_XOF_reset=true physical_applications={apps} polynomial_phase_claim=false initialized_prefix=false whole=false");
}
