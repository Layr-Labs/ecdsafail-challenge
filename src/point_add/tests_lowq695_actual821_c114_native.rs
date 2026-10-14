//! Frozen actual821 reflected dx2: genuine C114 HT with 24-bit quotient.
//! Continuous native FI/IF and phase; no initialized-prefix or polynomial claim.
use super::*;
use crate::point_add::frogdrop_col::{ColScr, column_pl};

#[test]
#[ignore = "ROOT fresh frozen compile and complete invoice; genuine missing-bit witness"]
fn lowq695_actual821_c114_q24_fullcolumn_continuous_native_phase_v1() {
    use crate::sim::Simulator;
    use sha3::{Shake256, digest::{Update, ExtendableOutput}};
    let (cols, _, _) = crate::point_add::pointadd_frogdrop::col_pars(
        &crate::point_add::frogdrop_sched::from_text(
            crate::point_add::pointadd_frogdrop::SCHED_FROGDROP));
    assert_eq!(cols.len(), 203);
    let cp = &cols[114];
    assert!(cp.ht && cp.dn && !cp.sw && !cp.dl && !cp.dq);
    assert_eq!((cp.n, cp.k, cp.h), (279, 20, 22));
    assert_eq!((cp.sz, cp.sy), ((127, 255), (1, 129)));
    assert!(crate::point_add::midg::TC >= 32);
    let mut b = default_builder();
    let f = trace_frame(&mut b);
    let mut fd = fd_of(&f);
    let sc = ColScr::carve_col(&f.pool, &fd.sx, &f.dirty,
                             cp.kp, cp.qb, cp.tail, false);
    let record = rec(&mut b, |b| column_pl(b, &mut fd, cp, &sc, None));
    let forward = default_emitted(&mut b, &record, false);
    let reverse = default_emitted(&mut b, &record, true);
    let retained = (forward.len() + reverse.len()) as u64;
    let applications = retained.checked_mul(2).unwrap();
    let nb = crate::circuit::analyze_ops(forward.iter().chain(reverse.iter())).1;
    eprintln!("LOWQ695_ACTUAL821_C114_COMPLETE_NATIVE_INVOICE N_F={} N_I={} physical_applications={applications} retained_ops={retained} app_cap=100000000 retained_cap=20000000 width=695 TC={} pairs=2 native_only=true allow_booth=true global_cancel=true payload_hooks=false fixture_created=false native_started=false",
              forward.len(), reverse.len(), crate::point_add::midg::TC);
    assert!(applications <= 100_000_000 && retained <= 20_000_000,
            "complete native FI/IF invoice before model, RNG, XOF or Sim");

    let xr = N::from_str_radix(
        "1768699576735cdf3c72fa66285e102621f59bfe5c53f5eb0be9c0464ade9071", 16).unwrap();
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
    use crate::point_add::frogdrop_sched::Kind;
    let j = 1 + shot.recs[..114].iter().filter(|rec|
        matches!(rec.kind, Kind::Hr | Kind::Ht | Kind::Dq)).count();
    assert_eq!(j, 114);
    assert_eq!(shot.recs[114].kind, Kind::Ht);
    assert_eq!((shot.recs[114].sz, shot.recs[114].sy), (204, 29));
    let true_q = r[j - 1] / r[j];
    assert_eq!(true_q, N::from(0xbf6af5u64));
    assert_eq!(true_q.bit_len(), 24);
    assert_eq!(r[j], N::from(0x1e6f1ba4u64));
    assert_eq!(r[j - 1], N::from(0x16c19cca687ae1u64));
    assert_eq!(r[j + 1], N::from(0x9451eedu64));
    assert_eq!(t[j].bit_len(), 204);
    assert_eq!(p, t[j] * r[j - 1] + t[j - 1] * r[j]);
    assert_eq!(p, t[j] * r[j + 1] + t[j + 1] * r[j]);
    let cut_in = 279 - r[j - 1].bit_len().max(r[j].bit_len());
    let cut_out = 279 - r[j].bit_len().max(r[j + 1].bit_len());
    assert_eq!((cut_in, cut_out), (226, 250));
    assert!(t[j].bit_len() <= cut_in && t[j + 1].bit_len() <= cut_out);
    let mut rng = Rng::new(0x695_821_c114);
    let mut input = vec![0u64; 695];
    for &q in &f.dirty { input[q.0 as usize] = rng.next(); }
    let mut want = input.clone();
    for lane in 0..64 {
        put(&mut input, &f.ring[..cut_in], lane, t[j]);
        put(&mut input, &top(&f.ring[cut_in..]), lane, r[j]);
        put(&mut input, &f.q, lane, r[j - 1]);
        put(&mut input, &f.sy, lane, N::from(29u64));
        put(&mut want, &f.ring[..cut_out], lane, t[j + 1]);
        put(&mut want, &top(&f.ring[cut_out..]), lane, r[j + 1]);
        put(&mut want, &f.q, lane, r[j]);
        put(&mut want, &fd.sy, lane, N::from(28u64));
    }
    input[f.ph.0 as usize] = u64::MAX;
    want[f.ph.0 as usize] = u64::MAX;
    eprintln!("LOWQ695_ACTUAL821_C114_EXACT_MODEL j=114 kind=HT true_q=bf6af5 quotient_bits=24 SZ=204 SY=29 cut_in=226 cut_out=250 PH1=true genuine_Euclid=true dirty259_varied=true all695=true fullcolumn=true payload_hooks=false initialized_prefix=false polynomial_phase_claim=false");
    let mut apps = 0u64;
    for inverse_first in [false, true] {
        let mut h = Shake256::default();
        h.update(b"lowq695-actual821-c114-q24-continuous-native-phase-v1");
        h.update(&[u8::from(inverse_first)]);
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(695, (nb as usize).max(1), &mut xof);
        sim.qubits = if inverse_first { want.clone() } else { input.clone() };
        let first = if inverse_first { &reverse } else { &forward };
        let second = if inverse_first { &forward } else { &reverse };
        sim.apply_iter(first.iter()); apps += first.len() as u64;
        assert_eq!(sim.phase, 0, "genuine C114 native midpoint phase");
        let midpoint = if inverse_first { &input } else { &want };
        trace_assert_all(&sim.qubits, midpoint, &f, &fd, "actual821_C114_q24_native_midpoint");
        sim.apply_iter(second.iter()); apps += second.len() as u64;
        assert_eq!(sim.phase, 0, "genuine C114 native return phase");
        assert_eq!(sim.qubits, if inverse_first { want.clone() } else { input.clone() },
                   "continuous C114 all695 return with unrestricted dirty payload");
    }
    assert_eq!(apps, applications);
    eprintln!("LOWQ695_ACTUAL821_C114_Q24_FULLCOLUMN_CONTINUOUS_NATIVE_PASS columns=1 packs=2 lanes=128 all695=true dirty259_DATA=true trueq24bit_bf6af5=true native_phase0=true FI=true IF=true no_interpass_classical_phase_XOF_reset=true physical_applications={apps} polynomial_phase_claim=false initialized_prefix=false whole=false");
}
