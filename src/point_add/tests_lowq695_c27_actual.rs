//! Fixed actual failure1030, division2, HR C27/j28. Test-only.
//! Same bytes apply to frozen head24 and the bank-funded head25 repair.
//! No initialized-prefix, deferred-row or whole correctness claim.
use super::*;
use crate::point_add::frogdrop_col::{ColScr, column_pl};

#[test]
#[ignore = "ROOT source/binary invoice and independent admission required"]
fn lowq695_actual1030_c27_column_state_phase_v1() {
    let (cols, _, _) = crate::point_add::pointadd_frogdrop::col_pars(
        &crate::point_add::frogdrop_sched::from_text(
            crate::point_add::pointadd_frogdrop::SCHED_FROGDROP));
    assert_eq!(cols.len(), 203);
    let cp = &cols[27];
    assert!(cp.hr && !cp.ht && !cp.sw && !cp.dl && !cp.dq && !cp.dn);
    assert_eq!(cp.sz, (151, 241));
    assert_eq!(cp.sy, (15, 102));
    let mut b = default_builder();
    let f = trace_frame(&mut b);
    let mut fd = fd_of(&f);
    let sc = ColScr::carve_col(&f.pool, &fd.sx, &f.dirty,
                             cp.kp, cp.qb, cp.tail, false);
    let record = rec(&mut b, |b| column_pl(b, &mut fd, cp, &sc, None));
    let forward = default_emitted(&mut b, &record, false);
    let reverse = default_emitted(&mut b, &record, true);
    let retained = (forward.len() + reverse.len()) as u64;
    let invoice = retained.checked_mul(2).unwrap();
    eprintln!("LOWQ695_ACTUAL1030_C27_INVOICE N_F={} N_I={} retained_ops={retained} physical_applications={invoice} app_cap=100000000 retained_cap=20000000 width=695 allow_booth=true global_cancel=true eager_rows=true payload_hooks=false fixture_created=false native_started=false",
              forward.len(), reverse.len());
    assert!(invoice <= 100_000_000 && retained <= 20_000_000,
            "complete same-binary F/I invoice before numeric fixtures/simulation");

    // Canonical extractor of failed V1 stream e6bbc957...bede3c derives
    // this non-reflected dx2 and independently matches the failed-log sum.
    // The immutable numeric model starts only after the admitted prepass.
    let xr = N::from_str_radix(
        "343597eb2a5671375eaea7a814b93d4fc61ef2ba1dc0f6b3fc57fdf6d70beb88", 16).unwrap();
    let p = crate::point_add::frogdrop_sched::p();
    let mut r = vec![p, xr];
    let mut t = vec![N::ZERO, N::from(1u64)];
    while !r.last().unwrap().is_zero() {
        let n = r.len();
        let q = r[n - 2] / r[n - 1];
        r.push(r[n - 2] - q * r[n - 1]);
        t.push(t[n - 2] + q * t[n - 1]);
    }
    let j = 28;
    assert_eq!(r[j - 1] / r[j], N::from(0x3ceb26u64));
    assert_eq!(r[j].bit_len(), 177);
    assert_eq!(t[j].bit_len(), 58);
    let shot = crate::point_add::frogdrop_sched::shot(xr, crate::point_add::frogdrop_sched::L0);
    assert!(shot.recs[..=27].iter().all(|x| x.kind == crate::point_add::frogdrop_sched::Kind::Hr));
    assert_eq!(shot.recs[27].sz, r[j].bit_len());
    assert_eq!(shot.recs[27].sy, t[j].bit_len());
    assert!(cp.sz.0 <= r[j].bit_len() && r[j].bit_len() <= cp.sz.1);
    assert!(cp.sy.0 <= t[j].bit_len() && t[j].bit_len() <= cp.sy.1);
    assert_eq!(p, r[j] * t[j - 1] + r[j - 1] * t[j]);
    assert_eq!(p, r[j] * t[j + 1] + r[j + 1] * t[j]);

    let mut rng = Rng::new(0x695_1030_c27);
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
        put(&mut input, &f.sy, lane, N::from(t[j].bit_len() as u64));
        put(&mut want, &f.ring[..cut_out], lane, r[j + 1]);
        put(&mut want, &top(&f.ring[cut_out..]), lane, t[j + 1]);
        put(&mut want, &f.q, lane, t[j]);
        put(&mut want, &fd.sy, lane, N::from(t[j + 1].bit_len() as u64));
    }
    assert_eq!(input[f.ph.0 as usize], 0);
    assert_eq!(want[f.ph.0 as usize], 0);
    eprintln!("LOWQ695_ACTUAL1030_C27_MODEL lanes=64 same_fixed_Euclid_input=true dirty259_varied=true j=28 trueq=0x3ceb26 initial_SZ177_SY58=true eager_no_payload_hooks=true initialized_prefix=false");
    let mut apps = 0;
    let mut coefficients = 0;
    let got = apply(&forward, &input, &mut apps, &mut coefficients);
    trace_assert_all(&got, &want, &f, &fd, "actual1030_C27_column_forward");
    assert_eq!(apply(&reverse, &got, &mut apps, &mut coefficients), input,
               "actual1030 C27 full695 FI including arbitrary259 passengers");
    assert_eq!(apps, invoice);
    eprintln!("LOWQ695_ACTUAL1030_C27_NATIVE_PASS packs=1 lanes=64 all695=true dirty259_DATA=true trueq=0x3ceb26 polynomial_phase0=true native_phase0=true FI=true physical_applications={apps} independent_hmr_measurement_events_times64={coefficients} initialized_prefix=false whole=false");
}
