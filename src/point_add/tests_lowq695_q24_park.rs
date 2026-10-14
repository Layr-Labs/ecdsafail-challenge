//! Helper-free24-bit leading-one park. This tests the exact reversible
//! helper and physical fitting contract, not full low-Z quotient24 support.
use super::*;
use crate::point_add::frogdrop::rot_by_range_care;
use crate::point_add::midg::park_quotient_normalized_record;

fn qloc(f: &Frame, sz: usize, kb: usize) -> QubitId {
    match kb { 21 => f.sx[3], 22 => f.sx[2], 23 => f.sx[0],
        _ => f.ring[(sz + kb) % 279] }
}
fn expect(input: &[u64], f: &Frame, szbits: usize, cycle: &[QubitId], act: QubitId,
          inverse: bool) -> Vec<u64> {
    let mut out = input.to_vec();
    for lane in 0..64 {
        if input[act.0 as usize] >> lane & 1 == 0 { continue; }
        let sz = get(input, &f.sz[..szbits], lane).as_limbs()[0] as usize;
        let sy = get(input, &f.sy, lane).as_limbs()[0] as usize;
        assert!((1..=128).contains(&sy));
        let lead = cycle[sy - 1];
        if !inverse { out[lead.0 as usize] ^= 1u64 << lane; }
        let order: Vec<_> = if inverse { (0..24).rev().collect() } else { (0..24).collect() };
        for kb in order {
            if sy + kb >= cycle.len() + 1 { continue; }
            let src = qloc(f, sz, kb); let target = cycle[sy + kb - 1];
            let d = ((out[src.0 as usize] ^ out[target.0 as usize]) >> lane) & 1;
            out[src.0 as usize] ^= d << lane; out[target.0 as usize] ^= d << lane;
        }
        if inverse { out[lead.0 as usize] ^= 1u64 << lane; }
    }
    out
}

#[test]
#[ignore = "ROOT fresh compiled-binary invoice and independent admission required"]
fn lowq695_q24_high_leading_y_park_all24_state_phase_v1() {
    let (cols, _, _) = crate::point_add::pointadd_frogdrop::col_pars(
        &crate::point_add::frogdrop_sched::from_text(crate::point_add::pointadd_frogdrop::SCHED_FROGDROP));
    assert_eq!(cols.len(), 203);
    assert_eq!(crate::point_add::mid2::QF, 24);
    assert_eq!(crate::point_add::pointadd_frogdrop::QB, 23);
    assert_eq!(crate::point_add::midg::TC, 32);
    assert_eq!(crate::point_add::midg::PARK_RES, 8);
    let mut records = Vec::new(); let mut invoice = 0u64; let mut retained = 0u64;
    for profile in 0..3 {
        let wide = profile == 2; let ht_payload = profile == 1;
        let mut cp = cols[if wide { 0 } else { 79 }].clone();
        cp.sy = (0, 128); // exact helper superset, not a changed schedule
        let mut b = default_builder(); let f = trace_frame(&mut b);
        let act = if ht_payload { f.pool[8] } else { f.act };
        let last = if ht_payload { f.act } else { f.pool[8] };
        let szbits = if wide { 9 } else { 8 };
        let mut cycle = f.q.clone(); cycle.push(f.pool[9]);
        cycle.extend([f.pool[11], f.pool[10], f.sx[1], f.sx[5], f.sx[6], f.sx[7], f.ph]);
        if !wide { cycle.push(last); }
        assert_eq!(cycle.len(), if wide { 136 } else { 137 });
        assert!(!cycle.contains(&act) && !cycle.contains(&f.sx[0]));
        let care = (0..24).map(|kb| (kb + cycle.len() - 1) % cycle.len()).collect();
        let rq = rec(&mut b, |b| rot_by_range_care(b, &cycle, &f.sy, 0, 128,
            true, &f.dirty, &care));
        let locs: Vec<_> = (0..24).map(|kb| match kb {
            21 => f.sx[3], 22 => f.sx[2], 23 => f.sx[0], _ => f.ring[kb] }).collect();
        let r = park_quotient_normalized_record(&mut b, &f.ring, &f.sz[..szbits], cp.sz,
            &f.sy, cp.sy.1, act, &locs, &cycle, &rq, f.sx[0], &f.dirty);
        let forward = default_emitted(&mut b, &r, false);
        let reverse = default_emitted(&mut b, &r, true);
        let n = (forward.len() + reverse.len()) as u64;
        // 3SYpacks x raw/licensed x3act masks; FI and IF; two backends.
        invoice += 72 * n; retained += n;
        eprintln!("Q24_PARK_INVOICE profile={profile} wide={wide} ht_payload={ht_payload} cycle_len={} N_F={} N_I={} packs=18 perF_perI_native_symbolic_copies=72 fixture_created=false native_started=false",
            cycle.len(), forward.len(), reverse.len());
        records.push((profile, wide, szbits, cp, f, act, cycle, forward, reverse));
    }
    eprintln!("Q24_PARK_COMPLETE_INVOICE applications={invoice} app_cap=100000000 retained={retained} retained_cap=20000000 fixture_created=false native_started=false");
    assert!(invoice <= 100_000_000 && retained <= 20_000_000);
    let mut apps = 0; let mut coeff = 0; let mut inactive_sy0 = 0;
    let mut bit_coverage = [0usize; 24]; let mut sy_coverage = [0usize; 129];
    let mut wrapped = 0; let mut q17_c79 = 0;
    for (profile, wide, szbits, cp, f, act, cycle, forward, reverse) in records {
        for licensed in [false, true] { for mode in 0..3 { for sypack in 0..3 {
            let mut rng = Rng::new(0x695_24_1ead + profile as u64 * 1000
                + u64::from(licensed) * 100 + mode as u64 * 10 + sypack as u64);
            let mut input: Vec<_> = (0..695).map(|_| rng.next()).collect();
            input[act.0 as usize] = [0u64, u64::MAX, 0xf0f0_3333_5555_0f0f][mode];
            // SX0 is q23 DATA, not a clean wrap workspace.
            for lane in 0..64 {
                let sy = match sypack {
                    0 => lane + 1, 1 => lane + 65,
                    _ => match lane { 0 => 0, 1 => 120, 2 => 128, 3 => 119,
                        4 => 121, 5 => 113, 6 => 114, 7 => 115, _ => lane - 7 },
                };
                let sz = if wide { [218usize, 230, 255, 256][lane % 4] }
                    else { [104usize, 120, 128, 133, 173, 215][lane % 6] };
                assert!((cp.sz.0..=cp.sz.1).contains(&sz));
                put(&mut input, &f.sz[..szbits], lane, N::from(sz as u64));
                put(&mut input, &f.sy, lane, N::from(sy as u64));
                if sy == 0 { input[act.0 as usize] &= !(1u64 << lane); inactive_sy0 += 1; }
                let active = input[act.0 as usize] >> lane & 1 != 0;
                if licensed && active {
                    sy_coverage[sy] += 1;
                    let y: N = (rng.below(sy) | (N::from(1u64) << (sy - 1)))
                        & ((N::from(1u64) << sy) - N::from(1u64));
                    put(&mut input, &f.q, lane, y);
                    for &q in &cycle[128..] { input[q.0 as usize] &= !(1u64 << lane); }
                    let cap = (cycle.len() + 1 - sy).min(24);
                    let qword = if sy == 120 && !wide { 0x20050u64 }
                        else { (rng.next() | (1u64 << (lane % cap))) & ((1u64 << cap) - 1) };
                    for kb in 0..24 {
                        let bit = qword >> kb & 1; let q = qloc(&f, sz, kb);
                        input[q.0 as usize] = (input[q.0 as usize] & !(1u64 << lane)) | (bit << lane);
                        if bit != 0 { bit_coverage[kb] += 1; }
                    }
                    if sy == 120 && !wide {
                        assert_eq!(qword, 0x20050); assert_eq!(sy + 17 - 1, 136); q17_c79 += 1;
                    }
                }
                if active { wrapped += (0..24).filter(|&kb| sy + kb >= cycle.len() + 1).count(); }
            }
            let want = expect(&input, &f, szbits, &cycle, act, false);
            let got = apply(&forward, &input, &mut apps, &mut coeff);
            assert_eq!(got, want, "helper-free24 park/all695 profile={profile} licensed={licensed} mode={mode} sypack={sypack}");
            if licensed { for lane in 0..64 {
                if input[act.0 as usize] >> lane & 1 == 0 { continue; }
                let sz = get(&input, &f.sz[..szbits], lane).as_limbs()[0] as usize;
                for kb in 0..24 { assert_eq!((got[qloc(&f, sz, kb).0 as usize] >> lane) & 1, 0,
                    "licensed24 park clears q23/f and all R donors before V"); }
            } }
            assert_eq!(apply(&reverse, &got, &mut apps, &mut coeff), input, "q24 park FI/all695");
            let want_i = expect(&input, &f, szbits, &cycle, act, true);
            let got_i = apply(&reverse, &input, &mut apps, &mut coeff);
            assert_eq!(got_i, want_i, "exact true inverse24 park");
            assert_eq!(apply(&forward, &got_i, &mut apps, &mut coeff), input, "q24 park IF/arbitrary inactive q23 DATA");
        } } }
    }
    assert_eq!(inactive_sy0, 18); assert!(wrapped > 0 && q17_c79 > 0);
    assert!(bit_coverage.iter().all(|&x| x > 0) && sy_coverage[1..].iter().all(|&x| x > 0));
    assert_eq!(apps, invoice);
    eprintln!("Q24_HIGH_LEADING_PARK_NATIVE_PASS packs=54 lanes=3456 width=695 all24_bits={bit_coverage:?} allSY1_to128=true inactiveSY0={inactive_sy0} wrapped={wrapped} q17_c79={q17_c79} C0_SZ256_cycle136=true both137cycles=true all695=true arbitraryinactiveq23_DATA=true polynomial_phase0=true native_phase0=true FI=true IF=true physical_applications={apps} independent_hmr_measurement_events_times64={coeff} full_lowZ_q24_claim=false whole=false");
}
