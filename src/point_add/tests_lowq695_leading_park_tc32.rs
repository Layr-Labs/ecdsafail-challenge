//! Q695 leading-one loan, using the exact production park and true inverse.
//! Raw DATA tests extend the reversible map; only the licensed cohort claims
//! that cleared Y's top plus every fitting q bit leaves headroom clean.
use super::*;
use crate::point_add::frogdrop::rot_by_range_care;
use crate::point_add::midg::park_quotient_normalized_record;

fn leading_park_expected(input: &[u64], f: &Frame, cycle: &[QubitId], act: QubitId,
                         inverse: bool) -> Vec<u64> {
    let mut out = input.to_vec();
    for lane in 0..64 {
        if (input[act.0 as usize] >> lane) & 1 == 0 { continue; }
        let sz = get(input, &f.sz[..8], lane).as_limbs()[0] as usize;
        let sy = get(input, &f.sy, lane).as_limbs()[0] as usize;
        assert!((1..=128).contains(&sy));
        let lead = cycle[sy - 1];
        if !inverse { out[lead.0 as usize] ^= 1u64 << lane; }
        let order: Vec<_> = if inverse { (0..23).rev().collect() } else { (0..23).collect() };
        for kb in order {
            if sy + kb >= cycle.len() + 1 { continue; }
            let qloc = match kb {
                21 => f.sx[3], 22 => f.sx[2], _ => f.ring[(sz + kb) % 279],
            };
            let target = cycle[sy + kb - 1];
            let d = ((out[qloc.0 as usize] ^ out[target.0 as usize]) >> lane) & 1;
            out[qloc.0 as usize] ^= d << lane;
            out[target.0 as usize] ^= d << lane;
        }
        if inverse { out[lead.0 as usize] ^= 1u64 << lane; }
    }
    out
}

#[test]
#[ignore = "ROOT fresh compiled-binary invoice and independent admission required"]
fn lowq695_leading_y_park_all23_tc32_state_phase_v2() {
    let (cols, _, _) = crate::point_add::pointadd_frogdrop::col_pars(
        &crate::point_add::frogdrop_sched::from_text(
            crate::point_add::pointadd_frogdrop::SCHED_FROGDROP));
    assert_eq!(cols.len(), 203);
    assert!(cols[79].hr && cols[79].ht && cols[79].sw && cols[79].dl && cols[79].dq);
    assert_eq!(cols[79].sz, (104, 215));
    assert_eq!(cols[79].sy, (36, 141));
    assert_eq!(crate::point_add::midg::PARK_RES, 8);
    assert_eq!(crate::point_add::midg::TC, 32);
    assert_eq!(crate::point_add::mid2::QF, 23);
    // Synthetic superset for the helper only: includes inactive SY0 and
    // every active size1..128. Production's203 profiles are unchanged.
    let mut cp = cols[79].clone();
    cp.sy = (0, 128);
    let mut records = Vec::new();
    let mut invoice = 0u64;
    let mut retained = 0u64;
    for ht_payload in [false, true] {
        let mut b = default_builder();
        let f = trace_frame(&mut b);
        let act = if ht_payload { f.pool[8] } else { f.act };
        let last = if ht_payload { f.act } else { f.pool[8] };
        let mut cycle = f.q.clone();
        cycle.push(f.pool[9]);
        cycle.extend([f.pool[11], f.pool[10], f.sx[1], f.sx[5],
                      f.sx[6], f.sx[7], f.ph, last]);
        assert_eq!(cycle.len(), 137);
        assert!(!cycle.contains(&act));
        let ds = (0..23).map(|kb| (kb + cycle.len() - 1) % cycle.len()).collect();
        let rq = rec(&mut b, |b| rot_by_range_care(b, &cycle, &f.sy, 0, 128,
            true, &f.dirty, &ds));
        let locs: Vec<_> = (0..23).map(|i| match i {
            21 => f.sx[3], 22 => f.sx[2], _ => f.ring[i],
        }).collect();
        let r = park_quotient_normalized_record(&mut b, &f.ring, &f.sz[..8], cp.sz,
            &f.sy, cp.sy.1, act, &locs, &cycle, &rq, f.sx[0], &f.dirty);
        let forward = default_emitted(&mut b, &r, false);
        let reverse = default_emitted(&mut b, &r, true);
        let one = (forward.len() + reverse.len()) as u64;
        retained = retained.checked_add(one).unwrap();
        // Three act masks x raw/licensed DATA; each runs FI and IF.
        invoice = invoice.checked_add(one.checked_mul(24).unwrap()).unwrap();
        eprintln!("LOWQ695_LEADING_PARK_INVOICE ht_payload={ht_payload} N_F={} N_I={} packs=6 combined_native_symbolic_applications_each_F=24 combined_native_symbolic_applications_each_I=24 retained_ops={one} width=695 allow_booth=true global_cancel=true fixture_created=false native_started=false",
                  forward.len(), reverse.len());
        records.push((ht_payload, f, act, cycle, forward, reverse));
    }
    eprintln!("LOWQ695_LEADING_PARK_COMPLETE_INVOICE physical_applications={invoice} app_cap=100000000 retained_ops={retained} retained_cap=20000000 fixture_created=false native_started=false");
    assert!(invoice <= 100_000_000 && retained <= 20_000_000);

    let mut apps = 0u64;
    let mut coefficients = 0u64;
    let mut forward_swaps = 0usize;
    let mut wrapped = 0usize;
    let mut inactive_sy0 = 0usize;
    let mut q17_c79 = 0usize;
    let mut bit_coverage = [0usize; 23];
    for (ht_payload, f, act, cycle, forward, reverse) in &records {
        for licensed in [false, true] {
            for mode in 0..3 {
                let mut rng = Rng::new(0x695_1ead + 100 * u64::from(*ht_payload)
                    + 10 * u64::from(licensed) + mode as u64);
                let mut input: Vec<_> = (0..695).map(|_| rng.next()).collect();
                input[act.0 as usize] = [0u64, u64::MAX, 0xf0f0_3333_5555_0f0f][mode];
                input[f.sx[0].0 as usize] = 0;
                for lane in 0..64 {
                    let sy = match lane {
                        0 => 0usize, 1 => 120, 2 => 128,
                        3 => 119, 4 => 121, 5 => 113, 6 => 114, 7 => 115,
                        _ => lane - 7,
                    };
                    let sz = [104usize, 120, 128, 133, 173, 215][lane % 6];
                    put(&mut input, &f.sz[..8], lane, N::from(sz as u64));
                    put(&mut input, &f.sy, lane, N::from(sy as u64));
                    if sy == 0 {
                        input[act.0 as usize] &= !(1u64 << lane);
                        inactive_sy0 += 1;
                    }
                    let active = (input[act.0 as usize] >> lane) & 1 != 0;
                    if licensed && active {
                        let y = (rng.below(sy) | (N::from(1u64) << (sy - 1)))
                            & ((N::from(1u64) << sy) - N::from(1u64));
                        put(&mut input, &f.q, lane, y);
                        for &q in &cycle[128..] { input[q.0 as usize] &= !(1u64 << lane); }
                        let cap = (cycle.len() + 1 - sy).min(23);
                        let qword = if sy == 120 { 0x20050u64 }
                            else { (rng.next() | (1u64 << (lane % cap))) & ((1u64 << cap) - 1) };
                        for kb in 0..23 {
                            let q = match kb {
                                21 => f.sx[3], 22 => f.sx[2], _ => f.ring[(sz + kb) % 279],
                            };
                            let bit = (qword >> kb) & 1;
                            input[q.0 as usize] = (input[q.0 as usize] & !(1u64 << lane)) | (bit << lane);
                            if bit != 0 { bit_coverage[kb] += 1; }
                        }
                        if sy == 120 {
                            assert_eq!(qword, 0x20050);
                            assert_eq!(sy + 17 - 1, 136);
                            q17_c79 += 1;
                        }
                    }
                    if active {
                        for kb in 0..23 {
                            if sy + kb >= cycle.len() + 1 { wrapped += 1; }
                            else { forward_swaps += 1; }
                        }
                    }
                }
                let want = leading_park_expected(&input, f, cycle, *act, false);
                let got = apply(forward, &input, &mut apps, &mut coefficients);
                assert_eq!(got, want, "exact normalized park, ht_payload={ht_payload} licensed={licensed} mode={mode}");
                if licensed {
                    for lane in 0..64 {
                        if (input[act.0 as usize] >> lane) & 1 == 0 { continue; }
                        let sy = get(&input, &f.sy, lane).as_limbs()[0] as usize;
                        let sz = get(&input, &f.sz[..8], lane).as_limbs()[0] as usize;
                        for kb in 0..23 {
                            let qloc = match kb {
                                21 => f.sx[3], 22 => f.sx[2], _ => f.ring[(sz + kb) % 279],
                            };
                            assert_eq!((got[qloc.0 as usize] >> lane) & 1, 0,
                                "licensed normalized park clears every q head owner, SY={sy}, kb={kb}");
                        }
                    }
                }
                assert_eq!(apply(reverse, &got, &mut apps, &mut coefficients), input,
                           "normalized park FI/all695/arbitrary inactive DATA");
                let want_i = leading_park_expected(&input, f, cycle, *act, true);
                let got_i = apply(reverse, &input, &mut apps, &mut coefficients);
                assert_eq!(got_i, want_i, "true inverse: swaps precede leading-bit restoration");
                assert_eq!(apply(forward, &got_i, &mut apps, &mut coefficients), input,
                           "normalized park IF/all695/arbitrary inactive DATA");
            }
        }
    }
    assert!(bit_coverage.iter().all(|&n| n > 0));
    assert!(forward_swaps > 0 && wrapped > 0 && inactive_sy0 == 12 && q17_c79 > 0);
    assert_eq!(apps, invoice);
    eprintln!("LOWQ695_LEADING_PARK_NATIVE_PASS packs=12 lanes=768 width=695 all23_set_bit_coverage={bit_coverage:?} q17_c79={q17_c79} inactive_sy0={inactive_sy0} swaps={forward_swaps} wrapped={wrapped} reserve=8 effective_extra_place=1 all695=true false_DATA=true polynomial_phase0=true native_phase0=true FI=true IF=true physical_applications={apps} independent_hmr_measurement_events_times64={coefficients} full_column=false whole=false");
}
