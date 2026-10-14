//! Actual1364 reflected division2 C79: literal q17 park/read/payload fragment.
//! The old and normalized helper run on the same exact numeric boundary.
//! This is not a full column, initialized traversal or whole qualification.
use super::*;
use crate::point_add::frogdrop::rot_by_range_care;
use crate::point_add::midg::{park_quotient_record, park_quotient_normalized_record};

#[test]
#[ignore = "ROOT source and complete same-binary invoice admission required"]
fn lowq695_actual1364_c79_park_payload_q17_state_phase_v1() {
    let (cols, _, _) = crate::point_add::pointadd_frogdrop::col_pars(
        &crate::point_add::frogdrop_sched::from_text(
            crate::point_add::pointadd_frogdrop::SCHED_FROGDROP));
    let cp = &cols[79];
    assert_eq!((cp.sz, cp.sy), ((104, 215), (36, 141)));
    assert!(cp.ht && !cp.dn);
    let mut records = Vec::new();
    let mut invoice = 0u64;
    for normalized in [false, true] {
        let mut b = default_builder();
        let f = trace_frame(&mut b);
        let fd = fd_of(&f);
        let act = f.pool[8];
        let mut cycle = f.q.clone();
        cycle.push(f.pool[9]);
        cycle.extend([f.pool[11], f.pool[10], f.sx[1], f.sx[5],
                      f.sx[6], f.sx[7], f.ph, f.sx[4]]);
        assert_eq!(cycle.len(), 137);
        let care = (0..23).map(|kb| if normalized { (kb + 136) % 137 } else { kb }).collect();
        let rq = rec(&mut b, |b| rot_by_range_care(b, &cycle, &f.sy,
            cp.sy.0.min(128), cp.sy.1.min(128), true, &f.dirty, &care));
        let locs: Vec<_> = (0..23).map(|kb| match kb {
            21 => f.sx[3], 22 => f.sx[2], _ => f.ring[kb],
        }).collect();
        let park = if normalized {
            park_quotient_normalized_record(&mut b, &f.ring, &f.pool[..8], cp.sz,
                &f.sy, cp.sy.1, act, &locs, &cycle, &rq, f.sx[0], &f.dirty)
        } else {
            park_quotient_record(&mut b, &f.ring, &f.pool[..8], cp.sz,
                &f.sy, cp.sy.1, act, &locs, &cycle, &rq, f.sx[0], &f.dirty)
        };
        let pl = crate::point_add::pointadd_frogdrop::pl_col(&f.dirty, &fd, &f.pool);
        let record = rec(&mut b, |b| {
            // These are the exact production stage5 PH flip, park, care
            // replay, kb17 read/guard/masked transition and inverse pair.
            b.x(f.ph);
            b.play(&park, false);
            b.play(&rq, false);
            let threshold = 137 + usize::from(normalized) - 17;
            crate::point_add::frogdrop_col::ge_const_compact(b, &f.sy,
                threshold as isize, f.sx[0], &[], &f.dirty);
            let read = cycle[if normalized { 16 } else { 17 }];
            let base = vec![(read, false), (act, false), (f.sx[0], true)];
            let target: Vec<_> = (17..259).map(|pos|
                crate::point_add::payload::wl(&pl.p, pos)).collect();
            crate::point_add::payload::trans_one_guard(b, &target,
                &f.ring[..242], 17, false, base,
                Some((&f.sy[4..], 128 >> 4)), f.sx[2], f.sx[3], &[],
                &pl.dirty, 263);
            crate::point_add::frogdrop_col::ge_const_compact(b, &f.sy,
                threshold as isize, f.sx[0], &[], &f.dirty);
            b.play(&rq, true);
            b.play(&park, true);
            b.x(f.ph);
        });
        let forward = default_emitted(&mut b, &record, false);
        let reverse = default_emitted(&mut b, &record, true);
        let retained = (forward.len() + reverse.len()) as u64;
        invoice += 3 * 2 * retained;
        eprintln!("LOWQ695_C79_PAYLOAD_INVOICE normalized={normalized} N_F={} N_I={} retained_ops={retained} total_apps_so_far={invoice} fixture_created=false native_started=false",
            forward.len(), reverse.len());
        assert!(retained <= 20_000_000);
        records.push((normalized, f, act, forward, reverse));
    }
    assert!(invoice <= 100_000_000, "both kernels, all3 modes, F/I, symbolic/native paid before fixtures");

    // Exact independently extracted scalar boundary, not case selection.
    let xr = N::from_str_radix("4f8e76a6b67f29f47569b98173f6285bce73b9f29f5387262a9b0059b3c102c5", 16).unwrap();
    let mut r = vec![crate::point_add::frogdrop_sched::p(), xr];
    let mut t = vec![N::ZERO, N::from(1u64)];
    while !r.last().unwrap().is_zero() {
        let i = r.len(); let q = r[i - 2] / r[i - 1];
        r.push(r[i - 2] - q * r[i - 1]);
        t.push(t[i - 2] + q * t[i - 1]);
    }
    assert_eq!(r[78] / r[79], N::from(0x20050u64));
    assert_eq!((r[79].bit_len(), t[79].bit_len()), (120, 120));
    let bound: N = (N::from(1u64) << 152usize) - N::from(1u64);
    let mut apps = 0; let mut coefficients = 0;
    for (normalized, f, act, forward, reverse) in records {
        for mode in 0..3 {
            let mut rng = Rng::new(0x695_1364_c79 + mode as u64);
            let active = [0u64, u64::MAX, 0xf0f0_3333_5555_0f0f][mode];
            let mut input = vec![0u64; 695];
            for &wire in f.ring.iter().chain(&f.q).chain(&f.dirty) {
                input[wire.0 as usize] = rng.next() & !active;
            }
            for &wire in &f.dirty { input[wire.0 as usize] = rng.next(); }
            input[act.0 as usize] = active;
            input[f.ph.0 as usize] = u64::MAX;
            for lane in 0..64 {
                put(&mut input, &f.pool[..8], lane, N::from(120u64));
                put(&mut input, &f.sy, lane, N::from(120u64));
                if active >> lane & 1 == 0 { continue; }
                put(&mut input, &f.ring[..120], lane, t[79]);
                put(&mut input, &top(&f.ring[159..]), lane, r[80]);
                put(&mut input, &f.q, lane, r[79]);
                for kb in 0..21 {
                    input[f.ring[120 + kb].0 as usize] |=
                        u64::from((0x20050u64 >> kb) & 1 != 0) << lane;
                }
            }
            let mut want = input.clone();
            if normalized {
                for lane in 0..64 {
                    if active >> lane & 1 == 0 { continue; }
                    let old = get(&input, &top(&f.dirty), lane);
                    let next = (old & !bound) | ((old + (t[79] << 17)) & bound);
                    put(&mut want, &top(&f.dirty), lane, next);
                    assert_ne!(old, next, "actual q17 contribution is nonzero");
                }
            }
            let got = apply(&forward, &input, &mut apps, &mut coefficients);
            assert_eq!(got, want, "actual C79 normalized={normalized} mode={mode}: all695/phase/one q17 payload");
            assert_eq!(apply(&reverse, &got, &mut apps, &mut coefficients), input,
                "actual C79 F/I restores every owner and arbitraryinactive DATA");
        }
    }
    assert_eq!(apps, invoice);
    eprintln!("LOWQ695_ACTUAL1364_C79_Q17_PAYLOAD_NATIVE_PASS packs=6 lanes=384 all695=true old_q17_payload_suppressed=true normalized_q17_payload_added=true inactive_DATA_returned=true true_inverse=true phase0=true physical_applications={apps} independent_hmr_measurement_events_times64={coefficients} full_column=false whole=false");
}
