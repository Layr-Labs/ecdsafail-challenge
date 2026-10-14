//! Paid high-Z q24/SX0, unchanged R30/TC32, arbitrary inactive f DATA.
//! ROOT alone compiles/prices/runs these fresh ignored finite fixtures.
use super::*;
use crate::point_add::frogdrop::rot_by_range_care;
use crate::point_add::midg::{highz_vform_record, park_quotient_normalized_record,
                            stage1_v_compact_controlled, HIGH_Z_K};

fn szreg<'a>(f: &'a Frame, cp: &ColPar) -> &'a [QubitId] {
    &f.pool[..if cp.sz.1 > 255 { 9 } else { 8 }]
}

fn base_scratch(f: &Frame, cp: &ColPar) -> S1 {
    let mt = (279 - (cp.sz.0 + 22) + 1).min(128usize.max(cp.xw) + 1);
    let kmax = 258usize.saturating_sub(cp.sz.0 + cp.sy.0).min(23).min(mt);
    let lsb = if cp.dn { cp.sy.1.max(28) } else { cp.sy.1 };
    let end = 128 - if cp.dn { 7 } else { 0 };
    let lo = lsb.max(cp.sy.1.min(128) + kmax);
    let mut bank = if lo < end { f.q[lo..end].to_vec() } else { vec![] };
    let paid = bank.pop();
    let mut r = f.ring[..22].to_vec();
    r.extend([f.sx[2], f.sx[3]]);
    if let Some(q) = paid { r.push(q); }
    S1 { r, f: f.sx[0], zero: f.ring[21], sgn: f.sx[0], gt: vec![f.sx[0]],
         anc: bank.iter().skip(1).copied().collect(), andc: bank.clone(), chain: bank,
         dirty: f.dirty.clone() }
}

fn extra_r(f: &Frame) -> [QubitId; 6] {
    [f.sx[1], f.sx[5], f.sx[6], f.sx[7], f.pool[11], f.pool[10]]
}

fn protect(b: &mut B, f: &Frame, cp: &ColPar) -> Vec<G> {
    let dest = (0..22 + TC).chain(279 - HIGH_Z_K..279).collect();
    rec(b, |b| rot_by_range_care(b, &f.ring, szreg(f, cp), cp.sz.0, cp.sz.1,
                              true, &f.dirty, &dest))
}

#[derive(Clone, Copy)]
enum VModel { HighOnly, Factory, BaseOnly }

fn model_head(sz: usize, base: &S1, model: VModel) -> usize {
    match model {
        VModel::HighOnly => HIGH_Z_K,
        VModel::Factory if sz >= 128 => HIGH_Z_K,
        _ => base.r.len(),
    }
}

fn delta(sz: usize, head: usize, divisor: N) -> N {
    let one = N::from(1u64);
    let reciprocal: N = ((one << (256usize - (sz - head))) - one) / (divisor | one);
    let u = (257usize - sz).saturating_sub(TC);
    (one << (257usize - sz)) - (((reciprocal >> u) + one) << u)
}

fn expected(input: &[u64], f: &Frame, cp: &ColPar, base: &S1,
            canonical: bool, model: VModel, inverse: bool) -> Vec<u64> {
    let mut out = input.to_vec();
    for lane in 0..64 {
        if input[f.act.0 as usize] >> lane & 1 == 0 { continue; }
        let sz = get(input, szreg(f, cp), lane).as_limbs()[0] as usize;
        if matches!(model, VModel::HighOnly) && sz < 128 { continue; }
        let head = model_head(sz, base, model);
        let divisor = if canonical { get(input, &f.ring[sz - head..sz], lane) }
            else { get(input, &f.ring[279 - head..], lane) };
        let t: N = N::from(1u64) << (257usize - sz);
        let change = delta(sz, head, divisor);
        let lane_of = |i: usize| f.ring[if canonical { (sz + 21 + i) % 279 } else { 21 + i }];
        let mut w = N::ZERO;
        for i in 0..=TC {
            let pos = 257isize - sz as isize - i as isize;
            if pos >= 0 && input[lane_of(i).0 as usize] >> lane & 1 != 0 {
                w |= N::from(1u64) << pos as usize;
            }
        }
        let next = if inverse { (w + t - change) & (t - N::from(1u64)) }
            else { (w + change) & (t - N::from(1u64)) };
        for i in 1..=TC {
            let pos = 257isize - sz as isize - i as isize;
            if pos >= 0 {
                let p = lane_of(i);
                out[p.0 as usize] = (out[p.0 as usize] & !(1u64 << lane))
                    | (u64::from(next.bit(pos as usize)) << lane);
            }
        }
    }
    out
}

fn p_input(f: &Frame, cp: &ColPar, base: &S1, mode: usize, model: VModel, seed: u64) -> Vec<u64> {
    let mut rng = Rng::new(seed);
    let mut input: Vec<_> = (0..695).map(|_| rng.next()).collect();
    let act = [0u64, u64::MAX, 0x00ff_0f0f_3333_5555][mode];
    input[f.act.0 as usize] = act;
    input[f.sx[0].0 as usize] = (rng.next() | 1 | (1u64 << 63)) & !act;
    for &p in &base.andc { input[p.0 as usize] = 0; }
    for lane in 0..64 {
        let sz = [101usize, 116, 121, 123, 124, 125, 127, 128, 129, 185, 224, 230, 232, 255, 256]
            [lane % 15].max(cp.sz.0).min(cp.sz.1);
        put(&mut input, szreg(f, cp), lane, N::from(sz as u64));
        if act >> lane & 1 == 0 {
            if lane == 0 { put(&mut input, szreg(f, cp), lane, N::ZERO); }
            continue;
        }
        let high = sz >= 128;
        let needs_high_r = high && !matches!(model, VModel::BaseOnly);
        if high || !matches!(model, VModel::HighOnly) {
            for &p in &base.r { input[p.0 as usize] &= !(1u64 << lane); }
        }
        for &p in &extra_r(f) {
            if needs_high_r { input[p.0 as usize] &= !(1u64 << lane); }
            else {
                // A low-Z park can hold q in all six extra reserve owners.
                // The masked high recurrence must return this live DATA.
                input[p.0 as usize] |= 1u64 << lane;
            }
        }
        let head = model_head(sz, base, model);
        let zh: N = match lane % 4 {
            0 => N::from(1u64) << (head - 1),
            1 => (N::from(1u64) << head) - N::from(1u64),
            _ => rng.below(head - 1) | (N::from(1u64) << (head - 1)),
        };
        put(&mut input, &f.ring[279 - head..], lane, zh);
        let d = zh | N::from(1u64);
        let fval: N = ((N::from(1u64) << (256usize - (sz - head))) - N::from(1u64)) / d;
        let u = (257usize - sz).saturating_sub(TC);
        let tie = (fval >> u) << u;
        let t: N = N::from(1u64) << (257usize - sz);
        let w = match lane % 4 {
            0 => tie, 1 => tie + N::from(1u64),
            2 => tie.saturating_sub(N::from(1u64)), _ => rng.below(257 - sz),
        } & (t - N::from(1u64));
        for i in 1..=TC {
            let pos = 257isize - sz as isize - i as isize;
            if pos >= 0 {
                let p = f.ring[21 + i];
                input[p.0 as usize] = (input[p.0 as usize] & !(1u64 << lane))
                    | (u64::from(w.bit(pos as usize)) << lane);
            }
        }
    }
    input
}

#[test]
#[ignore = "ROOT independent source/fresh exact invoice/native admission required"]
fn lowq695_q24_high_masked_vforms_fdata_state_phase_v1() {
    let (cols, _, _) = crate::point_add::pointadd_frogdrop::col_pars(
        &crate::point_add::frogdrop_sched::from_text(crate::point_add::pointadd_frogdrop::SCHED_FROGDROP));
    assert_eq!(cols.len(), 203);
    assert_eq!(TC, 32); assert_eq!(HIGH_Z_K, 30);
    assert_eq!(crate::point_add::mid2::QF, 24);
    let mut records = Vec::new(); let mut invoice = 0u64; let mut retained = 0u64;
    for c in [0usize, 10, 41] {
        let cp = cols[c].clone();
        for caller in [false, true] {
            let mut b = default_builder(); let f = trace_frame(&mut b); let base = base_scratch(&f, &cp);
            let p = protect(&mut b, &f, &cp);
            let r = if caller {
                highz_vform_record(&mut b, &f.ring, szreg(&f, &cp), cp.sz, &f.ring[21..22 + TC],
                                &base, f.act, &f.sx, &p, &extra_r(&f))
            } else {
                let mut high = base.clone(); high.r = f.ring[..22].to_vec();
                high.r.extend([f.sx[2], f.sx[3]]); high.r.extend(extra_r(&f));
                let extra = if cp.sz.0 < 128 { vec![(szreg(&f, &cp)[7], false)] } else { vec![] };
                let fv = stage1_v_compact_controlled(&mut b, &f.ring[279 - HIGH_Z_K..], &f.ring[21..22 + TC],
                    szreg(&f, &cp), cp.sz, &high, f.act, true, &extra);
                let fr = stage1_v_compact_controlled(&mut b, &f.ring[279 - HIGH_Z_K..], &f.ring[21..22 + TC],
                    szreg(&f, &cp), cp.sz, &high, f.act, false, &extra);
                rec(&mut b, |b| { b.play(&fv, false); b.play(&fr, true); })
            };
            let pi = if caller { default_emitted(&mut b, &p, true) } else { vec![] };
            let forward = default_emitted(&mut b, &r, false); let reverse = default_emitted(&mut b, &r, true);
            let n = (forward.len() + reverse.len()) as u64;
            invoice += 12 * n + 6 * pi.len() as u64;
            retained += n + pi.len() as u64;
            eprintln!("Q24_HIGH_R30_TC32_VFORM_INVOICE C={c} caller={caller} baseK={} helpers={} F_N={} I_N={} P_I_N={} copies3 FI_IF_symbolic_native=true fixture_created=false native_started=false",
                base.r.len(), base.andc.len(), forward.len(), reverse.len(), pi.len());
            records.push((c, cp.clone(), caller, f, base, pi, forward, reverse));
        }
    }
    eprintln!("Q24_HIGH_R30_TC32_VFORM_COMPLETE_INVOICE applications={invoice} app_cap=100000000 retained={retained} retained_cap=20000000 fixture_created=false native_started=false");
    assert!(invoice <= 100_000_000 && retained <= 20_000_000);
    let mut apps = 0; let mut coeff = 0; let mut low_live = 0; let mut high_count = 0;
    for (c, cp, caller, f, base, pi, forward, reverse) in records {
        for mode in 0..3 {
            let model = if caller { VModel::Factory } else { VModel::HighOnly };
            let pframe = p_input(&f, &cp, &base, mode, model, 0x695_30_32 + c as u64 * 100 + mode as u64);
            let input = if caller { apply(&pi, &pframe, &mut apps, &mut coeff) } else { pframe };
            for lane in 0..64 {
                if input[f.act.0 as usize] >> lane & 1 == 0 { continue; }
                let sz = get(&input, szreg(&f, &cp), lane).as_limbs()[0] as usize;
                if sz >= 128 { high_count += 1; } else {
                    for &q in &extra_r(&f) {
                        assert_eq!((input[q.0 as usize] >> lane) & 1, 1);
                    }
                    low_live += 1;
                }
            }
            let want = expected(&input, &f, &cp, &base, caller, model, false);
            let got = apply(&forward, &input, &mut apps, &mut coeff);
            assert_eq!(got, want, "high30/base24_25 all695 C={c} caller={caller} mode={mode}");
            assert_eq!(apply(&reverse, &got, &mut apps, &mut coeff), input, "masked factory/kernel FI");
            let want_i = expected(&input, &f, &cp, &base, caller, model, true);
            let got_i = apply(&reverse, &input, &mut apps, &mut coeff);
            assert_eq!(got_i, want_i, "inverse numeric V delta");
            assert_eq!(apply(&forward, &got_i, &mut apps, &mut coeff), input, "masked factory/kernel IF");
        }
    }
    assert!(low_live > 0 && high_count > 0); assert_eq!(apps, invoice);
    eprintln!("Q24_HIGH_R30_TC32_VFORMS_NATIVE_PASS packs=18 lanes=1152 width=695 low_live_six_reserve={low_live} high_active={high_count} all695=true polynomial_phase0=true native_phase0=true FI=true IF=true physical_applications={apps} independent_hmr_measurement_events_times64={coeff} whole=false");
}

#[test]
#[ignore = "ROOT independent source/fresh exact invoice/native admission required"]
fn lowq695_q24_high_hr_ht_parked_callers_fdata_state_phase_v1() {
    let (cols, _, _) = crate::point_add::pointadd_frogdrop::col_pars(
        &crate::point_add::frogdrop_sched::from_text(crate::point_add::pointadd_frogdrop::SCHED_FROGDROP));
    let mut records = Vec::new(); let mut invoice = 0u64; let mut retained = 0u64;
    // Public-range, gate-eligible park/V fragments, not genuine Euclid
    // prefix states. High HR/HT q23 fits with SZ128/SY104; low delayed-HR
    // and HT q16..q21 occupy all six reserve owners at SZ121/SY114.
    // The actual full C41/C43
    // Euclid caller is a separate ROOT fixture. Both V bodies use G.
    for ht in [false, true] { for low in [false, true] {
        let cp = cols[41].clone();
        let mut b = default_builder(); let f = trace_frame(&mut b); let base = base_scratch(&f, &cp);
        assert_eq!(base.r.len(), 24); assert!(base.andc.is_empty());
        let p = protect(&mut b, &f, &cp);
        let v = highz_vform_record(&mut b, &f.ring, szreg(&f, &cp), cp.sz, &f.ring[21..22 + TC],
                                &base, f.act, &f.sx, &p, &extra_r(&f));
        let mut cycle = f.q.clone(); cycle.push(f.pool[9]);
        cycle.extend([f.pool[11], f.pool[10], f.sx[1], f.sx[5], f.sx[6], f.sx[7], f.ph, f.pool[8]]);
        let care = (0..24).map(|kb| (kb + 136) % 137).collect();
        let rq = rec(&mut b, |b| rot_by_range_care(b, &cycle, &f.sy,
            cp.sy.0.min(128), cp.sy.1.min(128), true, &f.dirty, &care));
        let locs: Vec<_> = (0..24).map(|kb| match kb { 21 => f.sx[3], 22 => f.sx[2], 23 => f.sx[0], _ => f.ring[kb] }).collect();
        let park = park_quotient_normalized_record(&mut b, &f.ring, szreg(&f, &cp), cp.sz,
            &f.sy, cp.sy.1, f.act, &locs, &cycle, &rq, f.sx[0], &f.dirty);
        let r = rec(&mut b, |b| {
            if ht { b.x(f.ph); }
            b.play(&park, false); b.play(&v, !ht); b.play(&park, true);
            if ht { b.x(f.ph); }
        });
        let pi = default_emitted(&mut b, &p, true);
        let forward = default_emitted(&mut b, &r, false); let reverse = default_emitted(&mut b, &r, true);
        let n = (forward.len() + reverse.len()) as u64;
        invoice += 12 * n + 6 * pi.len() as u64; retained += n + pi.len() as u64;
        eprintln!("Q24_HIGH_R30_TC32_PARKED_INVOICE ht={ht} low={low} F_N={} I_N={} P_I_N={} fixture_created=false native_started=false",
            forward.len(), reverse.len(), pi.len());
        records.push((cp, ht, low, f, base, cycle, pi, forward, reverse));
    } }
    eprintln!("Q24_HIGH_R30_TC32_PARKED_COMPLETE_INVOICE applications={invoice} app_cap=100000000 retained={retained} retained_cap=20000000 fixture_created=false native_started=false");
    assert!(invoice <= 100_000_000 && retained <= 20_000_000);
    let mut apps = 0; let mut coeff = 0; let mut low_count = 0; let mut high_count = 0;
    for (cp, ht, low, f, base, cycle, pi, forward, reverse) in records {
        for mode in 0..3 {
            let mut pf = p_input(&f, &cp, &base, mode, VModel::Factory, 0x695_30_32_a4c + mode as u64);
            let sz = if low { 121usize } else { 128usize };
            let sy = if low { 114usize } else { 104usize };
            let qword = if low { (63u64 << 16) | 1 } else { (1u64 << 23) | 3 };
            let active = pf[f.act.0 as usize];
            for lane in 0..64 { put(&mut pf, szreg(&f, &cp), lane, N::from(sz as u64)); }
            // Recreate a clean P-frame with the final chosen size. The
            // value itself is fresh arbitrary DATA below the source top.
            for &q in &base.r { pf[q.0 as usize] &= !active; }
            for &q in &extra_r(&f) { pf[q.0 as usize] &= !active; }
            let mut input = apply(&pi, &pf, &mut apps, &mut coeff);
            for lane in 0..64 {
                put(&mut input, &f.sy, lane, N::from(sy as u64));
                if active >> lane & 1 == 0 { continue; }
                let y: N = (N::from(1u64) << (sy - 1)) | N::from(0x13579u64);
                put(&mut input, &f.q, lane, y);
                for &q in &cycle[128..] { input[q.0 as usize] &= !(1u64 << lane); }
                if ht { input[f.ph.0 as usize] |= 1u64 << lane; }
                for kb in 0..24 {
                    let q = match kb { 21 => f.sx[3], 22 => f.sx[2], 23 => f.sx[0], _ => f.ring[(sz + kb) % 279] };
                    input[q.0 as usize] = (input[q.0 as usize] & !(1u64 << lane))
                        | (((qword >> kb) & 1) << lane);
                }
                if low {
                    assert_eq!(sy + 16 - 1, 129); assert_eq!(sy + 21 - 1, 134);
                    assert_eq!((qword >> 16) & 63, 63); low_count += 1;
                } else { assert!(sy + 23 - 1 <= 128); high_count += 1; }
            }
            let want = expected(&input, &f, &cp, &base, true, VModel::Factory, !ht);
            let got = apply(&forward, &input, &mut apps, &mut coeff);
            assert_eq!(got, want, "parked HR/HT high30 or low24/all695 ht={ht} low={low} mode={mode}");
            assert_eq!(apply(&reverse, &got, &mut apps, &mut coeff), input, "parked HR/HT FI");
            let want_i = expected(&input, &f, &cp, &base, true, VModel::Factory, ht);
            let got_i = apply(&reverse, &input, &mut apps, &mut coeff);
            assert_eq!(got_i, want_i, "parked true inverse numeric V");
            assert_eq!(apply(&forward, &got_i, &mut apps, &mut coeff), input, "parked HR/HT IF");
        }
    }
    assert!(low_count > 0 && high_count > 0); assert_eq!(apps, invoice);
    eprintln!("Q24_HIGH_R30_TC32_PARKED_HR_HT_NATIVE_PASS packs=12 lanes=768 width=695 low_parked_q16_to_q21_six_reserve={low_count} high_q23={high_count} all695=true inactive_DATA=true polynomial_phase0=true native_phase0=true FI=true IF=true physical_applications={apps} independent_hmr_measurement_events_times64={coeff} full_column=false whole=false");
}

#[test]
#[ignore = "ROOT independent source/fresh exact invoice/native admission required"]
fn lowq695_q24_high_tc32_base_r24_r25_fdata_state_phase_v1() {
    let (cols, _, _) = crate::point_add::pointadd_frogdrop::col_pars(
        &crate::point_add::frogdrop_sched::from_text(crate::point_add::pointadd_frogdrop::SCHED_FROGDROP));
    assert_eq!(TC, 32); assert_eq!(HIGH_Z_K, 30);
    assert_eq!(crate::point_add::mid2::QF, 24);
    let mut records = Vec::new(); let mut invoice = 0u64; let mut retained = 0u64;
    // Standalone source-kernel superset, not public full-column states.
    // The real C10/C27/C138 public bank allocations leave39/2/0 helpers
    // after the paid loan. All current public low-Z profiles use base24;
    // direct base25 here also checks that kernel at the paid TC32 window.
    for (c, helpers) in [(10usize, 39usize), (27, 2), (138, 0)] {
        for head in [24usize, 25] {
            let mut b = default_builder(); let f = trace_frame(&mut b);
            let mut base = base_scratch(&f, &cols[c]);
            assert_eq!(base.r.len(), 25); assert_eq!(base.andc.len(), helpers);
            base.r.truncate(head);
            let mut cp = cols[c].clone(); cp.sz = (101, 256);
            let fv = stage1_v(&mut b, &f.ring[279 - head..], &f.ring[21..22 + TC],
                szreg(&f, &cp), cp.sz, &base, f.act, true);
            let fr = stage1_v(&mut b, &f.ring[279 - head..], &f.ring[21..22 + TC],
                szreg(&f, &cp), cp.sz, &base, f.act, false);
            let r = rec(&mut b, |b| { b.play(&fv, false); b.play(&fr, true); });
            let forward = default_emitted(&mut b, &r, false);
            let reverse = default_emitted(&mut b, &r, true);
            let n = (forward.len() + reverse.len()) as u64;
            invoice += 12 * n; retained += n;
            eprintln!("Q24_FDATA_TC32_BASE_INVOICE C={c} standaloneK={head} helpers={helpers} SZ_superset101_to256=true F_N={} I_N={} copies3 FI_IF_symbolic_native=true fixture_created=false native_started=false",
                forward.len(), reverse.len());
            records.push((c, cp, head, f, base, forward, reverse));
        }
    }
    eprintln!("Q24_FDATA_TC32_BASE_COMPLETE_INVOICE applications={invoice} app_cap=100000000 retained={retained} retained_cap=20000000 fixture_created=false native_started=false");
    assert!(invoice <= 100_000_000 && retained <= 20_000_000);
    let mut apps = 0; let mut coeff = 0;
    for (c, cp, head, f, base, forward, reverse) in records {
        for mode in 0..3 {
            let input = p_input(&f, &cp, &base, mode, VModel::BaseOnly,
                0x695_32_ba5e + c as u64 * 1000 + head as u64 * 10 + mode as u64);
            let want = expected(&input, &f, &cp, &base, false, VModel::BaseOnly, false);
            let got = apply(&forward, &input, &mut apps, &mut coeff);
            assert_eq!(got, want, "base TC32 numeric V/all695 C={c} K={head} mode={mode}");
            assert_eq!(apply(&reverse, &got, &mut apps, &mut coeff), input, "base TC32 FI/arbitrary inactive R and Win0");
            let want_i = expected(&input, &f, &cp, &base, false, VModel::BaseOnly, true);
            let got_i = apply(&reverse, &input, &mut apps, &mut coeff);
            assert_eq!(got_i, want_i, "base TC32 inverse numeric V");
            assert_eq!(apply(&forward, &got_i, &mut apps, &mut coeff), input, "base TC32 IF/all695");
        }
    }
    assert_eq!(apps, invoice);
    eprintln!("Q24_FDATA_TC32_BASE_R24_R25_NATIVE_PASS packs=18 lanes=1152 width=695 helpers39_2_0=true arbitrary_inactive_R_Win0_DATA=true all695=true polynomial_phase0=true native_phase0=true FI=true IF=true physical_applications={apps} independent_hmr_measurement_events_times64={coeff} full_column=false whole=false");
}
