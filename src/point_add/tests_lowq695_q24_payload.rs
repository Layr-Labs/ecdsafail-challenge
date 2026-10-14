//! Paid high-SZ bit23 payload components, not an initialized traversal.
//! Actual C114 park/read contribution; signed-zero KE24 digit boundary;
//! synthetic licensed low-SZ HR D^-1 boundary with the shorter read/pad bank.
use super::*;
use crate::point_add::frogdrop::rot_by_range_care;
use crate::point_add::frogdrop_col::ColScr;
use crate::point_add::midg::park_quotient_normalized_record;

fn continuous_pairs(forward: &[Op], reverse: &[Op], input: &[u64], want: &[u64],
                    f: &Frame, apps: &mut u64, label: &str) {
    use crate::sim::Simulator;
    use sha3::{Shake256, digest::{Update, ExtendableOutput}};
    let nb = crate::circuit::analyze_ops(forward.iter().chain(reverse.iter())).1;
    for inverse_first in [false, true] {
        let mut h = Shake256::default();
        h.update(b"lowq695-q24-high-payload-digit-continuous-v1");
        h.update(label.as_bytes()); h.update(&[u8::from(inverse_first)]);
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(695, (nb as usize).max(1), &mut xof);
        sim.qubits = if inverse_first { want.to_vec() } else { input.to_vec() };
        let first = if inverse_first { reverse } else { forward };
        let second = if inverse_first { forward } else { reverse };
        sim.apply_iter(first.iter()); *apps += first.len() as u64;
        assert_eq!(sim.phase, 0, "{label}: continuous midpoint phase");
        trace_assert_all(&sim.qubits, if inverse_first { input } else { want },
                         f, &fd_of(f), label);
        sim.apply_iter(second.iter()); *apps += second.len() as u64;
        assert_eq!(sim.phase, 0, "{label}: continuous return phase");
        assert_eq!(sim.qubits, if inverse_first { want.to_vec() } else { input.to_vec() },
                   "{label}: continuous FI/IF all695 return");
    }
}

#[test]
#[ignore = "ROOT fresh frozen compile and complete pre-model invoice admission required"]
fn lowq695_q24_high_payload_digit_transition_fdata_state_phase_v1() {
    assert_eq!((crate::point_add::mid2::QF, crate::point_add::payload::KE,
                crate::point_add::pointadd_frogdrop::QB), (24, 24, 23));
    let (cols, _, _) = crate::point_add::pointadd_frogdrop::col_pars(
        &crate::point_add::frogdrop_sched::from_text(
            crate::point_add::pointadd_frogdrop::SCHED_FROGDROP));
    assert_eq!(cols.len(), 203);
    let cp = &cols[114];
    assert!(cp.ht && cp.dn && !cp.hr && !cp.sw && !cp.dl && !cp.dq);
    assert_eq!((cp.sz, cp.sy), ((127, 255), (1, 129)));
    let low = &cols[64];
    assert!(low.hr && low.dl && low.sw && !low.dn && !low.tt);
    assert_eq!(low.dlr, 113);
    let mut records = Vec::new();
    let mut invoice = 0u64;
    // All three physical F/I families and both caps are priced before
    // constructing numeric inputs, RNG, payload models or Simulator.
    for kind in 0..3 {
        let mut b = default_builder();
        let f = trace_frame(&mut b); let fd = fd_of(&f);
        let row = if kind == 2 { low } else { cp };
        let sc = ColScr::carve_col(&f.pool, &fd.sx, &f.dirty,
                                  row.kp, row.qb, row.tail, false);
        let pl = crate::point_add::pointadd_frogdrop::pl_col(&f.dirty, &fd, &f.pool);
        let record = if kind == 0 {
            let act = f.pool[8];
            let mut cycle = f.q.clone(); cycle.push(f.pool[9]);
            cycle.extend([f.pool[11], f.pool[10], f.sx[1], f.sx[5],
                          f.sx[6], f.sx[7], f.ph, f.sx[4]]);
            assert_eq!(cycle.len(), 137);
            let care = (0..24).map(|kb| (kb + 136) % 137).collect();
            let rq = rec(&mut b, |b| rot_by_range_care(b, &cycle, &f.sy,
                cp.sy.0.min(128), cp.sy.1.min(128), true, &f.dirty, &care));
            let locs: Vec<_> = (0..24).map(|kb| match kb {
                21 => f.sx[3], 22 => f.sx[2], 23 => f.sx[0], _ => f.ring[kb],
            }).collect();
            let park = park_quotient_normalized_record(&mut b, &f.ring,
                &f.pool[..8], cp.sz, &f.sy, cp.sy.1, act, &locs,
                &cycle, &rq, f.sx[0], &f.dirty);
            rec(&mut b, |b| {
                // Exact stage5 PH flip, normalized park/read and kb23
                // masked transition. Payload retains the paired XOR
                // wrap flag on SX0 after the active q23 owner is parked.
                b.x(f.ph); b.play(&park, false); b.play(&rq, false);
                crate::point_add::frogdrop_col::ge_const_compact(b, &f.sy,
                    115, f.sx[0], &[], &f.dirty);
                let base = vec![(cycle[22], false), (act, false), (f.sx[0], true)];
                let target: Vec<_> = (23..259).map(|pos|
                    crate::point_add::payload::wl(&pl.p, pos)).collect();
                crate::point_add::payload::trans_one_guard(b, &target,
                    &f.ring[..236], 23, false, base,
                    Some((&f.sy[4..], 128 >> 4)), f.sx[2], f.sx[3],
                    &[], &pl.dirty, 263);
                crate::point_add::frogdrop_col::ge_const_compact(b, &f.sy,
                    115, f.sx[0], &[], &f.dirty);
                b.play(&rq, true); b.play(&park, true); b.x(f.ph);
            })
        } else if kind == 1 {
            rec(&mut b, |b| crate::point_add::payload::col_digit(b, &fd, cp, &sc, &pl))
        } else {
            // Capture stage4 in its own nested recording. Length offsets
            // into one optimized record are invalid: stage4 may cancel
            // gates from the stage3 prefix and move that earlier boundary.
            // The unused stage3 prefix gives no initialized-caller credit;
            // this structural capture does not inject a quantum clean cut.
            let mut stage_no = 0;
            let mut suffix = None;
            let _unused_prefix = rec(&mut b, |b| crate::point_add::midg::middle(
                b, &fd, low, &sc, Some(&pl), &[], &mut |b| {
                    stage_no += 1;
                    match stage_no {
                        1 => { b.begin(); true },
                        2 => { suffix = Some(b.end()); false },
                        _ => unreachable!("D^-1 capture must stop at stage4"),
                    }
                }));
            assert_eq!(stage_no, 2);
            suffix.expect("complete independently recorded stage4 D^-1")
        };
        let forward = default_emitted(&mut b, &record, false);
        let reverse = default_emitted(&mut b, &record, true);
        let retained = (forward.len() + reverse.len()) as u64;
        // Three masks. Each has four apply() calls =4(F+I) for the
        // symbolic/native backend pair, plus continuous native FI/IF
        // =2(F+I), without a classical/RNG/phase reset at the seam.
        invoice += 18 * retained;
        eprintln!("LOWQ695_Q24_PAYLOAD_COMPLETE_INVOICE kind={kind} N_F={} N_I={} retained_ops={retained} row_apps={} total_apps_so_far={invoice} masks=3 aggregate_cap=100000000 retained_cap=20000000 fixture_created=false native_started=false",
                  forward.len(), reverse.len(), 18 * retained);
        assert!(retained <= 20_000_000);
        records.push((kind, f, forward, reverse));
    }
    assert!(invoice <= 100_000_000, "all components and every backend before any model or simulation");

    // Canonical actual821 division2, not a selected or altered input.
    let xr = N::from_str_radix(
        "1768699576735cdf3c72fa66285e102621f59bfe5c53f5eb0be9c0464ade9071", 16).unwrap();
    let mut r = vec![crate::point_add::frogdrop_sched::p(), xr];
    let mut t = vec![N::ZERO, N::from(1u64)];
    while !r.last().unwrap().is_zero() {
        let i = r.len(); let q = r[i - 2] / r[i - 1];
        r.push(r[i - 2] - q * r[i - 1]);
        t.push(t[i - 2] + q * t[i - 1]);
    }
    assert_eq!(r[113] / r[114], N::from(0xbf6af5u64));
    assert_eq!((t[114].bit_len(), r[114].bit_len()), (204, 29));
    assert_eq!(r[114], N::from(0x1e6f1ba4u64));
    assert_eq!(r[115], N::from(0x9451eedu64));
    let payload_bound: N = (N::from(1u64) << 248usize) - N::from(1u64);
    let low_bound: N = (N::from(1u64) << 146usize) - N::from(1u64);
    let mut apps = 0; let mut coefficients = 0; let mut packs = 0;
    for (kind, f, forward, reverse) in records {
        for mode in 0..3 {
            let mut rng = Rng::new(0x695_24_114 + 100 * kind as u64 + mode as u64);
            let active = [0u64, u64::MAX, 0xf0f0_3333_5555_0f0f][mode];
            let mut input = vec![0u64; 695];
            for &wire in f.ring.iter().chain(&f.q) {
                input[wire.0 as usize] = rng.next() & !active;
            }
            // Counter zero is licensed for these component active flags.
            for &wire in &f.q[121..] { input[wire.0 as usize] = 0; }
            for &wire in &f.dirty { input[wire.0 as usize] = rng.next(); }
            if kind != 1 {
                input[f.sx[0].0 as usize] = (rng.next() | 1 | (1u64 << 63)) & !active;
            }
            input[f.ph.0 as usize] = if kind == 0 { u64::MAX }
                else if kind == 1 { active } else { !active };
            if kind == 0 { input[f.pool[8].0 as usize] = active; }
            for lane in 0..64 {
                let on = active >> lane & 1 != 0;
                let sz = if kind == 2 { 121u64 } else { 204u64 };
                let sy = if kind == 2 { 113u64 } else if kind == 0 && !on {
                    [0u64, 114, 115, 120, 128][lane % 5]
                } else { 29u64 };
                put(&mut input, &f.pool[..8], lane, N::from(sz));
                put(&mut input, &f.sy, lane, N::from(sy));
                if !on { continue; }
                if kind == 0 {
                    put(&mut input, &f.ring[..204], lane, t[114]);
                    put(&mut input, &top(&f.ring[251..]), lane, r[115]);
                    put(&mut input, &f.q, lane, r[114]);
                    for kb in 0..24 {
                        let dest = match kb { 21 => f.sx[3], 22 => f.sx[2],
                            23 => f.sx[0], _ => f.ring[204 + kb] };
                        input[dest.0 as usize] |= ((0xbf6af5u64 >> kb) & 1) << lane;
                    }
                } else if kind == 1 {
                    // True actual Y/T and a legal signed-zero payload
                    // component: e=2^23<=q, d=eY<r113, W=0.
                    put(&mut input, &f.ring[..226], lane, t[114]);
                    put(&mut input, &top(&f.ring[226..]), lane, r[113]);
                    put(&mut input, &f.q, lane, r[114]);
                    let d = r[114] << 23usize;
                    assert!(d < r[113] && d.bit_len() <= 54);
                    set_trace_payload(&mut input, &f.dirty, lane,
                                      &trace_payload_pre(d, N::ZERO, 204));
                } else {
                    // Synthetic D^-1 state obeys Xprev<Y, q<2^23,
                    // Xnext<2^(257-SZ), lowSZ121 and the old half139 bound.
                    let y = (N::from(1u64) << 112usize) | N::from(0x113u64);
                    put(&mut input, &f.ring[..121], lane,
                        (N::from(1u64) << 120usize) | N::from(0x121u64));
                    put(&mut input, &top(&f.ring[168..]), lane, y / N::from(3u64));
                    put(&mut input, &f.q, lane, y);
                    input[f.ring[121].0 as usize] |= 1 << lane;
                    input[f.sx[2].0 as usize] |= 1 << lane; // q22, q23 disabled/zero
                }
            }
            let mut want = input.clone();
            for lane in 0..64 {
                if active >> lane & 1 == 0 { continue; }
                if kind == 0 {
                    let old = get(&input, &top(&f.dirty), lane);
                    let next = (old & !payload_bound)
                        | ((old + (t[114] << 23usize)) & payload_bound);
                    assert_ne!(old, next, "nonzero actual q23 payload contribution");
                    put(&mut want, &top(&f.dirty), lane, next);
                } else if kind == 1 {
                    let post = t[114] << 23usize;
                    assert!(post.bit_len() <= 228);
                    set_trace_payload(&mut want, &f.dirty, lane,
                                      &trace_payload_off(N::ZERO, !post, 29));
                } else {
                    let y = get(&input, &f.q, lane);
                    let q = N::from(0x400001u64);
                    let next = y / N::from(3u64) + q * y;
                    assert!(next.bit_len() <= 136 && q.bit_len() == 23);
                    put(&mut want, &top(&f.ring[143..]), lane, next);
                    want[f.ring[121].0 as usize] &= !(1 << lane);
                    want[f.sx[2].0 as usize] &= !(1 << lane);
                    let old = get(&input, &top(&f.dirty), lane);
                    put(&mut want, &top(&f.dirty), lane,
                        (old & !low_bound) | ((old + q * y) & low_bound));
                }
            }
            let got = apply(&forward, &input, &mut apps, &mut coefficients);
            trace_assert_all(&got, &want, &f, &fd_of(&f), "q24_payload_digit_forward");
            assert_eq!(apply(&reverse, &got, &mut apps, &mut coefficients), input,
                       "q24 components F/I all695, inactive SX0 DATA and symbolic phase");
            let back = apply(&reverse, &want, &mut apps, &mut coefficients);
            assert_eq!(back, input, "q24 component inverse oracle");
            assert_eq!(apply(&forward, &back, &mut apps, &mut coefficients), want,
                       "q24 components I/F all695 and symbolic phase");
            continuous_pairs(&forward, &reverse, &input, &want, &f, &mut apps,
                             &format!("q24_component_kind{kind}_mode{mode}"));
            packs += 1;
        }
    }
    assert_eq!(apps, invoice, "complete symbolic/native plus continuous-native FI/IF inventory");
    eprintln!("LOWQ695_Q24_HIGH_PAYLOAD_DIGIT_TRANSITION_FDATA_NATIVE_PASS components=3 packs={packs} lanes={} all695=true actualC114_q23_slot51=true signed_zero_digit_e23=true lowSZ_HR_q23_disabled_read=true inactiveSX0_DATA=true inactiveSY_wrap0_114_115_120_128=true FI=true IF=true continuous_native_classical_XOF_phase=true phase0=true physical_applications={apps} independent_hmr_measurement_events_times64={coefficients} genuine_full_column=false initialized_prefix=false whole=false", 64 * packs);
}
