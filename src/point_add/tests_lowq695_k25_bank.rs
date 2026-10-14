//! Fresh R25 paidQbank loan component fixture; all source/native evidence is new.
//! Head25, TC25, actualone/small/rich banks, arbitraryinactive loan/Win0 DATA.
use super::*;
struct Frame {
    ring: Vec<QubitId>, sx: Vec<QubitId>, sz: Vec<QubitId>,
    bank: Vec<QubitId>, dirty: Vec<QubitId>, act: QubitId, c0: QubitId,
    q: Vec<QubitId>, sy: Vec<QubitId>, ph: QubitId, pool: Vec<QubitId>,
    reference_r: Vec<QubitId>, donor: QubitId,
}
fn frame(b: &mut B, cp: &ColPar, reference: bool) -> Frame {
    let mut f=super::frame(b,cp,reference);
    let donor=f.bank.pop().expect("all paid fixture profiles have an actualcleanbank donor");
    assert!(!f.bank.contains(&donor));
    if cp.dn { assert_eq!(donor,f.q[120]); } else { assert_eq!(donor,f.q[127]); }
    Frame { ring:f.ring,sx:f.sx,sz:f.sz,bank:f.bank,dirty:f.dirty,act:f.act,c0:f.c0,
        q:f.q,sy:f.sy,ph:f.ph,pool:f.pool,reference_r:f.reference_r,donor }
}
fn layout(f: &Frame, helpers: usize) -> S1 {
    assert!(helpers<=f.bank.len());let bank=f.bank[..helpers].to_vec();
    let mut r=if f.reference_r.is_empty(){f.ring[..22].to_vec()}else{f.ring[..21].to_vec()};
    if !f.reference_r.is_empty(){r.push(f.reference_r[0]);}
    r.extend([f.sx[2],f.sx[3],f.donor]);
    if !f.reference_r.is_empty(){r.push(f.reference_r[1]);}
    assert_eq!(r.len(),if f.reference_r.is_empty(){25}else{26});
    assert!(!r.contains(&f.act)&&!bank.contains(&f.donor));
    S1 {r,f:f.sx[0],zero:f.ring[21],sgn:f.sx[0],gt:vec![f.sx[0]],
        anc:bank.iter().skip(1).copied().collect(),andc:bank.clone(),chain:bank,dirty:f.dirty.clone()}
}


fn recipe(b: &mut B, f: &Frame, cp: &ColPar, helpers: usize, form: Form) -> Vec<G> {
    let s = layout(f, helpers);
    let fv = stage1_v(b, &f.ring[254..279], &f.ring[21..47], &f.sz, cp.sz, &s, f.act, true);
    let fr = stage1_v(b, &f.ring[254..279], &f.ring[21..47], &f.sz, cp.sz, &s, f.act, false);
    match form {
        Form::Window => fv,
        Form::Remainder => fr,
        Form::V => rec(b, |b| { b.play(&fv, false); b.play(&fr, true); }),
    }
}

fn protection(b: &mut B, f: &Frame, cp: &ColPar) -> Vec<G> {
    let dest = (0..20 + 2 + TC).chain(279 - 25..279).collect();
    rec(b, |b| crate::point_add::frogdrop::rot_by_range_care(b, &f.ring, &f.sz,
        cp.sz.0, cp.sz.1, true, &f.dirty, &dest))
}

fn input(f: &Frame, cp: &ColPar, mode: usize, seed: u64) -> Vec<u64> {
    let mut rng = Rng::new(seed);
    let mut q: Vec<_> = (0..695 + f.reference_r.len()).map(|_| rng.next()).collect();
    let act = [0, u64::MAX, 0x00ff_0f0f_3333_5555][mode];
    q[f.act.0 as usize] = act;
    q[f.donor.0 as usize] &= !act;
    for &p in f.ring[..22].iter().chain([f.sx[2], f.sx[3]].iter()) {
        q[p.0 as usize] &= !act;
    }
    q[f.ring[278].0 as usize] |= act;
    q[f.sx[0].0 as usize] = 0;
    // These are parked quotient passengers during the V-form in the full column.
    // sx[3] retains arbitrary inactive DATA; only the active R care is zero.
    for &p in &f.bank { q[p.0 as usize] = 0; }
    let sizes = [57usize, 128, 133, 230, 231, 232, 233, 234, 255, 256];
    let tt = N::from_str_radix("11884e93b469ce87829ca3198b81d79443", 16).unwrap();
    for lane in 0..64 {
        let sz = sizes[lane % sizes.len()].max(cp.sz.0).min(cp.sz.1);
        put(&mut q, &f.sz, lane, N::from(sz as u64));
        if ((act >> lane) & 1) == 0 { continue; }
        let zh = match lane % 5 {
            0 => N::from(1u64) << 24,
            1 => (N::from(1u64) << 25) - N::from(1u64),
            2 => tt >> (133 - 25),
            _ => rng.below(24) | (N::from(1u64) << 24),
        };
        put(&mut q, &f.ring[254..279], lane, zh);
        let ss = sz - 25;
        let divisor = zh | N::from(1u64);
        let reciprocal = ((N::from(1u64) << (256 - ss)) - N::from(1u64)) / divisor;
        let u = (257 - sz).saturating_sub(TC);
        let t = N::from(1u64) << (257 - sz);
        let tie = (reciprocal >> u) << u;
        let w = match lane % 4 {
            0 => tie, 1 => tie + N::from(1u64),
            2 => tie.saturating_sub(N::from(1u64)), _ => rng.below(257 - sz),
        } & (t - N::from(1u64));
        for i in 0..=TC {
            let pos = 257isize - sz as isize - i as isize;
            if pos >= 0 {
                let p = f.ring[21 + i];
                q[p.0 as usize] = (q[p.0 as usize] & !(1 << lane))
                    | (u64::from(w.bit(pos as usize)) << lane);
            }
        }
    }
    q
}

fn expected(f: &Frame, input: &[u64], form: Form, inverse_v: bool) -> Vec<u64> {
    let mut q = input.to_vec();
    for lane in 0..64 {
        if ((input[f.act.0 as usize] >> lane) & 1) == 0 { continue; }
        let sz = get(input, &f.sz, lane).as_limbs()[0] as usize;
        let divisor = get(input, &f.ring[254..279], lane) | N::from(1u64);
        let u = (257 - sz).saturating_sub(TC);
        let reciprocal = ((N::from(1u64) << (256 - (sz - 25))) - N::from(1u64)) / divisor;
        let t = N::from(1u64) << (257 - sz);
        let delta = t - (((reciprocal >> u) + N::from(1u64)) << u);
        if !matches!(form, Form::Remainder) {
            let mut w = N::ZERO;
            for i in 0..=TC {
                let pos = 257isize - sz as isize - i as isize;
                if pos >= 0 && ((input[f.ring[21 + i].0 as usize] >> lane) & 1) != 0 {
                    w |= N::from(1u64) << pos as usize;
                }
            }
            let w = if inverse_v { (w + t - delta) & (t - N::from(1u64)) }
                    else { (w + delta) & (t - N::from(1u64)) };
            for i in 1..=TC {
                let pos = 257isize - sz as isize - i as isize;
                if pos >= 0 {
                    let p = f.ring[21 + i];
                    q[p.0 as usize] = (q[p.0 as usize] & !(1 << lane))
                        | (u64::from(w.bit(pos as usize)) << lane);
                }
            }
        }
        if !matches!(form, Form::V) {
            let mut remainder = (N::from(1u64) << 24) - N::from(1u64);
            let mut phys = layout(f, f.bank.len()).r;
            for _ in 0..TC {
                remainder = (remainder * N::from(2u64) + N::from(1u64)) % divisor;
                let p = phys.pop().unwrap(); phys.insert(0, p);
            }
            put(&mut q, &phys, lane, remainder);
        }
    }
    q
}

fn profiles(cols: &[ColPar]) -> Vec<ColPar> {
    assert_eq!(cols.len(),203);
    assert_eq!(cols[10].sz,(189,255));assert_eq!(cols[27].sz,(151,241));
    assert!(cols[138].dn);
    vec![cols[10].clone(),cols[27].clone(),cols[138].clone()]
}

fn helper_sizes(f: &Frame) -> Vec<usize> {
    let mut sizes = vec![0, 1.min(f.bank.len()), 2.min(f.bank.len()), f.bank.len()];
    sizes.sort_unstable(); sizes.dedup(); sizes
}

fn application_invoice(cases: &[ColPar]) -> u64 {
    // This prepass emits every exact recipe from this same binary, before
    // any fixture creation, model expectation, Simulator or symbolic apply.
    let mut invoice = 0u64;
    for (profile, cp) in cases.iter().enumerate() {
        let mut geometry = builder(); let gf = frame(&mut geometry, cp, false);
        assert_eq!(cases.len(),3,"exact C10/C27/C138 paid-bank profiles");
        assert_eq!(gf.bank.len(),[39,2,0][profile],
            "post-loan C10 rich/C27 small/C138 one-lane-bank coverage");
        assert_eq!(gf.donor,gf.q[[127,127,120][profile]],
            "paid donor owner for C10/C27/C138");
        for helpers in helper_sizes(&gf) { for form in [Form::Window, Form::Remainder, Form::V] {
            let mut b = builder(); let f = frame(&mut b, cp, false);
            let r = recipe(&mut b, &f, cp, helpers, form);
            let forward = emitted(&mut b, &r, false); let reverse = emitted(&mut b, &r, true);
            let mut rb = builder(); let rf = frame(&mut rb, cp, true);
            let rr = recipe(&mut rb, &rf, cp, helpers, form);
            let rforward = emitted(&mut rb, &rr, false); let rreverse = emitted(&mut rb, &rr, true);
            let copies = if matches!(form, Form::V) { 6 } else { 3 };
            for ops in [&forward, &reverse, &rforward, &rreverse] { price_add(&mut invoice, ops, copies); }
            eprintln!("K25_BANK_INVOICE_KERNEL profile={profile} helpers={helpers} form={form:?} F_N={} I_N={} reference_F_N={} reference_I_N={} each_applications={copies}",
                forward.len(), reverse.len(), rforward.len(), rreverse.len());
        } }
    }
    for (profile, cp) in cases[..3].iter().enumerate() {
        let mut b = builder(); let f = frame(&mut b, cp, false);
        let p = protection(&mut b, &f, cp);
        let v = recipe(&mut b, &f, cp, f.bank.len(), Form::V);
        let call = rec(&mut b, |b| { b.play(&p, false); b.play(&v, false); b.play(&p, true); });
        let pf = emitted(&mut b, &p, false); let pi = emitted(&mut b, &p, true);
        let cf = emitted(&mut b, &call, false); let ci = emitted(&mut b, &call, true);
        let mut rb = builder(); let rf = frame(&mut rb, cp, true);
        let rp = protection(&mut rb, &rf, cp);
        let rv = recipe(&mut rb, &rf, cp, rf.bank.len(), Form::V);
        let rc = rec(&mut rb, |b| { b.play(&rp, false); b.play(&rv, false); b.play(&rp, true); });
        let rcf = emitted(&mut rb, &rc, false); let rci = emitted(&mut rb, &rc, true);
        price_add(&mut invoice, &pi, 3);
        for ops in [&pf, &cf, &ci, &rcf, &rci] { price_add(&mut invoice, ops, 6); }
        eprintln!("K25_BANK_INVOICE_CALLER profile={profile} P_F_N={} P_I_N={} F_N={} I_N={} reference_F_N={} reference_I_N={}",
            pf.len(), pi.len(), cf.len(), ci.len(), rcf.len(), rci.len());
    }
    eprintln!("K25_BANK_APPLICATION_INVOICE physical_applications={invoice} cap=100000000 candidate_width=695 reference_width=697 native_started=false same_binary=true profiles=3 caller_profiles=3");
    assert!(invoice <= 100_000_000, "full fixed K25 bankloan cohort exceeds cap before any native application");
    invoice
}

#[test]
#[ignore = "ROOT fresh prepass/native source admission required"]
fn lowq695_k25_bankloan_state_phase_v2() {
    let (cols, _, _) = crate::point_add::pointadd_frogdrop::col_pars(
        &crate::point_add::frogdrop_sched::from_text(crate::point_add::pointadd_frogdrop::SCHED_FROGDROP));
    let cases = profiles(&cols);
    let invoice = application_invoice(&cases);
    let mut apps = 0; let mut coefficients = 0; let mut packs = 0;
    for (profile, cp) in cases.iter().enumerate() {
        let range = cp.sz;
        let mut geometry = builder(); let f = frame(&mut geometry, &cp, false);
        for helpers in helper_sizes(&f) { for mode in 0..3 { for form in [Form::Window, Form::Remainder, Form::V] {
            let mut b = builder(); let f = frame(&mut b, &cp, false);
            let r = recipe(&mut b, &f, &cp, helpers, form);
            let forward = emitted(&mut b, &r, false); let reverse = emitted(&mut b, &r, true);
            assert!(!forward.iter().chain(&reverse).any(|op| op.kind == K::Hmr && op.q_target == f.sx[0]),
                "returned-f must never be an HMR reset target");
            let mut rb = builder(); let rf = frame(&mut rb, &cp, true);
            let rr = recipe(&mut rb, &rf, &cp, helpers, form);
            let rforward = emitted(&mut rb, &rr, false); let rreverse = emitted(&mut rb, &rr, true);
            let input = input(&f, &cp, mode, 0x4b32_3400 + helpers as u64 + mode as u64 + 4099 * profile as u64);
            let mut ri = input.clone(); ri.extend([0,0]);
            let a = apply(&forward, &input, &mut apps, &mut coefficients);
            let ra = apply(&rforward, &ri, &mut apps, &mut coefficients);
            if matches!(form, Form::V) { compare_reference(&ra, &a); }
            let rwant = expected(&rf, &ri, form, false);
            let ract = ri[rf.act.0 as usize];
            for i in 0..697 { assert_eq!(ra[i] & ract, rwant[i] & ract, "wide reference active q{i}"); }
            let want = expected(&f, &input, form, false);
            let act = input[f.act.0 as usize];
            for i in 0..695 { assert_eq!(a[i] & act, want[i] & act, "numeric active q{i} range={range:?} mode={mode} form={form:?}"); }
            assert_eq!(apply(&reverse, &a, &mut apps, &mut coefficients), input, "candidate FI");
            assert_eq!(apply(&rreverse, &ra, &mut apps, &mut coefficients), ri, "reference FI");
            if matches!(form, Form::V) {
                assert_eq!(a, want, "V direct all695 including false DATA");
                let ai = apply(&reverse, &input, &mut apps, &mut coefficients);
                let rai = apply(&rreverse, &ri, &mut apps, &mut coefficients);
                compare_reference(&rai, &ai);
                assert_eq!(ai, expected(&f, &input, form, true), "V direct inverse numeric");
                assert_eq!(apply(&forward, &ai, &mut apps, &mut coefficients), input, "candidate IF");
                assert_eq!(apply(&rforward, &rai, &mut apps, &mut coefficients), ri, "reference IF");
            }
            packs += 1;
        } } }
    }
    // The exact caller's cared protection + fv/fr^-1 + protection^-1 seam.
    for (profile, cp) in cases[..3].iter().enumerate() { for mode in 0..3 {
        let mut b = builder(); let f = frame(&mut b, cp, false);
        let p = protection(&mut b, &f, cp);
        let v = recipe(&mut b, &f, cp, f.bank.len(), Form::V);
        let call = rec(&mut b, |b| { b.play(&p, false); b.play(&v, false); b.play(&p, true); });
        let pforward = emitted(&mut b, &p, false); let preverse = emitted(&mut b, &p, true);
        let cf = emitted(&mut b, &call, false); let ci = emitted(&mut b, &call, true);
        let mut rb = builder(); let rf = frame(&mut rb, cp, true);
        let rp = protection(&mut rb, &rf, cp);
        let rv = recipe(&mut rb, &rf, cp, rf.bank.len(), Form::V);
        let rc = rec(&mut rb, |b| { b.play(&rp, false); b.play(&rv, false); b.play(&rp, true); });
        let rcf = emitted(&mut rb, &rc, false); let rci = emitted(&mut rb, &rc, true);
        let pi = input(&f, cp, mode, 0x4b32_345f + mode as u64 + 4099 * profile as u64);
        let input = apply(&preverse, &pi, &mut apps, &mut coefficients);
        let mut ri = input.clone(); ri.extend([0,0]);
        let a = apply(&cf, &input, &mut apps, &mut coefficients);
        let ra = apply(&rcf, &ri, &mut apps, &mut coefficients); compare_reference(&ra, &a);
        assert_eq!(apply(&pforward, &a, &mut apps, &mut coefficients), expected(&f, &pi, Form::V, false), "caller direct P-view");
        assert_eq!(apply(&ci, &a, &mut apps, &mut coefficients), input, "caller FI");
        assert_eq!(apply(&rci, &ra, &mut apps, &mut coefficients), ri, "reference caller FI");
        let ai = apply(&ci, &input, &mut apps, &mut coefficients);
        let rai = apply(&rci, &ri, &mut apps, &mut coefficients); compare_reference(&rai, &ai);
        assert_eq!(apply(&pforward, &ai, &mut apps, &mut coefficients), expected(&f, &pi, Form::V, true), "caller inverse P-view");
        assert_eq!(apply(&cf, &ai, &mut apps, &mut coefficients), input, "caller IF");
        assert_eq!(apply(&rcf, &rai, &mut apps, &mut coefficients), ri, "reference caller IF");
        packs += 1;
    } }
    assert_eq!(packs,81,"one/small/rich bank profiles and all three caller cohorts");
    assert_eq!(apps, invoice, "exact same-binary prepass application invoice");
    eprintln!("LOWQ695_K25_BANKLOAN_NATIVE_PASS candidate_width=695 reference_width=697 packs={packs} lanes={} physical_applications={apps} independent_hmr_measurement_events_times64={coefficients} all695=true false_R_window_Qbank_DATA=true original_donor_excluded_allhelpers=true head25=true zerohelpers_onebank=true caller_fv_fr=true profiles=3 caller_profiles=3 whole=false", 64 * packs);
}
