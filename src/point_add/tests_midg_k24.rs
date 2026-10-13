//! Finite K24 stage1_v test on the N281, 698-wire donor frame.
use super::builder::{B, G};
use super::frogdrop_col::{rec, ColPar};
use super::frogdrop_sched::N;
use super::midg::{stage1_v, S1, TC};
use super::tests_frogdrop::{run, Rng};
use crate::circuit::{Op, OperationType as K, QubitId, NO_BIT};

fn put(q: &mut [u64], reg: &[QubitId], lane: usize, v: N) {
    for (i, p) in reg.iter().enumerate() {
        q[p.0 as usize] = (q[p.0 as usize] & !(1u64 << lane))
            | (u64::from(v.bit(i)) << lane);
    }
}
fn get(q: &[u64], reg: &[QubitId], lane: usize) -> N {
    reg.iter().enumerate().fold(N::ZERO, |v, (i, p)|
        v | (N::from((q[p.0 as usize] >> lane) & 1) << i))
}
fn builder() -> B {
    assert!(std::env::var_os("LOWQ_EXACT_STREAM_PATH").is_none());
    B::new()
}
struct Frame {
    ring: Vec<QubitId>, sx: Vec<QubitId>, sz: Vec<QubitId>,
    bank: Vec<QubitId>, dirty: Vec<QubitId>, act: QubitId,
    separate_gt0: Option<QubitId>,
}
fn frame(b: &mut B, cp: &ColPar, reference: bool) -> Frame {
    assert_eq!((cp.n, cp.nq, cp.k, cp.h), (281, 128, 22, 24));
    let ring = b.alloc_n(281);
    let q = b.alloc_n(128);
    let _sy = b.alloc_n(8);
    let sx = b.alloc_n(8);
    let _ph = b.alloc();
    let pool = b.alloc_n(13);
    let dirty = b.alloc_n(259);
    assert_eq!(b.width(), 698);
    let mut sz = pool[..8].to_vec();
    if cp.sz.1 > 255 { sz.push(pool[8]); }
    let mt = (cp.n - (cp.sz.0 + cp.h) + 1).min(cp.nq.max(cp.xw) + 1);
    let kmax = 258usize.saturating_sub(cp.sz.0 + cp.sy.0).min(super::mid2::QF).min(mt);
    let lsb = if cp.dn { cp.sy.1.max(28) } else { cp.sy.1 };
    let end = cp.nq - if cp.dn { super::pointadd_frogdrop::CNTB } else { 0 };
    let start = lsb.max(cp.sy.1.min(cp.nq) + kmax);
    let bank = if start < end { q[start..end].to_vec() } else { vec![] };
    let separate_gt0 = if reference { Some(b.alloc()) } else { None };
    assert_eq!(b.width(), if reference { 699 } else { 698 });
    Frame { ring, sx, sz, bank, dirty, act: pool[12], separate_gt0 }
}
fn layout(f: &Frame, helpers: usize) -> S1 {
    assert!(helpers <= f.bank.len());
    let bank = f.bank[..helpers].to_vec();
    let mut r = f.ring[..23].to_vec();
    r.extend([f.sx[2], f.sx[4]]);
    let mut gt = vec![f.separate_gt0.unwrap_or(f.sx[0]), f.sx[3]];
    if let Some(&p) = bank.first() { gt.push(p); }
    S1 { r, f: f.sx[0], zero: f.ring[23], sgn: f.sx[0], gt,
        anc: bank.iter().skip(1).copied().collect(), andc: bank.clone(),
        chain: bank, dirty: f.dirty.clone() }
}
#[derive(Clone, Copy, Debug)]
enum Form { Window, Remainder, V }
fn recipe(b: &mut B, f: &Frame, cp: &ColPar, helpers: usize, form: Form) -> Vec<G> {
    let s = layout(f, helpers);
    let fv = stage1_v(b, &f.ring[257..281], &f.ring[23..48], &f.sz, cp.sz, &s, f.act, true);
    let fr = stage1_v(b, &f.ring[257..281], &f.ring[23..48], &f.sz, cp.sz, &s, f.act, false);
    match form {
        Form::Window => fv,
        Form::Remainder => fr,
        Form::V => rec(b, |b| { b.play(&fv, false); b.play(&fr, true); }),
    }
}
fn protection(b: &mut B, f: &Frame, cp: &ColPar) -> Vec<G> {
    let dest = (0..22 + 2 + TC).chain(281 - 24..281).collect();
    rec(b, |b| super::frogdrop::rot_by_range_care(b, &f.ring, &f.sz,
        cp.sz.0, cp.sz.1, true, &f.dirty, &dest))
}

#[test]
fn d1_protection_top24_exact() {
    let sched = super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP);
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(&sched);
    let mut rng = Rng::new(0xd1_24);
    for cp in profiles(&cols) {
        let mut b = builder();
        let f = frame(&mut b, &cp, false);
        let p = protection(&mut b, &f, &cp);
        let forward = emitted(&mut b, &p, false);
        let reverse = emitted(&mut b, &p, true);
        let mut input = vec![0u64; b.width() as usize];
        for &q in f.ring.iter().chain(f.dirty.iter()) { input[q.0 as usize] = rng.next(); }
        for lane in 0..64 {
            let size = cp.sz.0 + (rng.next() as usize % (cp.sz.1 - cp.sz.0 + 1));
            put(&mut input, &f.sz, lane, N::from(size as u64));
        }
        let got = run(&forward, input.len(), &|q| *q = input.clone());
        assert_eq!(got.phase, 0);
        let dest = (0..22 + 2 + TC).chain(281 - 24..281);
        for i in dest {
            for lane in 0..64 {
                let sz = get(&input, &f.sz, lane).as_limbs()[0] as usize;
                let want = (input[f.ring[(i + sz) % 281].0 as usize] >> lane) & 1;
                let actual = (got.q[f.ring[i].0 as usize] >> lane) & 1;
                assert_eq!(actual, want, "rotated lane {i}, size {sz}, shot {lane}");
            }
        }
        let back = run(&reverse, input.len(), &|q| *q = got.q.clone());
        assert_eq!(back.phase, 0);
        assert_eq!(back.q, input, "care rotation returns all lanes");
    }
}

#[test]
fn d1_active_columns_use_k24_head() {
    let sched = super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP);
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(&sched);
    let mut active = 0;
    for (i, cp) in cols.iter().enumerate() {
        if cp.hr || cp.ht {
            active += 1;
            assert_eq!((cp.n, cp.nq, cp.k, cp.h), (281, 128, 22, 24), "column {i}");
            assert!(cp.sz.0 >= 57 && cp.sz.1 <= 256, "column {i} sz {:?}", cp.sz);
        }
    }
    assert!(active > 0);
    eprintln!("D1_K24_ACTIVE_COLUMNS count={active}");
}
fn emitted(b: &mut B, r: &[G], inverse: bool) -> Vec<Op> {
    assert!(b.ops.is_empty());
    b.play(r, inverse);
    std::mem::take(&mut b.ops)
}
fn symbolic(ops: &[Op], mut q: Vec<u64>) -> (Vec<u64>, u64) {
    let mut measured = std::collections::BTreeMap::new();
    let mut phases = Vec::<u64>::new();
    let mut constant = 0u64;
    for op in ops {
        let t = op.q_target.0 as usize;
        let a = op.q_control1.0 as usize;
        let c = op.q_control2.0 as usize;
        match op.kind {
            K::X => { assert_eq!(op.c_condition, NO_BIT); q[t] ^= u64::MAX; }
            K::CX => { assert_eq!(op.c_condition, NO_BIT); q[t] ^= q[a]; }
            K::CCX => { assert_eq!(op.c_condition, NO_BIT); q[t] ^= q[a] & q[c]; }
            K::Swap => { assert_eq!(op.c_condition, NO_BIT); q.swap(a, t); }
            K::Hmr => {
                assert_eq!(op.c_condition, NO_BIT);
                assert_ne!(op.c_target, NO_BIT);
                measured.insert(op.c_target, phases.len());
                phases.push(q[t]); q[t] = 0;
            }
            K::CZ => {
                if op.c_condition == NO_BIT { constant ^= q[a] & q[t]; }
                else { phases[measured[&op.c_condition]] ^= q[a] & q[t]; }
            }
            other => panic!("unexpected K24 P operation {other:?}"),
        }
    }
    assert_eq!(constant, 0, "constant phase");
    assert!(phases.iter().all(|&v| v == 0), "independent HMR coefficient");
    (q, phases.len() as u64 * 64)
}
fn apply(ops: &[Op], input: &[u64], apps: &mut u64, coeff: &mut u64) -> Vec<u64> {
    *apps += 2 * ops.len() as u64;
    assert!(*apps <= 100_000_000, "K24 bounded physical application cap");
    let (q, n) = symbolic(ops, input.to_vec());
    *coeff += n;
    let actual = run(ops, input.len(), &|q| *q = input.to_vec());
    assert_eq!(actual.phase, 0, "native phase");
    assert_eq!(actual.q, q, "native vs independent symbolic");
    q
}
fn input(f: &Frame, cp: &ColPar, mode: usize, seed: u64) -> Vec<u64> {
    let mut rng = Rng::new(seed);
    let mut q: Vec<_> = (0..698).map(|_| rng.next()).collect();
    let act = [0, u64::MAX, 0x00ff_0f0f_3333_5555][mode];
    q[f.act.0 as usize] = act;
    for &p in f.ring[..23].iter().chain([f.sx[2], f.sx[4], f.ring[23]].iter()) {
        q[p.0 as usize] &= !act;
    }
    q[f.ring[280].0 as usize] |= act;
    q[f.sx[0].0 as usize] = 0;
    q[f.sx[3].0 as usize] = 0;
    for &p in &f.bank { q[p.0 as usize] = 0; }
    let sizes = [57usize, 128, 133, 230, 231, 232, 233, 234, 255, 256];
    let tt = N::from_str_radix("11884e93b469ce87829ca3198b81d79443", 16).unwrap();
    for lane in 0..64 {
        let sz = sizes[lane % sizes.len()].max(cp.sz.0).min(cp.sz.1);
        put(&mut q, &f.sz, lane, N::from(sz as u64));
        if ((act >> lane) & 1) == 0 { continue; }
        let zh = match lane % 5 {
            0 => N::from(1u64) << 23,
            1 => (N::from(1u64) << 24) - N::from(1u64),
            2 => tt >> (133 - 24),
            _ => rng.below(23) | (N::from(1u64) << 23),
        };
        put(&mut q, &f.ring[257..281], lane, zh);
        let ss = sz - 24;
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
                let p = f.ring[23 + i];
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
        let divisor = get(input, &f.ring[257..281], lane) | N::from(1u64);
        let u = (257 - sz).saturating_sub(TC);
        let reciprocal = ((N::from(1u64) << (256 - (sz - 24))) - N::from(1u64)) / divisor;
        let t = N::from(1u64) << (257 - sz);
        let delta = t - (((reciprocal >> u) + N::from(1u64)) << u);
        if !matches!(form, Form::Remainder) {
            let mut w = N::ZERO;
            for i in 0..=TC {
                let pos = 257isize - sz as isize - i as isize;
                if pos >= 0 && ((input[f.ring[23 + i].0 as usize] >> lane) & 1) != 0 {
                    w |= N::from(1u64) << pos as usize;
                }
            }
            let w = if inverse_v { (w + t - delta) & (t - N::from(1u64)) }
                    else { (w + delta) & (t - N::from(1u64)) };
            for i in 1..=TC {
                let pos = 257isize - sz as isize - i as isize;
                if pos >= 0 {
                    let p = f.ring[23 + i];
                    q[p.0 as usize] = (q[p.0 as usize] & !(1 << lane))
                        | (u64::from(w.bit(pos as usize)) << lane);
                }
            }
        }
        if !matches!(form, Form::V) {
            let mut remainder = (N::from(1u64) << 23) - N::from(1u64);
            let mut phys = f.ring[..23].to_vec(); phys.extend([f.sx[2], f.sx[4]]);
            for _ in 0..TC {
                remainder = (remainder * N::from(2u64) + N::from(1u64)) % divisor;
                let p = phys.pop().unwrap(); phys.insert(0, p);
            }
            put(&mut q, &phys, lane, remainder);
        }
    }
    q
}
fn compare_reference(reference: &[u64], actual: &[u64]) {
    assert_eq!(actual.len(), 698);
    assert_eq!(reference.len(), 699);
    assert_eq!(&reference[..698], actual, "all698 reference comparison");
    assert_eq!(reference[698], 0, "explicit test-only gt0 returns0");
}

fn profiles(cols: &[ColPar]) -> Vec<ColPar> {
    assert_eq!(cols.len(), 203);
    assert_eq!(cols[10].sz, (189, 255));
    assert_eq!(cols[10].sy, (1, 65));
    assert_eq!(cols[85].sz, (106, 234));
    assert_eq!(cols[85].sy, (23, 142));
    let mut synthetic = cols[10].clone(); synthetic.sz = (57, 256);
    vec![cols[10].clone(), cols[85].clone(), synthetic]
}
fn helper_sizes(f: &Frame) -> Vec<usize> {
    let mut sizes = vec![0, 1.min(f.bank.len()), 2.min(f.bank.len()), f.bank.len()];
    sizes.sort_unstable(); sizes.dedup(); sizes
}
fn price_add(invoice: &mut u64, ops: &[Op], applications: u64) {
    // Every apply() evaluates the same physical ops twice, independently:
    // symbolic HMR coefficients, then unchanged upstream Simulator.
    let add = (ops.len() as u64).checked_mul(2).unwrap().checked_mul(applications).unwrap();
    *invoice = invoice.checked_add(add).unwrap();
}
fn application_invoice(cases: &[ColPar]) -> u64 {
    // This prepass emits every exact recipe from this same binary, before
    // any fixture creation, model expectation, Simulator or symbolic apply.
    let mut invoice = 0u64;
    for (profile, cp) in cases.iter().enumerate() {
        let mut geometry = builder(); let gf = frame(&mut geometry, cp, false);
        if profile != 1 { assert_eq!(gf.bank.len(), 40, "C10 bank coverage"); }
        else { assert!(gf.bank.is_empty(), "C85 empty-bank coverage"); }
        for helpers in helper_sizes(&gf) { for form in [Form::Window, Form::Remainder, Form::V] {
            let mut b = builder(); let f = frame(&mut b, cp, false);
            let r = recipe(&mut b, &f, cp, helpers, form);
            let forward = emitted(&mut b, &r, false); let reverse = emitted(&mut b, &r, true);
            let mut rb = builder(); let rf = frame(&mut rb, cp, true);
            let rr = recipe(&mut rb, &rf, cp, helpers, form);
            let rforward = emitted(&mut rb, &rr, false); let rreverse = emitted(&mut rb, &rr, true);
            let copies = if matches!(form, Form::V) { 6 } else { 3 };
            for ops in [&forward, &reverse, &rforward, &rreverse] { price_add(&mut invoice, ops, copies); }
            eprintln!("K24_INVOICE_KERNEL profile={profile} helpers={helpers} form={form:?} F_N={} I_N={} reference_F_N={} reference_I_N={} each_applications={copies}",
                forward.len(), reverse.len(), rforward.len(), rreverse.len());
        } }
    }
    for (profile, cp) in cases[..2].iter().enumerate() {
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
        eprintln!("K24_INVOICE_CALLER profile={profile} P_F_N={} P_I_N={} F_N={} I_N={} reference_F_N={} reference_I_N={}",
            pf.len(), pi.len(), cf.len(), ci.len(), rcf.len(), rci.len());
    }
    eprintln!("K24_APPLICATION_INVOICE physical_applications={invoice} cap=100000000 candidate_width=698 reference_width=699 native_started=false same_binary=true profiles=3 caller_profiles=2");
    assert!(invoice <= 100_000_000, "full fixed K24 cohort exceeds cap before any native application");
    invoice
}

#[test]
fn f1_pair_cancellation_k24_actual699_vform() {
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    assert_eq!(cols.len(), 203);
    for &ci in &[10usize, 85] {
        let cp = &cols[ci];
        let build = |cancel: bool, inverse: bool| {
            let mut b = builder();
            b.cancel_simple_pairs = cancel;
            b.cancel_commuting_pairs = cancel;
            let f = frame(&mut b, cp, false);
            let r = recipe(&mut b, &f, cp, f.bank.len(), Form::V);
            let ops = emitted(&mut b, &r, inverse);
            (ops, b.tof)
        };
        let (of, oft) = build(false, false);
        let (oi, oit) = build(false, true);
        let (nf, nft) = build(true, false);
        let (ni, nit) = build(true, true);
        let mut g = builder(); let f = frame(&mut g, cp, false);
        let input = input(&f, cp, 2, 0xf1_699_b00 + ci as u64);
        let mut apps = 0; let mut coeff = 0;
        let a = apply(&of, &input, &mut apps, &mut coeff);
        assert_eq!(apply(&nf, &input, &mut apps, &mut coeff), a, "V forward col {ci}");
        let ai = apply(&oi, &input, &mut apps, &mut coeff);
        assert_eq!(apply(&ni, &input, &mut apps, &mut coeff), ai, "V inverse col {ci}");
        assert_eq!(apply(&oi, &a, &mut apps, &mut coeff), input, "V old FI col {ci}");
        assert_eq!(apply(&ni, &a, &mut apps, &mut coeff), input, "V new FI col {ci}");
        assert_eq!(apply(&of, &ai, &mut apps, &mut coeff), input, "V old IF col {ci}");
        assert_eq!(apply(&nf, &ai, &mut apps, &mut coeff), input, "V new IF col {ci}");
        eprintln!("F1_PAIR_K24_DIFF_PASS col={ci} width=698 old_F_T={oft} new_F_T={nft} old_I_T={oit} new_I_T={nit} packs=1 lanes=64 independent_phase_coefficients={coeff} all_wires=true");
    }
}

#[test]
#[ignore = "ROOT compile/native resource admission required; K24 P-kernel only"]
fn k24_returned_f_actual699_state_phase_v2() {
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
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
            let mut ri = input.clone(); ri.push(0);
            let a = apply(&forward, &input, &mut apps, &mut coefficients);
            let ra = apply(&rforward, &ri, &mut apps, &mut coefficients);
            compare_reference(&ra, &a);
            let want = expected(&f, &input, form, false);
            let act = input[f.act.0 as usize];
            for i in 0..698 { assert_eq!(a[i] & act, want[i] & act, "numeric active q{i} range={range:?} mode={mode} form={form:?}"); }
            assert_eq!(apply(&reverse, &a, &mut apps, &mut coefficients), input, "candidate FI");
            assert_eq!(apply(&rreverse, &ra, &mut apps, &mut coefficients), ri, "reference FI");
            if matches!(form, Form::V) {
                assert_eq!(a, want, "V direct all699 including false DATA");
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
    for (profile, cp) in cases[..2].iter().enumerate() { for mode in 0..3 {
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
        let mut ri = input.clone(); ri.push(0);
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
    assert_eq!(apps, invoice, "exact same-binary prepass application invoice");
    eprintln!("K24_RETURNED_F_NATIVE_PASS candidate_width=698 reference_width=699 packs={packs} lanes={} physical_applications={apps} independent_hmr_coefficients={coefficients} all698=true false_R_window_DATA=true caller_fv_fr=true profiles=3 caller_profiles=2 whole=false", 64 * packs);
}
