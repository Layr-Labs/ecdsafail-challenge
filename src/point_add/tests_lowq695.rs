//! Fresh official696 f4c570bc -> Q695 pool12/sign-R24 fixtures.
//! Candidate TC25/K24, reserve8, original203 and nonce387 are unchanged/increased.
//! ROOT owns every Rust/native job; no earlier native/whole PASS is inherited.
use crate::point_add::builder::{B, G};
use crate::point_add::frogdrop_col::{rec, ColPar};
use crate::point_add::frogdrop_sched::N;
use crate::point_add::midg::{stage1_v, S1, TC};
use crate::point_add::tests_frogdrop::{run, Rng};
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
    bank: Vec<QubitId>, dirty: Vec<QubitId>, act: QubitId, c0: QubitId,
    q: Vec<QubitId>, sy: Vec<QubitId>, ph: QubitId, pool: Vec<QubitId>,
    reference_r: Vec<QubitId>,
}
fn frame(b: &mut B, cp: &ColPar, reference: bool) -> Frame {
    assert_eq!((cp.n, cp.nq, cp.k, cp.h), (279, 128, 20, 22));
    assert_eq!(TC, 25);
    let ring = b.alloc_n(279); let q = b.alloc_n(128);
    let sy = b.alloc_n(8); let sx = b.alloc_n(8); let ph = b.alloc();
    let pool = b.alloc_n(12); let dirty = b.alloc_n(259);
    assert_eq!(b.width(), 695);
    let mut sz = pool[..8].to_vec(); if cp.sz.1 > 255 { sz.push(pool[8]); }
    let mt = (cp.n - (cp.sz.0 + cp.h) + 1).min(cp.nq.max(cp.xw) + 1);
    let kmax = 258usize.saturating_sub(cp.sz.0 + cp.sy.0)
        .min(crate::point_add::mid2::QF).min(mt);
    let lsb = if cp.dn { cp.sy.1.max(28) } else { cp.sy.1 };
    let end = cp.nq - if cp.dn { crate::point_add::pointadd_frogdrop::CNTB } else { 0 };
    let start = lsb.max(cp.sy.1.min(cp.nq) + kmax);
    let bank = if start < end { q[start..end].to_vec() } else { vec![] };
    // Wide reference keeps Win0 disjoint: two test-only lanes replace the
    // sign donor and supply R's25th bit. No such lane enters the candidate.
    let reference_r = if reference { b.alloc_n(2) } else { vec![] };
    assert_eq!(b.width(), if reference { 697 } else { 695 });
    Frame { ring, sx: sx.clone(), sz, bank, dirty, act: sx[4], c0: pool[11],
        q, sy, ph, pool, reference_r }
}
fn layout(f: &Frame, helpers: usize) -> S1 {
    assert!(helpers <= f.bank.len()); let bank = f.bank[..helpers].to_vec();
    let mut r = if f.reference_r.is_empty() { f.ring[..22].to_vec() }
                else { f.ring[..21].to_vec() };
    if !f.reference_r.is_empty() { r.push(f.reference_r[0]); }
    r.extend([f.sx[2], f.sx[3]]);
    if !f.reference_r.is_empty() { r.push(f.reference_r[1]); }
    assert_eq!(r.len(), if f.reference_r.is_empty() {24} else {25});
    assert!(!r.contains(&f.act));
    S1 { r, f: f.sx[0], zero: f.ring[21], sgn: f.sx[0], gt: vec![f.sx[0]],
        anc: bank.iter().skip(1).copied().collect(), andc: bank.clone(),
        chain: bank, dirty: f.dirty.clone() }
}
#[derive(Clone, Copy, Debug)]
enum Form { Window, Remainder, V }


fn recipe(b: &mut B, f: &Frame, cp: &ColPar, helpers: usize, form: Form) -> Vec<G> {
    let s = layout(f, helpers);
    let fv = stage1_v(b, &f.ring[255..279], &f.ring[21..47], &f.sz, cp.sz, &s, f.act, true);
    let fr = stage1_v(b, &f.ring[255..279], &f.ring[21..47], &f.sz, cp.sz, &s, f.act, false);
    match form {
        Form::Window => fv,
        Form::Remainder => fr,
        Form::V => rec(b, |b| { b.play(&fv, false); b.play(&fr, true); }),
    }
}

fn protection(b: &mut B, f: &Frame, cp: &ColPar) -> Vec<G> {
    let dest = (0..20 + 2 + TC).chain(279 - 24..279).collect();
    rec(b, |b| crate::point_add::frogdrop::rot_by_range_care(b, &f.ring, &f.sz,
        cp.sz.0, cp.sz.1, true, &f.dirty, &dest))
}

fn emitted(b: &mut B, r: &[G], inverse: bool) -> Vec<Op> {
    assert!(b.ops.is_empty());
    b.play(r, inverse);
    std::mem::take(&mut b.ops)
}

// Sparse Boolean polynomials in independent HMR outcomes. Coefficients are
// 64-shot bit masks; a sorted monomial records the outcome events it multiplies.
// Idempotence m*m=m makes this the exact Boolean ring, including random-mask
// data gates and nested conditions, rather than a forced-branch interpreter.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct BoolPoly(std::collections::BTreeMap<Vec<usize>, u64>);
impl BoolPoly {
    fn constant(mask: u64) -> Self {
        let mut p = Self::default();
        if mask != 0 { p.0.insert(vec![], mask); }
        p
    }
    fn one() -> Self { Self::constant(u64::MAX) }
    fn variable(event: usize) -> Self {
        Self(std::collections::BTreeMap::from([(vec![event], u64::MAX)]))
    }
    fn xor_assign(&mut self, other: &Self) {
        for (term, &mask) in &other.0 {
            let next = self.0.get(term).copied().unwrap_or(0) ^ mask;
            if next == 0 { self.0.remove(term); }
            else { self.0.insert(term.clone(), next); }
        }
    }
    fn xor(&self, other: &Self) -> Self {
        let mut p = self.clone(); p.xor_assign(other); p
    }
    fn and(&self, other: &Self) -> Self {
        if self.0.is_empty() || other.0.is_empty() { return Self::default(); }
        if let Some(&mask) = other.0.get(&vec![]) {
            if other.0.len() == 1 {
                return Self(self.0.iter().filter_map(|(term, &coef)|
                    if coef & mask == 0 { None } else { Some((term.clone(), coef & mask)) }).collect());
            }
        }
        if self.0.len() == 1 && self.0.contains_key(&vec![]) { return other.and(self); }
        let mut p = Self::default();
        for (a, &ca) in &self.0 { for (b, &cb) in &other.0 {
            let mask = ca & cb;
            if mask == 0 { continue; }
            let mut term = a.clone(); term.extend(b); term.sort_unstable(); term.dedup();
            let next = p.0.get(&term).copied().unwrap_or(0) ^ mask;
            if next == 0 { p.0.remove(&term); } else { p.0.insert(term, next); }
        }}
        p
    }
    fn as_constant(&self) -> u64 {
        assert!(self.0.keys().all(|term| term.is_empty()), "final data depends on an HMR outcome");
        self.0.get(&vec![]).copied().unwrap_or(0)
    }
}
fn symbolic(ops: &[Op], input: Vec<u64>) -> (Vec<u64>, u64) {
    use std::collections::HashMap;
    let mut q: Vec<_> = input.into_iter().map(BoolPoly::constant).collect();
    let mut bits: HashMap<u64, BoolPoly> = HashMap::new();
    let mut base = BoolPoly::one();
    let mut stack = Vec::new();
    let mut phase = BoolPoly::default();
    let mut measurements = 0usize;
    for op in ops {
        let t = op.q_target.0 as usize;
        let a = op.q_control1.0 as usize;
        let c = op.q_control2.0 as usize;
        let mut cond = base.clone();
        if op.c_condition != NO_BIT {
            cond = cond.and(&bits.get(&op.c_condition.0).cloned().unwrap_or_default());
        }
        match op.kind {
            K::X => q[t].xor_assign(&cond),
            K::CX => {
                let delta = cond.and(&q[a]); q[t].xor_assign(&delta);
            }
            K::CCX => {
                let delta = cond.and(&q[a]).and(&q[c]); q[t].xor_assign(&delta);
            }
            K::Swap => {
                let delta = q[a].xor(&q[t]).and(&cond);
                q[a].xor_assign(&delta); q[t].xor_assign(&delta);
            }
            K::Hmr | K::R => {
                let random = BoolPoly::variable(measurements); measurements += 1;
                phase.xor_assign(&q[t].and(&random).and(&cond));
                let not_cond = BoolPoly::one().xor(&cond);
                q[t] = q[t].and(&not_cond);
                if matches!(op.kind, K::Hmr) {
                    assert_ne!(op.c_target, NO_BIT);
                    let old = bits.get(&op.c_target.0).cloned().unwrap_or_default();
                    bits.insert(op.c_target.0, old.and(&not_cond).xor(&random.and(&cond)));
                }
            }
            K::CZ => phase.xor_assign(&cond.and(&q[a]).and(&q[t])),
            K::CCZ => phase.xor_assign(&cond.and(&q[a]).and(&q[c]).and(&q[t])),
            K::Z => phase.xor_assign(&cond.and(&q[t])),
            K::Neg => phase.xor_assign(&cond),
            K::BitInvert | K::BitStore0 | K::BitStore1 => {
                assert_ne!(op.c_target, NO_BIT);
                let old = bits.get(&op.c_target.0).cloned().unwrap_or_default();
                let next = match op.kind {
                    K::BitInvert => old.xor(&cond),
                    K::BitStore0 => old.and(&BoolPoly::one().xor(&cond)),
                    K::BitStore1 => old.and(&BoolPoly::one().xor(&cond)).xor(&cond),
                    _ => unreachable!(),
                };
                bits.insert(op.c_target.0, next);
            }
            K::PushCondition => {
                assert_ne!(op.c_condition, NO_BIT);
                stack.push(base.clone());
                base = base.and(&bits.get(&op.c_condition.0).cloned().unwrap_or_default());
            }
            K::PopCondition => {
                base = stack.pop().expect("unbalanced symbolic condition stack");
            }
            K::Register | K::AppendToRegister | K::DebugPrint => {},
        }
    }
    assert!(stack.is_empty(), "unterminated symbolic condition stack");
    assert!(phase.0.is_empty(), "nonzero independent HMR phase polynomial: {phase:?}");
    (q.iter().map(BoolPoly::as_constant).collect(), measurements as u64 * 64)
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
    let mut q: Vec<_> = (0..695 + f.reference_r.len()).map(|_| rng.next()).collect();
    let act = [0, u64::MAX, 0x00ff_0f0f_3333_5555][mode];
    q[f.act.0 as usize] = act;
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
            0 => N::from(1u64) << 23,
            1 => (N::from(1u64) << 24) - N::from(1u64),
            2 => tt >> (133 - 24),
            _ => rng.below(23) | (N::from(1u64) << 23),
        };
        put(&mut q, &f.ring[255..279], lane, zh);
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
        let divisor = get(input, &f.ring[255..279], lane) | N::from(1u64);
        let u = (257 - sz).saturating_sub(TC);
        let reciprocal = ((N::from(1u64) << (256 - (sz - 24))) - N::from(1u64)) / divisor;
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
            let mut remainder = (N::from(1u64) << 23) - N::from(1u64);
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

fn compare_reference(reference: &[u64], actual: &[u64]) {
    assert_eq!(actual.len(), 695); assert_eq!(reference.len(), 697);
    assert_eq!(&reference[..695], actual, "paired V all695 reference comparison");
    assert_eq!(&reference[695..], &[0,0], "both test-only reference R lanes return0");
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
    eprintln!("K24_APPLICATION_INVOICE physical_applications={invoice} cap=100000000 candidate_width=695 reference_width=697 native_started=false same_binary=true profiles=3 caller_profiles=2");
    assert!(invoice <= 100_000_000, "full fixed K24 cohort exceeds cap before any native application");
    invoice
}

#[test]
#[ignore = "ROOT exact same-binary prepass and fresh native admission required"]
fn lowq695_k24_sign_state_phase_v1() {
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
    assert_eq!(apps, invoice, "exact same-binary prepass application invoice");
    eprintln!("LOWQ695_K24_COMPACT_NATIVE_PASS candidate_width=695 reference_width=697 packs={packs} lanes={} physical_applications={apps} independent_hmr_coefficients={coefficients} all695=true false_R_window_DATA=true caller_fv_fr=true profiles=3 caller_profiles=2 whole=false", 64 * packs);
}

fn fd_of(f: &Frame) -> crate::point_add::frogdrop_col::Fd {
    crate::point_add::frogdrop_col::Fd { ring: f.ring.clone(), q: f.q.clone(), sy: f.sy.clone(), sx: f.sx.clone(),
        ph: f.ph, cnt: f.q[121..].to_vec() }
}

fn top(reg: &[QubitId]) -> Vec<QubitId> { reg.iter().rev().copied().collect() }

#[test]
#[ignore = "ROOT exact same-binary prepass and fresh native admission required"]
fn lowq695_q21_q22_parking_state_phase_v1() {
    use crate::point_add::frogdrop::rot_by_range_care;
    use crate::point_add::midg::park_quotient_record;
    let (cols, _, _) = crate::point_add::pointadd_frogdrop::col_pars(
        &crate::point_add::frogdrop_sched::from_text(crate::point_add::pointadd_frogdrop::SCHED_FROGDROP));
    let cp = &cols[85];
    let mut b = builder();
    let f = frame(&mut b, cp, false);
    let mut cycle = f.q.clone();
    cycle.push(f.pool[9]);
    cycle.extend([f.pool[11], f.pool[10], f.sx[1], f.sx[5], f.sx[6], f.sx[7], f.ph, f.pool[8]]);
    assert_eq!(cycle.len(), 137, "original Q128+x128+reserve8");
    let ds = (0..23).collect();
    let rq = rec(&mut b, |b| rot_by_range_care(b, &cycle, &f.sy, cp.sy.0.min(128), cp.sy.1.min(128),
        true, &f.dirty, &ds));
    let locs: Vec<_> = (0..23).map(|i| match i { 21 => f.sx[3], 22 => f.sx[2], _ => f.ring[i] }).collect();
    let r = park_quotient_record(&mut b, &f.ring, &f.sz, cp.sz, &f.sy, cp.sy.1, f.act,
        &locs, &cycle, &rq, f.sx[0], &f.dirty);
    let forward = emitted(&mut b, &r, false);
    let reverse = emitted(&mut b, &r, true);
    let invoice = 3 * 2 * (forward.len() + reverse.len()) as u64;
    eprintln!("LOWQ695_PARK_INVOICE N_F={} N_I={} physical_applications={invoice} width=695 native_started=false",
        forward.len(), reverse.len());
    assert!(invoice <= 100_000_000);
    let mut apps = 0; let mut coeff = 0; let mut swaps = 0; let mut wrapped = 0;
    for mode in 0..3 {
        let mut rng = Rng::new(0x279_2122 + mode as u64);
        let mut input: Vec<_> = (0..695).map(|_| rng.next()).collect();
        input[f.act.0 as usize] = [0, u64::MAX, 0xf0f0_3333_5555_0f0f][mode];
        input[f.sx[0].0 as usize] = 0;
        for lane in 0..64 {
            let sz = [106usize, 128, 133, 212, 234][lane % 5];
            let sy = [113usize, 114, 115, 116, 117, 126, 127, 128][lane % 8];
            put(&mut input, &f.sz, lane, N::from(sz as u64));
            put(&mut input, &f.sy, lane, N::from(sy as u64));
        }
        let mut want = input.clone();
        for lane in 0..64 {
            if ((input[f.act.0 as usize] >> lane) & 1) == 0 { continue; }
            let sz = get(&input, &f.sz, lane).as_limbs()[0] as usize;
            let sy = get(&input, &f.sy, lane).as_limbs()[0] as usize;
            for kb in 0..23 {
                if sy + kb >= cycle.len() { wrapped += 1; continue; }
                let z = if kb == 21 { f.sx[3] } else if kb == 22 { f.sx[2] } else { f.ring[(sz + kb) % 279] };
                let q = cycle[sy + kb];
                let bit = ((input[z.0 as usize] ^ input[q.0 as usize]) >> lane) & 1;
                want[z.0 as usize] ^= bit << lane;
                want[q.0 as usize] ^= bit << lane;
                swaps += 1;
            }
        }
        let got = apply(&forward, &input, &mut apps, &mut coeff);
        assert_eq!(got, want, "exact park mode {mode}; every inactive DATA lane returns");
        assert_eq!(apply(&reverse, &got, &mut apps, &mut coeff), input, "production park FI");
    }
    assert_eq!(apps, invoice);
    assert!(swaps > 0 && wrapped > 0);
    eprintln!("LOWQ695_Q21_Q22_PARK_NATIVE_PASS packs=3 lanes=192 width=695 swaps={swaps} wrapped={wrapped} reserve=8 physical_applications={apps} independent_hmr_coefficients={coeff} all695=true false_DATA=true whole=false");
}

#[test]
#[ignore = "ROOT exact same-binary prepass and fresh native admission required"]
fn lowq695_default_map_families_state_phase_v1() {
    use crate::point_add::frogdrop_col::{ColScr, map_stage};
    use crate::point_add::frogdrop_sched::{shot, Kind, L0};
    let (cols, _, _) = crate::point_add::pointadd_frogdrop::col_pars(
        &crate::point_add::frogdrop_sched::from_text(crate::point_add::pointadd_frogdrop::SCHED_FROGDROP));
    // A superset fixture envelope exercises each funding branch at the
    // retained m128/emax24 maximum. It changes no production schedule.
    let mut records = Vec::new(); let mut invoice = 0u64;
    for switching in [false, true] {
        let mut cp = cols[85].clone();
        cp.sw = switching; cp.dn = false; cp.cntw = 0;
        cp.sy = (1, 128); cp.smax = (1, 128); cp.m = 128;
        let mut b = default_builder();
        let f = frame(&mut b, &cp, false); let fd = fd_of(&f);
        let sc = ColScr::carve_col(&f.pool, &fd.sx, &f.dirty, cp.kp, cp.qb, cp.tail, false);
        let r = map_stage(&mut b, &fd, &cp, &sc);
        let forward = default_emitted(&mut b, &r, false); let reverse = default_emitted(&mut b, &r, true);
        invoice += 2 * (forward.len() + reverse.len()) as u64;
        eprintln!("LOWQ695_DEFAULT_MAP_INVOICE switching={switching} N_F={} N_I={} width=695 allow_booth=true global_cancel=true eager_rows=true native_started=false",
            forward.len(), reverse.len());
        records.push((f, forward, reverse));
    }
    assert!(invoice <= 100_000_000, "all map branches counted before fixtures or simulation");
    let p = crate::point_add::frogdrop_sched::p();
    let mut rng = Rng::new(0x279_4a9);
    let mut cases = Vec::new(); let mut counts = [0usize; 4];
    for _ in 0..10000 {
        if counts.iter().all(|&v| v == 16) { break; }
        let x = rng.below(255).max(N::from(1u64));
        let (mut r, mut t) = (vec![p, x], vec![N::ZERO, N::from(1u64)]);
        while !r.last().unwrap().is_zero() {
            let i = r.len(); let q = r[i - 2] / r[i - 1];
            r.push(r[i - 2] - q * r[i - 1]); t.push(t[i - 2] + q * t[i - 1]);
        }
        let mut j = 1;
        for rec in shot(x, L0).recs {
            let (bucket, vals) = match rec.kind {
                Kind::Sw => (0, Some((t[j - 1], r[j], t[j], r[j - 1]))),
                Kind::Dl => (1, Some((t[j + 1], r[j], t[j], r[j + 1]))),
                Kind::Dq => (2, Some((t[j], r[j + 1], r[j], t[j + 1]))),
                Kind::Hr => (3, Some((r[j], t[j + 1], t[j], r[j + 1]))),
                _ => (4, None),
            };
            if let Some((z, xv, y, out)) = vals {
                let m = xv.bit_len().max(y.bit_len());
                if counts[bucket] < 16 && m <= 128 && xv.trailing_zeros() <= 24 && y.trailing_zeros() <= 24
                    && z.bit_len() <= 279 - m && out.bit_len() <= 279 - m {
                    assert_eq!(p, z * xv + out * y);
                    cases.push((z, xv, y, out)); counts[bucket] += 1;
                }
            }
            if matches!(rec.kind, Kind::Hr | Kind::Ht | Kind::Dq) { j += 1; }
        }
    }
    assert_eq!(counts, [16; 4], "fixed licensed coverage, no runtime-error-based case selection");
    let mut apps = 0; let mut coeff = 0;
    for (branch, (f, forward, reverse)) in records.iter().enumerate() {
        let mut input = vec![0u64; 695];
        for &q in &f.dirty { input[q.0 as usize] = rng.next(); }
        // SW is a clean extension only on the ordinary branch. A switching
        // recipe must preserve arbitrary live SW, and both preserve PH DATA.
        if branch == 1 { input[f.pool[8].0 as usize] = rng.next(); }
        input[f.ph.0 as usize] = rng.next();
        let mut want = input.clone();
        for (lane, &(z, x, y, out)) in cases.iter().enumerate() {
            let cut = 279 - x.bit_len().max(y.bit_len());
            put(&mut input, &f.ring[..cut], lane, z);
            put(&mut input, &top(&f.ring[cut..]), lane, y);
            put(&mut input, &f.q, lane, x);
            put(&mut input, &f.sy, lane, N::from(y.bit_len() as u64));
            put(&mut want, &f.ring[..cut], lane, out);
            put(&mut want, &top(&f.ring[cut..]), lane, x);
            put(&mut want, &f.q, lane, y);
            put(&mut want, &f.sx, lane, N::from(x.bit_len() as u64));
        }
        let got = apply(forward, &input, &mut apps, &mut coeff);
        assert_eq!(got, want, "map funding branch {branch}: bottom, top, Q, sizes, all scratch and passengers");
        assert_eq!(apply(reverse, &got, &mut apps, &mut coeff), input, "map funding branch {branch} FI");
    }
    assert_eq!(apps, invoice);
    eprintln!("LOWQ695_DEFAULT_MAP_FAMILIES_NATIVE_PASS packs=2 lanes=128 cases={counts:?} width=695 ordinary_extension=2 switch_extension=1 emax=24 allow_booth=true global_cancel=true eager_rows=true all695=true physical_applications={apps} independent_hmr_coefficients={coeff} whole=false");
}

fn default_builder() -> B {
    for name in ["LOWQ_EXACT_STREAM_PATH", "F2_NO_GLOBAL_CANCEL", "FROGDROP_CK",
        "FD_MARK", "FD_MAPEXTRA", "FD_OLDPROBE", "D2_NOOPT"] {
        assert!(std::env::var_os(name).is_none(), "diagnostic configuration override {name}");
    }
    let mut b = builder();
    b.global_cancel = true;
    assert!(b.allow_booth && b.cancel_simple_pairs && b.cancel_commuting_pairs);
    b
}

fn default_emitted(b: &mut B, r: &[G], inverse: bool) -> Vec<Op> {
    assert!(b.global_cancel && b.allow_booth && b.ops.is_empty());
    b.play(r, inverse);
    b.flush_global();
    assert_eq!(b.pending_count(), 0);
    std::mem::take(&mut b.ops)
}

fn trace_frame(b: &mut B) -> Frame {
    // Same live traversal allocation order as point_add_pl after offsets:
    // x[256], payload y[256]+3, ring extension, Q, SY, SX, PH, pool.
    let mut ring = b.alloc_n(256);
    let dirty = b.alloc_n(259);
    ring.extend(b.alloc_n(23));
    let q = b.alloc_n(128);
    let sy = b.alloc_n(8);
    let sx = b.alloc_n(8);
    let ph = b.alloc();
    let pool = b.alloc_n(12);
    assert_eq!(b.width(), 695);
    let act = sx[4];
    Frame { ring, dirty, q, sy, sx, ph, act, c0: pool[11],
        sz: pool[..9].to_vec(), pool, bank: vec![], reference_r: vec![] }
}

fn trace_column_record(b: &mut B, f: &Frame, fd: &mut crate::point_add::frogdrop_col::Fd,
                       cp: &ColPar, stage: usize, initialize: bool) -> Vec<G> {
    use crate::point_add::frogdrop_col::{ColScr, column_pl, column_upto};
    let sc = ColScr::carve_col(&f.pool, &fd.sx, &f.dirty, cp.kp, cp.qb, cp.tail, cp.sz.1 > 255);
    let plc = crate::point_add::pointadd_frogdrop::pl_col(&f.dirty, fd, &f.pool);
    b.begin();
    if initialize { b.x(fd.ring[278]); b.x(fd.sy[0]); }
    if stage == 99 {
        column_pl(b, fd, cp, &sc, Some(&plc));
    } else {
        // The unchanged column_upto test hook returns when stn > upto.
        // Passing stage-1 therefore ends immediately after the named stage.
        assert!((1..=9).contains(&stage));
        column_upto(b, fd, cp, &sc, stage - 1, Some(&plc));
    }
    b.end()
}

fn trace_inputs(f: &Frame) -> (Vec<u64>, N, Vec<N>) {
    // This fixed case and seed are taken verbatim from the protected packed
    // d2_hr_digit_n280_packed diagnostic; no case is selected by a run result.
    let x = N::from_str_radix("70dddacfd33a34f528cce40d9366cd7cf10fa69c8f34abae2728b07a2e4b56e0", 16).unwrap();
    let dy = N::from_str_radix("103a92ea7a3771100adee61ee4d5f0a16324cad0b737e2f9e3c27ba78ac13969", 16).unwrap();
    let p = crate::point_add::frogdrop_sched::p();
    assert!(x > N::ZERO && x.bit_len() <= 255 && x < p);
    let mut rng = Rng::new(0xd2_697_24);
    let dys: Vec<_> = (0..64).map(|lane| if lane == 0 { dy } else { rng.below(256) % p }).collect();
    let mut input = vec![0u64; 695];
    for lane in 0..64 {
        put(&mut input, &f.ring[..256], lane, x);
        put(&mut input, &f.dirty[..256], lane, dys[lane]);
    }
    (input, x, dys)
}

fn trace_model(x: N, dys: &[N]) -> (Vec<N>, Vec<N>, Vec<Vec<N>>, Vec<Vec<N>>) {
    let mut r = vec![crate::point_add::frogdrop_sched::p(), x];
    let mut t = vec![N::ZERO, N::from(1u64)];
    for j in 1..=2 {
        let q = r[j - 1] / r[j];
        r.push(r[j - 1] - q * r[j]);
        t.push(t[j - 1] + q * t[j]);
    }
    assert!(!r[3].is_zero(), "fixed two-column input does not finish early");
    let mut ds = Vec::new(); let mut ws = Vec::new();
    for &dy in dys {
        let mut d = vec![N::ZERO, dy];
        let mut w = vec![N::ZERO, N::ZERO];
        for j in 1..=2 {
            let e = d[j] / r[j];
            d.push(d[j] - e * r[j]);
            let post = w[j].wrapping_add(e.wrapping_mul(t[j]));
            w.push((r[j - 1] / r[j]).wrapping_mul(t[j]).wrapping_add(!post));
        }
        ds.push(d); ws.push(w);
    }
    (r, t, ds, ws)
}

fn trace_payload_pre(d: N, w: N, bt: usize) -> Vec<bool> {
    let cut = 258 - bt;
    (0..259).map(|i| if i < cut { d.bit(i) } else { w.bit(258 - i) }).collect()
}

fn trace_payload_off(d: N, w: N, br: usize) -> Vec<bool> {
    let u = w.wrapping_add(N::from(1u64) << (258 - br));
    (0..259).map(|i| if i < br { d.bit(i) } else { u.bit(258 - i) }).collect()
}

fn set_trace_payload(q: &mut [u64], p: &[QubitId], lane: usize, bits: &[bool]) {
    assert_eq!(p.len(), bits.len());
    for (id, &bit) in p.iter().zip(bits) {
        q[id.0 as usize] = (q[id.0 as usize] & !(1 << lane)) | (u64::from(bit) << lane);
    }
}

fn trace_expected(f: &Frame, fd: &crate::point_add::frogdrop_col::Fd,
                  j: usize, r: &[N], t: &[N], ds: &[Vec<N>], ws: &[Vec<N>]) -> Vec<u64> {
    let mut want = vec![0u64; 695];
    for lane in 0..64 {
        let cut = 279 - t[j - 1].bit_len().max(t[j].bit_len());
        assert!(r[j].bit_len() <= cut);
        put(&mut want, &f.ring[..cut], lane, r[j]);
        put(&mut want, &top(&f.ring[cut..]), lane, t[j]);
        put(&mut want, &f.q, lane, t[j - 1]);
        put(&mut want, &fd.sy, lane, N::from(t[j].bit_len() as u64));
        set_trace_payload(&mut want, &f.dirty, lane, &trace_payload_pre(ds[lane][j], ws[lane][j], t[j].bit_len()));
    }
    // The zero initialization above explicitly checks all remaining ring,
    // SX, PH, SZ and every pool role; it is a model assertion, never a reset.
    want
}

fn trace_assert_all(got: &[u64], want: &[u64], f: &Frame,
                    fd: &crate::point_add::frogdrop_col::Fd, label: &str) {
    assert_eq!((got.len(), want.len()), (695, 695));
    let bad: Vec<_> = (0..695).filter(|&i| got[i] != want[i]).collect();
    if let Some(&first) = bad.first() {
        let lane = (got[first] ^ want[first]).trailing_zeros() as usize;
        let payload: Vec<_> = (0..259).filter(|&i|
            ((got[f.dirty[i].0 as usize] ^ want[f.dirty[i].0 as usize]) >> lane) & 1 != 0).collect();
        eprintln!("LOWQ695_TRACE_MISMATCH label={label} first_wire={first} shot={lane} differing_wires={} first_wires={:?} payload_lanes={:?}",
            bad.len(), &bad[..bad.len().min(24)], &payload[..payload.len().min(24)]);
        eprintln!("LOWQ695_TRACE_NUMERIC label={label} Q_got={:x} Q_want={:x} SY_got={:x} SY_want={:x} SX_got={:x} PH_got={:x}",
            get(got, &f.q, lane), get(want, &f.q, lane), get(got, &fd.sy, lane),
            get(want, &fd.sy, lane), get(got, &fd.sx, lane), get(got, &[fd.ph], lane));
    }
    assert!(bad.is_empty(), "{label}: all695 numeric state/payload/helper boundary");
}

fn late_fd_copy(fd: &crate::point_add::frogdrop_col::Fd) -> crate::point_add::frogdrop_col::Fd {
    crate::point_add::frogdrop_col::Fd { ring: fd.ring.clone(), q: fd.q.clone(),
        sy: fd.sy.clone(), sx: fd.sx.clone(), ph: fd.ph, cnt: fd.cnt.clone() }
}

fn late_invoice(label: &str, forward: &[Op], reverse: &[Op]) -> u64 {
    let stored = forward.len() + reverse.len();
    let invoice = 2 * stored as u64;
    eprintln!("LOWQ695_LATE_INVOICE label={label} F_vectors=1 I_vectors=1 N_F={} N_I={} physical_applications={invoice} retained_ops={stored} op_bytes={} cap=100000000 fixture_created=false native_started=false width=695 allow_booth=true global_cancel=true",
        forward.len(), reverse.len(), stored * std::mem::size_of::<Op>());
    assert!(invoice <= 100_000_000 && stored <= 20_000_000,
        "complete exact inventory before constructing cases or Simulator");
    invoice
}

#[test]
#[ignore = "ROOT exact same-binary prepass and fresh native admission required"]
fn lowq695_finish_column_default_state_phase_v1() {
    use crate::point_add::frogdrop_col::{ColScr, column_pl};
    let (cols, _, _) = crate::point_add::pointadd_frogdrop::col_pars(
        &crate::point_add::frogdrop_sched::from_text(crate::point_add::pointadd_frogdrop::SCHED_FROGDROP));
    assert_eq!(cols.len(), 203);
    let cp = cols.last().unwrap();
    assert!(cp.dn && cp.fin && cp.ht && !cp.sw && !cp.dq);
    let mut b = default_builder(); let f = trace_frame(&mut b); let mut fd = fd_of(&f);
    let sc = ColScr::carve_col(&f.pool, &fd.sx, &f.dirty, cp.kp, cp.qb, cp.tail, false);
    assert_eq!(sc.g, f.sx[4]);
    assert!(!fd.sy.contains(&sc.g) && fd.sx.contains(&sc.g));
    let r = rec(&mut b, |b| column_pl(b, &mut fd, cp, &sc, None));
    assert_eq!(sc.g, f.sx[4], "initial pool12 act binds physical initial SX4");
    assert!(fd.sy.contains(&sc.g) && !fd.sx.contains(&sc.g), "initialSX4 becomes newSY4 after the finishing column");
    let forward = default_emitted(&mut b, &r, false);
    let reverse = default_emitted(&mut b, &r, true);
    let invoice = late_invoice("full_last_column", &forward, &reverse);
    let p = crate::point_add::frogdrop_sched::p(); let mut rng = Rng::new(0x279_f1_15);
    let mut input = vec![0u64; 695];
    for &q in &f.dirty { input[q.0 as usize] = rng.next(); }
    let mut want = input.clone(); let mut populations = [0usize; 3];
    for lane in 0..64 {
        let rem = N::from((1u64 << 15) + 2 * lane as u64 + 1);
        let tl = p / (rem + N::from(1u64)) + (p / rem - p / (rem + N::from(1u64))) / N::from(4u64);
        let tp = p - rem * tl;
        assert!(tp > N::ZERO && tp < tl && tl / tp == N::from(1u64));
        let kind = lane % 3; populations[kind] += 1;
        // Done layout parity is genuine: A0 has odd cnt; B0 has even cnt.
        let oldcnt = if kind == 0 { 3 + 2 * (lane % 40) as u64 }
                     else { 2 + 2 * (lane % 40) as u64 };
        let (z, x, y, cnt, oz, ox, oy, ocnt) = match kind {
            0 => (tl, rem, N::from(1u64), oldcnt, tp, N::from(1u64), rem, oldcnt + 1),
            1 => (tp, N::from(1u64), rem, oldcnt, tl, rem, N::from(1u64), oldcnt + 1),
            _ => (tp, rem + N::from(1u64), rem, 0, tl, rem, N::from(1u64), 1),
        };
        assert!((cp.sz.0..=cp.sz.1).contains(&z.bit_len()));
        assert!((cp.sy.0..=cp.sy.1).contains(&y.bit_len()));
        assert!((cp.sz.0..=cp.sz.1).contains(&oz.bit_len()));
        assert!(cnt < (1u64 << cp.cntw) && ocnt < (1u64 << fd.cnt.len()));
        let cut = 279 - x.bit_len().max(y.bit_len());
        assert!(z.bit_len() <= cut);
        put(&mut input, &f.ring[..cut], lane, z);
        put(&mut input, &top(&f.ring[cut..]), lane, y);
        put(&mut input, &f.q, lane, x); put(&mut input, &fd.cnt, lane, N::from(cnt));
        put(&mut input, &f.sy, lane, N::from(y.bit_len() as u64));
        input[f.ph.0 as usize] |= 1 << lane;
        let outcut = 279 - ox.bit_len().max(oy.bit_len());
        assert!(oz.bit_len() <= outcut);
        put(&mut want, &f.ring[..outcut], lane, oz);
        put(&mut want, &top(&f.ring[outcut..]), lane, oy);
        put(&mut want, &f.q, lane, ox); put(&mut want, &fd.cnt, lane, N::from(ocnt));
        put(&mut want, &fd.sy, lane, N::from(oy.bit_len() as u64));
        put(&mut want, &fd.sx, lane, N::ZERO); want[f.ph.0 as usize] |= 1 << lane;
    }
    assert_eq!(populations, [22, 21, 21]);
    assert_eq!(want[fd.sy[4].0 as usize].count_ones() as usize, populations[0]);
    let mut apps = 0; let mut coeff = 0;
    let got = apply(&forward, &input, &mut apps, &mut coeff);
    trace_assert_all(&got, &want, &f, &fd, "last_column_A0_B0_newfin");
    assert_eq!(apply(&reverse, &got, &mut apps, &mut coeff), input, "last column all695 FI");
    assert_eq!(apps, invoice);
    eprintln!("LOWQ695_LAST_COLUMN_NATIVE_PASS packs=1 lanes=64 populations={populations:?} all695=true passengers259=true finish_owner_initialSX4_newSY4=true newSY4_live=true physical_applications={apps} independent_hmr_measurement_events_times64={coeff} eager_rows=true whole=false");
}

struct LateEndCase { t: N, previous_r: N, d: N, w: N }

fn late_end_cases(sz: (usize, usize)) -> Vec<LateEndCase> {
    // Same Euclid/payload recurrence as the protected model. Selection uses
    // only the unchanged licensed envelope, never an emitted/native result.
    let p = crate::point_add::frogdrop_sched::p(); let mut rng = Rng::new(0x279_05_e0d);
    let mut out = Vec::new();
    for _ in 0..10_000 {
        if out.len() == 64 { break; }
        let x = rng.below(255).max(N::from(1u64));
        let (mut r, mut t) = (vec![p, x], vec![N::ZERO, N::from(1u64)]);
        while !r.last().unwrap().is_zero() {
            let j = r.len(); let q = r[j - 2] / r[j - 1];
            r.push(r[j - 2] - q * r[j - 1]); t.push(t[j - 2] + q * t[j - 1]);
        }
        let mut d = rng.below(256) % p; let mut w = N::ZERO;
        for j in 1..r.len() - 1 {
            let e = d / r[j]; let q = r[j - 1] / r[j];
            let last = j + 2 == r.len();
            if last && r[j] == N::from(1u64) && (sz.0..=sz.1).contains(&t[j].bit_len())
                && (228..=257).contains(&(r[j].bit_len() + t[j].bit_len()))
                && q.bit_len() <= crate::point_add::payload::KE
                && e.bit_len() <= crate::point_add::payload::KE
                && r[j - 1].bit_len() <= crate::point_add::payload::KD {
                assert_eq!(p, r[j - 1] * t[j] + t[j - 1]);
                out.push(LateEndCase { t: t[j], previous_r: r[j - 1], d, w });
                break;
            }
            d -= e * r[j];
            w = q.wrapping_mul(t[j]).wrapping_add(!w.wrapping_add(e.wrapping_mul(t[j])));
        }
    }
    assert_eq!(out.len(), 64, "unchanged domain coverage, no outcome-based selection");
    out
}

#[test]
#[ignore = "ROOT exact same-binary prepass and fresh native admission required"]
fn lowq695_actual_end_payload_both_parities_state_phase_v1() {
    use crate::point_add::frogdrop_col::{ColScr, traversal_end_pl};
    let (_, b0, last) = crate::point_add::pointadd_frogdrop::col_pars(
        &crate::point_add::frogdrop_sched::from_text(crate::point_add::pointadd_frogdrop::SCHED_FROGDROP));
    let cp = b0.unwrap(); assert_eq!(cp.m, 28);
    let mut b = default_builder(); let f = trace_frame(&mut b); let mut fd = fd_of(&f);
    let pl = crate::point_add::pointadd_frogdrop::pl_col(&f.dirty, &fd, &f.pool);
    let carve = |sx: &[QubitId]| ColScr::carve(&f.pool, sx, &f.dirty, cp.kp, cp.qb, cp.tail);
    let r = rec(&mut b, |b| traversal_end_pl(b, &mut fd, Some(&cp), &last, &carve, Some(&pl)));
    let forward = default_emitted(&mut b, &r, false);
    let reverse = default_emitted(&mut b, &r, true);
    assert!(forward.iter().chain(&reverse).any(|op| op.q_target == f.sx[7] && matches!(op.kind, K::Hmr)),
        "controlled replay really uses the returned SX7 AND temporary");
    let invoice = late_invoice("actual_end_with_payload", &forward, &reverse);
    let cs = late_end_cases(last.sz); let p = crate::point_add::frogdrop_sched::p();
    let mut input = vec![0u64; 695]; let mut want = input.clone();
    let mut populations = [0usize; 3];
    for (lane, c) in cs.iter().enumerate() {
        let cnt = [1u64, 2, 3, 4, 1, 126, 127, 64][lane % 8];
        let previous_t = p - c.previous_r * c.t;
        let (z, x, y) = if cnt & 1 == 0 {
            populations[2] += 1;
            (previous_t, N::from(1u64), c.previous_r)
        } else {
            populations[usize::from(cnt != 1)] += 1;
            (c.t, c.previous_r, N::from(1u64))
        };
        let cut = 279 - x.bit_len().max(y.bit_len());
        assert!(z.bit_len() <= cut);
        put(&mut input, &f.ring[..cut], lane, z);
        put(&mut input, &top(&f.ring[cut..]), lane, y);
        put(&mut input, &f.q, lane, x); put(&mut input, &fd.cnt, lane, N::from(cnt));
        put(&mut input, &f.sy, lane, N::from(y.bit_len() as u64));
        input[f.ph.0 as usize] |= 1 << lane;
        let payload = if cnt == 1 { trace_payload_off(c.d, c.w, c.previous_r.bit_len()) }
                      else { trace_payload_pre(c.d, c.w, c.t.bit_len()) };
        set_trace_payload(&mut input, &f.dirty, lane, &payload);
        put(&mut want, &top(&f.ring), lane, N::from(1u64));
        put(&mut want, &f.ring[..256], lane, c.t);
        put(&mut want, &f.q, lane, c.previous_r); put(&mut want, &fd.cnt, lane, N::from(cnt));
        put(&mut want, &fd.sy, lane, N::from(1u64)); want[f.ph.0 as usize] |= 1 << lane;
        let wpost = c.w.wrapping_add(c.d.wrapping_mul(c.t));
        let next = c.previous_r.wrapping_mul(c.t).wrapping_add(!wpost);
        set_trace_payload(&mut want, &f.dirty, lane, &trace_payload_off(N::ZERO, next, 1));
    }
    assert_eq!(populations, [16, 16, 32], "cnt1 A0, older A0, B0");
    assert_eq!(input[f.q[120].0 as usize], 0, "Q120 strictly zero at actual end entry");
    assert_eq!(input[f.sx[7].0 as usize], 0, "SX7 replay helper globally zero at entry");
    let mut apps = 0; let mut coeff = 0;
    let got = apply(&forward, &input, &mut apps, &mut coeff);
    assert_eq!(got[f.q[120].0 as usize], 0, "Q120 returned after actual end and payload");
    assert_eq!(got[f.sx[7].0 as usize], 0, "SX7 replay helper globally returned");
    assert_eq!(got[f.sx[5].0 as usize], 0, "SX5 end extension globally returned");
    trace_assert_all(&got, &want, &f, &fd, "actual_end_payload_both_parities");
    assert_eq!(apply(&reverse, &got, &mut apps, &mut coeff), input, "actual end all695 FI including payload259");
    assert_eq!(apps, invoice);
    eprintln!("LOWQ695_ACTUAL_END_PAYLOAD_NATIVE_PASS packs=1 lanes=64 populations={populations:?} helperSX7_strict0=true Q120_strict0=true all695=true payload259_numeric=true physical_applications={apps} independent_hmr_measurement_events_times64={coeff} eager_rows=true whole=false");
}

fn late_assert_closed_conditions(ops: &[Op], label: &str) {
    let mut depth = 0usize;
    for op in ops {
        match op.kind {
            K::PushCondition => depth += 1,
            K::PopCondition => depth = depth.checked_sub(1).expect("condition stack underflow"),
            _ => {},
        }
    }
    assert_eq!(depth, 0, "{label}: native apply_iter seam must have an empty condition stack");
}

#[test]
#[ignore = "ROOT exact same-binary prepass and fresh native admission required"]
fn lowq695_first2_deferred_payload_caller_state_phase_v1() {
    use crate::point_add::frogdrop_col::{ColScr, column_pl};
    use crate::circuit::analyze_ops;
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};
    assert!(std::env::var_os("FD_NODEFER").is_none());
    let (cols, _, _) = crate::point_add::pointadd_frogdrop::col_pars(
        &crate::point_add::frogdrop_sched::from_text(crate::point_add::pointadd_frogdrop::SCHED_FROGDROP));
    assert_eq!(cols.len(), 203);
    let mut b = default_builder(); let f = trace_frame(&mut b); let mut fd = fd_of(&f);
    b.deferred_forward();
    b.x(f.ring[278]); b.x(fd.sy[0]);
    for cp in &cols[..2] {
        let sc = ColScr::carve_col(&f.pool, &fd.sx, &f.dirty, cp.kp, cp.qb, cp.tail, cp.sz.1 > 255);
        let pl = crate::point_add::pointadd_frogdrop::pl_col(&f.dirty, &fd, &f.pool);
        let r = rec(&mut b, |b| column_pl(b, &mut fd, cp, &sc, Some(&pl)));
        b.play(&r, false);
    }
    b.flush_global(); assert_eq!(b.pending_count(), 0);
    let mut ops = std::mem::take(&mut b.ops); let boundary = ops.len();
    let end_fd = late_fd_copy(&fd);
    let row_masks = b.deferred_tape_rows(); let box_masks = b.deferred_tape_boxes();
    assert!(row_masks > 0, "fixture must exercise real deferred row masks");
    // Scheme G replaces the legacy middle that records tag501/tag502 boxes.
    // The active first2 path has deferred rows, and zero whole-erasure boxes.
    assert_eq!(box_masks, 0, "active Scheme G first2 has no legacy erasure boxes");
    b.deferred_suspend();
    // Production T2 keeps the changed payload as arbitrary dirty DATA and
    // mirrors the Euclid rows without replaying the payload. This short
    // diagnostic omits the intervening pl_convert; its dirty DATA is the
    // actual computed two-column payload, never an injected model value.
    b.deferred_inverse();
    for cp in cols[..2].iter().rev() {
        assert!(!cp.nomap);
        std::mem::swap(&mut fd.sy, &mut fd.sx);
        let start = (fd.sy.clone(), fd.sx.clone());
        let sc = ColScr::carve_col(&f.pool, &fd.sx, &f.dirty, cp.kp, cp.qb, cp.tail, cp.sz.1 > 255);
        let r = rec(&mut b, |b| column_pl(b, &mut fd, cp, &sc, None));
        b.play(&r, true);
        fd.sy = start.0; fd.sx = start.1;
    }
    b.x(f.ring[278]); b.x(fd.sy[0]);
    b.deferred_finish();
    assert_eq!((b.deferred_tape_rows(), b.deferred_tape_boxes()), (0, 0));
    b.flush_global(); assert_eq!(b.pending_count(), 0);
    let inverse = std::mem::take(&mut b.ops);
    late_assert_closed_conditions(&ops, "deferred forward prefix");
    late_assert_closed_conditions(&inverse, "deferred inverse prefix");
    let invoice = late_invoice("first2_deferred_payload_nonpayload_pair", &ops, &inverse);
    ops.extend(inverse);
    let (aq, nb, _, _) = analyze_ops(ops.iter());
    assert!(aq <= 695 && nb > 0);
    eprintln!("LOWQ695_DEFERRED_METADATA rows={row_masks} boxes={box_masks} classical_bits={nb} single_native_Simulator=true single_XOF=true seam_conditions_closed=true fixture_created=false native_started=false");
    let (input, x, dys) = trace_inputs(&f);
    let shot = crate::point_add::frogdrop_sched::shot(x, crate::point_add::frogdrop_sched::L0);
    assert!(shot.recs[..2].iter().all(|r| matches!(r.kind, crate::point_add::frogdrop_sched::Kind::Hr)));
    let (rr, tt, ds, ws) = trace_model(x, &dys);
    let want_f = trace_expected(&f, &end_fd, 3, &rr, &tt, &ds, &ws);
    let mut want_i = input.clone();
    for &q in &f.dirty { want_i[q.0 as usize] = want_f[q.0 as usize]; }
    // One symbolic invocation retains the full classical masks and unpaid
    // forward phase until the actual mirrored inverse has corrected it.
    let (symbolic_final, coefficients) = symbolic(&ops, input.clone());
    assert_eq!(symbolic_final, want_i, "all695 full deferred pair with retained computed payload");
    let mut h = sha3::Shake256::default(); h.update(b"frogdrop-test"); let mut xof = h.finalize_xof();
    let mut sim = Simulator::new(695, (nb as usize).max(1), &mut xof);
    sim.qubits = input;
    sim.apply_iter(ops[..boundary].iter());
    trace_assert_all(&sim.qubits, &want_f, &f, &end_fd, "deferred_prefix2_forward");
    eprintln!("LOWQ695_DEFERRED_F_BOUNDARY all695=true payload259=true phase_pending={:016x} native_classical_reset=false rng_reset=false", sim.phase);
    sim.apply_iter(ops[boundary..].iter());
    trace_assert_all(&sim.qubits, &want_i, &f, &fd, "deferred_prefix2_inverse_no_payload");
    assert_eq!(sim.qubits, symbolic_final);
    assert_eq!(sim.phase, 0, "complete continuous native deferred phase correction");
    assert_eq!(invoice, 2 * ops.len() as u64);
    eprintln!("LOWQ695_FIRST2_DEFERRED_CALLER_NATIVE_PASS columns=2 lanes=64 all695=true payload259_numeric=true retained_payload=true full_symbolic_phase0=true continuous_native_classical_XOF_phase=true rows={row_masks} boxes={box_masks} physical_applications={invoice} independent_hmr_measurement_events_times64={coefficients} forward_payload_inverse_without_payload=true endpoint_flush=true whole=false");
}

#[path = "tests_lowq695_c27_actual.rs"]
mod actual_c27_native;

#[path = "tests_lowq695_k25_bank.rs"]
mod paid_bank_native;

#[path = "tests_lowq695_leading_park.rs"]
mod lowq695_leading_park_native;

#[path = "tests_lowq695_c79_payload.rs"]
mod actual_c79_payload_native;

#[path = "tests_lowq695_highz30_tc32.rs"]
mod highz30_tc32_native;

#[path = "tests_lowq695_leading_park_tc32.rs"]
mod leading_park_tc32_native;

#[path = "tests_lowq695_c41_c43_actual_native.rs"]
mod actual_c41_c43_native;

#[path = "tests_lowq695_q24_high.rs"]
mod q24_high_native;

#[path = "tests_lowq695_q24_park.rs"]
mod q24_park_native;

#[path = "tests_lowq695_q24_payload.rs"]
mod q24_payload_native;

#[path = "tests_lowq695_actual821_c114_native.rs"]
mod actual821_c114_native;
