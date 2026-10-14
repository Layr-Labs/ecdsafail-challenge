//! Fresh official696-derived695 C75 fixed genuine transition fixture. ROOT owns runtime.
//! Included as a child of payload so the exact private dig_scr_z carve can be inspected.
use super::*;
use crate::point_add::builder::{B, G};
use crate::point_add::frogdrop_col::{rec, ColPar, ColScr, Fd};
use crate::point_add::frogdrop_sched::N;
use crate::point_add::tests_frogdrop::{run, Rng};
use crate::circuit::{Op, OperationType as K, QubitId, NO_BIT};

const WIDTH: usize = 695;
const CAP: u64 = 100_000_000;

fn put(q: &mut [u64], reg: &[QubitId], lane: usize, value: N) {
    for (i, p) in reg.iter().enumerate() {
        q[p.0 as usize] = (q[p.0 as usize] & !(1u64 << lane)) | (u64::from(value.bit(i)) << lane);
    }
}
fn top(v: &[QubitId]) -> Vec<QubitId> { v.iter().rev().copied().collect() }
fn builder() -> B {
    assert!(std::env::var_os("LOWQ_EXACT_STREAM_PATH").is_none());
    for key in ["FD_POOL", "FD_DIGIT_IP", "FD_DIG_NE", "FD_DIG_ZPAD", "D2_DIGIT_STOP", "FD_OLDMID", "FD_NOMAPANDC"] {
        assert!(std::env::var_os(key).is_none(), "fixture binds default production: {key}");
    }
    B::new()
}
struct Frame { fd: Fd, pool: Vec<QubitId>, p: Vec<QubitId> }
fn frame(b: &mut B) -> Frame {
    let ring = b.alloc_n(279); let q = b.alloc_n(128);
    let cnt = q[121..].to_vec();
    let fd = Fd { ring, q, sy: b.alloc_n(8), sx: b.alloc_n(8), ph: b.alloc(), cnt };
    let pool = b.alloc_n(12); let p = b.alloc_n(NP);
    assert_eq!(b.width(), WIDTH as u64);
    Frame { fd, pool, p }
}
fn columns() -> (Vec<ColPar>, ColPar, ColPar) {
    let (cols, end, last) = crate::point_add::pointadd_frogdrop::col_pars(
        &crate::point_add::frogdrop_sched::from_text(crate::point_add::pointadd_frogdrop::SCHED_FROGDROP));
    assert_eq!(cols.len(), 203);
    for cp in &cols { assert_eq!((cp.n, cp.k, cp.h, cp.kp, cp.qb), (279, 20, 22, 24, 23)); }
    (cols, end.unwrap(), last)
}
fn sc(f: &Frame, cp: &ColPar) -> ColScr {
    ColScr::carve_col(&f.pool, &f.fd.sx, &f.p, cp.kp, cp.qb, cp.tail, cp.sz.1 > 255)
}
fn fd_copy(fd: &Fd) -> Fd {
    Fd { ring: fd.ring.clone(), q: fd.q.clone(), sy: fd.sy.clone(), sx: fd.sx.clone(), ph: fd.ph, cnt: fd.cnt.clone() }
}
fn plc(f: &Frame) -> PlCol {
    crate::point_add::pointadd_frogdrop::pl_col(&f.p, &f.fd, &f.pool)
}
fn emitted(b: &mut B, r: &[G], inverse: bool) -> Vec<Op> {
    assert!(b.ops.is_empty()); b.play(r, inverse); b.flush_global(); std::mem::take(&mut b.ops)
}
fn invoice(label: &str, forward: &[Op], reverse: &[Op], pairs: u64) -> u64 {
    let n = pairs * 2 * (forward.len() + reverse.len()) as u64;
    eprintln!("POOL12_INVOICE label={label} N_F={} N_I={} pairs={pairs} physical_applications={n} cap={CAP} native_started=false width={WIDTH}", forward.len(), reverse.len());
    assert!(n <= CAP, "exact complete fixture invoice before case generation/simulation"); n
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


// Appended to copied independent phase helpers in a separate test-only leaf.
include!("firstht_dl_cases695.rs");

fn hx(v: &str) -> N { N::from_str_radix(v, 16).unwrap() }
fn set_bit(q: &mut [u64], p: QubitId, lane: usize, value: bool) {
    q[p.0 as usize] = (q[p.0 as usize] & !(1u64 << lane)) | (u64::from(value) << lane);
}
fn coordinate(q: &mut [u64], fd: &Fd, lane: usize, z: N, x: N, y: N, ph: bool, cnt: u64) {
    let cut = fd.ring.len() - x.bit_len().max(y.bit_len());
    assert!(z.bit_len() <= cut && x.bit_len() <= 128 && y.bit_len() <= 255);
    put(q, &fd.ring, lane, z);
    put(q, &top(&fd.ring[cut..]), lane, y);
    put(q, &fd.q, lane, x);
    // cnt aliases Q121..127 only on done shots. Active X occupies all128
    // lanes and must never be truncated by a synthetic zero-counter write.
    if cnt != 0 {
        assert!(x.bit_len() <= 121 && cnt < 128);
        put(q, &fd.cnt, lane, N::from(cnt));
    }
    let expected_q = x | (N::from(cnt) << 121);
    let mut actual_q = N::ZERO;
    for (i, &p) in fd.q.iter().enumerate() {
        if (q[p.0 as usize] >> lane) & 1 == 1 { actual_q |= N::from(1u64) << i; }
    }
    assert_eq!(actual_q, expected_q, "all128 Q bits preserved; zero cnt is a label, not a write");
    put(q, &fd.sy, lane, N::from(y.bit_len() as u64));
    set_bit(q, fd.ph, lane, ph);
}

#[test]
#[ignore = "ROOT fresh compile/count/native admission; fixed C75 firstHT/DQ/DL witnesses and full numeric column"]
fn lowq695_firstht_dl_fullcolumn_state_phase_v1() {
    use crate::point_add::frogdrop_col::{column_upto, probe_gated};
    use crate::point_add::frogdrop::{Cut, msb_probe_cut_range};
    let (cols, _, _) = columns(); let cp = &cols[75];
    assert!(cp.hr && cp.ht && cp.sw && cp.psw && cp.dl && cp.dq && !cp.dn);
    assert!(!crate::point_add::midg::G_IP5);
    let mut records = Vec::new(); let mut total = 0;
    // These independent complete recipes are invoiced before parsing any
    // fixed case, symbolic phase evaluation or native simulation. Payload
    // is an unrestricted dirty passenger; none of these calls runs payload
    // hooks. Actual full payload geometry and deferred caller remain owed.
    for mode in 0..4 {
        let mut b = builder(); let f = frame(&mut b); let sc = sc(&f, cp); let mut fd = fd_copy(&f.fd);
        assert!(!b.global_cancel && b.allow_booth, "eager recipe / default Booth scope");
        assert_eq!(sc.g, f.fd.sx[4]); assert_eq!(sc.u2[4], sc.sw);
        assert!(!sc.u2.contains(&sc.g));
        let r = if mode == 0 {
            // Literal historical broken firstHT subrecipe, the deliberately bad
            // zero-entry loan. A negative control keeps the source failure
            // observable instead of only testing the repaired result.
            let rev = top(&f.fd.ring);
            let cut = Cut { v: sc.sz.clone(), a: (cp.n - cp.h) as isize, neg: true };
            let pt = rec(&mut b, |b| msb_probe_cut_range(b, &rev, &cut,
                cp.n - cp.h - cp.sz.1, cp.n - cp.h - cp.sz.0, 0, (cp.xw + 1).min(cp.n),
                &sc.u2, sc.f, &[], &[], sc.bq, sc.cmpc, &f.p));
            let pu = rec(&mut b, |b| probe_gated(b, &f.fd.q, 0, 128, &f.fd.sy,
                &[(sc.g, false)], &[sc.f], sc.bq, &[sc.cmpc], &f.p));
            rec(&mut b, |b| { b.play(&pt, false); b.play(&pu, false); b.play(&pt, true); })
        } else {
            // upto1 includes stages1/2; upto7 includes the actual stage8 DL
            // carry/probe cleanup; upto99 includes the complete map/tail.
            let upto = [0, 1, 7, 99][mode];
            rec(&mut b, |b| column_upto(b, &mut fd, cp, &sc, upto, None))
        };
        let forward = emitted(&mut b, &r, false); let reverse = emitted(&mut b, &r, true);
        let label = ["literal_old_firstHT_negative", "actual_C75_stages1_2", "actual_C75_through_stage8_DL", "actual_C75_full_HT_DQ_map"][mode];
        total += invoice(label, &forward, &reverse, 1);
        records.push((mode, f, sc, fd, forward, reverse));
    }
    assert!(total <= CAP, "combined fresh fixture cap before the first model/native call");
    let mut apps = 0; let mut coeff = 0;
    for (mode, f, sc, fd, forward, reverse) in records {
        let mut input = vec![0; WIDTH]; let mut rng = Rng::new(0x695_01_7500 + mode as u64);
        for &q in &f.p { input[q.0 as usize] = rng.next(); }
        let mut want = input.clone(); let mut bad = 0usize; let mut dl = 0usize; let mut dq = 0usize; let mut first = 0usize;
        for lane in 0..64 {
            let index = if mode == 0 { lane % 16 } else { lane };
            let (zh, xh, yh, ph, sw, nzh, nxh, nyh, nph, nsw, ncnt) = CASES[index];
            let (z, x, y) = (hx(zh), hx(xh), hx(yh));
            assert!((cp.sz.0..=cp.sz.1).contains(&z.bit_len()));
            assert!((cp.sy.0..=cp.sy.1).contains(&y.bit_len()));
            coordinate(&mut input, &f.fd, lane, z, x, y, ph, 0);
            set_bit(&mut input, sc.sw, lane, sw);
            if mode == 0 {
                // Every first16 case is a genuine current Sw (PH0). This
                // is its post-wide-swap entry to the defective T recipe.
                assert!(!ph && !sw && z.bit_len() <= 128 && z.bit_len() <= y.bit_len());
                coordinate(&mut input, &f.fd, lane, z, y, x, false, 0);
                put(&mut input, &f.fd.sy, lane, N::from(y.bit_len() as u64));
                put(&mut input, &sc.sz, lane, N::from(z.bit_len() as u64));
                set_bit(&mut input, sc.sw, lane, true);
                if x.bit(15) { bad += 1; }
            }
            if index >= 32 && index < 48 { dq += 1; }
            if index >= 16 && index < 32 { first += 1; }
            if index >= 48 && index < 56 { dl += 1; }
        }
        want.clone_from(&input);
        for lane in 0..64 {
            let index = if mode == 0 { lane % 16 } else { lane };
            let (zh, xh, yh, ph, _sw, nzh, nxh, nyh, nph, nsw, ncnt) = CASES[index];
            let (z, x, y) = (hx(zh), hx(xh), hx(yh));
            if mode == 0 {
                let expected_sy = y.bit_len() ^ if x.bit(15) { 128 } else { 0 };
                put(&mut want, &f.fd.sy, lane, N::from(expected_sy as u64));
            } else if mode == 1 {
                let skip = (16..48).contains(&index);
                let (mx, my) = if skip { (x, y) } else { (y, x) };
                coordinate(&mut want, &f.fd, lane, z, mx, my, ph, 0);
                put(&mut want, &f.fd.sy, lane, N::from(mx.bit_len() as u64));
                put(&mut want, &sc.sz, lane, N::from(z.bit_len() as u64));
                set_bit(&mut want, sc.sw, lane, index < 16);
            } else if mode == 2 {
                let delayed = (48..56).contains(&index);
                let tn = if delayed {
                    // p = r_prev*t_j + r_j*t_prev from the exact walk.
                    let p = crate::point_add::frogdrop_sched::p();
                    assert_eq!((p-z*x) % y, N::ZERO);
                    ((p-z*x)/y/z)*y+x
                } else { N::ZERO };
                let (mx, my) = match index {
                    0..=15 => (x, y),
                    16..=31 | 60..=63 => (hx(nyh), hx(nxh)),
                    32..=47 => (y, x),
                    48..=55 => (tn & ((N::from(1u64) << 128) - N::from(1u64)), y),
                    56..=59 => (hx(nyh), y),
                    _ => unreachable!(),
                };
                coordinate(&mut want, &f.fd, lane, z, mx, my, ph, 0);
                put(&mut want, &f.fd.sy, lane, N::from(my.bit_len() as u64));
                set_bit(&mut want, sc.sw, lane, index < 16 || (48..56).contains(&index));
                if (48..56).contains(&index) {
                    // Actual DL stage8 leaves T_next's high bits at
                    // ring[l], above Z, and only low128 in Q.
                    assert!(tn.bit_len() <= cp.xw.min(cp.n / 2));
                    for l in 128..cp.xw.min(cp.n / 2) {
                        set_bit(&mut want, f.fd.ring[l], lane, tn.bit(l));
                        set_bit(&mut want, f.fd.ring[cp.n - 1 - l], lane, false);
                    }
                    put(&mut want, &f.fd.q, lane, tn & ((N::from(1u64) << 128) - N::from(1u64)));
                }
            } else {
                coordinate(&mut want, &fd, lane, hx(nzh), hx(nxh), hx(nyh), nph, ncnt);
                put(&mut want, &fd.sx, lane, N::ZERO);
                set_bit(&mut want, sc.sw, lane, nsw);
            }
        }
        if mode == 0 { assert_eq!(bad, 32, "negative control fires on8/16 fixed Sw witnesses times4"); }
        else { assert_eq!((first, dq, dl), (16, 16, 8)); }
        let got = apply(&forward, &input, &mut apps, &mut coeff);
        assert_eq!(got, want, "mode={mode}: all695, exact fixed C75 walk state/scratch and unrestricted payload passengers");
        assert_eq!(apply(&reverse, &got, &mut apps, &mut coeff), input, "mode={mode}: complete FI");
    }
    assert_eq!(apps, total);
    eprintln!("LOWQ695_FIRSTHT_DL_NATIVE_PASS recipes=4 lanes=256 firstHT=16 DQ=16 DL=8 negative_triggered=32 eager=true defaultBooth=true payload_hooks=false all695=true applications={apps} independent_outcome_checks={coeff} whole=false");
}
