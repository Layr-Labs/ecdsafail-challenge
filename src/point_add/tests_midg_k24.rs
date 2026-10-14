//! Finite K24 stage1_v test on the N276, 693-wire candidate frame.
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
    bank: Vec<QubitId>, dirty: Vec<QubitId>, act: QubitId, c0: QubitId,
    separate_gt0: Option<QubitId>,
}
fn frame(b: &mut B, cp: &ColPar, reference: bool) -> Frame {
    assert_eq!((cp.n, cp.nq, cp.k, cp.h), (276, 128, 17, 19));
    let ring = b.alloc_n(276);
    let q = b.alloc_n(128);
    let _sy = b.alloc_n(8);
    let sx = b.alloc_n(8);
    let _ph = b.alloc();
    let pool = b.alloc_n(13);
    let dirty = b.alloc_n(259);
    assert_eq!(b.width(), 693);
    let mut sz = pool[..8].to_vec();
    if cp.sz.1 > 255 { sz.push(pool[8]); }
    let mt = (cp.n - (cp.sz.0 + cp.h) + 1).min(cp.nq.max(cp.xw) + 1);
    let kmax = 258usize.saturating_sub(cp.sz.0 + cp.sy.0).min(super::mid2::QF).min(mt);
    let lsb = if cp.dn { cp.sy.1.max(28) } else { cp.sy.1 };
    let end = cp.nq - if cp.dn { super::pointadd_frogdrop::CNTB } else { 0 };
    let start = lsb.max(cp.sy.1.min(cp.nq) + kmax);
    let bank = if start < end { q[start..end].to_vec() } else { vec![] };
    let separate_gt0 = if reference { Some(b.alloc()) } else { None };
    assert_eq!(b.width(), if reference { 694 } else { 693 });
    Frame { ring, sx, sz, bank, dirty, act: pool[12], c0: pool[11], separate_gt0 }
}
fn layout(f: &Frame, helpers: usize) -> S1 {
    assert!(helpers <= f.bank.len());
    let bank = f.bank[..helpers].to_vec();
    let mut r = f.ring[..19].to_vec();
    r.extend([f.sx[1], f.sx[2], f.sx[3], f.sx[4], f.sx[5]]);
    r.push(f.ring[275]);
    let gt = vec![f.separate_gt0.unwrap_or(f.sx[0])];
    S1 { r, f: f.sx[0], zero: f.ring[18], sgn: f.sx[0], gt,
        anc: bank.iter().skip(1).copied().collect(), andc: bank.clone(),
        chain: bank, dirty: f.dirty.clone() }
}
#[derive(Clone, Copy, Debug)]
enum Form { Window, Remainder, V }
fn recipe(b: &mut B, f: &Frame, cp: &ColPar, helpers: usize, form: Form) -> Vec<G> {
    let s = layout(f, helpers);
    let fv = stage1_v(b, &f.ring[252..276], &f.ring[18..19 + TC], &f.sz, cp.sz, &s, f.act, true);
    let fr = stage1_v(b, &f.ring[252..276], &f.ring[18..19 + TC], &f.sz, cp.sz, &s, f.act, false);
    match form {
        Form::Window => rec(b, |b| { b.x(f.ring[275]); b.play(&fv, false); b.x(f.ring[275]); }),
        Form::Remainder => rec(b, |b| { b.x(f.ring[275]); b.play(&fr, false); b.x(f.ring[275]); }),
        Form::V => rec(b, |b| { b.x(f.ring[275]); b.play(&fv, false); b.play(&fr, true); b.x(f.ring[275]); }),
    }
}
fn protection(b: &mut B, f: &Frame, cp: &ColPar) -> Vec<G> {
    let dest = (0..17 + 2 + TC).chain(276 - 24..276).collect();
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
        let dest = (0..17 + 2 + TC).chain(276 - 24..276);
        for i in dest {
            for lane in 0..64 {
                let sz = get(&input, &f.sz, lane).as_limbs()[0] as usize;
                let want = (input[f.ring[(i + sz) % 276].0 as usize] >> lane) & 1;
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
            assert_eq!((cp.n, cp.nq, cp.k, cp.h), (276, 128, 17, 19), "column {i}");
            assert!(cp.sz.0 >= 57 && cp.sz.1 <= 256, "column {i} sz {:?}", cp.sz);
        }
    }
    assert!(active > 0);
    eprintln!("D1_K24_ACTIVE_COLUMNS count={active}");
}

#[test]
fn d2_sz_gate_roundtrip() {
    let mut b = builder();
    let sz = b.alloc_n(8);
    let sy = b.alloc_n(8);
    let c0 = b.alloc();
    let pzero = b.alloc();
    let x128 = b.alloc();
    let out = b.alloc();
    let dirty = b.alloc_n(259);
    let v = sz[..6].to_vec();
    let vg = rec(&mut b, |b| {
        super::frogdrop::reg_add_into(b, &v, &sy[..6], &[], c0);
        for i in 0..6 {
            if (38 >> i) & 1 == 1 { super::modp_frogdrop::inc_dirty_free(b, &v[i..], &dirty); }
        }
    });
    let query = rec(&mut b, |b| {
        b.play(&vg, false);
        super::frogdrop_col::ge_cd(b, &v, 19, out, &[c0, pzero, x128], &dirty);
        b.play(&vg, true);
    });
    let forward = emitted(&mut b, &query, false);
    let inverse = emitted(&mut b, &query, true);
    let mut rng = Rng::new(0xd2_697_001);
    let mut input = vec![0u64; b.width() as usize];
    for &p in &dirty { input[p.0 as usize] = rng.next(); }
    input[out.0 as usize] = rng.next();
    for lane in 0..64 {
        put(&mut input, &sz, lane, N::from((rng.next() % 256) as u64));
        put(&mut input, &sy, lane, N::from((rng.next() % 256) as u64));
    }
    let f = run(&forward, input.len(), &|q| *q = input.clone());
    assert_eq!(f.phase, 0);
    for lane in 0..64 {
        let zs = get(&input, &sz, lane).as_limbs()[0] as usize;
        let ys = get(&input, &sy, lane).as_limbs()[0] as usize;
        let expected = ((zs + ys + 38) % 64 >= 19) as u64;
        assert_eq!((f.q[out.0 as usize] >> lane) & 1,
                   ((input[out.0 as usize] >> lane) & 1) ^ expected);
    }
    let mut want = input.clone();
    want[out.0 as usize] = f.q[out.0 as usize];
    assert_eq!(f.q, want, "only predicate target changes; dirty passengers return");
    let back = run(&inverse, input.len(), &|q| *q = f.q.clone());
    assert_eq!(back.phase, 0);
    assert_eq!(back.q, input);
    let (sym, _) = symbolic(&forward, input);
    assert_eq!(sym, want, "all independent HMR phase coefficients cancel");
}

#[test]
fn d2_k24_empty_bank_vform() {
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    let cp = &cols[85];
    let mut b = builder();
    let f = frame(&mut b, cp, false);
    assert!(f.bank.is_empty(), "binding switch-column Q bank is not a clean helper");
    let r = recipe(&mut b, &f, cp, 0, Form::V);
    let forward = emitted(&mut b, &r, false);
    let inverse = emitted(&mut b, &r, true);
    let mut apps = 0;
    let mut coeff = 0;
    for mode in 0..3 {
        let input = input(&f, cp, mode, 0xd2_697_100 + mode as u64);
        let want = expected(&f, &input, Form::V, false);
        let got = apply(&forward, &input, &mut apps, &mut coeff);
        assert_eq!(got, want, "mode {mode} forward");
        let back = apply(&inverse, &got, &mut apps, &mut coeff);
        assert_eq!(back, input, "mode {mode} inverse");
    }
    eprintln!("D2_K24_EMPTY_BANK_PASS width={} applications={apps} coefficients={coeff}", b.width());
}

#[test]
fn d4_n278_k24_forward_inverse_dirty_passengers() {
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    for &ci in &[10usize, 85] {
        let cp = &cols[ci];
        let mut b = builder();
        let f = frame(&mut b, cp, false);
        let s = layout(&f, f.bank.len());
        assert_eq!(s.r.len(), 25);
        assert_eq!(&s.r[..19], &f.ring[..19]);
        assert_eq!(&s.r[19..24], &f.sx[1..6]);
        assert_eq!(s.r[24], f.ring[275]);
        assert_eq!(s.zero, f.ring[18]);
        let r = recipe(&mut b, &f, cp, f.bank.len(), Form::V);
        let forward = emitted(&mut b, &r, false);
        let inverse = emitted(&mut b, &r, true);
        let mut apps = 0;
        let mut coeff = 0;
        for mode in 0..4 {
            let input = input(&f, cp, mode, 0xd4_695_100 + 17 * ci as u64 + mode as u64);
            let want = expected(&f, &input, Form::V, false);
            let got = apply(&forward, &input, &mut apps, &mut coeff);
            assert_eq!(got, want, "col {ci} mode {mode} forward and zero scratch");
            assert_eq!(apply(&inverse, &got, &mut apps, &mut coeff), input,
                       "col {ci} mode {mode} inverse, dirty passengers, zero phase");
        }
    }
}

#[test]
fn d4b_borrowed_sy_rotation_forward_inverse_dirty_phase() {
    let mut b = builder();
    let mut cycle = b.alloc_n(135);
    let sy = b.alloc_n(8);
    cycle.push(sy[7]);
    let temp = b.alloc();
    let dirty = b.alloc_n(259);
    let normal = super::midg::borrowed_sy_normal(&mut b, &sy, &dirty);
    let rotate = super::midg::borrowed_sy_rotate(&mut b, &cycle, &sy, temp, &dirty);
    b.play(&normal, false);
    b.play(&rotate, false);
    let forward_end = b.ops.len();
    b.play(&rotate, true);
    b.play(&normal, false);
    let mut rng = Rng::new(0xd4b_128_007);
    let mut input = vec![0u64; b.width() as usize];
    for &q in cycle[..135].iter().chain(dirty.iter()) { input[q.0 as usize] = rng.next(); }
    let mut sizes = vec![];
    for shot in 0..64 {
        let size = match shot % 8 { 0 => 1, 1 => 127, 2 => 128, _ => 1 + (rng.next() as usize % 128) };
        sizes.push(size);
        put(&mut input, &sy, shot, N::from(size as u64));
    }
    let forward = run(&b.ops[..forward_end], input.len(), &|q| *q = input.clone());
    assert_eq!(forward.phase, 0, "forward phase");
    assert_eq!(forward.q[temp.0 as usize], 0, "rotation temp returns");
    for &q in &dirty { assert_eq!(forward.q[q.0 as usize], input[q.0 as usize], "dirty passenger q{}", q.0); }
    for shot in 0..64 {
        let syv = sizes[shot];
        for i in 0..cycle.len() {
            let src = (i + syv) % cycle.len();
            let want = if src == cycle.len() - 1 { 0 } else { (input[cycle[src].0 as usize] >> shot) & 1 };
            let got = (forward.q[cycle[i].0 as usize] >> shot) & 1;
            assert_eq!(got, want, "shot {shot} sy {syv} cycle lane {i}");
        }
        for &q in &sy[..7] {
            assert_eq!((forward.q[q.0 as usize] >> shot) & 1, (input[q.0 as usize] >> shot) & 1);
        }
    }
    let inverse = run(&b.ops[forward_end..], input.len(), &|q| *q = forward.q.clone());
    assert_eq!(inverse.phase, 0, "inverse phase");
    assert_eq!(inverse.q, input, "arbitrary cycle data and dirty passengers restore");
    eprintln!("D4B_BORROWED_SY_ROTATION_PASS shots=64 cycle={} dirty={} forward_ops={} inverse_ops={}",
        cycle.len(), dirty.len(), forward_end, b.ops.len() - forward_end);
}

#[test]
fn d5_virtual_zero_csub_empty_bank_forward_inverse_dirty_phase() {
    let mut old = builder();
    let t = old.alloc_n(24);
    let s = old.alloc_n(23);
    let c0 = old.alloc();
    let out = old.alloc();
    let zero = old.alloc();
    let dirty = old.alloc_n(259);
    let mut full_s = s.clone();
    full_s.push(zero);
    old.begin();
    super::frogdrop::cmp_csub_carries(&mut old, &t, &full_s, c0, out, &[]);
    let old_gate = old.end();
    let old_fwd = emitted(&mut old, &old_gate, false);

    let mut new = builder();
    let t2 = new.alloc_n(24);
    let s2 = new.alloc_n(23);
    let c02 = new.alloc();
    let out2 = new.alloc();
    let zero2 = new.alloc();
    let dirty2 = new.alloc_n(259);
    assert_eq!((&t, &s, c0, out, zero, &dirty), (&t2, &s2, c02, out2, zero2, &dirty2));
    new.begin();
    super::frogdrop::cmp_csub_carries_vz(&mut new, &t2, &s2, c02, out2, &[]);
    let new_gate = new.end();
    let new_fwd = emitted(&mut new, &new_gate, false);
    let new_inv = emitted(&mut new, &new_gate, true);
    let mut rng = Rng::new(0xd5_694_001);
    let mut input = vec![0u64; new.width() as usize];
    for &q in t.iter().chain(s.iter()).chain(dirty.iter()) { input[q.0 as usize] = rng.next(); }
    input[c0.0 as usize] = rng.next();
    let old_result = run(&old_fwd, input.len(), &|q| *q = input.clone());
    let new_result = run(&new_fwd, input.len(), &|q| *q = input.clone());
    assert_eq!(new_result.phase, 0);
    assert_eq!(new_result.q, old_result.q, "virtual zero agrees on arbitrary data and dirty passengers");
    let back = run(&new_inv, input.len(), &|q| *q = new_result.q.clone());
    assert_eq!(back.phase, 0);
    assert_eq!(back.q, input, "inverse restores data, scratch and passengers");
}

#[test]
fn d6_virtual_high_one_zero_csub_forward_inverse_dirty_phase() {
    let mut old = builder();
    let t = old.alloc_n(24);
    let low = old.alloc_n(22);
    let one = old.alloc();
    let zero = old.alloc();
    let c0 = old.alloc();
    let out = old.alloc();
    let dirty = old.alloc_n(259);
    let full = low.iter().copied().chain([one, zero]).collect::<Vec<_>>();
    let gate = rec(&mut old, |b| super::frogdrop::cmp_csub_carries(b, &t, &full, c0, out, &[]));
    let reference = emitted(&mut old, &gate, false);

    let mut new = builder();
    let t2 = new.alloc_n(24);
    let low2 = new.alloc_n(22);
    let one2 = new.alloc();
    let zero2 = new.alloc();
    let c02 = new.alloc();
    let out2 = new.alloc();
    let dirty2 = new.alloc_n(259);
    assert_eq!((&t, &low, one, zero, c0, out, &dirty),
               (&t2, &low2, one2, zero2, c02, out2, &dirty2));
    let gate2 = rec(&mut new, |b| super::frogdrop::cmp_csub_carries_vh10(b, &t2, &low2, c02, out2, &dirty2));
    let forward = emitted(&mut new, &gate2, false);
    let inverse = emitted(&mut new, &gate2, true);
    let mut rng = Rng::new(0xd6_693_100);
    for mode in 0..4 {
        let mut input = vec![0u64; new.width() as usize];
        input[one.0 as usize] = !0;
        if mode & 1 != 0 {
            for &q in t.iter().chain(low.iter()).chain(dirty.iter()) { input[q.0 as usize] = rng.next(); }
        } else {
            for &q in t.iter().chain(low.iter()) { input[q.0 as usize] = rng.next(); }
        }
        if mode & 2 != 0 { input[c0.0 as usize] = rng.next(); }
        let want = run(&reference, input.len(), &|q| *q = input.clone());
        let got = run(&forward, input.len(), &|q| *q = input.clone());
        assert_eq!(got.phase, 0, "mode {mode} forward phase");
        assert_eq!(got.q, want.q, "mode {mode} virtual high constants");
        let back = run(&inverse, input.len(), &|q| *q = got.q.clone());
        assert_eq!(back.phase, 0, "mode {mode} inverse phase");
        assert_eq!(back.q, input, "mode {mode} inverse restores scratch/passengers");
    }
}

#[test]
fn d6_n276_k24_vform_leading_one_forward_inverse_dirty_phase() {
    let build = |reference: bool| {
        let mut b = builder();
        let ring = b.alloc_n(276);
        let _q = b.alloc_n(128);
        let _sy = b.alloc_n(8);
        let sx = b.alloc_n(8);
        let _ph = b.alloc();
        let pool = b.alloc_n(13);
        let dirty = b.alloc_n(259);
        let separate = if reference { Some(b.alloc()) } else { None };
        assert_eq!(b.width(), if reference { 694 } else { 693 });
        let mut r = ring[..19].to_vec();
        r.extend(&sx[1..6]);
        r.push(separate.unwrap_or(ring[275]));
        let s = S1 { r, f: sx[0], zero: ring[18], sgn: sx[0], gt: vec![sx[0]],
                     anc: vec![], andc: vec![], chain: vec![], dirty: dirty.clone() };
        let fv = stage1_v(&mut b, &ring[252..276], &ring[18..19 + TC], &pool[..8], (57, 256), &s, pool[12], true);
        let fr = stage1_v(&mut b, &ring[252..276], &ring[18..19 + TC], &pool[..8], (57, 256), &s, pool[12], false);
        let v = rec(&mut b, |b| {
            if !reference { b.x(ring[275]); }
            b.play(&fv, false);
            b.play(&fr, true);
            if !reference { b.x(ring[275]); }
        });
        let forward = emitted(&mut b, &v, false);
        let inverse = emitted(&mut b, &v, true);
        (ring, sx, pool, dirty, forward, inverse)
    };
    let (ring, sx, pool, dirty, forward, inverse) = build(false);
    let (_, _, _, _, reference, _) = build(true);
    let mut rng = Rng::new(0xd6_693_24);
    for mode in 0..4 {
        let mut input = vec![0u64; 693];
        for &q in ring.iter().chain(sx.iter()).chain(pool.iter()).chain(dirty.iter()) {
            input[q.0 as usize] = rng.next();
        }
        input[sx[0].0 as usize] = 0;
        let active = [!0u64, 0, 0xa55a_c33c_0ff0_f00f, 0x00ff_0f0f_3333_5555][mode];
        input[pool[12].0 as usize] = active;
        for &q in ring[..19].iter().chain(sx[1..6].iter()) { input[q.0 as usize] &= !active; }
        input[ring[275].0 as usize] |= active;
        for lane in 0..64 {
            let size = [57usize, 128, 133, 230, 231, 232, 255, 256][lane % 8];
            put(&mut input, &pool[..8], lane, N::from(size as u64));
        }
        let mut ri = input.clone(); ri.push(0);
        let want = run(&reference, ri.len(), &|q| *q = ri.clone());
        let got = run(&forward, input.len(), &|q| *q = input.clone());
        assert_eq!(got.phase, 0, "mode {mode} forward phase");
        assert_eq!(&want.q[..693], &got.q, "mode {mode} virtual leading one V form");
        assert_eq!(want.q[693], 0, "mode {mode} reference extra returned");
        let back = run(&inverse, input.len(), &|q| *q = got.q.clone());
        assert_eq!(back.phase, 0, "mode {mode} inverse phase");
        assert_eq!(back.q, input, "mode {mode} dirty passengers and scratch returned");
    }
}

#[test]
fn d6_delayed_hr_sy7_pad_forward_inverse_dirty_phase() {
    let mut b = builder();
    let t = b.alloc_n(132);
    let slow = b.alloc_n(130);
    let sy = b.alloc_n(8);
    let high_zero = b.alloc();
    let s: Vec<QubitId> = slow.iter().copied().chain([sy[7], high_zero]).collect();
    let ctrl = b.alloc();
    let g = b.alloc();
    let c0 = b.alloc();
    let dirty = b.alloc_n(32);
    let norm = super::midg::borrowed_sy_normal(&mut b, &sy, &dirty);
    let body = rec(&mut b, |b| {
        b.play(&norm, false);
        super::payload::trans_one(b, &t, &s, 0, false, vec![(ctrl, false)], None,
                                  g, c0, &[], &dirty);
        b.play(&norm, true);
    });
    let forward = emitted(&mut b, &body, false);
    let inverse = emitted(&mut b, &body, true);
    let mut rng = Rng::new(0xd6_693_130);
    let mut input = vec![0u64; b.width() as usize];
    for &q in &dirty { input[q.0 as usize] = rng.next(); }
    let mask = (N::from(1u64) << 132) - N::from(1u64);
    let mut want = input.clone();
    for lane in 0..64 {
        let size = [1usize, 96, 127, 128, 0, 129, 64, 128][lane % 8];
        let active = (1..=128).contains(&size) && lane % 3 != 0;
        let tv = N::from(rng.next()) | (N::from(rng.next()) << 64)
            | (N::from(rng.next() & 15) << 128);
        let sv = N::from(rng.next()) | (N::from(rng.next()) << 64)
            | (N::from(rng.next() & 3) << 128);
        put(&mut input, &t, lane, tv);
        put(&mut input, &slow, lane, sv);
        put(&mut input, &sy, lane, N::from(size as u64));
        if active { input[ctrl.0 as usize] |= 1u64 << lane; }
        put(&mut want, &t, lane, (tv + if active { sv } else { N::ZERO }) & mask);
        put(&mut want, &slow, lane, sv);
        put(&mut want, &sy, lane, N::from(size as u64));
        if active { want[ctrl.0 as usize] |= 1u64 << lane; }
    }
    let got = run(&forward, input.len(), &|q| *q = input.clone());
    assert_eq!(got.phase, 0, "normalized pad forward phase");
    assert_eq!(got.q, want, "normalized pad target, size, source, dirty and scratch");
    let back = run(&inverse, input.len(), &|q| *q = got.q.clone());
    assert_eq!(back.phase, 0, "normalized pad inverse phase");
    assert_eq!(back.q, input, "normalized pad inverse restores arbitrary data");
}

#[test]
fn d6_q18_preposition_forward_inverse_boundary_dirty_phase() {
    let mut b = builder();
    let cycle = b.alloc_n(136);
    let sy = b.alloc_n(8);
    let act = b.alloc();
    let dirty = b.alloc_n(259);
    let q18 = cycle[135];
    let move18 = super::midg::preposition_qk(&mut b, &cycle, &sy, q18, 18, act, (1, 128), &dirty);
    let fwd = emitted(&mut b, &move18, false);
    let inv = emitted(&mut b, &move18, true);
    let mut rng = Rng::new(0xd6_693_018);
    let mut input = vec![0u64; b.width() as usize];
    for &q in cycle.iter().chain(dirty.iter()) { input[q.0 as usize] = rng.next(); }
    input[act.0 as usize] = 0x6e7b_59d3_2c5a_a55a;
    let mut sizes = vec![];
    for shot in 0..64 {
        let size = match shot % 8 { 0 => 1, 1 => 116, 2 => 117, 3 => 118, 4 => 127, 5 => 128,
                                      _ => 1 + (rng.next() as usize % 128) };
        sizes.push(size);
        put(&mut input, &sy, shot, N::from(size as u64));
        let idx = size + 18;
        if (input[act.0 as usize] >> shot) & 1 != 0 && idx < cycle.len() && idx != 135 {
            input[cycle[idx].0 as usize] &= !(1u64 << shot);
        }
    }
    let mut want = input.clone();
    for shot in 0..64 {
        let idx = sizes[shot] + 18;
        if (input[act.0 as usize] >> shot) & 1 == 0 || idx >= cycle.len() || idx == 135 { continue; }
        let bit = (input[q18.0 as usize] >> shot) & 1;
        want[q18.0 as usize] &= !(1u64 << shot);
        want[cycle[idx].0 as usize] |= bit << shot;
    }
    let got = run(&fwd, input.len(), &|q| *q = input.clone());
    assert_eq!(got.phase, 0);
    assert_eq!(got.q, want, "size indexed q18 move preserves arbitrary cycle data and dirty lanes");
    let back = run(&inv, input.len(), &|q| *q = got.q.clone());
    assert_eq!(back.phase, 0);
    assert_eq!(back.q, input, "inverse restores q18, Q cycle, scratch and passengers");
}

#[test]
fn d5_q19_preposition_forward_inverse_boundary_dirty_phase() {
    let mut b = builder();
    let cycle = b.alloc_n(136);
    let sy = b.alloc_n(8);
    let act = b.alloc();
    let dirty = b.alloc_n(259);
    let q19 = cycle[135];
    let move19 = super::midg::preposition_q19(&mut b, &cycle, &sy, q19, act, (1, 128), &dirty);
    let fwd = emitted(&mut b, &move19, false);
    let inv = emitted(&mut b, &move19, true);
    let mut rng = Rng::new(0xd5_694_019);
    let mut input = vec![0u64; b.width() as usize];
    for &q in cycle.iter().chain(dirty.iter()) { input[q.0 as usize] = rng.next(); }
    input[act.0 as usize] = 0x6e7b_59d3_2c5a_a55a;
    let mut sizes = vec![];
    for shot in 0..64 {
        let size = match shot % 8 { 0 => 1, 1 => 115, 2 => 116, 3 => 117, 4 => 127, 5 => 128,
                                      _ => 1 + (rng.next() as usize % 128) };
        sizes.push(size);
        put(&mut input, &sy, shot, N::from(size as u64));
        let idx = size + 19;
        if (input[act.0 as usize] >> shot) & 1 != 0 && idx < cycle.len() && idx != 135 {
            input[cycle[idx].0 as usize] &= !(1u64 << shot);
        }
    }
    let mut want = input.clone();
    for shot in 0..64 {
        let idx = sizes[shot] + 19;
        if (input[act.0 as usize] >> shot) & 1 == 0 || idx >= cycle.len() || idx == 135 { continue; }
        let bit = (input[q19.0 as usize] >> shot) & 1;
        want[q19.0 as usize] &= !(1u64 << shot);
        want[cycle[idx].0 as usize] |= bit << shot;
    }
    let got = run(&fwd, input.len(), &|q| *q = input.clone());
    assert_eq!(got.phase, 0);
    assert_eq!(got.q, want, "size indexed q19 move preserves arbitrary cycle data and dirty lanes");
    let back = run(&inv, input.len(), &|q| *q = got.q.clone());
    assert_eq!(back.phase, 0);
    assert_eq!(back.q, input, "inverse restores q19, Q cycle, scratch and passengers");
}

#[test]
fn d5_n277_k24_forward_inverse_dirty_passengers() {
    d4_n278_k24_forward_inverse_dirty_passengers();
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
    let mut q: Vec<_> = (0..if f.separate_gt0.is_some() { 694 } else { 693 }).map(|_| rng.next()).collect();
    let act = [0, u64::MAX, 0x00ff_0f0f_3333_5555, 0xa55a_c33c_0ff0_f00f][mode];
    q[f.act.0 as usize] = act;
    for &p in f.ring[..19].iter().chain([f.sx[1], f.sx[2], f.sx[3], f.sx[4], f.sx[5]].iter()) {
        q[p.0 as usize] &= !act;
    }
    q[f.ring[275].0 as usize] |= act;
    q[f.sx[0].0 as usize] = 0;
    // These are parked quotient passengers during the V-form in the full column.
    q[f.sx[2].0 as usize] = 0;
    q[f.sx[3].0 as usize] = 0;
    q[f.sx[4].0 as usize] = 0;
    q[f.sx[5].0 as usize] = 0;
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
        put(&mut q, &f.ring[252..276], lane, zh);
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
                let p = f.ring[18 + i];
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
        let divisor = get(input, &f.ring[252..276], lane) | N::from(1u64);
        let u = (257 - sz).saturating_sub(TC);
        let reciprocal = ((N::from(1u64) << (256 - (sz - 24))) - N::from(1u64)) / divisor;
        let t = N::from(1u64) << (257 - sz);
        let delta = t - (((reciprocal >> u) + N::from(1u64)) << u);
        if !matches!(form, Form::Remainder) {
            let mut w = N::ZERO;
            for i in 0..=TC {
                let pos = 257isize - sz as isize - i as isize;
                if pos >= 0 && ((input[f.ring[18 + i].0 as usize] >> lane) & 1) != 0 {
                    w |= N::from(1u64) << pos as usize;
                }
            }
            let w = if inverse_v { (w + t - delta) & (t - N::from(1u64)) }
                    else { (w + delta) & (t - N::from(1u64)) };
            for i in 1..=TC {
                let pos = 257isize - sz as isize - i as isize;
                if pos >= 0 {
                    let p = f.ring[18 + i];
                    q[p.0 as usize] = (q[p.0 as usize] & !(1 << lane))
                        | (u64::from(w.bit(pos as usize)) << lane);
                }
            }
        }
        if !matches!(form, Form::V) {
            let mut remainder = (N::from(1u64) << 23) - N::from(1u64);
            let mut phys = f.ring[..19].to_vec(); phys.extend([f.sx[1], f.sx[2], f.sx[3], f.sx[4], f.sx[5], f.ring[275]]);
            for _ in 0..TC {
                remainder = (remainder * N::from(2u64) + N::from(1u64)) % divisor;
                let p = phys.pop().unwrap(); phys.insert(0, p);
            }
            put(&mut q, &phys, lane, remainder);
            q[f.ring[275].0 as usize] ^= 1u64 << lane;
        }
    }
    q
}
fn compare_reference(reference: &[u64], actual: &[u64]) {
    assert_eq!(actual.len(), 693);
    assert_eq!(reference.len(), 694);
    assert_eq!(&reference[..693], actual, "all693 reference comparison");
    assert_eq!(reference[693], 0, "explicit test-only gt0 returns0");
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
    eprintln!("K24_APPLICATION_INVOICE physical_applications={invoice} cap=100000000 candidate_width=693 reference_width=694 native_started=false same_binary=true profiles=3 caller_profiles=2");
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
        eprintln!("F1_PAIR_K24_DIFF_PASS col={ci} width=693 old_F_T={oft} new_F_T={nft} old_I_T={oit} new_I_T={nit} packs=1 lanes=64 independent_phase_coefficients={coeff} all_wires=true");
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
            for i in 0..693 { assert_eq!(a[i] & act, want[i] & act, "numeric active q{i} range={range:?} mode={mode} form={form:?}"); }
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
    eprintln!("K24_RETURNED_F_NATIVE_PASS candidate_width=693 reference_width=694 packs={packs} lanes={} physical_applications={apps} independent_hmr_coefficients={coefficients} all693=true false_R_window_DATA=true caller_fv_fr=true profiles=3 caller_profiles=2 whole=false", 64 * packs);
}
