//! Scheme G unit tests (midg.rs).

use super::builder::B;
use super::frogdrop_sched::N;
use super::midg::*;
use super::tests_frogdrop::{run, Rng};
use crate::circuit::QubitId;

fn put(words: &mut [u64], qs: &[QubitId], shot: usize, val: &N) {
    for (i, &q) in qs.iter().enumerate() {
        if val.bit(i) { words[q.0 as usize] |= 1 << shot } else { words[q.0 as usize] &= !(1 << shot) }
    }
}
fn get(words: &[u64], qs: &[QubitId], shot: usize) -> N {
    let mut v = N::ZERO;
    for (i, &q) in qs.iter().enumerate() {
        if (words[q.0 as usize] >> shot) & 1 == 1 { v |= N::from(1u64) << i; }
    }
    v
}
fn pval() -> N {
    (N::from(1u64) << 256) - (N::from(1u64) << 32) - N::from(977u64)
}
fn bl(v: &N) -> usize { v.bit_len() }

#[test]
fn b7b_masked_add_dirty_forward_inverse() {
    for &sub in &[false, true] {
        let mut b = B::new();
        let t = b.alloc_n(129);
        let q = b.alloc_n(129);
        let sy = b.alloc_n(8);
        let ctl = b.alloc();
        let c0 = b.alloc();
        let mask = b.alloc();
        let pre = b.alloc_n(5);
        let dirty = b.alloc_n(12);
        b.begin();
        b7b_masked_add_y(&mut b, &t, &q, &sy, 1, 128, ctl, c0, mask, &pre, &dirty, sub);
        let rec = b.end();
        b.play(&rec, false);
        eprintln!("B7B_MASKED_ADD sub={sub} T={} ops={}", b.tof, rec.len());
        let fwd = b.ops.len();
        b.play(&rec, true);
        let mut rng = Rng::new(0xb7b695 ^ (sub as u64));
        let mut cases = vec![];
        for shot in 0..64 {
            let ys = [1usize, 2, 7, 31, 63, 116, 127, 128][shot % 8];
            let y = rng.below(ys - 1) | (N::from(1u64) << (ys - 1));
            let qv = y | (rng.below(129 - ys - 1) << (ys + 1));
            let tv = rng.below(129);
            let av = shot % 3 != 0;
            let dv = rng.below(12);
            cases.push((ys, y, qv, tv, av, dv));
        }
        let init = |w: &mut Vec<u64>| {
            for (shot, &(ys, _, qv, tv, av, dv)) in cases.iter().enumerate() {
                put(w, &t, shot, &tv);
                put(w, &q, shot, &qv);
                put(w, &sy, shot, &N::from(ys));
                put(w, &dirty, shot, &dv);
                if av { w[ctl.0 as usize] |= 1 << shot; }
            }
        };
        let s = run(&b.ops[..fwd], b.width() as usize, &init);
        for (shot, &(ys, y, qv, tv, av, dv)) in cases.iter().enumerate() {
            let low = (N::from(1u64) << (ys + 1)) - N::from(1u64);
            let x = tv & low;
            let want = if !av { tv } else if sub { (tv & !low) | x.wrapping_sub(y) & low }
                       else { (tv & !low) | (x + y) & low };
            assert_eq!(get(&s.q, &t, shot), want, "t shot {shot} sy {ys} sub {sub}");
            assert_eq!(get(&s.q, &q, shot), qv);
            assert_eq!(get(&s.q, &sy, shot), N::from(ys));
            assert_eq!(get(&s.q, &dirty, shot), dv);
            for &x in &[c0, mask] { assert_eq!((s.q[x.0 as usize] >> shot) & 1, 0); }
            for &x in &pre { assert_eq!((s.q[x.0 as usize] >> shot) & 1, 0); }
        }
        assert_eq!(s.phase, 0);
        let back = run(&b.ops, b.width() as usize, &init);
        assert_eq!(back.phase, 0);
        for (shot, &(_, _, qv, tv, av, dv)) in cases.iter().enumerate() {
            assert_eq!(get(&back.q, &t, shot), tv);
            assert_eq!(get(&back.q, &q, shot), qv);
            assert_eq!(get(&back.q, &dirty, shot), dv);
            assert_eq!((back.q[ctl.0 as usize] >> shot) & 1, av as u64);
        }
    }
}

/// B7B: a parked quotient is arbitrary source garbage above sy+1. The
/// comparator must restore it, write only through sy, and invert exactly.
#[test]
fn b7b_masked_y_ripple_dirty_forward_inverse() {
    for &cmpl in &[false, true] {
        let mut b = B::new();
        let t = b.alloc_n(129);
        let q = b.alloc_n(129);
        let sy = b.alloc_n(8);
        let ak = b.alloc();
        let c = b.alloc();
        let c0 = b.alloc();
        let g = b.alloc();
        let pre = b.alloc_n(7);
        let dirty = b.alloc_n(12);
        b.begin();
        b7b_masked_cmp_y(&mut b, &t, &q, &sy, 1, 128, ak, c, c0, g, &pre, &dirty, cmpl);
        let rec = b.end();
        b.play(&rec, false);
        eprintln!("B7B_MASKED_KERNEL cmpl={cmpl} T={} ops={}", b.tof, rec.len());
        let fwd = b.ops.len();
        b.play(&rec, true);
        let mut rng = Rng::new(0xb7b690 ^ (cmpl as u64));
        let mut cases = vec![];
        for shot in 0..64 {
            let ys = [1usize, 2, 7, 31, 63, 116, 127, 128][shot % 8];
            let y = rng.below(ys - 1) | (N::from(1u64) << (ys - 1));
            let qv = y | (rng.below(129 - ys - 1) << (ys + 1));
            let tv = rng.below(129);
            let av = shot % 3 != 0;
            let dv = rng.below(12);
            cases.push((ys, y, qv, tv, av, dv));
        }
        let init = |w: &mut Vec<u64>| {
            for (shot, &(ys, _, qv, tv, av, dv)) in cases.iter().enumerate() {
                put(w, &t, shot, &tv);
                put(w, &q, shot, &qv);
                put(w, &sy, shot, &N::from(ys));
                put(w, &dirty, shot, &dv);
                if av { w[ak.0 as usize] |= 1 << shot; }
            }
        };
        let s = run(&b.ops[..fwd], b.width() as usize, &init);
        for (shot, &(ys, y, qv, tv, av, dv)) in cases.iter().enumerate() {
            let low = (N::from(1u64) << (ys + 1)) - N::from(1u64);
            let x = tv & low;
            let yes = av && if cmpl { x >= y } else { x + y <= low };
            let want = if !yes { tv } else if cmpl { (tv & !low) | (x - y) }
                       else { (tv & !low) | (x + y) };
            assert_eq!(get(&s.q, &t, shot), want,
                "t shot {shot} sy {ys} cmpl {cmpl} x={x} y={y} ak={av} c={}",
                (s.q[c.0 as usize] >> shot) & 1);
            assert_eq!(get(&s.q, &q, shot), qv, "q shot {shot}");
            assert_eq!(get(&s.q, &sy, shot), N::from(ys));
            assert_eq!(get(&s.q, &dirty, shot), dv);
            assert_eq!((s.q[c.0 as usize] >> shot) & 1, yes as u64);
            for &x in &[c0, g] { assert_eq!((s.q[x.0 as usize] >> shot) & 1, 0); }
            for &x in &pre { assert_eq!((s.q[x.0 as usize] >> shot) & 1, 0); }
        }
        assert_eq!(s.phase, 0);
        let back = run(&b.ops, b.width() as usize, &init);
        assert_eq!(back.phase, 0);
        for (shot, &(ys, _, qv, tv, av, dv)) in cases.iter().enumerate() {
            assert_eq!(get(&back.q, &t, shot), tv);
            assert_eq!(get(&back.q, &q, shot), qv);
            assert_eq!(get(&back.q, &sy, shot), N::from(ys));
            assert_eq!(get(&back.q, &dirty, shot), dv);
            assert_eq!((back.q[ak.0 as usize] >> shot) & 1, av as u64);
            for &x in &[c, c0, g] { assert_eq!((back.q[x.0 as usize] >> shot) & 1, 0); }
        }
    }
}

#[test]
fn b7b_v_bit_top_and_lower_forward_inverse() {
    let mut b = B::new();
    let t = b.alloc_n(129);
    let q = b.alloc_n(129);
    let sy = b.alloc_n(8);
    let ak = b.alloc();
    let top = b.alloc();
    let c = b.alloc();
    let c0 = b.alloc();
    let pre = b.alloc_n(7);
    let dirty = b.alloc_n(12);
    b.begin();
    b7b_v_bit(&mut b, &t, &q, &sy, 1, 128, ak, top, c, c0, &pre, &dirty);
    let rec = b.end();
    b.play(&rec, false);
    eprintln!("B7B_V_BIT T={} ops={}", b.tof, rec.len());
    let fwd = b.ops.len();
    b.play(&rec, true);
    let mut rng = Rng::new(0xb7b691);
    let mut cases = vec![];
    for shot in 0..64 {
        let ys = [1usize, 2, 7, 31, 63, 116, 127, 128][shot % 8];
        let y = rng.below(ys - 1) | (N::from(1u64) << (ys - 1));
        let low = (N::from(1u64) << ys) - N::from(1u64);
        let root_top = shot % 2 == 0;
        let av = shot % 5 != 0;
        let high = rng.below(128 - ys) << (ys + 1);
        let tv = (rng.below(ys) & low) | high |
                 (if root_top { N::ZERO } else { N::from(1u64) << ys });
        let dv = rng.below(12);
        cases.push((ys, y, tv, root_top, av, dv));
    }
    let init = |w: &mut Vec<u64>| {
        for (shot, &(ys, y, tv, root_top, av, dv)) in cases.iter().enumerate() {
            put(w, &t, shot, &tv);
            put(w, &q, shot, &y);
            put(w, &sy, shot, &N::from(ys));
            put(w, &dirty, shot, &dv);
            if root_top { w[top.0 as usize] |= 1 << shot; }
            if av { w[ak.0 as usize] |= 1 << shot; }
        }
    };
    let f = run(&b.ops[..fwd], b.width() as usize, &init);
    for (shot, &(ys, y, tv, root_top, av, dv)) in cases.iter().enumerate() {
        let low = (N::from(1u64) << ys) - N::from(1u64);
        let x = tv & low;
        let bit = av && x + y <= low;
        let want = if !av { tv } else { (tv & !(low | (N::from(1u64) << ys))) |
            (if bit { x + y } else { x }) |
            (if bit { N::from(1u64) << ys } else { N::ZERO }) };
        assert_eq!(get(&f.q, &t, shot), want,
                   "shot={shot} sy={ys} top={root_top} x={x} y={y} bit={bit}");
        assert_eq!(get(&f.q, &q, shot), y);
        assert_eq!(get(&f.q, &sy, shot), N::from(ys));
        assert_eq!(get(&f.q, &dirty, shot), dv);
        assert_eq!((f.q[c.0 as usize] >> shot) & 1, 0);
        assert_eq!((f.q[c0.0 as usize] >> shot) & 1, 0);
        for &p in &pre { assert_eq!((f.q[p.0 as usize] >> shot) & 1, 0); }
    }
    assert_eq!(f.phase, 0);
    let back = run(&b.ops, b.width() as usize, &init);
    assert_eq!(back.phase, 0);
    for (shot, &(ys, y, tv, root_top, av, dv)) in cases.iter().enumerate() {
        assert_eq!(get(&back.q, &t, shot), tv);
        assert_eq!(get(&back.q, &q, shot), y);
        assert_eq!(get(&back.q, &sy, shot), N::from(ys));
        assert_eq!(get(&back.q, &dirty, shot), dv);
        assert_eq!((back.q[top.0 as usize] >> shot) & 1, root_top as u64);
        assert_eq!((back.q[ak.0 as usize] >> shot) & 1, av as u64);
    }
}

#[test]
fn b7b_q0_move_sy128_dirty_forward_inverse() {
    let mut b = B::new();
    let q = b.alloc_n(128);
    let x128 = b.alloc();
    let sy = b.alloc_n(8);
    let slot = b.alloc();
    let act = b.alloc();
    let pre = b.alloc_n(3);
    let dirty = b.alloc_n(12);
    b.begin();
    b7b_move_q0(&mut b, &q, x128, &sy, 1, 128, slot, act, &pre, &dirty);
    let rec = b.end();
    b.play(&rec, false);
    eprintln!("B7B_Q0_MOVE T={} ops={}", b.tof, rec.len());
    let fwd = b.ops.len();
    b.play(&rec, true);
    let mut rng = Rng::new(0xb7b692);
    let mut cases = vec![];
    for shot in 0..64 {
        let ys = [1usize, 2, 7, 31, 63, 116, 127, 128][shot % 8];
        let mut qv = rng.below(129);
        if shot % 2 == 0 { qv |= N::from(1u64) << ys; }
        else { qv &= !(N::from(1u64) << ys); }
        cases.push((ys, qv, shot % 3 != 0, rng.below(12)));
    }
    let init = |w: &mut Vec<u64>| {
        for (shot, &(ys, qv, av, dv)) in cases.iter().enumerate() {
            put(w, &q, shot, &qv);
            if qv.bit(128) { w[x128.0 as usize] |= 1 << shot; }
            put(w, &sy, shot, &N::from(ys));
            put(w, &dirty, shot, &dv);
            if av { w[act.0 as usize] |= 1 << shot; }
        }
    };
    let f = run(&b.ops[..fwd], b.width() as usize, &init);
    for (shot, &(ys, qv, av, dv)) in cases.iter().enumerate() {
        let bit = av && qv.bit(ys);
        let want = if av { qv & !(N::from(1u64) << ys) } else { qv };
        let got = get(&f.q, &q, shot) |
            (N::from((f.q[x128.0 as usize] >> shot) & 1) << 128);
        assert_eq!(got, want, "shot={shot} sy={ys}");
        assert_eq!((f.q[slot.0 as usize] >> shot) & 1, bit as u64);
        assert_eq!(get(&f.q, &sy, shot), N::from(ys));
        assert_eq!(get(&f.q, &dirty, shot), dv);
        for &p in &pre { assert_eq!((f.q[p.0 as usize] >> shot) & 1, 0); }
    }
    assert_eq!(f.phase, 0);
    let back = run(&b.ops, b.width() as usize, &init);
    assert_eq!(back.phase, 0);
    for (shot, &(ys, qv, av, dv)) in cases.iter().enumerate() {
        let got = get(&back.q, &q, shot) |
            (N::from((back.q[x128.0 as usize] >> shot) & 1) << 128);
        assert_eq!(got, qv);
        assert_eq!(get(&back.q, &sy, shot), N::from(ys));
        assert_eq!(get(&back.q, &dirty, shot), dv);
        assert_eq!((back.q[slot.0 as usize] >> shot) & 1, 0);
        assert_eq!((back.q[act.0 as usize] >> shot) & 1, av as u64);
    }
}

#[test]
fn b7b_masked_v_top_and_lower_dirty_forward_inverse() {
    let mut b = B::new();
    let t = b.alloc_n(129);
    let q = b.alloc_n(129);
    let sy = b.alloc_n(8);
    let ak = b.alloc();
    let top = b.alloc();
    let c = b.alloc();
    let c0 = b.alloc();
    let mask = b.alloc();
    let pre = b.alloc_n(5);
    let dirty = b.alloc_n(12);
    b.begin();
    b7b_masked_v_cmp(&mut b, &t, &q, &sy, 1, 128, ak, top, c, c0, mask, &pre, &dirty);
    let rec = b.end();
    b.play(&rec, false);
    eprintln!("B7B_MASKED_V T={} ops={}", b.tof, rec.len());
    let fwd = b.ops.len();
    b.play(&rec, true);
    let mut rng = Rng::new(0xb7b693);
    let mut cases = vec![];
    for shot in 0..64 {
        let ys = [1usize, 2, 7, 31, 63, 116, 127, 128][shot % 8];
        let y = rng.below(ys - 1) | (N::from(1u64) << (ys - 1));
        let qv = y | (rng.below(128 - ys) << (ys + 1));
        let root_top = shot % 2 == 0;
        let av = shot % 5 != 0;
        let high = rng.below(128 - ys) << (ys + 1);
        let tv = rng.below(ys) | high |
                 (if root_top { N::ZERO } else { N::from(1u64) << ys });
        cases.push((ys, y, qv, tv, root_top, av, rng.below(12)));
    }
    let init = |w: &mut Vec<u64>| {
        for (shot, &(ys, _, qv, tv, root_top, av, dv)) in cases.iter().enumerate() {
            put(w, &q, shot, &qv);
            put(w, &t, shot, &tv);
            put(w, &sy, shot, &N::from(ys));
            put(w, &dirty, shot, &dv);
            if root_top { w[top.0 as usize] |= 1 << shot; }
            if av { w[ak.0 as usize] |= 1 << shot; }
        }
    };
    let f = run(&b.ops[..fwd], b.width() as usize, &init);
    for (shot, &(ys, y, qv, tv, root_top, av, dv)) in cases.iter().enumerate() {
        let low = (N::from(1u64) << ys) - N::from(1u64);
        let x = tv & low;
        let bit = av && x + y <= low;
        let want = (tv & !low) | (if bit { x + y } else { x });
        assert_eq!(get(&f.q, &t, shot), want,
            "shot={shot} sy={ys} top={root_top} x={x} y={y} bit={bit}");
        assert_eq!(get(&f.q, &q, shot), qv);
        assert_eq!(get(&f.q, &sy, shot), N::from(ys));
        assert_eq!(get(&f.q, &dirty, shot), dv);
        assert_eq!((f.q[c.0 as usize] >> shot) & 1, bit as u64);
        for &z in &[c0, mask] { assert_eq!((f.q[z.0 as usize] >> shot) & 1, 0); }
        for &z in &pre { assert_eq!((f.q[z.0 as usize] >> shot) & 1, 0); }
    }
    assert_eq!(f.phase, 0);
    let back = run(&b.ops, b.width() as usize, &init);
    assert_eq!(back.phase, 0);
    for (shot, &(ys, _, qv, tv, root_top, av, dv)) in cases.iter().enumerate() {
        assert_eq!(get(&back.q, &t, shot), tv);
        assert_eq!(get(&back.q, &q, shot), qv);
        assert_eq!(get(&back.q, &sy, shot), N::from(ys));
        assert_eq!(get(&back.q, &dirty, shot), dv);
        assert_eq!((back.q[top.0 as usize] >> shot) & 1, root_top as u64);
        assert_eq!((back.q[ak.0 as usize] >> shot) & 1, av as u64);
    }
}

/// model: over(W) = [(W >> u) > (F >> u)], F = floor((2^(256-s) - 1) / Zh), Zh = (Z >> s) | 1, s = sz - K
fn over_model(w: &N, z: &N, k: usize) -> bool {
    let sz = bl(z);
    let s = sz - k;
    let zh = (*z >> s) | N::from(1u64);
    let f = ((N::from(1u64) << (256 - s)) - N::from(1u64)) / zh;
    assert_eq!(bl(&f), 257 - sz);
    let u = (257 - sz).saturating_sub(TC);
    (*w >> u) > (f >> u)
}

/// stage1_test on 64 shots per seed: Z with bl(Z) in [szlo, szhi], W near F (ties, +-1, +-small) or random below
/// 2^(258 - sz); lanes past W's position 0 hold junk that must survive.
fn run_stage1(seed: u64, szlo: usize, szhi: usize) {
    let k = 23usize;
    let mut b = B::new();
    let zh = b.alloc_n(k);
    let win = b.alloc_n(TC + 1);
    let sz = b.alloc_n(9);
    let s = S1 { r: b.alloc_n(k + 1), f: b.alloc(), zero: b.alloc(), sgn: b.alloc(), gt: b.alloc_n(3), anc: vec![], andc: b.alloc_n(10),
                 chain: b.alloc_n(9), dirty: b.alloc_n(48) };
    let t = b.alloc();
    let ctl = b.alloc();
    let temps = b.alloc_n(2);
    let fwd = stage1_fwd(&mut b, &zh, &win, &sz, (szlo, szhi), &s);
    stage1_test(&mut b, &fwd, &s, t, &[(ctl, false)], &temps, true);
    let mut rng = Rng::new(seed);
    struct Sh { z: N, w: N, sz: usize, junk: N, ctl: u64, d: N }
    let mut shots = vec![];
    for i in 0..64 {
        let szv = szlo + (rng.next() as usize) % (szhi - szlo + 1);
        let z = (rng.below(szv - 1)) | (N::from(1u64) << (szv - 1));
        let ss = szv - k;
        let zhv = (z >> ss) | N::from(1u64);
        let f = ((N::from(1u64) << (256 - ss)) - N::from(1u64)) / zhv;
        let u = (257 - szv).saturating_sub(TC);
        let mode = rng.next() % 6;
        let w = match mode {
            0 => f,
            1 => f + N::from(1u64),
            2 => if f > N::ZERO { f - N::from(1u64) } else { f },
            3 => ((f >> u) << u) + (rng.below(u.max(1)) % (N::from(1u64) << u)),
            4 => (((f >> u) + N::from(1u64)) << u) + (rng.below(u.max(1)) % (N::from(1u64) << u)),
            _ => rng.below(258 - szv),
        };
        let w = w % (N::from(1u64) << (258 - szv));
        shots.push(Sh { z, w, sz: szv, junk: rng.below(TC + 1), ctl: rng.next() & 1, d: rng.below(48) });
        let _ = i;
    }
    let sim = run(&b.ops, b.width() as usize, &|wd| {
        for (si, sh) in shots.iter().enumerate() {
            let ss = sh.sz - k;
            put(wd, &zh, si, &(sh.z >> ss));
            // window: index 0 = position 257 - sz, index 1 + j = position 256 - sz - j; below position 0: junk
            let mut wv = N::ZERO;
            for i in 0..=TC {
                let pos = 257isize - sh.sz as isize - i as isize;
                let bit = if pos >= 0 { sh.w.bit(pos as usize) } else { sh.junk.bit(i) };
                if bit { wv |= N::from(1u64) << i; }
            }
            put(wd, &win, si, &wv);
            put(wd, &sz, si, &N::from(sh.sz as u64));
            put(wd, &s.dirty, si, &sh.d);
            if sh.ctl == 1 { wd[ctl.0 as usize] |= 1 << si; }
        }
    });
    assert_eq!(sim.phase, 0, "phase garbage");
    let mut nover = 0;
    for (si, sh) in shots.iter().enumerate() {
        let want = sh.ctl == 1 && over_model(&sh.w, &sh.z, k);
        if want { nover += 1; }
        assert_eq!((sim.q[t.0 as usize] >> si) & 1 == 1, want, "shot {si}: t (sz {}, ctl {})", sh.sz, sh.ctl);
        assert_eq!(get(&sim.q, &zh, si), sh.z >> (sh.sz - k), "shot {si}: zh");
        assert_eq!(get(&sim.q, &s.dirty, si), sh.d, "shot {si}: dirty");
        assert_eq!(get(&sim.q, &sz, si), N::from(sh.sz as u64), "shot {si}: sz");
        let mut wv = N::ZERO;
        for i in 0..=TC {
            let pos = 257isize - sh.sz as isize - i as isize;
            let bit = if pos >= 0 { sh.w.bit(pos as usize) } else { sh.junk.bit(i) };
            if bit { wv |= N::from(1u64) << i; }
        }
        assert_eq!(get(&sim.q, &win, si), wv, "shot {si}: window");
        for &q in s.r.iter().chain([s.f, s.zero, s.sgn].iter()).chain(s.gt.iter()).chain(s.chain.iter()).chain(temps.iter()) {
            assert_eq!((sim.q[q.0 as usize] >> si) & 1, 0, "shot {si}: scratch q{}", q.0);
        }
    }
    eprintln!("stage1 seed {seed} sz [{szlo},{szhi}]: ok, {nover} over, {} T, {} ops", sim.tof, b.ops.len());
}

#[test]
fn midg_stage1_mid() {
    for seed in 1..4 { run_stage1(seed, 128, 200); }
}

#[test]
fn midg_stage1_early() {
    for seed in 11..14 { run_stage1(seed, 220, 256); }
}

#[test]
fn midg_stage1_p() {
    // the real dividend: p >> s must be all ones for s >= 33
    let p = pval();
    for s in 33..240usize { assert_eq!(p >> s, (N::from(1u64) << (256 - s)) - N::from(1u64)); }
}

// Round-two tests are deliberately ignored until ROOT admits a bounded test
// job. They use the upstream builder, unchanged stage1_v and simulator. This
// is a P-frame differential test on 699 wires, not a whole-column or online
// claim, and does not establish the caller's envelope by injecting a fixture.
use super::builder::G;
use super::frogdrop_col::ColPar;
use crate::circuit::{Op, OperationType as VK, NO_BIT};

struct VBankFrame {
    ring: Vec<QubitId>,
    q: Vec<QubitId>,
    sy: Vec<QubitId>,
    sx: Vec<QubitId>,
    ph: QubitId,
    pool: Vec<QubitId>,
    dirty: Vec<QubitId>,
    sz: Vec<QubitId>,
    bank: Vec<QubitId>,
    bank_lo: usize,
    bank_hi: usize,
}

fn vbank_builder() -> B {
    // Reject a stream destination before B::new can open it.
    assert!(std::env::var_os("LOWQ_EXACT_STREAM_PATH").is_none());
    B::new()
}

fn vbank_frame(b: &mut B, cp: &ColPar) -> VBankFrame {
    assert!(std::env::var_os("LOWQ_EXACT_STREAM_PATH").is_none());
    assert_eq!((cp.n, cp.nq, cp.k, cp.kp, cp.qb, cp.h), (282, 128, 23, 24, 24, 25));
    // The exact short Scheme-G geometry; the other 259 wires are dirty DATA.
    let ring = b.alloc_n(cp.n);
    let q = b.alloc_n(cp.nq);
    let sy = b.alloc_n(8);
    let sx = b.alloc_n(8);
    let ph = b.alloc();
    let pool = b.alloc_n(13);
    let dirty = b.alloc_n(259);
    assert_eq!(b.width(), 699);
    let mut sz = pool[..8].to_vec();
    if cp.sz.1 > 255 { sz.push(pool[8]); }
    let lsb = if cp.dn { cp.sy.1.max(28) } else { cp.sy.1 };
    let loan_end = cp.nq - if cp.dn { super::pointadd_frogdrop::CNTB } else { 0 };
    let mt = (cp.n - (cp.sz.0 + cp.h) + 1).min(cp.nq.max(cp.xw) + 1);
    let kmax = 258usize.saturating_sub(cp.sz.0 + cp.sy.0).min(super::mid2::QF).min(mt);
    let bank_lo = lsb.max(cp.sy.1.min(cp.nq) + kmax);
    let bank = if bank_lo < loan_end { q[bank_lo..loan_end].to_vec() } else { vec![] };
    assert!(!bank.iter().any(|p| ring.contains(p) || sy.contains(p) || sx.contains(p)
        || pool.contains(p) || dirty.contains(p) || *p == ph));
    VBankFrame { ring, q, sy, sx, ph, pool, dirty, sz, bank, bank_lo, bank_hi: loan_end }
}

fn vbank_s1(f: &VBankFrame, helpers: usize) -> S1 {
    assert!(helpers <= f.bank.len());
    let bank = f.bank[..helpers].to_vec();
    let mut gt = f.sx[2..4].to_vec();
    if let Some(&p) = bank.first() { gt.push(p); }
    S1 { r: f.ring[..24].to_vec(), f: f.sx[0], zero: f.ring[24], sgn: f.sx[0], gt,
         anc: bank.iter().skip(1).copied().collect(), andc: bank.clone(), chain: bank,
         dirty: f.dirty.clone() }
}

#[derive(Clone, Copy, Debug)]
enum VBankForm { Window, Remainder, V }

fn vbank_recipe(b: &mut B, f: &VBankFrame, cp: &ColPar, helpers: usize, form: VBankForm) -> Vec<G> {
    let s = vbank_s1(f, helpers);
    let zh = &f.ring[259..282];
    let win = &f.ring[24..49];
    let act = f.pool[12];
    match form {
        VBankForm::Window => stage1_v(b, zh, win, &f.sz, cp.sz, &s, act, true),
        VBankForm::Remainder => stage1_v(b, zh, win, &f.sz, cp.sz, &s, act, false),
        VBankForm::V => {
            let fv = stage1_v(b, zh, win, &f.sz, cp.sz, &s, act, true);
            let fr = stage1_v(b, zh, win, &f.sz, cp.sz, &s, act, false);
            b.begin();
            b.play(&fv, false);
            b.play(&fr, true);
            b.end()
        }
    }
}

fn vbank_entry(q: &[u64], donors: &[QubitId]) -> Result<(), (QubitId, u64)> {
    for &p in donors {
        if q[p.0 as usize] != 0 { return Err((p, q[p.0 as usize])); }
    }
    Ok(())
}

// One independent phase coefficient for every emitted HMR, even when the
// builder reuses classical bit 0. Zero coefficients cover every HMR outcome.
fn vbank_symbolic(ops: &[Op], mut q: Vec<u64>) -> (Vec<u64>, usize) {
    assert_eq!(q.len(), 699);
    let mut measured = std::collections::BTreeMap::new();
    let mut phase = Vec::<u64>::new();
    let mut constant_phase = 0u64;
    for op in ops {
        let t = op.q_target.0 as usize;
        let a = op.q_control1.0 as usize;
        let c = op.q_control2.0 as usize;
        match op.kind {
            VK::X => { assert_eq!(op.c_condition, NO_BIT); q[t] ^= u64::MAX; }
            VK::CX => { assert_eq!(op.c_condition, NO_BIT); q[t] ^= q[a]; }
            VK::CCX => { assert_eq!(op.c_condition, NO_BIT); q[t] ^= q[a] & q[c]; }
            VK::Swap => { assert_eq!(op.c_condition, NO_BIT); q.swap(a, t); }
            VK::Hmr => {
                assert_eq!(op.c_condition, NO_BIT);
                assert_ne!(op.c_target, NO_BIT);
                measured.insert(op.c_target, phase.len());
                phase.push(q[t]);
                q[t] = 0;
            }
            VK::CZ => {
                if op.c_condition == NO_BIT { constant_phase ^= q[a] & q[t]; }
                else { phase[measured[&op.c_condition]] ^= q[a] & q[t]; }
            }
            other => panic!("unexpected P-frame operation {other:?}"),
        }
    }
    assert_eq!(constant_phase, 0, "constant phase garbage");
    assert!(phase.iter().all(|&p| p == 0), "nonzero independent HMR coefficient");
    (q, phase.len())
}

fn vbank_input(f: &VBankFrame, cp: &ColPar, seed: u64, mode: usize) -> Vec<u64> {
    let mut rng = Rng::new(seed);
    let mut q: Vec<u64> = (0..699).map(|_| rng.next()).collect();
    let act = match mode {
        0 => 0,
        1 => u64::MAX,
        2 => 0x5555_5555_5555_5555,
        3 => 0x00ff_0f0f_3333_5555,
        _ => panic!("unknown control pattern"),
    };
    q[f.pool[12].0 as usize] = act;
    // Only the real scratch is initialized globally. Inactive R and win[0]
    // are arbitrary DATA. Other SX lanes and c0/pzero/x128 are parked DATA.
    for &p in &f.ring[..24] { q[p.0 as usize] &= !act; }
    q[f.ring[24].0 as usize] &= !act;
    q[f.ring[281].0 as usize] |= act;
    for p in [f.sx[0], f.sx[2], f.sx[3]] { q[p.0 as usize] = 0; }
    for &p in &f.bank { q[p.0 as usize] = 0; }
    for lane in 0..64 {
        let sv = match lane % 4 {
            0 => cp.sz.0,
            1 => cp.sz.1,
            _ => cp.sz.0 + rng.next() as usize % (cp.sz.1 - cp.sz.0 + 1),
        };
        put(&mut q, &f.sz, lane, &N::from(sv as u64));
    }
    // Non-donor Q, SY, PH, dirty and reserve wires are neither reset nor
    // filtered. This is not an all-Q-zero or Cartesian all-inputs claim.
    assert!(f.q.iter().filter(|p| !f.bank.contains(p)).any(|p| q[p.0 as usize] != 0));
    assert!(f.sy.iter().chain(f.dirty.iter()).any(|p| q[p.0 as usize] != 0));
    let _ = f.ph;
    vbank_entry(&q, &f.bank).unwrap();
    q
}

fn vbank_apply(ops: &[Op], input: &[u64], applications: &mut u64, coefficients: &mut u64) -> Vec<u64> {
    *applications += 2 * ops.len() as u64; // symbolic and upstream simulator
    assert!(*applications <= 100_000_000, "bounded P-kernel application cap");
    let (q, n) = vbank_symbolic(ops, input.to_vec());
    *coefficients += n as u64 * 64;
    let native = run(ops, 699, &|w| { *w = input.to_vec(); });
    assert_eq!(native.phase, 0, "upstream simulator phase");
    assert_eq!(native.q, q, "native/symbolic state mismatch");
    q
}

const V_BANK_COHORTS: [&[usize]; 2] = [
    &[0, 25, 29, 50, 90, 145, 202],
    &[1, 14, 27, 28, 31, 115, 170],
];

fn vbank_cohort_invoice(cols: &[ColPar], selected: &[usize]) -> u64 {
    let mut total = 0u64;
    for &ci in selected {
        let cp = &cols[ci];
        let mut geometry = vbank_builder();
        let frame = vbank_frame(&mut geometry, cp);
        let mut sizes: Vec<usize> = [0usize, 1, 2, 4, 8, 24, frame.bank.len()]
            .iter().map(|&n| n.min(frame.bank.len())).collect();
        sizes.sort_unstable();
        sizes.dedup();
        for helpers in sizes {
            let mut old = vbank_builder();
            let of = vbank_frame(&mut old, cp);
            let ore = vbank_recipe(&mut old, &of, cp, 0, VBankForm::V);
            let mut new = vbank_builder();
            let nf = vbank_frame(&mut new, cp);
            let nre = vbank_recipe(&mut new, &nf, cp, helpers, VBankForm::V);
            old.play(&ore, false);
            old.play(&ore, true);
            new.play(&nre, false);
            new.play(&nre, true);
            // Per mode: Window+Remainder FI contribute two copies of these
            // F+I ops; V FI/IF contribute four, including both simulators.
            // The four unchanged input/control modes therefore multiply24.
            total += 24 * (old.ops.len() + new.ops.len()) as u64;
        }
    }
    assert!(total <= 100_000_000, "cohort exact application invoice cap");
    total
}

fn run_vbank_native_cohort(cohort: usize) {
    assert!(cohort < V_BANK_COHORTS.len());
    let selected = V_BANK_COHORTS[cohort];
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    assert_eq!(cols.len(), 203);
    let invoice = vbank_cohort_invoice(&cols, selected);
    eprintln!("VFORM_Q_BANK_COHORT_READY cohort={} columns=7 physical_applications={} cap=100000000", cohort, invoice);
    let mut cases = 0u64;
    let mut expected_rejections = 0u64;
    let mut applications = 0u64;
    let mut coefficients = 0u64;
    for &ci in selected {
        let cp = &cols[ci];
        let mut geometry = vbank_builder();
        let frame = vbank_frame(&mut geometry, cp);
        let mut sizes: Vec<usize> = [0usize, 1, 2, 4, 8, 24, frame.bank.len()]
            .iter().map(|&n| n.min(frame.bank.len())).collect();
        sizes.sort_unstable();
        sizes.dedup();
        for helpers in sizes {
            for mode in 0..4 {
                let input = vbank_input(&frame, cp, 0x505f_5642 + 4099 * ci as u64 + mode as u64, mode);
                if helpers > 0 && mode == 2 {
                    let mut bad = input.clone();
                    let p = frame.bank[0];
                    let false_lane = !input[frame.pool[12].0 as usize] & 2;
                    assert_ne!(false_lane, 0);
                    bad[p.0 as usize] ^= false_lane;
                    assert_eq!(vbank_entry(&bad, &frame.bank), Err((p, false_lane)),
                        "expected Q-support/clean-loan mismatch on inactive lane");
                    expected_rejections += 1;
                }
                for form in [VBankForm::Window, VBankForm::Remainder, VBankForm::V] {
                    let mut old = vbank_builder();
                    let of = vbank_frame(&mut old, cp);
                    let ore = vbank_recipe(&mut old, &of, cp, 0, form);
                    let mut new = vbank_builder();
                    let nf = vbank_frame(&mut new, cp);
                    let nre = vbank_recipe(&mut new, &nf, cp, helpers, form);
                    old.play(&ore, false);
                    new.play(&nre, false);
                    let forward_old = std::mem::take(&mut old.ops);
                    let forward_new = std::mem::take(&mut new.ops);
                    old.play(&ore, true);
                    new.play(&nre, true);
                    let inverse_old = std::mem::take(&mut old.ops);
                    let inverse_new = std::mem::take(&mut new.ops);
                    if helpers == 0 {
                        assert_eq!(forward_old, forward_new, "zero-bank literal emission");
                        assert_eq!(inverse_old, inverse_new, "zero-bank inverse emission");
                    }
                    let a = vbank_apply(&forward_old, &input, &mut applications, &mut coefficients);
                    let z = vbank_apply(&forward_new, &input, &mut applications, &mut coefficients);
                    assert_eq!(a, z, "all699 forward ci={ci} helpers={helpers} mode={mode} form={form:?}");
                    vbank_entry(&z, &nf.bank).unwrap();
                    assert_eq!(vbank_apply(&inverse_old, &a, &mut applications, &mut coefficients), input,
                        "all699 old FI");
                    assert_eq!(vbank_apply(&inverse_new, &z, &mut applications, &mut coefficients), input,
                        "all699 new FI");
                    if matches!(form, VBankForm::V) {
                        let a = vbank_apply(&inverse_old, &input, &mut applications, &mut coefficients);
                        let z = vbank_apply(&inverse_new, &input, &mut applications, &mut coefficients);
                        assert_eq!(a, z, "all699 inverse V form");
                        assert_eq!(vbank_apply(&forward_old, &a, &mut applications, &mut coefficients), input,
                            "all699 old IF");
                        assert_eq!(vbank_apply(&forward_new, &z, &mut applications, &mut coefficients), input,
                            "all699 new IF");
                    }
                    cases += 64;
                }
            }
        }
    }
    assert_eq!(applications, invoice, "same-source exact application invoice");
    assert_eq!(cases, [21504u64, 20736][cohort]);
    assert_eq!(expected_rejections, [21u64, 20][cohort]);
    eprintln!("VFORM_Q_BANK_NATIVE_PASS cohort={} width=699 columns={} cases={} expected_entry_rejections={} physical_applications={} independent_hmr_coefficients={} all699=true false_R_DATA=true non_donor_Q_DATA=true whole=false",
        cohort, selected.len(), cases, expected_rejections, applications, coefficients);
}

#[test]
#[ignore = "ROOT resource admission required; actual699 cohort0 P-kernel only"]
fn midg_vform_q_high_bank_actual699_cohort0_v4() { run_vbank_native_cohort(0); }

#[test]
#[ignore = "ROOT resource admission required; actual699 cohort1 P-kernel only"]
fn midg_vform_q_high_bank_actual699_cohort1_v4() { run_vbank_native_cohort(1); }

#[test]
#[ignore = "ROOT resource admission required; P-kernel price only"]
fn midg_vform_q_high_bank_203_source_prices_v1() {
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    assert_eq!(cols.len(), 203);
    let mut saved = 0u64;
    let mut applications = 0u64;
    eprintln!("VFORM_Q_BANK_PRICE_HEADER column\thr\tht\tdn\tbank_lo\tbank_hi\thelpers\told_F_N\told_F_T\told_I_N\told_I_T\tnew_F_N\tnew_F_T\tnew_I_N\tnew_I_T\ttraversal_saved_T\twhole4_saved_T");
    for (ci, cp) in cols.iter().enumerate() {
        let mut old = vbank_builder();
        let of = vbank_frame(&mut old, cp);
        let ore = vbank_recipe(&mut old, &of, cp, 0, VBankForm::V);
        let mut new = vbank_builder();
        let nf = vbank_frame(&mut new, cp);
        let nre = vbank_recipe(&mut new, &nf, cp, nf.bank.len(), VBankForm::V);
        old.play(&ore, false);
        new.play(&nre, false);
        let (ofn, oft, nfn, nft) = (old.ops.len(), old.tof, new.ops.len(), new.tof);
        old.ops.clear();
        new.ops.clear();
        old.play(&ore, true);
        new.play(&nre, true);
        let (oin, oit, nin, nit) = (old.ops.len(), old.tof - oft, new.ops.len(), new.tof - nft);
        applications += (ofn + nfn + oin + nin) as u64;
        assert!(applications <= 20_000_000, "bounded P-kernel pricing cap");
        assert!(oft + oit >= nft + nit, "helper bank regresses reciprocal price");
        let multiplicity = u64::from(cp.hr) + u64::from(cp.ht);
        let delta = multiplicity * (oft + oit - nft - nit);
        saved += delta;
        eprintln!("VFORM_Q_BANK_PRICE_ROW {ci}\t{}\t{}\t{}\t{}\t{}\t{}\t{ofn}\t{oft}\t{oin}\t{oit}\t{nfn}\t{nft}\t{nin}\t{nit}\t{delta}\t{}",
            u8::from(cp.hr), u8::from(cp.ht), u8::from(cp.dn), nf.bank_lo, nf.bank_hi, nf.bank.len(), 4 * delta);
    }
    // A middle has one V entry and one V exit per HR/HT path. The point-add
    // circuit has four traversal applications. traversal_end_pl adds no middle.
    eprintln!("VFORM_Q_BANK_PRICE_PASS columns=203 width=699 traversal_saved_T={} whole4_projected_saved_T={} physical_emitted_ops={} scope=P_frames_only exact_whole_count=false",
        saved, 4 * saved, applications);
}

