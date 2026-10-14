use super::builder::B;
use super::modp_frogdrop::{add_const_exact, add_small, Ms, C};
use super::tests_frogdrop::{run, Rng};

#[test]
fn raw64_fold_same_on_every_low_carry_case_and_dirty_loan() {
    for &(k, lo, lowbits) in &[(C, 0usize, 10usize), (C - 1, 4, 6)] {
        let mut new = B::new();
        let t = new.alloc_n(256);
        let ctl = new.alloc();
        let dirty = new.alloc_n(100);
        let ms = Ms { k: ctl };
        add_small(&mut new, &ms, &t, lo, Some(ctl), k, &dirty);
        let mut old = B::new();
        let ot = old.alloc_n(256);
        let oc = old.alloc();
        let od = old.alloc_n(100);
        add_const_exact(&mut old, &ot[..64], Some(oc), k, &od);
        assert_eq!(old.width(), new.width());
        assert!(new.tof < old.tof, "new {} old {}", new.tof, old.tof);

        // All low words crossed with both enables and both arbitrary loan
        // values. High words include wrap, all-ones and independent junk.
        let ncases = (1usize << lowbits) * 8;
        let mut rng = Rng::new(k);
        for base in (0..ncases).step_by(64) {
            let mut init = vec![0u64; new.width() as usize];
            let mut inputs = [0u64; 64];
            let mut enables = [false; 64];
            for shot in 0..64 {
                let idx = base + shot;
                let low = (idx & ((1 << lowbits) - 1)) as u64;
                let enable = ((idx >> lowbits) & 1) != 0;
                let loan = ((idx >> (lowbits + 1)) & 1) != 0;
                let highkind = (idx >> (lowbits + 2)) & 1;
                let raw = if highkind == 0 {
                    ((!0u64 >> (lowbits + lo)) << (lowbits + lo)) | (low << lo)
                } else {
                    (rng.next() & (!0u64 << (lowbits + lo))) | (low << lo)
                } | (rng.next() & ((1u64 << lo) - 1));
                inputs[shot] = raw;
                enables[shot] = enable;
                for j in 0..64 {
                    if (raw >> j) & 1 != 0 { init[t[j].0 as usize] |= 1 << shot; }
                }
                if enable { init[ctl.0 as usize] |= 1 << shot; }
                if loan { init[dirty[0].0 as usize] |= 1 << shot; }
            }
            for &q in t.iter().skip(64).chain(dirty.iter().skip(1)) {
                init[q.0 as usize] = rng.next();
            }
            let a = run(&new.ops, new.width() as usize, &|q| q.clone_from(&init));
            let o = run(&old.ops, old.width() as usize, &|q| q.clone_from(&init));
            assert_eq!(a.phase, 0);
            assert_eq!(o.phase, 0);
            assert_eq!(a.q, o.q, "k{k} base{base}");
            for shot in 0..64 {
                let mut got = 0u64;
                for j in 0..64 { got |= ((a.q[t[j].0 as usize] >> shot) & 1) << j; }
                let want = inputs[shot].wrapping_add(if enables[shot] { k } else { 0 });
                assert_eq!(got, want, "k{k} raw{} ctl{}", inputs[shot], enables[shot]);
            }
            for &q in t.iter().skip(64).chain(dirty.iter()).chain([ctl].iter()) {
                assert_eq!(a.q[q.0 as usize], init[q.0 as usize], "returned q{}", q.0);
            }
        }
        eprintln!("RAW64_FOLD_PASS k={k} lo={lo} cases={ncases} newT={} oldT={} saving={} allhelpers_restored=true phase0=true", new.tof, old.tof, old.tof-new.tof);
    }
}

#[test]
fn raw64_fold_inverse_returns_entire_state() {
    let mut b = B::new();
    let t = b.alloc_n(256);
    let ctl = b.alloc();
    let dirty = b.alloc_n(100);
    let ms = Ms { k: ctl };
    for &(lo, k) in &[(0, C), (4, C - 1)] {
        b.begin();
        add_small(&mut b, &ms, &t, lo, Some(ctl), k, &dirty);
        let rec = b.end();
        b.play(&rec, false);
        b.play(&rec, true);
    }
    let mut rng = Rng::new(0xc0ffeed);
    for _ in 0..32 {
        let init: Vec<u64> = (0..b.width()).map(|_| rng.next()).collect();
        let out = run(&b.ops, b.width() as usize, &|q| q.clone_from(&init));
        assert_eq!(out.phase, 0);
        assert_eq!(out.q, init);
    }
    eprintln!("RAW64_FOLD_FI_PASS cases=2048 arbitraryallstate=true phase0=true");
}
