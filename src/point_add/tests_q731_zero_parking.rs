//! Root-integrated bounded tests; not a whole-record certificate.
use super::*;

// Source-only draft. Append inside tests_frogdrop.rs, whose native run/put/get
// helpers this uses. No test was compiled or executed by the author. This is a
// bounded component check, not a whole-circuit or trusted-packet certificate.

#[test]
fn reserved_c0_keeps_live_buffer_during_subset_switch() {
    use super::super::frogdrop::pipeline_subset_with_reserved_c0;
    let (k, kp, qb, tot) = (29usize, 30usize, 26usize, 83usize);
    let one = N::from(1u64);
    let zhead = N::from(276177160u64);
    let yhead = N::from(939524096u64);
    let zd = zhead | one;
    let yd = yhead | one;
    let f = ((one << 60) - one) / zd;
    let qwant = f / yd;
    let rhowant = f % yd;
    let rwant = ((one << 60) - one) % zd;
    assert_eq!(qwant, N::from(4u64));
    assert!(rhowant >= N::from(3u64) << 27);
    let ma: Vec<bool> = (0..qb).map(|i| i == 2 || i == 3).collect();
    let mb: Vec<bool> = (0..qb).map(|i| i < 2).collect();
    for ncar in [0usize, 8, 31] {
        let mut b = B::new();
        let zh = b.alloc_n(k);
        let yh = b.alloc_n(kp);
        let start = b.alloc_n(9);
        let stored = b.alloc_n(2);
        let ps = PScr { r: b.alloc_n(k+1), rho: b.alloc_n(kp+1),
            q0: (0..qb).map(|i| stored[i%2]).collect(), f: b.alloc(), g: b.alloc(),
            c0: b.alloc(), zero: b.alloc(), one: b.alloc(), spre: b.alloc_n(6),
            tmp: b.alloc(), dirty: vec![] };
        let carries = b.alloc_n(ncar);
        let beta = b.alloc();
        let (head, tails, switches, rf, rhof) = pipeline_subset_with_reserved_c0(
            &mut b, &zh, &yh, &start, -232, tot, qb, &ps, &carries,
            &[ma.clone(), mb.clone()], ps.f, 0, true, true);
        let rz = rf[k];
        let buffer = ps.r[k];
        assert_ne!(rz, buffer);
        let aligned: Vec<_> = rf.iter().map(|&q|
            if q == rz { buffer } else if q == buffer { rz } else { q }).collect();
        b.play(&head, false); b.play(&tails[0], false); b.swap(rz, buffer);
        // The test keeps beta coherent; half of the batch has a live set buffer.
        b.cx(beta, buffer);
        let na = b.ops.len();
        b.swap(buffer, ps.c0); b.swap(rz, buffer);
        b.play(&switches[0].0, true); b.play(&switches[0].1, false);
        b.swap(rz, buffer); b.swap(buffer, ps.c0);
        let nb = b.ops.len();
        // Reverse the switch with the same donor lifetime.
        b.swap(buffer, ps.c0); b.swap(rz, buffer);
        b.play(&switches[0].1, true); b.play(&switches[0].0, false);
        b.swap(rz, buffer); b.swap(buffer, ps.c0);
        b.cx(beta, buffer); b.swap(rz, buffer);
        b.play(&tails[0], true); b.play(&head, true);
        let init = |w: &mut Vec<u64>| {
            for sh in 0..64 {
                put(w, &zh, sh, &zhead); put(w, &yh, sh, &yhead);
                put(w, &start, sh, &N::from(255u64));
                put(w, &[beta], sh, &N::from((sh%2) as u64));
            }
        };
        let width = b.width() as usize;
        let ra = run(&b.ops[..na], width, &init);
        let rb = run(&b.ops[..nb], width, &init);
        let done = run(&b.ops, width, &init);
        for (state, want) in [(&ra, N::from(4u64)), (&rb, N::ZERO)] {
            assert_eq!(state.phase, 0);
            for sh in 0..64 {
                assert_eq!(get(&state.q, &aligned[..k], sh), rwant);
                assert_eq!(get(&state.q, &[buffer], sh), N::from((sh%2) as u64));
                assert_eq!(get(&state.q, &rhof, sh), rhowant);
                // Read only the active mask's distinct stored output lanes.
                let mask = if want.is_zero() { &mb } else { &ma };
                for bit in 0..qb {
                    if mask[bit] {
                        assert_eq!(get(&state.q, &[ps.q0[bit]], sh), N::from(u64::from(want.bit(bit))));
                    }
                }
                for &q in [ps.f, ps.g, ps.c0, ps.zero, ps.tmp].iter()
                    .chain(ps.spre.iter()).chain(carries.iter()) {
                    assert_eq!(get(&state.q, &[q], sh), N::ZERO);
                }
            }
        }
        assert_eq!(done.phase, 0);
        for sh in 0..64 {
            assert_eq!(get(&done.q, &zh, sh), zhead);
            assert_eq!(get(&done.q, &yh, sh), yhead);
            assert_eq!(get(&done.q, &start, sh), N::from(255u64));
            assert_eq!(get(&done.q, &[beta], sh), N::from((sh%2) as u64));
            for &q in ps.r.iter().chain(ps.rho.iter()).chain(stored.iter())
                .chain([ps.f,ps.g,ps.c0,ps.zero,ps.one,ps.tmp].iter())
                .chain(ps.spre.iter()).chain(carries.iter()) {
                assert_eq!(get(&done.q, &[q], sh), N::ZERO);
            }
        }
    }
}

#[test]
fn standing731_geometry_keeps_original_precision() {
    use super::super::{pointadd_frogdrop as pa,frogdrop_col::{Fd,ColScr,pool_size}};
    assert_eq!((pa::N,pa::K,pa::KP,pa::QB,pa::TOT,pa::NQ,pa::SW),(287,29,30,24,83,128,8));
    let mut b=B::new();
    let mut ring=b.alloc_n(256);let payload=b.alloc_n(259);
    ring.extend(b.alloc_n(pa::N-256));
    let q=b.alloc_n(pa::NQ);let cnt=q[pa::NQ-pa::CNTB..].to_vec();
    let fd=Fd{ring,q,sy:b.alloc_n(pa::SW),sx:b.alloc_n(pa::SW),ph:b.alloc(),cnt};
    let pool=b.alloc_n(pool_size(pa::KP,pa::QB,pa::SW));
    let sc=ColScr::carve(&pool,&fd.sx,&payload,pa::KP,pa::QB,pa::TAIL);
    assert_eq!(b.peak,731);assert_eq!(pool.len(),40);
    assert_eq!(pa::N-257,pa::K+1);
    assert_eq!((pa::K+pa::K+1-pa::TOT%(pa::K+1))%(pa::K+1),6);
    for v in [&sc.ps.r,&sc.ps.rho,&sc.ps.q0,&sc.ps.spre,&sc.ps.dirty] {
        assert!(!v.contains(&sc.ps.c0));
    }
    assert_eq!(sc.ps.c0,pool[14]);
    assert_eq!(sc.ps.rho.len(),31);
    assert!(b.ops.is_empty());
    println!("ZERO_PARKING_STANDING731 K29_KP30_UNCHANGED donor_pool14 Rzero_owner6 no_emission=true");
}
