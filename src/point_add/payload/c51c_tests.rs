use super::*;
use super::super::frogdrop_col::rec;
use super::super::tests_frogdrop::{run, Rng};
use super::super::frogdrop_sched::N;

fn put(ws: &mut [u64], lanes: &[QubitId], shot: usize, value: usize) {
    for (i, &q) in lanes.iter().enumerate() {
        if (value >> i) & 1 != 0 { ws[q.0 as usize] |= 1u64 << shot; }
    }
}

/// C51C S3 prerequisite: the high three lanes of (sz + sy - 232) are zero on
/// active model-clean levels, but remain arbitrary on delayed non-act shots.
/// Their decoder compute/erase must therefore be unitary, and every output
/// toggle retains act as a control. This is a kernel, not the full digit.
#[test]
fn c51c_guarded_size_offset_cc_all_wire() {
    let mut b = B::new();
    let sz = b.alloc_n(8);
    let sy = b.alloc_n(8);
    let act = b.alloc();
    let out = b.alloc();
    let out2 = b.alloc();
    let c0 = b.alloc();
    let dirty = b.alloc_n(24);
    let body = rec(&mut b, |b| {
        let sum = rec(b, |b| super::super::frogdrop::reg_add_into(b, &sz, &sy, &[], c0));
        b.play(&sum, false);
        let bias = rec(b, |b| super::super::frogdrop::add_const_dirty_exact(b, &sz, 232, &dirty));
        b.play(&bias, true);
        super::super::mask::R11O11_DECCC.with(|c| *c.borrow_mut() = sz[5..8].to_vec());
        let mut dec = Dec::new(&sz[..5], &sz[5..8]);
        for k in 0..=25 {
            let mut controls = dec.ctrls(b, k);
            controls.push((act, false));
            mc_xor(b, &controls, out, &[], &dirty);
        }
        dec.clear(b);
        // A CC lane passed as an mc_xor temp must be filtered. Direct AND
        // compute/erase on another CC lane must lower to CCX in both legs.
        mc_xor(b, &[(act, false), (sy[0], false), (sy[1], false)], out2, &[sz[6]], &dirty);
        b.and_c(act, sy[0], sz[7]);
        b.and_u(act, sy[0], sz[7]);
        super::super::mask::R11O11_DECCC.with(|c| c.borrow_mut().clear());
        b.play(&bias, false);
        b.play(&sum, true);
    });
    b.play(&body, false);
    let forward = b.ops.len();
    b.play(&body, true);

    let mut rng = Rng::new(0xc51c_0232);
    let mut init = vec![0u64; b.width() as usize];
    let mut out2_expected = 0u64;
    for shot in 0..64 {
        let active = shot % 4 != 0;
        let (szv, syv) = if active {
            let s = 232 + (shot % 26);
            let y = 1 + (shot * 17 % 128);
            (s - y, y)
        } else if shot == 0 { (116, 100) } else {
            (1 + shot * 3 % 128, 1 + shot * 11 % 128)
        };
        put(&mut init, &sz, shot, szv);
        put(&mut init, &sy, shot, syv);
        if active { init[act.0 as usize] |= 1u64 << shot; }
        if active && syv & 3 == 3 { out2_expected |= 1u64 << shot; }
        for &q in &dirty { if rng.next() & 1 != 0 { init[q.0 as usize] |= 1u64 << shot; } }
    }
    let result = run(&b.ops[..forward], b.width() as usize,
        &|ws| ws[..init.len()].copy_from_slice(&init));
    assert_eq!(result.phase, 0, "forward phase");
    for (i, &value) in result.q.iter().enumerate() {
        let expected = if i == out.0 as usize { init[i] ^ init[act.0 as usize] }
            else if i == out2.0 as usize { init[i] ^ out2_expected }
            else { init[i] };
        assert_eq!(value, expected, "forward lane {i}");
    }
    let inverse = run(&b.ops, b.width() as usize,
        &|ws| ws[..init.len()].copy_from_slice(&init));
    assert_eq!(inverse.phase, 0, "inverse phase");
    assert_eq!(inverse.q, init, "inverse all wires");
    eprintln!("C51D_NONACT_PASSENGER sz=116 sy=100 shot=0 forward_phase=0 inverse_phase=0 inverse_all_wires=true");
}

fn put_n(ws: &mut [u64], lanes: &[QubitId], shot: usize, value: N) {
    for (i, &q) in lanes.iter().enumerate() {
        if ((value >> i) & N::from(1u64)) != N::ZERO { ws[q.0 as usize] |= 1u64 << shot; }
    }
}

/// Isolated long-division construction probe. Six physical free lanes are
/// supplemented by the upper three offset-size lanes. The source must restore
/// the original size before every size-dependent read and preserve passengers.
#[test]
fn c51c_offset_digit_divide_trial() {
    offset_digit_trial("divide");
}

#[test]
fn c51c_offset_digit_relocate_trial() {
    offset_digit_trial("relocate");
}

#[test]
fn c51c_offset_digit_inverse_trial() {
    offset_digit_trial("inverse");
}

#[test]
fn c51c_offset_digit_full_trial() {
    offset_digit_trial("full");
}

fn offset_digit_trial(stage: &str) {
    std::env::set_var("D2_DIGIT_STOP", stage);
    D2_DIGIT_TARGET.with(|t| t.set(true));
    for (szv, syv, active) in [(213usize, 44usize, true), (255, 2, true),
                               (190, 44, true), (116, 100, false)] {
        let mut b = B::new();
        let p = b.alloc_n(NP);
        let ring = b.alloc_n(257);
        let y = b.alloc_n(129);
        let sz = b.alloc_n(8);
        let sy = b.alloc_n(8);
        let act = b.alloc();
        let top = b.alloc();
        let adj = b.alloc();
        let free = b.alloc_n(6);
        let dirty = b.alloc_n(24);
        let bank: Vec<QubitId> = std::iter::once(free[0]).chain(sz[5..8].iter().copied())
            .chain(free[1..].iter().copied()).collect();
        let mut ds = dig_scr_z(&bank, &sz, &sy, &dirty, true);
        ds.smin = 232;
        let ph = Ph { ht: false, sz_mask: true, virt_m1: false,
            rv: sz.clone(), rr: (szv, szv), tv: sy.clone(), tr: (syv, syv),
            src_r: ring.clone(), src_t: y.clone() };
        let body = rec(&mut b, |b| {
            b.x(top); b.cx(ring[szv - 1], top); b.cx(top, ring[szv - 1]);
            b.cswap(act, ring[szv], adj);
            digit(b, &p, &ph, act, &ds, &dirty);
            b.cswap(act, ring[szv], adj);
            b.cx(top, ring[szv - 1]); b.cx(ring[szv - 1], top); b.x(top);
        });
        b.play(&body, false);
        let forward = b.ops.len();
        b.play(&body, true);
        let mut rng = Rng::new(0xc51c_0257 ^ szv as u64);
        let mut init = vec![0u64; b.width() as usize];
        let mut remainders = vec![N::ZERO; 64];
        let mut quotients = vec![N::ZERO; 64];
        for shot in 0..64 {
            let r = rng.below(szv - 1) | (N::from(1u64) << (szv - 1));
            let sampled = rng.below((szv + (257 - szv - syv)).min(258));
            // The inherited 23-bit quotient cap is part of the model-clean
            // contract. The g=23 edge otherwise includes excluded shots.
            let d = if active { sampled % (r << 23) } else { sampled };
            remainders[shot] = d % r;
            put_n(&mut init, &p, shot, d);
            let t = rng.below(syv - 1) | (N::from(1u64) << (syv - 1));
            put_n(&mut init, &y, shot, t);
            put(&mut init, &sz, shot, szv);
            put(&mut init, &sy, shot, syv);
            if active && shot % 8 != 0 { init[act.0 as usize] |= 1u64 << shot; }
            for &q in &dirty { if rng.next() & 1 != 0 { init[q.0 as usize] |= 1u64 << shot; } }
            for i in 0..szv - 1 {
                if ((r >> i) & N::from(1u64)) != N::ZERO { init[ring[i].0 as usize] |= 1u64 << shot; }
            }
            let q = d / r;
            quotients[shot] = q;
            if ((q >> (257 - szv - syv)) & N::from(1u64)) != N::ZERO {
                init[ring[szv - 1].0 as usize] |= 1u64 << shot;
            }
        }
        let got = run(&b.ops[..forward], b.width() as usize,
            &|ws| ws[..init.len()].copy_from_slice(&init));
        assert_eq!(got.phase, 0, "forward phase sz={szv} sy={syv}");
        for &wire in ring.iter().chain(&y).chain(&sz).chain(&sy).chain(&dirty).chain(&[act, top, adj]) {
            assert_eq!(got.q[wire.0 as usize], init[wire.0 as usize],
                "passenger {:?} sz={szv} sy={syv}", wire);
        }
        for shot in 0..64 {
            if active && shot % 8 != 0 {
                for i in 0..szv {
                    let have = (got.q[p[i].0 as usize] >> shot) & 1 != 0;
                    let want = ((remainders[shot] >> i) & N::from(1u64)) != N::ZERO;
                    assert_eq!(have, want, "remainder bit {i} shot {shot} sz={szv} sy={syv}");
                }
                if stage == "relocate" {
                    let g = 257 - szv - syv;
                    for k in 0..=g.min(KE - 1) {
                        let pos = NP - 1 - (syv + 1 + k);
                        let have = (got.q[p[pos].0 as usize] >> shot) & 1 != 0;
                        let want = ((quotients[shot] >> k) & N::from(1u64)) != N::ZERO;
                        assert_eq!(have, want,
                            "relocated quotient bit {k} shot {shot} sz={szv} sy={syv}");
                    }
                }
            }
        }
        let inv = run(&b.ops, b.width() as usize,
            &|ws| ws[..init.len()].copy_from_slice(&init));
        assert_eq!(inv.phase, 0, "inverse phase sz={szv} sy={syv}");
        assert_eq!(inv.q, init, "inverse all wires sz={szv} sy={syv}");
    }
    D2_DIGIT_TARGET.with(|t| t.set(false));
    std::env::remove_var("D2_DIGIT_STOP");
}
