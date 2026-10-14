//! Lilypad-GCD audit build tests: forward walk and regenerating walk against an integer model on 64 shots every tick
//! (rings, h, Q word, scratch, phase), and the paired forward + inverse round trip at a qubit cap with Toffoli
//! counts (expected executed, the metric) and the peak.
//! LILYPAD_SCHED = schedule file, LILYPAD_QB = Q lanes (default 20), LILYPAD_CAP = cap (pool fills to it), LILYPAD_TICKS,
//! LILYPAD_SEED.
use super::builder::B;
use super::frogdrop_sched::{p, N};
use super::lilypad::*;
use super::pointadd_lilypad;
use super::tests_frogdrop::Rng;
use super::tests_strip::{get_s, get_u, put};
use crate::circuit::{analyze_ops, QubitId};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};

fn env_usize(k: &str, d: usize) -> usize {
    std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d)
}

fn sched() -> PSched {
    let f = std::env::var("LILYPAD_SCHED").expect("LILYPAD_SCHED");
    PSched::from_text(&std::fs::read_to_string(f).unwrap())
}

/// Exhaust all `(e,g4:g3:g2)` assignments through the Q885 three-high
/// decoder, including both recording directions and forced HMR outcomes.
#[test]
fn lilypad_decode3_high_exact() {
    use sha3::digest::XofReader;
    struct Fixed(u8);
    impl XofReader for Fixed {
        fn read(&mut self, out: &mut [u8]) { out.fill(self.0); }
    }

    for inverse in [false, true] {
        let mut b = B::new();
        let g = b.alloc_n(3);
        let e = b.alloc();
        let high = b.alloc_n(3);
        let w = b.alloc();
        let out = b.alloc_n(3);
        b.begin();
        decode3_high_lilypad(&mut b, g[0], g[1], g[2], e, &high, w);
        for d in 0..3 { b.cx(high[d], out[d]); }
        clear_decode3_high_lilypad(&mut b, g[0], g[1], g[2], e, &high, w);
        let rec = b.end();
        assert_eq!(b.measure(&rec, false), 4.0);
        assert_eq!(b.measure(&rec, true), 4.0);
        b.play(&rec, inverse);

        for byte in [0u8, 255, 170] {
            let mut xof = Fixed(byte);
            let mut sim = Simulator::new(b.width() as usize, 1, &mut xof);
            for shot in 0..32 {
                let v = shot & 15;
                for k in 0..3 {
                    if (v >> k) & 1 != 0 { sim.qubits[g[k].0 as usize] |= 1u64 << shot; }
                }
                if (v >> 3) & 1 != 0 { sim.qubits[e.0 as usize] |= 1u64 << shot; }
            }
            sim.apply_iter(b.ops.iter());
            assert_eq!(sim.phase, 0, "inverse {inverse}, forced HMR byte {byte}");
            for shot in 0..32 {
                let v = shot & 15;
                let gv = v & 7;
                let ev = (v >> 3) & 1;
                for k in 0..3 {
                    assert_eq!((sim.qubits[g[k].0 as usize] >> shot) & 1, ((gv >> k) & 1) as u64);
                    assert_eq!((sim.qubits[high[k].0 as usize] >> shot) & 1, 0);
                    assert_eq!((sim.qubits[out[k].0 as usize] >> shot) & 1, (ev == 1 && gv == k) as u64);
                }
                assert_eq!((sim.qubits[e.0 as usize] >> shot) & 1, ev as u64);
                assert_eq!((sim.qubits[w.0 as usize] >> shot) & 1, 0);
            }
        }
    }
}

#[test]
fn lilypad_dec_topless_exact() {
    let mut b = B::new();
    let ctrl = b.alloc();
    let bits = b.alloc_n(5);
    let anc = b.alloc_n(3);
    super::arith::dec_topless(&mut b, ctrl, &bits, &anc);
    let mut xr = xof(b"lilypad-dec-topless");
    let mut s = Simulator::new(b.width() as usize, 1, &mut xr);
    for shot in 0..64 {
        let value = shot & 31;
        let cv = (shot >> 5) & 1;
        if cv != 0 {
            s.qubits[ctrl.0 as usize] |= 1u64 << shot;
        }
        for (i, q) in bits.iter().enumerate() {
            if value >> i & 1 != 0 {
                s.qubits[q.0 as usize] |= 1u64 << shot;
            }
        }
    }
    s.apply_iter(b.ops.iter());
    assert_eq!(s.phase, 0);
    for shot in 0..64 {
        let value = shot & 31;
        let cv = (shot >> 5) & 1;
        assert_eq!(get_u(&s.qubits, &bits, shot) as usize, (value + 32 - cv) & 31, "shot {shot}");
        assert!(anc.iter().all(|q| (s.qubits[q.0 as usize] >> shot) & 1 == 0));
    }
}

#[test]
fn lilypad_const_add_topless_exact() {
    for n in 2usize..=5 {
        for k in 1u64..1u64 << n {
            for shortage in 1usize..=2 {
            let mut b = B::new();
            let ctrl = b.alloc();
            let target = b.alloc_n(n);
            let need = n - 1 - (k.trailing_zeros() as usize).min(n - 1);
            if need < shortage + 1 {
                continue;
            }
            let i0 = k.trailing_zeros() as usize;
            let tail_len = shortage + 1;
            let start = n - tail_len;
            if start - i0 < tail_len - 2 {
                continue;
            }
            let pool = b.alloc_n(need - shortage);
            super::modp_ft::const_add_pool(&mut b, &target, ctrl, k, &pool);
            let mut xr = xof(format!("lilypad-const-topless-{n}-{k}-{shortage}").as_bytes());
            let mut s = Simulator::new(b.width() as usize, 1, &mut xr);
            for shot in 0..64 {
                let value = shot & ((1usize << n) - 1);
                let cv = (shot >> n) & 1;
                if cv != 0 {
                    s.qubits[ctrl.0 as usize] |= 1u64 << shot;
                }
                for (i, q) in target.iter().enumerate() {
                    if value >> i & 1 != 0 {
                        s.qubits[q.0 as usize] |= 1u64 << shot;
                    }
                }
            }
            s.apply_iter(b.ops.iter());
            assert_eq!(s.phase, 0, "n={n} k={k} shortage={shortage}");
            for shot in 0..64 {
                let value = shot & ((1usize << n) - 1);
                let cv = (shot >> n) & 1;
                let want = (value + cv * k as usize) & ((1usize << n) - 1);
                assert_eq!(get_u(&s.qubits, &target, shot) as usize, want, "n={n} k={k} shortage={shortage} shot={shot}");
                assert!(pool.iter().all(|q| (s.qubits[q.0 as usize] >> shot) & 1 == 0));
            }
            }
        }
    }
}

#[test]
fn lilypad_const_add_multi_topless_exact() {
    let n = 8usize;
    for shortage in 3usize..=4 {
        for k in 1u64..1u64 << n {
            let need = n - 1 - (k.trailing_zeros() as usize).min(n - 1);
            if need < shortage + 1 {
                continue;
            }
            let i0 = k.trailing_zeros() as usize;
            let tail_len = shortage + 1;
            let start = n - tail_len;
            if start - i0 < tail_len - 2 {
                continue;
            }
            let mut b = B::new();
            let ctrl = b.alloc();
            let target = b.alloc_n(n);
            let pool = b.alloc_n(need - shortage);
            super::modp_ft::const_add_pool(&mut b, &target, ctrl, k, &pool);
            for cv in 0usize..=1 {
                for batch in 0usize..4 {
                let mut xr = xof(format!("lilypad-const-multi-topless-{k}-{shortage}-{cv}").as_bytes());
                let mut s = Simulator::new(b.width() as usize, 1, &mut xr);
                if cv != 0 {
                    s.qubits[ctrl.0 as usize] = u64::MAX;
                }
                for shot in 0..64usize {
                    let value = batch * 64 + shot;
                    for (i, q) in target.iter().enumerate() {
                        if value >> i & 1 != 0 {
                            s.qubits[q.0 as usize] |= 1u64 << shot;
                        }
                    }
                }
                s.apply_iter(b.ops.iter());
                assert_eq!(s.phase, 0, "k={k} shortage={shortage} cv={cv}");
                for shot in 0..64usize {
                    let value = batch * 64 + shot;
                    let want = (value + cv * k as usize) & 255;
                    assert_eq!(get_u(&s.qubits, &target, shot) as usize, want, "k={k} shortage={shortage} cv={cv} value={value}");
                    assert!(pool.iter().all(|q| (s.qubits[q.0 as usize] >> shot) & 1 == 0));
                }
                }
            }
        }
    }
}

#[test]
fn lilypad_const_add_deep_topless_exact() {
    let n = 16usize;
    let constants = [1u64, 0x3d1, 0x1001, 0x9a5b];
    for shortage in 5usize..=8 {
        for &k in &constants {
            let need = n - 1 - (k.trailing_zeros() as usize).min(n - 1);
            if need < shortage + 1 {
                continue;
            }
            let i0 = k.trailing_zeros() as usize;
            let tail_len = shortage + 1;
            let start = n - tail_len;
            if start - i0 < tail_len - 2 {
                continue;
            }
            let mut b = B::new();
            let ctrl = b.alloc();
            let target = b.alloc_n(n);
            let pool = b.alloc_n(need - shortage);
            super::modp_ft::const_add_pool(&mut b, &target, ctrl, k, &pool);
            for cv in 0usize..=1 {
                for batch in 0usize..16 {
                    let mut xr = xof(format!("lilypad-const-deep-topless-{k}-{shortage}-{cv}-{batch}").as_bytes());
                    let mut s = Simulator::new(b.width() as usize, 1, &mut xr);
                    if cv != 0 {
                        s.qubits[ctrl.0 as usize] = u64::MAX;
                    }
                    for shot in 0..64usize {
                        let value = ((batch * 4093 + shot * 977) ^ (shot << 9)) & 0xffff;
                        for (i, q) in target.iter().enumerate() {
                            if value >> i & 1 != 0 {
                                s.qubits[q.0 as usize] |= 1u64 << shot;
                            }
                        }
                    }
                    s.apply_iter(b.ops.iter());
                    assert_eq!(s.phase, 0, "k={k} shortage={shortage} cv={cv} batch={batch}");
                    for shot in 0..64usize {
                        let value = ((batch * 4093 + shot * 977) ^ (shot << 9)) & 0xffff;
                        let want = (value + cv * k as usize) & 0xffff;
                        assert_eq!(
                            get_u(&s.qubits, &target, shot) as usize,
                            want,
                            "k={k} shortage={shortage} cv={cv} batch={batch} shot={shot}"
                        );
                        assert!(pool.iter().all(|q| (s.qubits[q.0 as usize] >> shot) & 1 == 0));
                    }
                }
            }
        }
    }
}

#[test]
fn lilypad_paged_vlow_oracle_small_exact() {
    const R: usize = 3;
    const NV: usize = 3 * R + 1;
    const P: usize = 251;

    let mut b = B::new();
    let g = b.alloc_n(R);
    let f = b.alloc_n(R);
    let u = b.alloc_n(R);
    let rho = b.alloc();
    let out = b.alloc_n(R);
    let keep = b.alloc_n(R);
    let dirty = b.alloc_n(NV - 2);
    let vars: Vec<QubitId> = g
        .iter()
        .chain(&f)
        .chain(&u)
        .copied()
        .chain(std::iter::once(rho))
        .collect();

    let synth = |b: &mut B, target: QubitId, bit: usize| {
        let n = 1usize << NV;
        let mut anf = vec![0u8; n];
        for assignment in 0..n {
            let read = |offset: usize| -> usize { (assignment >> offset) & ((1 << R) - 1) };
            let gv = read(0);
            let fv = read(R);
            let uv = read(2 * R);
            let rv = (assignment >> (3 * R)) & 1;
            let value = if fv & 1 == 0 {
                0
            } else {
                let modulus = 1usize << R;
                let sign_p = if rv == 0 { P % modulus } else { modulus - (P % modulus) };
                let inv = (1..modulus).find(|x| (fv * x) % modulus == 1).unwrap();
                ((gv * uv + sign_p) * inv) % modulus
            };
            anf[assignment] = ((value >> bit) & 1) as u8;
        }
        for k in 0..NV {
            for mask in 0..n {
                if mask & (1 << k) != 0 {
                    anf[mask] ^= anf[mask ^ (1 << k)];
                }
            }
        }
        for (mask, coefficient) in anf.into_iter().enumerate() {
            if coefficient == 0 {
                continue;
            }
            let controls: Vec<(QubitId, bool)> = (0..NV)
                .filter(|k| mask & (1 << k) != 0)
                .map(|k| (vars[k], false))
                .collect();
            super::mask::mc_xor(b, &controls, target, &[], &dirty);
        }
    };

    for (bit, &target) in out.iter().enumerate() {
        synth(&mut b, target, bit);
        b.cx(target, keep[bit]);
    }
    for (bit, &target) in out.iter().enumerate().rev() {
        synth(&mut b, target, bit);
    }

    for batch in 0usize..(1usize << (NV - 6)) {
        let mut xr = xof(format!("lilypad-paged-vlow-{batch}").as_bytes());
        let mut s = Simulator::new(b.width() as usize, 1, &mut xr);
        for shot in 0..64usize {
            let assignment = batch * 64 + shot;
            for (k, q) in vars.iter().enumerate() {
                if assignment >> k & 1 != 0 {
                    s.qubits[q.0 as usize] |= 1u64 << shot;
                }
            }
            for (k, q) in dirty.iter().enumerate() {
                if ((assignment.rotate_left((k + 1) as u32) ^ (shot * 0x9e37)) >> k) & 1 != 0 {
                    s.qubits[q.0 as usize] |= 1u64 << shot;
                }
            }
        }
        let dirty_before: Vec<u64> = dirty.iter().map(|q| s.qubits[q.0 as usize]).collect();
        s.apply_iter(b.ops.iter());
        assert_eq!(s.phase, 0, "batch={batch}");
        for shot in 0..64usize {
            let assignment = batch * 64 + shot;
            let read = |offset: usize| -> usize { (assignment >> offset) & ((1 << R) - 1) };
            let gv = read(0);
            let fv = read(R);
            let uv = read(2 * R);
            let rv = (assignment >> (3 * R)) & 1;
            let want = if fv & 1 == 0 {
                0
            } else {
                let modulus = 1usize << R;
                let sign_p = if rv == 0 { P % modulus } else { modulus - (P % modulus) };
                let inv = (1..modulus).find(|x| (fv * x) % modulus == 1).unwrap();
                ((gv * uv + sign_p) * inv) % modulus
            };
            assert_eq!(get_u(&s.qubits, &keep, shot) as usize, want, "batch={batch} shot={shot}");
            assert_eq!(get_u(&s.qubits, &out, shot), 0, "oracle output not cleared");
        }
        for (k, q) in dirty.iter().enumerate() {
            assert_eq!(s.qubits[q.0 as usize], dirty_before[k], "dirty lane {k}");
        }
    }
}

#[test]
fn lilypad_dirty_increment_exact() {
    let mut b = B::new();
    let value = b.alloc_n(7);
    let dirty = b.alloc_n(4);
    super::lilypad::inc_unctl_dirty(&mut b, &value, &dirty);

    for batch in 0usize..2 {
        let mut xr = xof(format!("lilypad-dirty-increment-{batch}").as_bytes());
        let mut s = Simulator::new(b.width() as usize, 1, &mut xr);
        for shot in 0..64usize {
            let input = batch * 64 + shot;
            for (k, q) in value.iter().enumerate() {
                if input >> k & 1 != 0 {
                    s.qubits[q.0 as usize] |= 1u64 << shot;
                }
            }
            for (k, q) in dirty.iter().enumerate() {
                if ((input * 0x5d + k * 0x31) >> (k + 1)) & 1 != 0 {
                    s.qubits[q.0 as usize] |= 1u64 << shot;
                }
            }
        }
        let dirty_before: Vec<u64> = dirty.iter().map(|q| s.qubits[q.0 as usize]).collect();
        s.apply_iter(b.ops.iter());
        assert_eq!(s.phase, 0);
        for shot in 0..64usize {
            let input = batch * 64 + shot;
            assert_eq!(get_u(&s.qubits, &value, shot) as usize, (input + 1) & 127);
        }
        for (k, q) in dirty.iter().enumerate() {
            assert_eq!(s.qubits[q.0 as usize], dirty_before[k], "dirty lane {k}");
        }
    }
}

#[test]
fn lilypad_direct_cap_q11_exact() {
    let mut b = B::new();
    let h = b.alloc_n(7);
    let log = b.alloc_n(8);
    let sigma = b.alloc();
    let event = b.alloc();
    let dirty = b.alloc_n(4);
    super::lilypad::cap_logic_q11_direct(&mut b, &h, &log, sigma, event, &dirty);

    let ref_h = b.alloc_n(7);
    let ref_log = b.alloc_n(8);
    let ref_sigma = b.alloc();
    let ref_sc = PScr {
        e: b.alloc(),
        sg: ref_sigma,
        d: b.alloc_n(1),
        tmp: b.alloc_n(1),
        sp: b.alloc_n(4),
        pool: vec![],
    };
    let ref_w = PWalk {
        a: vec![],
        bb: vec![],
        q: vec![],
        h: ref_h.clone(),
        capq: 11,
        log: ref_log.clone(),
    };
    super::lilypad::cap_logic(&mut b, &ref_w, &ref_sc);

    // Complete valid two-slot support before a non-overflow push: slot 1 is
    // empty, slot 0 may hold any four-bit prior overflow.
    for old_log0 in 0usize..16 {
        for batch in 0usize..4 {
            let mut xr = xof(format!("lilypad-direct-cap-{old_log0}-{batch}").as_bytes());
            let mut s = Simulator::new(b.width() as usize, 1, &mut xr);
            for shot in 0..64usize {
                let h0 = batch * 32 + (shot & 31);
                let sig = (shot >> 5) & 1;
                for (k, q) in h.iter().enumerate() {
                    if h0 >> k & 1 != 0 {
                        s.qubits[q.0 as usize] |= 1u64 << shot;
                        s.qubits[ref_h[k].0 as usize] |= 1u64 << shot;
                    }
                }
                for (k, q) in log[..4].iter().enumerate() {
                    if old_log0 >> k & 1 != 0 {
                        s.qubits[q.0 as usize] |= 1u64 << shot;
                        s.qubits[ref_log[k].0 as usize] |= 1u64 << shot;
                    }
                }
                if sig != 0 {
                    s.qubits[sigma.0 as usize] |= 1u64 << shot;
                    s.qubits[ref_sigma.0 as usize] |= 1u64 << shot;
                }
                for (k, q) in dirty.iter().enumerate() {
                    if ((h0 * 0x35 + old_log0 * 0x17 + k) >> (k + 1)) & 1 != 0 {
                        s.qubits[q.0 as usize] |= 1u64 << shot;
                    }
                }
            }
            let dirty_before: Vec<u64> = dirty.iter().map(|q| s.qubits[q.0 as usize]).collect();
            s.apply_iter(b.ops.iter());
            assert_eq!(s.phase, 0);
            assert_eq!(s.qubits[event.0 as usize], 0, "event lane");
            for shot in 0..64usize {
                let h0 = batch * 32 + (shot & 31);
                let sig = (shot >> 5) & 1;
                assert_eq!(
                    get_u(&s.qubits, &h, shot),
                    get_u(&s.qubits, &ref_h, shot),
                    "h old={h0} sig={sig}"
                );
                assert_eq!(
                    get_u(&s.qubits, &log, shot),
                    get_u(&s.qubits, &ref_log, shot),
                    "log old={h0} sig={sig}"
                );
            }
            for (k, q) in dirty.iter().enumerate() {
                assert_eq!(s.qubits[q.0 as usize], dirty_before[k], "dirty lane {k}");
            }
            for q in ref_sc
                .d
                .iter()
                .chain(&ref_sc.tmp)
                .chain(&ref_sc.sp)
                .chain(std::iter::once(&ref_sc.e))
            {
                assert_eq!(s.qubits[q.0 as usize], 0, "reference scratch q{}", q.0);
            }
        }
    }
}

#[test]
fn lilypad_direct_terminal_flags_differential() {
    let mut b = B::new();

    let old_h = b.alloc_n(7);
    let old_sg = b.alloc();
    let old_cf2 = b.alloc();
    let old_d = b.alloc();
    let old_e = b.alloc();
    let old_qtop = b.alloc();
    let old_tmp = b.alloc_n(5);
    let (pq, z0, z1, y, wn) = (old_tmp[0], old_tmp[1], old_tmp[2], old_tmp[3], old_tmp[4]);
    let old_hl: Vec<(QubitId, bool)> = old_h[1..].iter().copied().map(|q| (q, true)).collect();
    let htemps = vec![z0, z1, y, wn];
    b.begin();
    b.mbu_compute(pq, &old_hl, &htemps);
    b.x(old_h[0]);
    b.and_c(pq, old_h[0], z0);
    b.x(old_h[0]);
    b.and_c(pq, old_h[0], z1);
    b.and_c(z0, old_sg, y);
    let old_ft = b.end();
    b.begin();
    b.cx(z1, y);
    b.x(old_cf2);
    b.and_c(y, old_cf2, old_d);
    b.x(old_cf2);
    b.cx(z1, y);
    let old_fd = b.end();
    b.begin();
    b.cx(z0, old_e);
    b.cx(y, old_e);
    b.cx(old_d, old_e);
    b.x(old_sg);
    b.ccx(old_h[6], old_sg, old_e);
    b.x(old_sg);
    let old_fe = b.end();
    b.play(&old_ft, false);
    b.play(&old_fd, false);
    b.play(&old_fe, false);
    b.cx(y, old_qtop);
    b.ccx(old_h[6], old_sg, old_qtop);
    b.play(&old_ft, true);

    let new_h = b.alloc_n(7);
    let new_sg = b.alloc();
    let new_cf2 = b.alloc();
    let new_d = b.alloc();
    let new_e = b.alloc();
    let new_qtop = b.alloc();
    let dirty = b.alloc_n(7);
    b.begin();
    let h0: Vec<(QubitId, bool)> = new_h.iter().copied().map(|q| (q, true)).collect();
    let mut y_d = h0.clone();
    y_d.extend([(new_sg, false), (new_cf2, true)]);
    super::mask::mc_xor(&mut b, &y_d, new_d, &[], &dirty);
    let mut h1_d = h0;
    h1_d[0].1 = false;
    h1_d.push((new_cf2, true));
    super::mask::mc_xor(&mut b, &h1_d, new_d, &[], &dirty);
    let new_fd = b.end();
    b.begin();
    let h0: Vec<(QubitId, bool)> = new_h.iter().copied().map(|q| (q, true)).collect();
    super::mask::mc_xor(&mut b, &h0, new_e, &[], &dirty);
    let mut y_e = h0;
    y_e.push((new_sg, false));
    super::mask::mc_xor(&mut b, &y_e, new_e, &[], &dirty);
    b.cx(new_d, new_e);
    super::mask::mc_xor(&mut b, &[(new_h[6], false), (new_sg, true)], new_e, &[], &dirty);
    let new_fe = b.end();
    b.play(&new_fd, false);
    b.play(&new_fe, false);
    let mut marker: Vec<(QubitId, bool)> = new_h.iter().copied().map(|q| (q, true)).collect();
    marker.push((new_sg, false));
    super::mask::mc_xor(&mut b, &marker, new_qtop, &[], &dirty);
    super::mask::mc_xor(&mut b, &[(new_h[6], false), (new_sg, false)], new_qtop, &[], &dirty);

    let old_keep = b.alloc_n(3);
    let new_keep = b.alloc_n(3);
    for (source, target) in [old_d, old_e, old_qtop].into_iter().zip(&old_keep) {
        b.cx(source, *target);
    }
    for (source, target) in [new_d, new_e, new_qtop].into_iter().zip(&new_keep) {
        b.cx(source, *target);
    }

    // Change every borrowed lane between direct compute and uncompute. An
    // arbitrary-dirty construction must still clear d/e and preserve the
    // changed dirty state exactly.
    for &q in &dirty {
        b.x(q);
    }
    b.play(&new_fe, true);
    b.play(&new_fd, true);
    b.play(&old_ft, false);
    b.play(&old_fe, true);
    b.play(&old_fd, true);
    b.play(&old_ft, true);

    for batch in 0usize..16 {
        let mut xr = xof(format!("lilypad-terminal-flags-{batch}").as_bytes());
        let mut s = Simulator::new(b.width() as usize, 1, &mut xr);
        for shot in 0..64usize {
            let assignment = batch * 64 + shot;
            let hv = assignment & 127;
            let sg = (assignment >> 7) & 1;
            let cf2 = (assignment >> 8) & 1;
            let qt = (assignment >> 9) & 1;
            for (k, (&oq, &nq)) in old_h.iter().zip(&new_h).enumerate() {
                if hv >> k & 1 != 0 {
                    s.qubits[oq.0 as usize] |= 1u64 << shot;
                    s.qubits[nq.0 as usize] |= 1u64 << shot;
                }
            }
            for q in if sg != 0 { [Some(old_sg), Some(new_sg)] } else { [None, None] }.into_iter().flatten() {
                s.qubits[q.0 as usize] |= 1u64 << shot;
            }
            for q in if cf2 != 0 { [Some(old_cf2), Some(new_cf2)] } else { [None, None] }.into_iter().flatten() {
                s.qubits[q.0 as usize] |= 1u64 << shot;
            }
            for q in if qt != 0 { [Some(old_qtop), Some(new_qtop)] } else { [None, None] }.into_iter().flatten() {
                s.qubits[q.0 as usize] |= 1u64 << shot;
            }
            for (k, q) in dirty.iter().enumerate() {
                if ((assignment * 0x6d + k * 0x2b) >> (k + 1)) & 1 != 0 {
                    s.qubits[q.0 as usize] |= 1u64 << shot;
                }
            }
        }
        let dirty_before: Vec<u64> = dirty.iter().map(|q| s.qubits[q.0 as usize] ^ u64::MAX).collect();
        s.apply_iter(b.ops.iter());
        assert_eq!(s.phase, 0, "batch={batch}");
        for shot in 0..64usize {
            assert_eq!(get_u(&s.qubits, &old_keep, shot), get_u(&s.qubits, &new_keep, shot), "batch={batch} shot={shot}");
            assert_eq!(get_u(&s.qubits, &[old_d, old_e], shot), 0, "old scratch");
            assert_eq!(get_u(&s.qubits, &[new_d, new_e], shot), 0, "new scratch");
        }
        for (k, q) in dirty.iter().enumerate() {
            assert_eq!(s.qubits[q.0 as usize], dirty_before[k], "dirty lane {k}");
        }
    }
}

#[test]
fn lilypad_direct_marker_clear_differential() {
    let mut b = B::new();

    let old_h = b.alloc_n(7);
    let old_cf1 = b.alloc();
    let old_qtop = b.alloc();
    let old_z = b.alloc();
    let old_y = b.alloc();
    let old_temps = b.alloc_n(5);
    let old_lits: Vec<(QubitId, bool)> = old_h.iter().copied().map(|q| (q, true)).collect();
    b.mbu_compute(old_z, &old_lits, &old_temps);
    b.and_c(old_z, old_cf1, old_y);
    b.cx(old_y, old_qtop);
    b.and_u(old_z, old_cf1, old_y);
    b.mbu_erase(old_z, &old_lits, &old_temps);

    let new_h = b.alloc_n(7);
    let new_cf1 = b.alloc();
    let new_qtop = b.alloc();
    let dirty = b.alloc_n(6);
    let mut marker: Vec<(QubitId, bool)> = new_h.iter().copied().map(|q| (q, true)).collect();
    marker.push((new_cf1, false));
    super::mask::mc_xor(&mut b, &marker, new_qtop, &[], &dirty);

    for batch in 0usize..8 {
        let mut xr = xof(format!("lilypad-marker-clear-{batch}").as_bytes());
        let mut s = Simulator::new(b.width() as usize, 1, &mut xr);
        for shot in 0..64usize {
            let assignment = batch * 64 + shot;
            let hv = assignment & 127;
            let cf1 = (assignment >> 7) & 1;
            let qt = (assignment >> 8) & 1;
            for (k, (&oq, &nq)) in old_h.iter().zip(&new_h).enumerate() {
                if hv >> k & 1 != 0 {
                    s.qubits[oq.0 as usize] |= 1u64 << shot;
                    s.qubits[nq.0 as usize] |= 1u64 << shot;
                }
            }
            if cf1 != 0 {
                s.qubits[old_cf1.0 as usize] |= 1u64 << shot;
                s.qubits[new_cf1.0 as usize] |= 1u64 << shot;
            }
            if qt != 0 {
                s.qubits[old_qtop.0 as usize] |= 1u64 << shot;
                s.qubits[new_qtop.0 as usize] |= 1u64 << shot;
            }
            for (k, q) in dirty.iter().enumerate() {
                if ((assignment * 0x47 + k * 0x19) >> (k + 1)) & 1 != 0 {
                    s.qubits[q.0 as usize] |= 1u64 << shot;
                }
            }
        }
        let dirty_before: Vec<u64> = dirty.iter().map(|q| s.qubits[q.0 as usize]).collect();
        s.apply_iter(b.ops.iter());
        assert_eq!(s.phase, 0, "batch={batch}");
        for shot in 0..64usize {
            assert_eq!(
                (s.qubits[old_qtop.0 as usize] >> shot) & 1,
                (s.qubits[new_qtop.0 as usize] >> shot) & 1,
                "batch={batch} shot={shot}"
            );
        }
        for q in [old_z, old_y].into_iter().chain(old_temps.iter().copied()) {
            assert_eq!(s.qubits[q.0 as usize], 0, "old scratch q{}", q.0);
        }
        for (k, q) in dirty.iter().enumerate() {
            assert_eq!(s.qubits[q.0 as usize], dirty_before[k], "dirty lane {k}");
        }
    }
}

#[test]
fn lilypad_finish_mask_stream_differential() {
    let mut b = B::new();
    let g = b.alloc_n(4);
    let e = b.alloc();
    let bsig = b.alloc_n(12);
    let q_old = b.alloc_n(12);
    let q_new = b.alloc_n(12);
    let q_direct = b.alloc_n(12);
    let tmp_old = b.alloc();
    let tmp_new = b.alloc();
    let d = b.alloc();
    let dirty = b.alloc_n(4);

    finish_mask(&mut b, &q_old, &bsig, &g, e, &[tmp_old], &[], Some(d));
    b.cx(e, q_new[10]);
    b.ccx(e, bsig[1], q_new[11]);
    b.cx(e, tmp_new);
    for l in 0..11usize {
        let c = l >> 2;
        let controls = [
            (e, false),
            (g[2], c & 1 == 0),
            (g[3], c & 2 == 0),
            (g[0], l & 1 == 0),
            (g[1], l & 2 == 0),
        ];
        super::mask::mc_xor(&mut b, &controls, tmp_new, &[], &q_new[..3]);
        if l + 2 < 12 {
            b.ccx(tmp_new, bsig[l + 2], q_new[l]);
        }
    }
    finish_mask_no_tmp(&mut b, &q_direct, &bsig, &g, e, &dirty);

    for batch in 0usize..8 {
        let mut xr = xof(format!("lilypad-finish-mask-stream-{batch}").as_bytes());
        let mut s = Simulator::new(b.width() as usize, 1, &mut xr);
        for shot in 0..64usize {
            let a = batch * 64 + shot;
            for (k, q) in g.iter().enumerate() {
                if a >> k & 1 != 0 { s.qubits[q.0 as usize] |= 1u64 << shot; }
            }
            if a >> 4 & 1 != 0 { s.qubits[e.0 as usize] |= 1u64 << shot; }
            if a >> 5 & 1 != 0 { s.qubits[bsig[1].0 as usize] |= 1u64 << shot; }
            if a >> 6 & 1 != 0 { s.qubits[bsig[2].0 as usize] |= 1u64 << shot; }
            for k in 3..12 {
                if ((a * 0x5d + k * 0x31) >> (k & 7)) & 1 != 0 {
                    s.qubits[bsig[k].0 as usize] |= 1u64 << shot;
                }
            }
            if a >> 7 & 1 != 0 {
                s.qubits[q_old[0].0 as usize] |= 1u64 << shot;
                s.qubits[q_new[0].0 as usize] |= 1u64 << shot;
                s.qubits[q_direct[0].0 as usize] |= 1u64 << shot;
            }
            if a >> 8 & 1 != 0 {
                s.qubits[q_old[11].0 as usize] |= 1u64 << shot;
                s.qubits[q_new[11].0 as usize] |= 1u64 << shot;
                s.qubits[q_direct[11].0 as usize] |= 1u64 << shot;
            }
            for (k, q) in dirty.iter().enumerate() {
                if ((a * 0x6d + k * 0x2b) >> (k + 1)) & 1 != 0 {
                    s.qubits[q.0 as usize] |= 1u64 << shot;
                }
            }
        }
        let dirty_before: Vec<u64> = dirty.iter().map(|q| s.qubits[q.0 as usize]).collect();
        s.apply_iter(b.ops.iter());
        assert_eq!(s.phase, 0, "batch={batch}");
        for k in 0..12 {
            assert_eq!(s.qubits[q_old[k].0 as usize], s.qubits[q_new[k].0 as usize], "batch={batch} q={k}");
            assert_eq!(s.qubits[q_old[k].0 as usize], s.qubits[q_direct[k].0 as usize], "batch={batch} direct q={k}");
        }
        assert_eq!(s.qubits[tmp_old.0 as usize], s.qubits[tmp_new.0 as usize], "batch={batch}: flag workspace");
        for (k, q) in dirty.iter().enumerate() {
            assert_eq!(s.qubits[q.0 as usize], dirty_before[k], "batch={batch}: dirty lane {k}");
        }
    }
}

#[test]
fn lilypad_crot_up2_dirty_differential() {
    for r in [1usize, 2, 4, 8] {
        let mut b = B::new();
        let c1 = b.alloc();
        let c2 = b.alloc();
        let q_old = b.alloc_n(12);
        let q_new = b.alloc_n(12);
        let tmp = b.alloc();
        let dirty = b.alloc_n(4);

        b.and_c(c1, c2, tmp);
        super::frogdrop::crot_up(&mut b, tmp, &q_old, r);
        b.and_u(c1, c2, tmp);
        crot_up2_dirty(&mut b, c1, c2, &q_new, r, &dirty);

        for batch in 0usize..8 {
            let mut xr = xof(format!("lilypad-crot-up2-dirty-{r}-{batch}").as_bytes());
            let mut s = Simulator::new(b.width() as usize, 1, &mut xr);
            for shot in 0..64usize {
                let a = batch * 64 + shot;
                if a & 1 != 0 { s.qubits[c1.0 as usize] |= 1u64 << shot; }
                if a & 2 != 0 { s.qubits[c2.0 as usize] |= 1u64 << shot; }
                for k in 0..12 {
                    if ((a * 0x9d + k * 0x53) >> (k & 7)) & 1 != 0 {
                        s.qubits[q_old[k].0 as usize] |= 1u64 << shot;
                        s.qubits[q_new[k].0 as usize] |= 1u64 << shot;
                    }
                }
                for (k, q) in dirty.iter().enumerate() {
                    if ((a * 0x6b + k * 0x37) >> (k + 2)) & 1 != 0 {
                        s.qubits[q.0 as usize] |= 1u64 << shot;
                    }
                }
            }
            let dirty_before: Vec<u64> = dirty.iter().map(|q| s.qubits[q.0 as usize]).collect();
            s.apply_iter(b.ops.iter());
            assert_eq!(s.phase, 0, "r={r} batch={batch}");
            assert_eq!(s.qubits[tmp.0 as usize], 0, "r={r} batch={batch}: tmp");
            for k in 0..12 {
                assert_eq!(
                    s.qubits[q_old[k].0 as usize],
                    s.qubits[q_new[k].0 as usize],
                    "r={r} batch={batch} q={k}"
                );
            }
            for (k, q) in dirty.iter().enumerate() {
                assert_eq!(s.qubits[q.0 as usize], dirty_before[k], "r={r} batch={batch}: dirty {k}");
            }
        }
    }
}

#[test]
fn lilypad_finish_mul_no_tmp_word_spec() {
    for width in 3usize..=12 {
        let mut b = B::new();
        let a = b.alloc_n(width - 1);
        let q = b.alloc_n(width);
        let e = b.alloc();
        let dirty = b.alloc_n(4);
        finish_mul_no_tmp(&mut b, &a, &q, e, &dirty);

        for batch in 0usize..16 {
            let mut xr = xof(format!("lilypad-finish-mul-no-tmp-{width}-{batch}").as_bytes());
            let mut s = Simulator::new(b.width() as usize, 1, &mut xr);
            for shot in 0..64usize {
                let row = batch * 64 + shot;
                for (k, x) in a.iter().enumerate() {
                    if ((row * 0x9d + k * 0x53) >> (k & 7)) & 1 != 0 {
                        s.qubits[x.0 as usize] |= 1u64 << shot;
                    }
                }
                for (k, x) in q.iter().enumerate() {
                    if ((row * 0x6d + k * 0x2b) >> ((k + 3) & 7)) & 1 != 0 {
                        s.qubits[x.0 as usize] |= 1u64 << shot;
                    }
                }
                if row & 1 != 0 { s.qubits[e.0 as usize] |= 1u64 << shot; }
                for (k, x) in dirty.iter().enumerate() {
                    if ((row * 0x47 + k * 0x19) >> (k + 1)) & 1 != 0 {
                        s.qubits[x.0 as usize] |= 1u64 << shot;
                    }
                }
            }
            let initial = s.qubits.clone();
            s.apply_iter(b.ops.iter());
            assert_eq!(s.phase, 0, "width={width} batch={batch}");
            for shot in 0..64usize {
                let av = a.iter().enumerate().fold(0u64, |v, (k, x)| {
                    v | (((initial[x.0 as usize] >> shot) & 1) << k)
                });
                let qv = q.iter().enumerate().fold(0u64, |v, (k, x)| {
                    v | (((initial[x.0 as usize] >> shot) & 1) << k)
                });
                let enabled = (initial[e.0 as usize] >> shot) & 1 != 0;
                let mask = (1u64 << width) - 1;
                let want = if enabled { qv.wrapping_mul(1 + 2 * av) & mask } else { qv };
                let got = q.iter().enumerate().fold(0u64, |v, (k, x)| {
                    v | (((s.qubits[x.0 as usize] >> shot) & 1) << k)
                });
                assert_eq!(got, want, "width={width} batch={batch} shot={shot} a={av} q={qv}");
            }
            for x in a.iter().chain(std::iter::once(&e)).chain(dirty.iter()) {
                assert_eq!(s.qubits[x.0 as usize], initial[x.0 as usize], "width={width} batch={batch} lane={}", x.0);
            }
        }
    }
}

#[test]
fn lilypad_page_codec_u_to_v_exact() {
    for width in 3usize..=13 {
        let mut b = B::new();
        let u = b.alloc_n(width);
        let u_roundtrip = b.alloc_n(width);
        let g = b.alloc_n(width);
        let f = b.alloc_n(width);
        let rho = b.alloc();
        let one = b.alloc();
        let dirty = b.alloc_n(12);
        b.x(one);

        page_codec_u_to_v(&mut b, &u, &g, &f, rho, one, &dirty);
        b.begin();
        page_codec_u_to_v(&mut b, &u_roundtrip, &g, &f, rho, one, &dirty);
        let codec = b.end();
        b.play(&codec, false);
        b.play(&codec, true);
        if matches!(width, 10 | 13) {
            let expected = super::tests_chunked::expected_t(&b.ops);
            eprintln!("page codec width={width}: three bodies expected_T={expected:.1}, per-body={:.1}", expected / 3.0);
        }

        for batch in 0usize..8 {
            let mut xr = xof(format!("lilypad-page-codec-{width}-{batch}").as_bytes());
            let mut s = Simulator::new(b.width() as usize, 1, &mut xr);
            for shot in 0..64usize {
                let row = batch * 64 + shot;
                let mask = (1u64 << width) - 1;
                let uv = (row as u64 * 0x19d + 0x53) & mask;
                let gv = ((row as u64 * 0x16b + 0x37) & mask) | 1;
                let fv = ((row as u64 * 0x12d + 0x2b) & mask) | 1;
                put(&mut s.qubits, &u, shot, N::from(uv));
                put(&mut s.qubits, &u_roundtrip, shot, N::from(uv));
                put(&mut s.qubits, &g, shot, N::from(gv));
                put(&mut s.qubits, &f, shot, N::from(fv));
                if row & 1 != 0 { s.qubits[rho.0 as usize] |= 1u64 << shot; }
                for (k, x) in dirty.iter().enumerate() {
                    if ((row * 0x47 + k * 0x19) >> (k + 1)) & 1 != 0 {
                        s.qubits[x.0 as usize] |= 1u64 << shot;
                    }
                }
            }
            let initial = s.qubits.clone();
            s.apply_iter(b.ops.iter());
            assert_eq!(s.phase, 0, "width={width} batch={batch}");
            let mask = (1u64 << width) - 1;
            let p = p().as_limbs()[0] & mask;
            for shot in 0..64usize {
                let read = |qs: &[QubitId], words: &[u64]| {
                    qs.iter().enumerate().fold(0u64, |v, (k, x)| {
                        v | (((words[x.0 as usize] >> shot) & 1) << k)
                    })
                };
                let uv = read(&u, &initial);
                let gv = read(&g, &initial);
                let fv = read(&f, &initial);
                let mut finv = 1u64;
                for _ in 0..width {
                    finv = finv.wrapping_mul(2u64.wrapping_sub(fv.wrapping_mul(finv))) & mask;
                }
                let signed_p = if (initial[rho.0 as usize] >> shot) & 1 != 0 {
                    (!p).wrapping_add(1) & mask
                } else {
                    p
                };
                let want = (gv.wrapping_mul(uv).wrapping_add(signed_p)).wrapping_mul(finv) & mask;
                assert_eq!(read(&u, &s.qubits), want, "width={width} batch={batch} shot={shot}");
                assert_eq!(read(&u_roundtrip, &s.qubits), uv, "roundtrip width={width} batch={batch} shot={shot}");
            }
            for x in g.iter().chain(f.iter()).chain(std::iter::once(&rho)).chain(dirty.iter()) {
                assert_eq!(s.qubits[x.0 as usize], initial[x.0 as usize], "width={width} batch={batch} lane={}", x.0);
            }
            assert_eq!(s.qubits[one.0 as usize], u64::MAX, "width={width} batch={batch}: one");
        }
    }
}

const TOP: usize = 383;
fn sar1(v: N) -> N {
    let top = N::from(1u64) << TOP;
    (v >> 1usize) | (v & top)
}
fn tcb(v: N) -> usize {
    if v.bit(TOP) {
        (!v).bit_len() + 1
    } else {
        v.bit_len() + 1
    }
}

#[derive(Clone, Debug)]
struct Pm {
    f: N,
    g: N,
    cf: N,
    cg: N,
    d2: i64,
    cur: Vec<(usize, u8)>,
    pend: Vec<(usize, u8)>,
    bad: Option<String>,
    nev: usize,
}

impl Pm {
    fn new(x: N) -> Pm {
        Pm { f: p(), g: x, cf: N::ZERO, cg: N::from(1u64), d2: 1, cur: vec![], pend: vec![], bad: None, nev: 0 }
    }
    fn tick(&mut self, t: usize, sch: &PSched, qb: usize) {
        if self.bad.is_some() {
            return;
        }
        let (kv, kc) = (sch.kv[t], sch.kc[t]);
        let e = self.g.bit(0);
        let sw = e && self.d2 > 0;
        let r = !sw && self.d2 < 0;
        let pre = [self.f, self.g, self.cf, self.cg];
        if sw {
            let (f, g, cf, cg) = (self.f, self.g, self.cf, self.cg);
            self.f = g;
            self.g = sar1(g.wrapping_sub(f));
            self.cf = cg << 1usize;
            self.cg = cg.wrapping_sub(cf);
            self.d2 = 2 - self.d2;
            let q = env_usize("LILYPAD_CAPQ", 0) as i64;
            if q > 0 && self.d2 <= -(2 * q - 1) {
                let o = (-(2 * q - 1) - self.d2) / 2;
                self.d2 = -(2 * q - 1);
                self.nev += 1;
                if o > 15 || self.nev > env_usize("LILYPAD_K", 2) {
                    self.bad = Some(format!("cap log overflow t {t}"));
                }
            }
        } else {
            let gn = if e { self.g.wrapping_add(self.f) } else { self.g };
            self.g = sar1(gn);
            if e {
                self.cg = self.cg.wrapping_add(self.cf);
            }
            self.cf <<= 1usize;
            self.d2 += 2;
        }
        let vw = [tcb(pre[0]), tcb(pre[1]), tcb(self.f), tcb(self.g) + 1].into_iter().max().unwrap();
        let cw = [tcb(pre[2]), tcb(pre[3]), tcb(sar1(self.cf)), tcb(self.cg)].into_iter().max().unwrap();
        if vw > kv || cw > kc {
            self.bad = Some(format!("width t {t}: v {vw}/{kv} c {cw}/{kc}"));
        }
        if t == sch.s && (tcb(self.f).max(tcb(self.g)) > sch.kv[t + 1] || tcb(self.cf).max(tcb(self.cg)) > sch.kc[t + 1]) {
            self.bad = Some("end width".into());
        }
        let h = (self.d2 - 1) / 2;
        if !(-64..=63).contains(&h) {
            self.bad = Some("h range".into());
        }
        // digit word (marker + digits), ring frame positions
        if sw {
            assert!(self.cur.is_empty(), "t {t}: swap inside a run");
            self.cur = vec![(t, 1)];
        } else if r {
            self.cur.push((t, e as u8));
        }
        if self.cur.iter().chain(self.pend.iter()).any(|&(tau, _)| t - tau >= qb) {
            self.bad = Some(format!("QB overflow t {t}"));
        }
        if sw && self.d2 == 1 {
            self.cur.clear();
        }
        if r && self.d2 == 1 {
            let ic = self.cur.len().saturating_sub(1);
            let deferred = t % 2 == 1;
            let tau = if deferred { (t + 1).min(sch.s) } else { t };
            let region = sch.w - sch.c[tau];
            if 2 * ic + 2 + usize::from(deferred) > region {
                self.bad = Some(format!("window overflow t {t}"));
            }
            if t % 2 == 0 {
                self.cur.clear();
            } else {
                self.pend = std::mem::take(&mut self.cur);
            }
        }
        if t % 2 == 0 {
            self.pend.clear();
        }
    }
    fn qval(&self, t: usize, qb: usize) -> u64 {
        self.cur.iter().chain(self.pend.iter()).map(|&(tau, bit)| (bit as u64) << (qb - 1 - (t - tau))).sum()
    }
}

fn rand_x(rng: &mut Rng) -> N {
    let mut v = rng.below(256) % p();
    if v == N::ZERO {
        v = N::from(3u64);
    }
    v
}

struct Setup {
    b: B,
    y: Vec<QubitId>,
    x: Vec<QubitId>,
    w: PWalk,
}

fn setup(sch: &PSched, qb: usize, with_y: bool, with_q: bool) -> Setup {
    let capq = env_usize("LILYPAD_CAPQ", 0);
    setup_with_capq(sch, qb, with_y, with_q, capq)
}

fn setup_with_capq(sch: &PSched, qb: usize, with_y: bool, with_q: bool, capq: usize) -> Setup {
    let mut b = B::new();
    let y = if with_y { b.alloc_n(256) } else { vec![] };
    let x = b.alloc_n(256);
    let mut a = x.clone();
    a.extend(b.alloc_n(sch.w - 256));
    let w = PWalk { a, bb: b.alloc_n(sch.w), q: if with_q { b.alloc_n(qb) } else { vec![] }, h: b.alloc_n(HB), capq,
        log: if capq > 0 { b.alloc_n(4 * env_usize("LILYPAD_K", 2)) } else { vec![] } };
    Setup { b, y, x, w }
}

fn decode(w: &PWalk, sch: &PSched, t: usize, st: &[u64], k: usize) -> (N, N, N, N, u64) {
    let c = sch.c[t];
    let xv: Vec<QubitId> = (0..c).map(|f| w.af(t, f)).collect();
    let xc: Vec<QubitId> = (0..sch.w - c).map(|s| w.asig(t, s)).collect();
    let yv: Vec<QubitId> = (0..c).map(|f| w.bf(f)).collect();
    let yc: Vec<QubitId> = (0..sch.w - c).map(|s| w.bsig(s)).collect();
    (get_s(st, &yv, k), get_s(st, &xv, k), get_s(st, &xc, k), get_s(st, &yc, k), get_u(st, &w.h, k))
}

fn sim<'a>(b: &B, xof: &'a mut sha3::Shake256Reader) -> Simulator<'a, sha3::Shake256Reader> {
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), xof)
}

fn xof(tag: &[u8]) -> sha3::Shake256Reader {
    let mut h = sha3::Shake256::default();
    h.update(tag);
    h.finalize_xof()
}

fn terminal_witness() -> N {
    let s = std::env::var("LILYPAD_X").unwrap_or_else(|_| "576d9924e2cf53d5f1c40cade115d639a7c3dbd1f3c764f069848459a53b1499".into());
    N::from_str_radix(s.trim_start_matches("0x"), 16).unwrap()
}

fn check_tick(w: &PWalk, sch: &PSched, t: usize, st: &[u64], ms: &[Pm], qb: usize, with_q: bool) -> usize {
    let mut nbad = 0;
    for (k, m) in ms.iter().enumerate() {
        if m.bad.is_some() {
            nbad += 1;
            continue;
        }
        let got = decode(w, sch, t + 1, st, k);
        let want = (m.f, m.g, m.cf, m.cg, (((m.d2 - 1) / 2) as u64) & 127);
        assert!(got == want, "tick {t} shot {k}:\n got {:?}\nwant {:?}", got, want);
        if with_q {
            assert_eq!(get_u(st, &w.qfr(t), k), m.qval(t, qb), "tick {t} shot {k}: Q (cur {:?} pend {:?})", m.cur, m.pend);
        }
    }
    nbad
}

/// Forward walk against the model every tick; scratch clean; per-tick expected Toffoli.
#[test]
#[ignore]
fn lilypad_fwd_check() {
    let sch = sched();
    let ticks = env_usize("LILYPAD_TICKS", sch.s);
    let room = env_usize("LILYPAD_ROOM", 24);
    let mut s0 = setup(&sch, 0, false, false);
    let sc = PScr::alloc_fwd(&mut s0.b, room);
    let Setup { mut b, x, w, .. } = s0;
    init(&mut b, &w);
    let mut bounds = vec![b.ops.len()];
    let m = b.fresh_bits(ticks + 1);
    for t in 1..=ticks {
        step_core(&mut b, &w, t, &sch, &sc, sc.e, &[], None);
        halve_h(&mut b, &w, t, &sch, &sc);
        b.hmr_to(sc.e, m[t]);
        bounds.push(b.ops.len());
    }
    let exp = super::tests_chunked::expected_t(&b.ops);
    eprintln!("lilypad fwd: {ticks} ticks, emitted {} expected {exp:.0} ({:.1}/tick), peak {}", b.tof, exp / ticks as f64, b.peak);
    let mut rng = Rng::new(env_usize("LILYPAD_SEED", 1) as u64);
    let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-fwd");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
    }
    let mut ms: Vec<Pm> = xs.iter().map(|&v| Pm::new(v)).collect();
    s.apply_iter(b.ops[..bounds[0]].iter());
    let scratch: Vec<QubitId> = [sc.e, sc.sg].iter().cloned().chain(sc.tmp.iter().cloned()).chain(sc.pool.iter().cloned()).collect();
    let mut nbad = 0;
    for t in 1..=ticks {
        s.apply_iter(b.ops[bounds[t - 1]..bounds[t]].iter());
        for m in ms.iter_mut() {
            m.tick(t, &sch, 64);
        }
        nbad = check_tick(&w, &sch, t, &s.qubits, &ms, 64, false);
        for &q in &scratch {
            assert_eq!(s.qubits[q.0 as usize] & ms.iter().enumerate().filter(|(_, m)| m.bad.is_none()).map(|(k, _)| 1u64 << k).sum::<u64>(), 0, "tick {t}: scratch dirty");
        }
    }
    let gzero = ms.iter().filter(|m| m.bad.is_none() && m.g == N::ZERO).count();
    eprintln!("lilypad fwd ok: {ticks} ticks, 64 shots match ({nbad} outside the envelope), g = 0 at the end on {gzero}");
}

/// The regenerating walk run forward: rings, h and Q (marker + digits, deferred erasures) match the model every
/// tick, phase 0, Q = 0 at the end.
#[test]
#[ignore]
fn lilypad_regen_check() {
    let sch = sched();
    let qb = env_usize("LILYPAD_QB", 20);
    let ticks = env_usize("LILYPAD_TICKS", sch.s);
    let room = env_usize("LILYPAD_ROOM", 24);
    let mut s0 = setup(&sch, qb, false, true);
    let sc = PScr::alloc_inv(&mut s0.b, room);
    let Setup { mut b, x, w, .. } = s0;
    init(&mut b, &w);
    let mut bounds = vec![b.ops.len()];
    let mut inv_cost = 0.0;
    for t in 1..=ticks {
        let (p1, p3) = rec_regen(&mut b, &w, t, &sch, &sc, None);
        inv_cost += b.measure(&p1, true) + b.measure(&p3, true);
        b.play(&p1, false);
        b.play(&p3, false);
        bounds.push(b.ops.len());
    }
    let exp = super::tests_chunked::expected_t(&b.ops);
    eprintln!("lilypad regen (qb {qb}): {ticks} ticks, played forward: emitted {} expected {exp:.0}; as the inverse walk plays it: {inv_cost:.0} ({:.1}/tick); peak {}",
        b.tof, inv_cost / ticks as f64, b.peak);
    let mut rng = Rng::new(env_usize("LILYPAD_SEED", 2) as u64);
    let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-regen");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
    }
    let mut ms: Vec<Pm> = xs.iter().map(|&v| Pm::new(v)).collect();
    s.apply_iter(b.ops[..bounds[0]].iter());
    let mut scratch: Vec<QubitId> = [sc.e, sc.sg].iter().cloned().chain(sc.tmp.iter().cloned()).chain(sc.pool.iter().cloned()).collect();
    scratch.extend(&sc.d);
    scratch.extend(&sc.sp);
    let mut nbad = 0;
    let mut erased = 0u64;
    for t in 1..=ticks {
        s.apply_iter(b.ops[bounds[t - 1]..bounds[t]].iter());
        for m in ms.iter_mut() {
            let had = !m.cur.is_empty() || !m.pend.is_empty();
            m.tick(t, &sch, qb);
            if had && m.cur.is_empty() && m.pend.is_empty() {
                erased += 1;
            }
        }
        nbad = check_tick(&w, &sch, t, &s.qubits, &ms, qb, true);
        let good: u64 = ms.iter().enumerate().filter(|(_, m)| m.bad.is_none()).map(|(k, _)| 1u64 << k).sum();
        for &q in &scratch {
            assert_eq!(s.qubits[q.0 as usize] & good, 0, "tick {t}: scratch q{} dirty", q.0);
        }
        assert_eq!(s.phase & good, 0, "tick {t}: phase");
    }
    let open = ms.iter().filter(|m| m.bad.is_none() && (!m.cur.is_empty() || !m.pend.is_empty())).count();
    eprintln!("lilypad regen ok: {ticks} ticks, 64 shots, Q/rings/h match every tick, phase 0, {erased} word erasures, {nbad} outside, {open} with an open word at the end");
}

/// Paired forward + inverse at a cap (y register live, as in the point add): round trip exact (x back, all else 0,
/// phase 0) and the expected Toffoli of each walk; SEC profile when LILYPAD_SEC is set.
#[test]
#[ignore]
fn lilypad_count() {
    use super::frogstrip::SEC;
    let sch = sched();
    let qb = env_usize("LILYPAD_QB", 20);
    let cap = env_usize("LILYPAD_CAP", 906) as u64;
    let prof = std::env::var("LILYPAD_SEC").is_ok();
    if prof {
        SEC.with(|s| *s.borrow_mut() = Some(Default::default()));
    }
    let s0 = setup(&sch, qb, true, false);
    let Setup { mut b, y, x, mut w } = s0;
    let live_f = b.live + 2 + NT as u64;
    let nev: usize = 0;
    let _ = nev;
    let room_f = cap.saturating_sub(live_f) as usize;
    let sc = PScr::alloc_fwd(&mut b, room_f);
    let div = b.new_division();
    let n0 = b.ops.len();
    let m = walk_forward(&mut b, &w, &sch, &sc, Some(div));
    let n1 = b.ops.len();
    sc.release(&mut b);
    let pk_f = b.peak;
    w.q = b.alloc_n(qb);
    let live_i = b.live + 3 + NT as u64 + SB as u64;
    let room_i = cap.saturating_sub(live_i) as usize;
    let sc = PScr::alloc_inv(&mut b, room_i);
    walk_inverse(&mut b, &w, &sch, &sc, &m, Some(div));
    let n2 = b.ops.len();
    b.close_division(div);
    let ef = super::tests_chunked::expected_t(&b.ops[n0..n1]);
    let ei = super::tests_chunked::expected_t(&b.ops[n1..n2]);
    eprintln!(
        "LILYPAD_COUNT W {} S {} qb {qb} cap {cap}: fwd live {live_f} pool {room_f} | inv live {live_i} pool {room_i} | fwd {ef:.0} ({:.1}/tick) inv {ei:.0} ({:.1}/tick) ratio {:.3} | peak fwd {pk_f} overall {}",
        sch.w, sch.s, ef / sch.s as f64, ei / sch.s as f64, ei / ef, b.peak
    );
    if prof {
        let mm = SEC.with(|s| s.borrow_mut().take().unwrap());
        for (k, (sum, n)) in &mm {
            eprintln!("SEC {k:14} total {sum:>10.0}  n {n:>5}  avg {:>8.1}", sum / *n as f64);
        }
    }
    if std::env::var("LILYPAD_NOSIM").is_ok() {
        return;
    }
    let mut rng = Rng::new(env_usize("LILYPAD_SEED", 3) as u64);
    let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let ys: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-count");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
        put(&mut s.qubits, &y, k, ys[k]);
    }
    s.apply_iter(b.ops.iter());
    let mut ms: Vec<Pm> = xs.iter().map(|&v| Pm::new(v)).collect();
    for t in 1..=sch.s {
        for mm in ms.iter_mut() {
            mm.tick(t, &sch, qb);
        }
    }
    let good: Vec<usize> = (0..64).filter(|&k| ms[k].bad.is_none() && ms[k].cur.is_empty() && ms[k].pend.is_empty()).collect();
    let gm: u64 = good.iter().map(|&k| 1u64 << k).sum();
    let mut other: Vec<QubitId> = w.a[256..].to_vec();
    other.extend(&w.bb);
    other.extend(&w.q);
    other.extend(&w.h);
    other.extend(&w.log);
    for &k in &good {
        assert_eq!(get_s(&s.qubits, &x, k) & ((N::from(1u64) << 256) - N::from(1u64)), xs[k], "shot {k}: x");
        assert_eq!(get_s(&s.qubits, &y, k) & ((N::from(1u64) << 256) - N::from(1u64)), ys[k], "shot {k}: y");
    }
    for &q in &other {
        assert_eq!(s.qubits[q.0 as usize] & gm, 0, "q{} dirty after the round trip", q.0);
    }
    assert_eq!(s.phase & gm, 0, "round-trip phase");
    eprintln!("lilypad round trip ok on {} / 64 shots (rest outside the envelope / QB)", good.len());
}

fn build_roundtrip(sch: &PSched, qb: usize, cap: u64) -> (B, Vec<QubitId>, Vec<QubitId>) {
    let Setup { mut b, y, x, mut w } = setup(sch, qb, true, false);
    let room_f = cap.saturating_sub(b.live + 2 + NT as u64) as usize;
    let sc = PScr::alloc_fwd(&mut b, room_f);
    let div = b.new_division();
    let m = walk_forward(&mut b, &w, sch, &sc, Some(div));
    sc.release(&mut b);
    w.q = b.alloc_n(qb);
    let room_i = cap.saturating_sub(b.live + 3 + NT as u64 + SB as u64) as usize;
    let sc = PScr::alloc_inv(&mut b, room_i);
    walk_inverse(&mut b, &w, sch, &sc, &m, Some(div));
    b.close_division(div);
    (b, x, y)
}

fn verify_roundtrip_batch(
    b: &B,
    x: &[QubitId],
    y: &[QubitId],
    sch: &PSched,
    qb: usize,
    xs: &[N],
    ys: &[N],
    tag: &[u8],
) -> (usize, usize) {
    let mut xr = xof(tag);
    let mut s = sim(b, &mut xr);
    for k in 0..xs.len() {
        put(&mut s.qubits, x, k, xs[k]);
        put(&mut s.qubits, y, k, ys[k]);
    }
    s.apply_iter(b.ops.iter());
    let mut models: Vec<Pm> = xs.iter().map(|&v| Pm::new(v)).collect();
    for t in 1..=sch.s {
        for m in &mut models {
            m.tick(t, sch, qb);
        }
    }
    for m in &mut models {
        if m.bad.is_none() && m.g != N::ZERO {
            m.bad = Some("overrun".into());
        }
    }
    let good: Vec<usize> = (0..xs.len()).filter(|&k| models[k].bad.is_none()).collect();
    let gm: u64 = good.iter().map(|&k| 1u64 << k).sum();
    let mask = (N::from(1u64) << 256) - N::from(1u64);
    for &k in &good {
        assert_eq!(get_s(&s.qubits, x, k) & mask, xs[k], "shot {k}: x");
        assert_eq!(get_s(&s.qubits, y, k) & mask, ys[k], "shot {k}: y");
    }
    let mut data = vec![false; s.qubits.len()];
    for q in x.iter().chain(y.iter()) {
        data[q.0 as usize] = true;
    }
    for (i, row) in s.qubits.iter().enumerate() {
        if !data[i] {
            assert_eq!(*row & gm, 0, "ancilla q{i} dirty");
        }
    }
    assert_eq!(s.phase & gm, 0, "round-trip phase");
    (good.len(), xs.len() - good.len())
}

/// First gate-level q=11 campaign: at least 10k random secp256k1 inputs.
/// Predicted envelope/QB/log failures are counted; every other shot must be
/// value-, ancilla-, and phase-exact.
#[test]
#[ignore]
fn lilypad_design_d_roundtrip_10k() {
    let sch = sched();
    let qb = env_usize("LILYPAD_QB", 13);
    let cap = env_usize("LILYPAD_CAP", 893) as u64;
    let (b, x, y) = build_roundtrip(&sch, qb, cap);
    let mut rng = Rng::new(env_usize("LILYPAD_SEED", 0x11d) as u64);
    let mut checked = 0;
    let mut predicted = 0;
    for batch in 0..157usize {
        let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
        let ys: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
        let tag = format!("lilypad-q11-10k-{batch}");
        let (g, p) = verify_roundtrip_batch(&b, &x, &y, &sch, qb, &xs, &ys, tag.as_bytes());
        checked += g;
        predicted += p;
    }
    eprintln!("lilypad q11 10k: {checked} exact, {predicted} predicted approximation failures, total {}", checked + predicted);
    assert_eq!(checked + predicted, 10_048);
}

/// Cofactor-favoring split edge cases and a classical search for runs still
/// open at S.  Every selected input is then checked through the real gate walk.
#[test]
#[ignore]
fn lilypad_edge_inputs() {
    let sch = sched();
    let qb = env_usize("LILYPAD_QB", 13);
    let cap = env_usize("LILYPAD_CAP", 893) as u64;
    let (b, x, y) = build_roundtrip(&sch, qb, cap);
    let mut xs = vec![];
    let mut edge_rng = Rng::new(0xc0fa_c701u64);
    for k in 15..=19 {
        for _ in 0..4 {
            let odd = (rand_x(&mut edge_rng) >> k) | N::from(1u64);
            xs.push(odd << k);
        }
    }
    let mut rng = Rng::new(0x6e64_7275_6eu64);
    let mut scanned = 0usize;
    let mut open = 0usize;
    while scanned < 1_500_000 && open < 8 {
        let v = rand_x(&mut rng);
        let mut m = Pm::new(v);
        for t in 1..=sch.s {
            m.tick(t, &sch, qb);
        }
        if m.bad.is_none() && (!m.cur.is_empty() || !m.pend.is_empty()) {
            xs.push(v);
            open += 1;
        }
        scanned += 1;
    }
    assert!(open > 0, "no terminal-open-run witness in {scanned} inputs");
    let ys: Vec<N> = (0..xs.len()).map(|i| N::from((i + 17) as u64)).collect();
    let (g, pred) = verify_roundtrip_batch(&b, &x, &y, &sch, qb, &xs, &ys, b"lilypad-edge-inputs");
    eprintln!("lilypad edge inputs: {g} exact, {pred} predicted failures, {open} terminal-open witnesses from {scanned} scanned");
    assert_eq!(g, xs.len());
}

#[test]
#[ignore]
fn lilypad_terminal_word_trace() {
    let sch = sched();
    let qb = env_usize("LILYPAD_QB", 13);
    let cap = env_usize("LILYPAD_CAP", 893) as u64;
    let Setup { mut b, x, y, mut w } = setup(&sch, qb, true, false);
    let room_f = cap.saturating_sub(b.live + 2 + NT as u64) as usize;
    let sf = PScr::alloc_fwd(&mut b, room_f);
    let div = b.new_division();
    walk_forward(&mut b, &w, &sch, &sf, Some(div));
    sf.release(&mut b);
    let nf = b.ops.len();
    w.q = b.alloc_n(qb);
    let room_i = cap.saturating_sub(b.live + 3 + NT as u64 + SB as u64) as usize;
    let si = PScr::alloc_inv(&mut b, room_i);
    let tb = terminal_eraser(&mut b, &w, &sch, &si);
    let xval = terminal_witness();
    let mut pm = Pm::new(xval);
    for t in 1..=sch.s {
        pm.tick(t, &sch, qb);
    }
    let qwant = pm.qval(sch.s, qb);
    let mut xr = xof(b"lilypad-terminal-word-trace");
    let mut s = sim(&b, &mut xr);
    put(&mut s.qubits, &x, 0, xval);
    put(&mut s.qubits, &y, 0, N::from(17u64));
    s.apply_iter(b.ops[..nf].iter());
    let hend = get_u(&s.qubits, &w.h, 0);
    let mut qs = vec![];
    for end in [tb[1], tb[2], tb[3], b.ops.len()] {
        let start = if qs.is_empty() { nf } else { [tb[1], tb[2], tb[3]][qs.len() - 1] };
        s.apply_iter(b.ops[start..end].iter());
        qs.push(get_u(&s.qubits, &w.qfr(sch.s), 0));
    }
    let qgot = *qs.last().unwrap();
    eprintln!("terminal trace: h={hend} Q(word/rot/mul/final)={qs:?} want={qwant} phase={}", s.phase & 1);
    assert_eq!(qgot, qwant);
}

#[test]
#[ignore]
fn lilypad_terminal_integrated_trace() {
    let sch = sched();
    let qb = env_usize("LILYPAD_QB", 13);
    let cap = env_usize("LILYPAD_CAP", 893) as u64;
    let Setup { mut b, x, y, mut w } = setup(&sch, qb, true, false);
    let room_f = cap.saturating_sub(b.live + 2 + NT as u64) as usize;
    let sf = PScr::alloc_fwd(&mut b, room_f);
    let div = b.new_division();
    let meas = walk_forward(&mut b, &w, &sch, &sf, Some(div));
    sf.release(&mut b);
    let nf = b.ops.len();
    w.q = b.alloc_n(qb);
    let room_i = cap.saturating_sub(b.live + 3 + NT as u64 + SB as u64) as usize;
    let si = PScr::alloc_inv(&mut b, room_i);
    let (p1, p3) = rec_regen(&mut b, &w, sch.s, &sch, &si, Some(div));
    b.play(&p3, true);
    let np3 = b.ops.len();
    b.z_if(w.qfr(sch.s)[qb - 1], meas[sch.s]);
    let nz = b.ops.len();
    b.play(&p1, true);
    let nstep = b.ops.len();
    let (p1b, p3b) = rec_regen(&mut b, &w, sch.s - 1, &sch, &si, Some(div));
    b.play(&p3b, true);
    let np3b = b.ops.len();
    b.z_if(w.qfr(sch.s - 1)[qb - 1], meas[sch.s - 1]);
    let nzb = b.ops.len();
    b.play(&p1b, true);
    let nstepb = b.ops.len();
    let xval = terminal_witness();
    let mut xr = xof(b"lilypad-terminal-integrated-trace");
    let mut s = sim(&b, &mut xr);
    put(&mut s.qubits, &x, 0, xval);
    put(&mut s.qubits, &y, 0, N::from(17u64));
    s.apply_iter(b.ops[..nf].iter());
    let mut vals = vec![];
    for (lo, hi) in [(nf, np3), (np3, nz), (nz, nstep)] {
        s.apply_iter(b.ops[lo..hi].iter());
        vals.push((get_u(&s.qubits, &w.qfr(sch.s), 0), get_u(&s.qubits, &w.h, 0), s.phase & 1));
    }
    let mut vals_b = vec![];
    for (lo, hi) in [(nstep, np3b), (np3b, nzb), (nzb, nstepb)] {
        s.apply_iter(b.ops[lo..hi].iter());
        vals_b.push((get_u(&s.qubits, &w.qfr(sch.s - 1), 0), get_u(&s.qubits, &w.h, 0), s.phase & 1));
    }
    let scratch: Vec<QubitId> = [si.e, si.sg]
        .into_iter()
        .chain(si.d.iter().copied())
        .chain(si.tmp.iter().copied())
        .chain(si.sp.iter().copied())
        .chain(si.pool.iter().copied())
        .collect();
    let dirty: Vec<u64> = scratch.iter().filter(|q| s.qubits[q.0 as usize] & 1 != 0).map(|q| q.0).collect();
    eprintln!("terminal integrated t532={vals:?} t531={vals_b:?}; dirty scratch={dirty:?}");
    assert_eq!(vals[0].0, 3 << (qb - 2));
    assert_eq!(vals[2].0, 1 << (qb - 2));
    assert_eq!(vals_b[0].0, 1 << (qb - 1));
    assert_eq!(vals_b[2].0, 0);
    assert!(dirty.is_empty());
}

#[test]
#[ignore]
fn lilypad_terminal_full_inverse_trace() {
    let sch = sched();
    let qb = env_usize("LILYPAD_QB", 13);
    let cap = env_usize("LILYPAD_CAP", 893) as u64;
    let Setup { mut b, x, y, mut w } = setup(&sch, qb, true, false);
    let room_f = cap.saturating_sub(b.live + 2 + NT as u64) as usize;
    let sf = PScr::alloc_fwd(&mut b, room_f);
    let div = b.new_division();
    let meas = walk_forward(&mut b, &w, &sch, &sf, Some(div));
    sf.release(&mut b);
    let nf = b.ops.len();
    w.q = b.alloc_n(qb);
    let room_i = cap.saturating_sub(b.live + 3 + NT as u64 + SB as u64) as usize;
    let si = PScr::alloc_inv(&mut b, room_i);
    let mut bounds = vec![];
    for t in (1..=sch.s).rev() {
        let lo = b.ops.len();
        let (p1, p3) = rec_regen(&mut b, &w, t, &sch, &si, Some(div));
        b.play(&p3, true);
        b.z_if(w.qfr(t)[qb - 1], meas[t]);
        b.play(&p1, true);
        bounds.push((t, lo, b.ops.len()));
    }
    let xval = terminal_witness();
    let mut hist = vec![Pm::new(xval)];
    for t in 1..=sch.s {
        let mut m = hist.last().unwrap().clone();
        m.tick(t, &sch, qb);
        hist.push(m);
    }
    let mut xr = xof(b"lilypad-terminal-full-inverse-trace");
    let mut s = sim(&b, &mut xr);
    put(&mut s.qubits, &x, 0, xval);
    put(&mut s.qubits, &y, 0, N::from(17u64));
    s.apply_iter(b.ops[..nf].iter());
    for (t, lo, hi) in bounds {
        s.apply_iter(b.ops[lo..hi].iter());
        let got = decode(&w, &sch, t, &s.qubits, 0);
        let m = &hist[t - 1];
        let want = (m.f, m.g, m.cf, m.cg, (m.d2.div_euclid(2) as u64) & 127);
        if got != want {
            eprintln!("first inverse mismatch after tick {t}: Q={} phase={}\n got={got:?}\nwant={want:?}", get_u(&s.qubits, &w.qfr(t), 0), s.phase & 1);
            panic!("inverse mismatch at tick {t}");
        }
    }
    eprintln!("terminal full inverse trace exact; phase={}", s.phase & 1);
}

#[test]
#[ignore]
fn lilypad_c6_reference_corpus() {
    let sch = sched();
    let qb = env_usize("LILYPAD_QB", 13);
    let cap = env_usize("LILYPAD_CAP", 893) as u64;
    let path = std::env::var("LILYPAD_C6_CORPUS").expect("LILYPAD_C6_CORPUS");
    let xs: Vec<N> = std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .filter_map(|l| l.split_whitespace().next())
        .filter(|s| s.starts_with("0x"))
        .map(|s| N::from_str_radix(&s[2..], 16).unwrap())
        .collect();
    assert!(!xs.is_empty() && xs.len() <= 64);
    let ys: Vec<N> = (0..xs.len()).map(|i| N::from((i + 101) as u64)).collect();
    let (b, x, y) = build_roundtrip(&sch, qb, cap);
    let (good, predicted) = verify_roundtrip_batch(&b, &x, &y, &sch, qb, &xs, &ys, b"lilypad-c6-reference-corpus");
    eprintln!("Lilypad C6 auditor corpus: {good} exact, {predicted} predicted failures");
    assert_eq!(good + predicted, xs.len());
}

#[test]
#[ignore]
fn lilypad_recorded_input_replay() {
    let sch = sched();
    let qb = env_usize("LILYPAD_QB", 20);
    let cap = env_usize("LILYPAD_CAP", 920) as u64;
    let dir = std::env::var("LILYPAD_REPLAY_DIR").expect("LILYPAD_REPLAY_DIR");
    let mut xs: Vec<N> = vec![];
    for ent in std::fs::read_dir(dir).unwrap() {
        let path = ent.unwrap().path();
        if path.extension().and_then(|s| s.to_str()) != Some("json") {
            continue;
        }
        let txt = std::fs::read_to_string(path).unwrap();
        for (i, _) in txt.match_indices("0x") {
            let h: String = txt[i + 2..].chars().take_while(|c| c.is_ascii_hexdigit()).collect();
            if h.len() == 64 {
                let x = N::from_str_radix(&h, 16).unwrap();
                if !xs.contains(&x) {
                    xs.push(x);
                }
            }
        }
    }
    assert!(!xs.is_empty());
    let (b, x, y) = build_roundtrip(&sch, qb, cap);
    let mut exact = 0;
    let mut predicted = 0;
    for (batch, ch) in xs.chunks(64).enumerate() {
        let ys: Vec<N> = (0..ch.len()).map(|i| N::from((1000 + batch * 64 + i) as u64)).collect();
        let tag = format!("lilypad-recorded-replay-{batch}");
        let (g, p) = verify_roundtrip_batch(&b, &x, &y, &sch, qb, ch, &ys, tag.as_bytes());
        exact += g;
        predicted += p;
    }
    eprintln!("Lilypad recorded replay: {} inputs, {exact} exact, {predicted} predicted", xs.len());
    assert_eq!(exact + predicted, xs.len());
}

#[test]
#[ignore]
fn lilypad_endpoint_adapter() {
    let mut b = B::new();
    let y = b.alloc_n(256);
    let x = b.alloc_n(256);
    let dv = pointadd_lilypad::div_forward(&mut b, &x, &y);
    let inv = dv.inv.clone();
    let key = dv.key;
    let cleared_y = dv.w.bb.clone();
    let sch = dv.sch.clone();
    let mut rng = Rng::new(0x1eaf_ada7u64);
    let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let ys: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-endpoint-adapter");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
        put(&mut s.qubits, &y, k, ys[k]);
    }
    s.apply_iter(b.ops.iter());
    let p = p();
    let two_s = N::from(2u64).pow_mod(N::from(sch.s as u64), p);
    let mut exact = 0usize;
    for k in 0..64 {
        let mut m = Pm::new(xs[k]);
        for t in 1..=sch.s {
            m.tick(t, &sch, 13);
        }
        if m.bad.is_some() || m.g != N::ZERO {
            continue;
        }
        exact += 1;
        let c = get_s(&s.qubits, &inv, k);
        let cmod = if c.bit(TOP) {
            let a = (!c).wrapping_add(N::from(1u64)) % p;
            if a == N::ZERO { N::ZERO } else { p - a }
        } else {
            c % p
        };
        let got = cmod.mul_mod(xs[k], p);
        let neg = (s.qubits[key.0 as usize] >> k) & 1 != 0;
        let want = if neg { p - two_s } else { two_s };
        assert_eq!(got, want, "shot {k}: endpoint relation");
        for &q in &cleared_y {
            assert_eq!((s.qubits[q.0 as usize] >> k) & 1, 0, "shot {k}: endpoint Y q{}", q.0);
        }
    }
    eprintln!("Lilypad endpoint adapter: {exact}/64 exact within the registered envelope");
    assert!(exact >= 60);
}

#[test]
#[ignore]
fn lilypad_one_division() {
    let mut b = B::new();
    let x = b.alloc_n(256);
    let y = b.alloc_n(256);
    pointadd_lilypad::one_division_probe(&mut b, &x, &y);
    let expected_t = super::tests_chunked::expected_t(&b.ops);
    eprintln!("Lilypad one division: peak {} expected T {expected_t:.0} ops {}", b.peak, b.ops.len());
    let sch = pointadd_lilypad::sched();
    let mut rng = Rng::new(0x1d1f_1510u64);
    let mut xs = vec![];
    while xs.len() < 64 {
        let v = rand_x(&mut rng);
        let mut m = Pm::new(v);
        for t in 1..=sch.s { m.tick(t, &sch, 13); }
        if m.bad.is_none() && m.g == N::ZERO { xs.push(v); }
    }
    let ys: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-one-division");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
        put(&mut s.qubits, &y, k, ys[k]);
    }
    s.apply_iter(b.ops.iter());
    let pm = p();
    for k in 0..64 {
        let got_x = get_s(&s.qubits, &x, k) & ((N::from(1u64) << 256) - N::from(1u64));
        let got_y = get_s(&s.qubits, &y, k) & ((N::from(1u64) << 256) - N::from(1u64));
        let want_y = ys[k].mul_mod(xs[k].pow_mod(pm - N::from(2u64), pm), pm);
        assert_eq!(got_x, xs[k], "shot {k}: dx");
        assert_eq!(got_y, want_y, "shot {k}: lambda");
    }
    let mut data = vec![false; s.qubits.len()];
    for q in x.iter().chain(y.iter()) { data[q.0 as usize] = true; }
    for (i, row) in s.qubits.iter().enumerate() {
        if !data[i] { assert_eq!(*row, 0, "ancilla q{i}"); }
    }
    assert_eq!(s.phase, 0, "one-division phase");
}

fn lilypad_curve() -> crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve {
    type U = ruint::aliases::U256;
    let hx = |h: &str| U::from_str_radix(h, 16).unwrap();
    crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve {
        modulus: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
        a: U::ZERO,
        b: U::from(7u64),
        gx: hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
        gy: hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
        order: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
    }
}

#[test]
#[ignore]
fn lilypad_point_add_end_to_end() {
    if let Ok(cap) = std::env::var("LILYPAD_E2E_CAP") {
        pointadd_lilypad::test_peak(Some(cap.parse().unwrap()));
    }
    let mut b = B::new();
    let (xq, yq) = pointadd_lilypad::point_add(&mut b);
    let ops = std::mem::take(&mut b.ops);
    let (nq, nb, _, regs) = analyze_ops(ops.iter());
    let analytic = super::tests_chunked::expected_t(&ops);
    eprintln!("Lilypad point add: ops {} qubits {nq} allocator peak {} analytic T {analytic:.0}", ops.len(), b.peak);
    assert!(nq <= 893 && b.peak <= 893);
    let curve = lilypad_curve();
    let to_u = |v: &N| -> ruint::aliases::U256 { ruint::aliases::U256::from_limbs(v.as_limbs()[0..4].try_into().unwrap()) };
    let mut rng = Rng::new(0x1a1d_2026u64);
    let mut cases = vec![];
    while cases.len() < 64 {
        let k1 = to_u(&(rng.below(250) + N::from(1u64)));
        let k2 = to_u(&(rng.below(250) + N::from(1u64)));
        let t = curve.mul(curve.gx, curve.gy, k1);
        let o = curve.mul(curve.gx, curve.gy, k2);
        if t.0 == o.0 { continue; }
        let e = curve.add(t.0, t.1, o.0, o.1);
        cases.push((t, o, e));
    }
    let mut h = sha3::Shake256::default();
    h.update(b"lilypad-point-add-e2e");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new(nq as usize, nb as usize, &mut xof);
    for (k, (t, o, _)) in cases.iter().enumerate() {
        s.set_register(&regs[0], t.0, k);
        s.set_register(&regs[1], t.1, k);
        s.set_register(&regs[2], o.0, k);
        s.set_register(&regs[3], o.1, k);
    }
    s.apply_iter(ops.iter());
    for (k, (_, _, e)) in cases.iter().enumerate() {
        assert_eq!(s.get_register(&regs[0], k), e.0, "shot {k}: x3");
        assert_eq!(s.get_register(&regs[1], k), e.1, "shot {k}: y3");
    }
    assert_eq!(s.phase, 0, "point-add phase");
    let data: std::collections::HashSet<u64> = xq.iter().chain(yq.iter()).map(|q| q.0).collect();
    for q in 0..nq {
        if !data.contains(&q) { assert_eq!(s.qubits[q as usize], 0, "ancilla q{q}"); }
    }
    eprintln!("Lilypad point add exact 64/64; avg executed T {}", s.stats.toffoli_gates / 64);
    pointadd_lilypad::test_peak(None);
}

/// Replay one explicit affine point-addition witness at one or more peak caps.
/// This is a diagnostic bridge between a salted full-circuit failure and the
/// per-division Lilypad replay, and deliberately has no production selector.
#[test]
#[ignore]
fn lilypad_point_add_witness() {
    type U = ruint::aliases::U256;
    let vals: Vec<U> = std::env::var("LILYPAD_PA_CASE")
        .expect("LILYPAD_PA_CASE=tx,ty,ox,oy")
        .split(',')
        .map(|v| U::from_str_radix(v.trim().trim_start_matches("0x"), 16).unwrap())
        .collect();
    assert_eq!(vals.len(), 4);
    let caps: Vec<u64> = std::env::var("LILYPAD_PA_CAPS")
        .unwrap_or_else(|_| pointadd_lilypad::PEAK0.to_string())
        .split(',')
        .map(|v| v.parse().unwrap())
        .collect();
    let curve = lilypad_curve();
    let expected = curve.add(vals[0], vals[1], vals[2], vals[3]);
    if let Ok(value) = std::env::var("LILYPAD_PA_L1") {
        let enabled = value != "0";
        pointadd_lilypad::test_layer_overrides(Some(enabled), Some(enabled));
    }
    if let Ok(value) = std::env::var("LILYPAD_PA_L2") {
        super::lilypad_g::test_l2_override(Some(value != "0"));
    }
    if let Ok(value) = std::env::var("LILYPAD_PA_L5") {
        super::lilypad_g::test_l5_override(Some(value != "0"));
    }

    for cap in caps {
        pointadd_lilypad::test_peak(Some(cap));
        let mut b = B::new();
        let (xq, yq) = pointadd_lilypad::point_add(&mut b);
        let ops = std::mem::take(&mut b.ops);
        let (nq, nb, _, regs) = analyze_ops(ops.iter());
        let mut xr = xof(format!("lilypad-pa-witness-{cap}").as_bytes());
        let mut s = Simulator::new(nq as usize, nb as usize, &mut xr);
        s.set_register(&regs[0], vals[0], 0);
        s.set_register(&regs[1], vals[1], 0);
        s.set_register(&regs[2], vals[2], 0);
        s.set_register(&regs[3], vals[3], 0);
        s.apply_iter(ops.iter());
        let got = (s.get_register(&regs[0], 0), s.get_register(&regs[1], 0));
        let data: std::collections::HashSet<u64> = xq.iter().chain(yq.iter()).map(|q| q.0).collect();
        let dirty: Vec<_> = (0..nq)
            .filter(|q| !data.contains(q) && (s.qubits[*q as usize] & 1) != 0)
            .collect();
        eprintln!(
            "LILYPAD_PA_WITNESS cap={cap} peak={} value_ok={} phase={} dirty={} got=({:#x},{:#x}) expected=({:#x},{:#x})",
            b.peak,
            got == expected,
            s.phase & 1,
            dirty.len(),
            got.0,
            got.1,
            expected.0,
            expected.1
        );
    }
    pointadd_lilypad::test_peak(None);
    pointadd_lilypad::test_layer_overrides(None, None);
    super::lilypad_g::test_l2_override(None);
    super::lilypad_g::test_l5_override(None);
}

/// Stable raw-stream fingerprint used by the layered optimization gates. The
/// top-level nonce tail is outside this builder, so equal digests prove that a
/// disabled layer leaves the complete point-add body byte-for-byte unchanged.
#[test]
#[ignore]
fn lilypad_raw_stream_digest() {
    let mut b = B::new();
    let _ = pointadd_lilypad::point_add(&mut b);
    let mut h = <sha3::Sha3_256 as sha3::Digest>::new();
    for op in &b.ops {
        sha3::Digest::update(&mut h, [op.kind as u8]);
        for v in [
            op.q_control2.0,
            op.q_control1.0,
            op.q_target.0,
            op.c_target.0,
            op.c_condition.0,
            op.r_target.0,
        ] {
            sha3::Digest::update(&mut h, v.to_le_bytes());
        }
    }
    let digest = sha3::Digest::finalize(h);
    eprintln!("LILYPAD_RAW_SHA3_256={digest:x} ops={} peak={} expected_t={:.1}",
        b.ops.len(), b.peak, b.tof as f64 - b.tof_cond as f64 / 2.0);
}

#[test]
#[ignore]
fn lilypad_layered_peak_sweep() {
    let caps: Vec<u64> = std::env::var("LILYPAD_LAYER_CAPS")
        .unwrap_or_else(|_| "893,889,885,881,877,873".into())
        .split(',')
        .map(|s| s.parse().unwrap())
        .collect();
    for cap in caps {
        pointadd_lilypad::test_peak(Some(cap));
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut b = B::new();
            let _ = pointadd_lilypad::point_add(&mut b);
            let expected = super::tests_chunked::expected_t(&b.ops);
            eprintln!(
                "LOWQ_SWEEP requested={cap} actual_peak={} qubits={} expected_t={expected:.1} ops={}",
                b.peak,
                analyze_ops(b.ops.iter()).0,
                b.ops.len()
            );
        }));
        if result.is_err() {
            eprintln!("LOWQ_SWEEP requested={cap} BUILD_FAILED");
        }
        pointadd_lilypad::test_peak(None);
    }
}

#[test]
#[ignore]
fn lilypad_q890_window_sweep() {
    pointadd_lilypad::test_peak(Some(890));
    for wm in [66usize, 65, 64, 63, 62, 61, 60] {
        super::modp_ft::test_signed_wm_max(Some(wm));
        let mut b = B::new();
        let _ = pointadd_lilypad::point_add(&mut b);
        let expected = super::tests_chunked::expected_t(&b.ops);
        eprintln!("LOWQ_WM cap=890 wm_max={wm} peak={} expected_t={expected:.1} ops={}", b.peak, b.ops.len());
    }
    super::modp_ft::test_signed_wm_max(None);
    pointadd_lilypad::test_peak(None);
}

#[test]
#[ignore]
fn lilypad_layers_phase_witness() {
    type U = ruint::aliases::U256;
    let hx = |s: &str| U::from_str_radix(s, 16).unwrap();
    let t = (
        hx("2e29985a142ec0b528ce20c32d01e6740add40cd7b7f024cb3be5c1ffe2f45f5"),
        hx("a9e58767c1db0814c92a8f8a18c5110d072cffdb7175b06fab62eae39ca84800"),
    );
    let o = (
        hx("81338ceb22e3d0b6637e9ef36feada8b8623f51411f35c29f1ba744470c93678"),
        hx("7a93e397f1658fd916f15460d3cc8e729a79e62ee3574108d881bf4482c6019b"),
    );
    let expected = lilypad_curve().add(t.0, t.1, o.0, o.1);
    for &(name, l1, l2, l3) in &[
        ("base", false, false, false),
        ("l1", true, false, false),
        ("l1+l2", true, true, false),
        ("l1+l2+l3", true, true, true),
    ] {
        pointadd_lilypad::test_layer_overrides(Some(l1), Some(l3));
        super::lilypad_g::test_l2_override(Some(l2));
        let mut b = B::new();
        let (xq, yq) = pointadd_lilypad::point_add(&mut b);
        let (nq, nb, _, regs) = analyze_ops(b.ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(format!("layers-phase-witness-{name}").as_bytes());
        let mut xof = h.finalize_xof();
        let mut s = Simulator::new(nq as usize, nb as usize, &mut xof);
        for shot in 0..64 {
            s.set_register(&regs[0], t.0, shot);
            s.set_register(&regs[1], t.1, shot);
            s.set_register(&regs[2], o.0, shot);
            s.set_register(&regs[3], o.1, shot);
        }
        s.apply_iter(b.ops.iter());
        let mut bad = 0u32;
        for shot in 0..64 {
            bad += u32::from(s.get_register(&regs[0], shot) != expected.0 || s.get_register(&regs[1], shot) != expected.1);
        }
        let data: std::collections::HashSet<u64> = xq.iter().chain(yq.iter()).map(|q| q.0).collect();
        let dirty = (0..nq).filter(|q| !data.contains(q) && s.qubits[*q as usize] != 0).count();
        eprintln!("LAYER_WITNESS {name}: bad={bad} phase={} dirty={dirty}", s.phase.count_ones());
    }
    pointadd_lilypad::test_layer_overrides(None, None);
    super::lilypad_g::test_l2_override(None);
}

#[test]
#[ignore]
fn lilypad_failure_localization() {
    let path = std::env::var("LILYPAD_CASES").expect("LILYPAD_CASES");
    let vals: Vec<[ruint::aliases::U256; 4]> = std::fs::read_to_string(path).unwrap().lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let v: Vec<_> = l.split_whitespace().map(|h| ruint::aliases::U256::from_str_radix(h, 16).unwrap()).collect();
            [v[0], v[1], v[2], v[3]]
        }).collect();
    pointadd_lilypad::CKS.with(|c| c.borrow_mut().clear());
    let mut b = B::new();
    let _ = pointadd_lilypad::point_add(&mut b);
    let ops = std::mem::take(&mut b.ops);
    let cks = pointadd_lilypad::CKS.with(|c| c.borrow().clone());
    let (nq, nb, _, regs) = analyze_ops(ops.iter());
    let curve = lilypad_curve();
    let p = curve.modulus;
    let sub = |a, z| if a >= z { a - z } else { p - (z - a) };
    let mut expected = vec![];
    for v in &vals {
        let dx = sub(v[0], v[2]);
        let dy = sub(v[1], v[3]);
        let lam = dy.mul_mod(dx.pow_mod(p - ruint::aliases::U256::from(2u64), p), p);
        let mut dx2 = lam.mul_mod(lam, p);
        dx2 = sub(dx2, dx);
        for _ in 0..3 { dx2 = sub(dx2, v[2]); }
        let ndy0 = lam.mul_mod(dx2, p);
        let ndy = if ndy0.is_zero() { ndy0 } else { p - ndy0 };
        let x3 = (dx2 + v[2]) % p;
        let y3 = sub(ndy, v[3]);
        expected.push((dx, dy, lam, dx2, ndy, x3, y3));
    }
    let mut h = sha3::Shake256::default(); h.update(b"lilypad-localize"); let mut xof = h.finalize_xof();
    let mut s = Simulator::new(nq as usize, nb as usize, &mut xof);
    for (k, v) in vals.iter().enumerate() {
        s.set_register(&regs[0], v[0], k); s.set_register(&regs[1], v[1], k);
        s.set_register(&regs[2], v[2], k); s.set_register(&regs[3], v[3], k);
    }
    let mut lo = 0usize;
    for (name, hi) in cks {
        s.apply_iter(ops[lo..hi].iter()); lo = hi;
        let want = match name.as_str() {
            "-- division 1" => Some((0usize, 1usize)),
            "walk inverse 1 end" | "-- x: dx' = lambda^2 - " => Some((0, 2)),
            "-- ndy = -lambda * dx'," => Some((3, 2)),
            "-- division 2: recomput" | "-- x3 = dx' + ox, y3 = " => Some((3, 4)),
            "end" => Some((5, 6)),
            _ => None,
        };
        if let Some((ix, iy)) = want {
            let mut bad = 0;
            for (k, e) in expected.iter().enumerate() {
                let a = [e.0, e.1, e.2, e.3, e.4, e.5, e.6];
                if s.get_register(&regs[0], k) != a[ix] || s.get_register(&regs[1], k) != a[iy] { bad += 1; }
            }
            eprintln!("LOC {name}: bad {bad}/{} phase {:#x}", vals.len(), s.phase);
        }
    }
    s.apply_iter(ops[lo..].iter());
}

#[test]
#[ignore]
fn lilypad_residual_walks_exact() {
    let path = std::env::var("LILYPAD_CASES").expect("LILYPAD_CASES");
    let curve = lilypad_curve();
    let p = curve.modulus;
    let sub = |a, z| if a >= z { a - z } else { p - (z - a) };
    let to_n = |u: ruint::aliases::U256| N::from_limbs([u.as_limbs()[0], u.as_limbs()[1], u.as_limbs()[2], u.as_limbs()[3], 0, 0]);
    let mut xs = vec![];
    for line in std::fs::read_to_string(path).unwrap().lines().filter(|l| !l.trim().is_empty()) {
        let v: Vec<_> = line.split_whitespace().map(|h| ruint::aliases::U256::from_str_radix(h, 16).unwrap()).collect();
        let dx = sub(v[0], v[2]);
        let dy = sub(v[1], v[3]);
        let lam = dy.mul_mod(dx.pow_mod(p - ruint::aliases::U256::from(2u64), p), p);
        let mut dx2 = sub(lam.mul_mod(lam, p), dx);
        for _ in 0..3 { dx2 = sub(dx2, v[2]); }
        xs.push(to_n(dx)); xs.push(to_n(dx2));
    }
    let sch = sched();
    let mut predicted_flags = vec![];
    for &v in &xs {
        let mut m = Pm::new(v);
        for t in 1..=sch.s { m.tick(t, &sch, 13); }
        if m.bad.is_none() && m.g != N::ZERO { m.bad = Some("overrun".into()); }
        predicted_flags.push(m.bad.clone());
    }
    for (i, pair) in predicted_flags.chunks(2).enumerate() {
        eprintln!("residual {i}: div1={:?} div2={:?}", pair[0], pair[1]);
        assert_eq!(usize::from(pair[0].is_some()) + usize::from(pair[1].is_some()), 1, "case {i}: expected one failing division");
    }
    let (b, x, y) = build_roundtrip(&sch, 13, 893);
    let ys: Vec<N> = (0..xs.len()).map(|i| N::from((i + 7) as u64)).collect();
    let (good, predicted) = verify_roundtrip_batch(&b, &x, &y, &sch, 13, &xs, &ys, b"lilypad-residual-walks");
    eprintln!("Lilypad residual operands: {good} exact walks, {predicted} predicted");
    assert_eq!(good + predicted, xs.len());
    assert_eq!(predicted, 12);
}

/// Closed native square at caps (LILYPAD_SQCAPS): expected executed Toffoli (conditional CCX weighted 1/2 per depth).
#[test]
#[ignore]
fn lilypad_square_caps() {
    use crate::circuit::OperationType as K;
    let caps: Vec<usize> = std::env::var("LILYPAD_SQCAPS").unwrap_or("935".into()).split(',').map(|s| s.parse().unwrap()).collect();
    for cap in caps {
        let r = std::panic::catch_unwind(|| super::super::public_square_port::native_square_ops_at_cap(cap));
        match r {
            Err(_) => eprintln!("SQUARE cap {cap}: unbuildable"),
            Ok(ops) => {
                let (nq, _, _, _) = analyze_ops(ops.iter());
                let (mut w, mut st, mut tot, mut nat) = (1.0f64, vec![], 0.0, 0u64);
                for op in &ops {
                    match op.kind {
                        K::PushCondition => { st.push(w); w *= 0.5; }
                        K::PopCondition => w = st.pop().unwrap(),
                        K::CCX | K::CCZ => { tot += w; nat += 1; }
                        _ => {}
                    }
                }
                eprintln!("SQUARE cap {cap}: qubits {nq} native {nat} expected {tot:.0}");
            }
        }
    }
}

/// square_acc (z += y^2 mod p) as the replacement square below cap 935: expected T at pools (LILYPAD_SQPOOLS),
/// value-checked on 64 shots.
#[test]
#[ignore]
fn lilypad_square_acc_pools() {
    use super::modp_ft::{square_acc, Ms};
    let pools: Vec<usize> = std::env::var("LILYPAD_SQPOOLS").unwrap_or("256".into()).split(',').map(|s| s.parse().unwrap()).collect();
    let pm = p();
    for pool in pools {
        let mut b = B::new();
        let (z, y) = (b.alloc_n(256), b.alloc_n(256));
        let ms = Ms { k: b.alloc(), r: b.alloc_n(pool), one: b.alloc() };
        b.x(ms.one);
        let tmp = b.alloc();
        let n0 = b.ops.len();
        let mut zz = z.clone();
        square_acc(&mut b, &ms, &mut zz, &y, tmp);
        let e = super::tests_chunked::expected_t(&b.ops[n0..]);
        let mut rng = Rng::new(pool as u64);
        let zs: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
        let ys: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
        let mut xr = xof(b"lilypad-sq");
        let mut s = sim(&b, &mut xr);
        for k in 0..64 {
            put(&mut s.qubits, &z, k, zs[k]);
            put(&mut s.qubits, &y, k, ys[k]);
        }
        s.apply_iter(b.ops.iter());
        let mut bad = 0;
        for k in 0..64 {
            let want = (zs[k] + ys[k].mul_mod(ys[k], pm)) % pm;
            if get_u256(&s.qubits, &zz, k) != want {
                bad += 1;
            }
        }
        eprintln!("SQACC pool {pool}: live+pool {} expected {e:.0} bad {bad} phase {:#x}", 512 + pool + 3, s.phase);
    }
}
fn get_u256(w: &[u64], qs: &[QubitId], k: usize) -> N {
    let mut v = N::ZERO;
    for (i, &q) in qs.iter().enumerate() {
        if (w[q.0 as usize] >> k) & 1 == 1 {
            v |= N::from(1u64) << i;
        }
    }
    v
}

/// The narrow MBU shell (pointadd_strip's sequence) at cap STRIP_PEAK with Lilypad-GCD's interface and walk stubs: after a
/// forward walk the live set is y + C (LILYPAD_CLEN lanes) + key + h (6) + log (LILYPAD_LOG); tails use S = LILYPAD_S halvings;
/// the square is ctrl_neg + square_acc (the closed square does not fit below 935). Expected T per phase.
#[test]
#[ignore]
fn lilypad_shell_stub() {
    use super::modp_frogdrop::load_bits;
    use super::modp_ft::{ctrl_neg, mod_double_n, modadd, modsub, product_inv, product_tail_neg_stream, square_acc, Ms};
    use super::pointadd_strip::{peak, rec_product, rec_product_tail_s, reduce_ct, uncompute_product_tail_s};
    let clen = env_usize("LILYPAD_CLEN", 288);
    let nlog = env_usize("LILYPAD_LOG", 8);
    let s_h = env_usize("LILYPAD_S", 532);
    let lhat = s_h - 256;
    let mut b = B::new();
    let x = b.alloc_n(256);
    let y = b.alloc_n(256);
    let ox: Vec<crate::circuit::BitId> = b.declare_bits(2, 256);
    let oy: Vec<crate::circuit::BitId> = b.declare_bits(3, 256);
    let mut marks: Vec<(String, usize, u64)> = vec![("start".into(), 0, 0)];
    let mark = |b: &B, m: &mut Vec<(String, usize, u64)>, s: &str| m.push((s.to_string(), b.ops.len(), b.peak));
    {
        let t = b.alloc_n(256);
        let ms = Ms::alloc_room(&mut b, peak());
        load_bits(&mut b, &t, &ox);
        modsub(&mut b, &ms, &x, &t, y[0]);
        load_bits(&mut b, &t, &ox);
        load_bits(&mut b, &t, &oy);
        modsub(&mut b, &ms, &y, &t, x[0]);
        load_bits(&mut b, &t, &oy);
        b.free_n(&t);
        ms.release(&mut b);
    }
    mark(&b, &mut marks, "setup");
    // walk stub: x -> (C, key, h, log)
    let fwd_stub = |b: &mut B| -> (Vec<QubitId>, QubitId, Vec<QubitId>) {
        b.free_n(&x);
        let c = b.alloc_n(clen);
        let key = b.alloc();
        let ex = b.alloc_n(6 + nlog);
        (c, key, ex)
    };
    let inv_stub = |b: &mut B, c: Vec<QubitId>, key: QubitId, ex: Vec<QubitId>| {
        b.free_n(&c);
        b.free(key);
        b.free_n(&ex);
        for &q in &x {
            b.acquire(q);
        }
    };
    let (c, key, ex) = fwd_stub(&mut b);
    let live_end = b.live;
    let m1 = b.fresh_bits(256);
    reduce_ct(&mut b, &c, false);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(&mut b, peak());
        let mut zz = z.clone();
        product_tail_neg_stream(&mut b, &ms, &mut zz, &y, &c[..256], s_h, &m1);
        let mut pos: Vec<QubitId> = zz.clone();
        for i in 0..256 {
            if pos[i] != z[i] {
                let j = pos.iter().position(|&q| q == z[i]).unwrap();
                b.swap(pos[i], pos[j]);
                pos.swap(i, j);
            }
        }
        ctrl_neg(&mut b, &ms, &z, Some(key));
        ms.release(&mut b);
        for i in 0..256 {
            b.swap(z[i], y[i]);
        }
        b.free_n(&z);
    }
    reduce_ct(&mut b, &c, true);
    mark(&b, &mut marks, "lambda tail (+reduce, undo)");
    inv_stub(&mut b, c, key, ex);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(&mut b, peak());
        let r = rec_product(&mut b, &ms, &z, &y, &x, false);
        b.play(&r, false);
        for i in 0..256 {
            b.z_if(z[i], m1[i]);
        }
        let mut zz = z.clone();
        product_inv(&mut b, &ms, &mut zz, &y, &x);
        b.free_n(&z);
        ms.release(&mut b);
    }
    mark(&b, &mut marks, "dy fix");
    {
        let ms = Ms::alloc_room(&mut b, peak());
        ctrl_neg(&mut b, &ms, &x, None);
        let tmp = b.alloc();
        let mut xx = x.clone();
        square_acc(&mut b, &ms, &mut xx, &y, tmp);
        assert_eq!(xx, x);
        b.free(tmp);
        ms.release(&mut b);
        let t = b.alloc_n(256);
        let ms = Ms::alloc_room(&mut b, peak());
        load_bits(&mut b, &t, &ox);
        for _ in 0..3 {
            modsub(&mut b, &ms, &x, &t, y[0]);
        }
        load_bits(&mut b, &t, &ox);
        b.free_n(&t);
        ms.release(&mut b);
    }
    mark(&b, &mut marks, "x' (neg + square_acc + 3 modsub)");
    let m2 = b.fresh_bits(256);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(&mut b, peak());
        let mut yy = y.clone();
        mod_double_n(&mut b, &ms, &mut yy, lhat);
        let mut zz = z.clone();
        product_tail_neg_stream(&mut b, &ms, &mut zz, &yy, &x, lhat, &m2);
        let mut pos: Vec<QubitId> = zz.clone();
        for i in 0..256 {
            if pos[i] != z[i] {
                let j = pos.iter().position(|&q| q == z[i]).unwrap();
                b.swap(pos[i], pos[j]);
                pos.swap(i, j);
            }
        }
        ms.release(&mut b);
        for i in 0..256 {
            b.swap(z[i], y[i]);
        }
        b.free_n(&z);
    }
    mark(&b, &mut marks, "ndy tail");
    let (c, key, ex) = fwd_stub(&mut b);
    reduce_ct(&mut b, &c, false);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(&mut b, peak());
        let tt = s_h - lhat;
        let r = rec_product_tail_s(&mut b, &ms, &z, &c[..256], &y, tt, Some((key, true)));
        b.play(&r, false);
        for i in 0..256 {
            b.z_if(z[i], m2[i]);
        }
        uncompute_product_tail_s(&mut b, &ms, &z, &c[..256], &y, tt, Some((key, true)), 48);
        b.free_n(&z);
        ms.release(&mut b);
    }
    reduce_ct(&mut b, &c, true);
    mark(&b, &mut marks, "lambda fix (+reduce, undo)");
    inv_stub(&mut b, c, key, ex);
    {
        let t = b.alloc_n(256);
        let ms = Ms::alloc_room(&mut b, peak());
        load_bits(&mut b, &t, &ox);
        modadd(&mut b, &ms, &x, &t, y[0]);
        load_bits(&mut b, &t, &ox);
        load_bits(&mut b, &t, &oy);
        modsub(&mut b, &ms, &y, &t, x[0]);
        load_bits(&mut b, &t, &oy);
        b.free_n(&t);
        ms.release(&mut b);
    }
    mark(&b, &mut marks, "final");
    let mut tot = 0.0;
    for w in marks.windows(2) {
        let e = super::tests_chunked::expected_t(&b.ops[w[0].1..w[1].1]);
        tot += e;
        eprintln!("SHELL cap {} clen {clen} log {nlog}: {:36} {e:>9.0}  (peak so far {})", peak(), w[1].0, w[1].2);
    }
    eprintln!("SHELL cap {} clen {clen} log {nlog} S {s_h}: live at the C end {live_end}; total {tot:.0}; peak {}", peak(), b.peak);
}

// ------------------------------------------------------------------------------------------------ Lilypad-G
use super::lilypad_g::*;

#[derive(Clone, Debug)]
struct Gm {
    f: N,
    g: N,
    cf: N,
    cg: N,
    rho: bool,
    pm: Pm,
    bad: bool,
}

impl Gm {
    fn new(x: N) -> Self {
        let pp = p();
        Self {
            f: pp,
            g: (x << 1usize).wrapping_sub(pp),
            cf: N::ZERO,
            cg: N::from(2u64),
            rho: false,
            pm: Pm::new(x),
            bad: false,
        }
    }

    fn tick(&mut self, t: usize, sch: &PSched, qb: usize) {
        if self.bad || self.pm.bad.is_some() {
            self.bad = true;
            self.pm.tick(t, sch, qb);
            return;
        }
        let (kv, kc) = (sch.kv[t], sch.kc[t]);
        let d = self.g.bit(1) == self.f.bit(1);
        let e = d ^ self.rho;
        assert_eq!(e, self.pm.g.bit(0), "tick {t}: forced digit differs from Lilypad e");
        let sw = e && self.pm.d2 > 0;
        let pre = [self.f, self.g, self.cf, self.cg];
        let mid = if d { self.g.wrapping_add(self.f) } else { self.g.wrapping_sub(self.f) };
        let midc = if d { self.cg.wrapping_add(self.cf) } else { self.cg.wrapping_sub(self.cf) };
        self.g = sar1(mid);
        self.cg = midc;
        self.cf <<= 1usize;
        if sw {
            std::mem::swap(&mut self.f, &mut self.g);
            std::mem::swap(&mut self.cf, &mut self.cg);
            self.rho = !self.rho;
        }
        let vw = [tcb(pre[0]), tcb(pre[1]), tcb(mid)].into_iter().max().unwrap();
        let stored_c = |v: N| if HALF_COFACTOR_G { sar1(v) } else { v };
        let cw = [tcb(stored_c(pre[2])), tcb(stored_c(pre[3])), tcb(stored_c(midc))]
            .into_iter()
            .max()
            .unwrap();
        if vw > kv || cw > kc {
            self.bad = true;
        }
        if t == sch.s
            && (tcb(self.f).max(tcb(self.g)) > sch.kv[t + 1]
                || tcb(stored_c(self.cf)).max(tcb(stored_c(self.cg))) > sch.kc[t + 1])
        {
            self.bad = true;
        }
        self.pm.tick(t, sch, qb);
        if self.pm.bad.as_ref().is_some_and(|s| s.starts_with("width") || s.starts_with("end width")) {
            self.pm.bad = None;
        }
        if self.pm.bad.is_some() {
            self.bad = true;
        }
    }
}

fn check_tick_g(
    w: &PWalk,
    sch: &PSched,
    t: usize,
    st: &[u64],
    ms: &[Gm],
    qb: usize,
    with_q: bool,
) -> usize {
    let mut nbad = 0;
    for (k, m) in ms.iter().enumerate() {
        if m.bad {
            nbad += 1;
            continue;
        }
        let mut got = decode(w, sch, t + 1, st, k);
        let stored_c = |v: N| if HALF_COFACTOR_G { sar1(v) } else { v };
        let mut want = (m.f, m.g, stored_c(m.cf), stored_c(m.cg), (((m.pm.d2 - 1) / 2) as u64) & 127);
        if super::lilypad_g::test_page3_storage() && with_q {
            got.3 &= !N::from(7u64);
            want.3 &= !N::from(7u64);
        }
        assert_eq!(got, want, "Lilypad-G tick {t} shot {k}");
        let mut got_rho = (t & 1 == 1) ^ ((st[w.h[0].0 as usize] >> k) & 1 == 1);
        if w.log.len() >= 8 {
            got_rho ^= ((st[w.log[0].0 as usize] ^ st[w.log[4].0 as usize]) >> k) & 1 == 1;
        }
        assert_eq!(got_rho, m.rho, "Lilypad-G tick {t} shot {k}: derived rho");
        if with_q {
            assert_eq!(get_u(st, &w.qfr(t), k), m.pm.qval(t, qb), "Lilypad-G tick {t} shot {k}: Q");
        }
    }
    nbad
}

#[test]
#[ignore]
fn lilypad_g_fwd_check() {
    use super::frogstrip::SEC;
    let sch = sched_g();
    let ticks = env_usize("LILYPAD_TICKS", sch.s);
    let room = env_usize("LILYPAD_ROOM", 27);
    let prof = std::env::var("LILYPAD_SEC").is_ok();
    if prof {
        SEC.with(|s| *s.borrow_mut() = Some(Default::default()));
    }
    let mut s0 = setup(&sch, 0, false, false);
    let sc = PScr::alloc_fwd(&mut s0.b, room);
    let Setup { mut b, x, w, .. } = s0;
    init_g(&mut b, &w, &sch, &sc);
    let division = b.new_division();
    let mut bounds = vec![b.ops.len()];
    let m = b.fresh_bits(ticks + 1);
    for t in 1..=ticks {
        let rho = rho_stable(&w, t - 1);
        step_core_g(&mut b, &w, t, &sch, &sc, &rho, sc.e, &[], Some((division, false)));
        halve_g(&mut b, &w, t, &sch, &sc);
        b.hmr_to(sc.e, m[t]);
        bounds.push(b.ops.len());
    }
    let exp = super::tests_chunked::expected_t(&b.ops[bounds[0]..]);
    eprintln!("Lilypad-G forward: {ticks} ticks, expected {exp:.0} ({:.1}/tick), peak {}", exp / ticks as f64, b.peak);
    if prof {
        let mm = SEC.with(|s| s.borrow_mut().take().unwrap());
        for (name, (sum, n)) in &mm {
            eprintln!("SEC {name:14} total {sum:>10.0} n {n:>5} avg {:>8.1}", sum / *n as f64);
        }
    }
    let mut rng = Rng::new(env_usize("LILYPAD_SEED", 1) as u64);
    let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-g-forward");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
    }
    let mut ms: Vec<Gm> = xs.iter().map(|&v| Gm::new(v)).collect();
    s.apply_iter(b.ops[..bounds[0]].iter());
    let scratch: Vec<QubitId> = [sc.e, sc.sg]
        .iter()
        .copied()
        .chain(sc.tmp.iter().copied())
        .chain(sc.pool.iter().copied())
        .collect();
    let mut nbad = 0;
    for t in 1..=ticks {
        s.apply_iter(b.ops[bounds[t - 1]..bounds[t]].iter());
        for mm in &mut ms {
            mm.tick(t, &sch, 64);
        }
        nbad = check_tick_g(&w, &sch, t, &s.qubits, &ms, 64, false);
        let good: u64 = ms.iter().enumerate().filter(|(_, m)| !m.bad).map(|(k, _)| 1u64 << k).sum();
        for &q in &scratch {
            assert_eq!(s.qubits[q.0 as usize] & good, 0, "tick {t}: scratch q{} dirty", q.0);
        }
    }
    eprintln!("Lilypad-G forward exact on {} / 64 shots", 64 - nbad);
}

#[test]
#[ignore]
fn lilypad_g_pre_swap_page_source_audit() {
    const R: usize = 3;
    let sch = sched_g();
    let ticks = env_usize("LILYPAD_TICKS", sch.s);
    let mut s0 = setup_with_capq(&sch, 13, false, false, 11);
    let sc = PScr::alloc_fwd(&mut s0.b, 27);
    let Setup { mut b, x, w, .. } = s0;
    init_g(&mut b, &w, &sch, &sc);
    let m = b.fresh_bits(ticks + 1);
    let mut starts = vec![b.ops.len()];
    let mut mids = vec![b.ops.len()];
    for t in 1..=ticks {
        let rho = rho_stable(&w, t - 1);
        step_core_g(&mut b, &w, t, &sch, &sc, &rho, sc.e, &[], None);
        mids.push(b.ops.len());
        halve_g(&mut b, &w, t, &sch, &sc);
        b.hmr_to(sc.e, m[t]);
        starts.push(b.ops.len());
    }

    let mut rng = Rng::new(env_usize("LILYPAD_SEED", 2) as u64);
    let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-g-pre-swap-page-source");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 { put(&mut s.qubits, &x, k, xs[k]); }
    s.apply_iter(b.ops[..starts[0]].iter());

    let page = |st: &[u64], qs: &[QubitId], shot: usize| -> usize { get_u(st, qs, shot) as usize & 7 };
    let mut before_ok = 0usize;
    let mut after_ok = 0usize;
    let mut samples = 0usize;
    for t in 1..=ticks {
        s.apply_iter(b.ops[starts[t - 1]..mids[t]].iter());
        if t % 2 == 0 {
            let gq: Vec<QubitId> = (0..R).map(|i| w.af(t + 1, i)).collect();
            let fq: Vec<QubitId> = (0..R).map(|i| w.bf(i)).collect();
            let uq: Vec<QubitId> = (0..R).map(|i| w.asig(t + 1, i)).collect();
            let vq: Vec<QubitId> = (0..R).map(|i| w.bsig(i)).collect();
            for k in 0..64 {
                let (g, f, u, v) = (
                    page(&s.qubits, &gq, k),
                    page(&s.qubits, &fq, k),
                    page(&s.qubits, &uq, k),
                    page(&s.qubits, &vq, k),
                );
                assert_eq!(f & 1, 1, "tick={t} shot={k}: F even");
                let inv = (1usize..8).find(|z| (f * z) & 7 == 1).unwrap();
                let mut rb = ((t - 1) & 1 == 1) ^ (((s.qubits[w.h[0].0 as usize] >> k) & 1) != 0);
                if w.log.len() >= 8 {
                    rb ^= (((s.qubits[w.log[0].0 as usize] ^ s.qubits[w.log[4].0 as usize]) >> k) & 1) != 0;
                }
                let sigma = ((s.qubits[sc.sg.0 as usize] >> k) & 1) != 0;
                let ra = rb ^ sigma;
                let calc = |rho: bool| ((g * u + if rho { 1 } else { 7 }) * inv) & 7;
                before_ok += usize::from(calc(rb) == v);
                after_ok += usize::from(calc(ra) == v);
                samples += 1;
                if t == 4 && k == 6 {
                    eprintln!("page witness t4/s6: g={g} f={f} u={u} v={v} rho_before={rb} sigma={sigma} rho_after={ra} calc_before={} calc_after={}", calc(rb), calc(ra));
                }
            }
        }
        s.apply_iter(b.ops[mids[t]..starts[t]].iter());
    }
    eprintln!("pre-swap page audit: samples={samples} rho_before={before_ok} rho_after={after_ok}");
    assert!(before_ok == samples || after_ok == samples, "neither rho view reconstructs the physical page");
}

#[test]
#[ignore]
fn lilypad_g_stable_page_codec_audit() {
    let r = env_usize("LILYPAD_PAGE_AUDIT_R", 10);
    assert!((3..=13).contains(&r));
    let sch = sched_g();
    let ticks = env_usize("LILYPAD_TICKS", sch.s);
    let mut s0 = setup_with_capq(&sch, 13, false, false, 11);
    let sc = PScr::alloc_fwd(&mut s0.b, 27);
    let Setup { mut b, x, w, .. } = s0;
    init_g(&mut b, &w, &sch, &sc);
    let m = b.fresh_bits(ticks + 1);
    let mut bounds = vec![b.ops.len()];
    for t in 1..=ticks {
        let rho = rho_stable(&w, t - 1);
        step_core_g(&mut b, &w, t, &sch, &sc, &rho, sc.e, &[], None);
        halve_g(&mut b, &w, t, &sch, &sc);
        b.hmr_to(sc.e, m[t]);
        bounds.push(b.ops.len());
    }

    let mut rng = Rng::new(env_usize("LILYPAD_SEED", 2) as u64);
    let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-g-stable-page-codec");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 { put(&mut s.qubits, &x, k, xs[k]); }
    s.apply_iter(b.ops[..bounds[0]].iter());

    let mask = (1usize << r) - 1;
    let p_low = p().as_limbs()[0] as usize & mask;
    let read = |st: &[u64], qs: &[QubitId], shot: usize| -> usize { get_u(st, qs, shot) as usize & mask };
    let mut checked = 0usize;
    for t in 1..=ticks {
        let value_len = sch.c[t];
        let gq: Vec<QubitId> = (0..r).map(|i| w.af(t, i.min(value_len - 1))).collect();
        let fq: Vec<QubitId> = (0..r).map(|i| w.bf(i.min(value_len - 1))).collect();
        let uq: Vec<QubitId> = (0..r).map(|i| w.asig(t, i)).collect();
        let vq: Vec<QubitId> = (0..r).map(|i| w.bsig(i)).collect();
        for k in 0..64 {
            let (g, f, u, v) = (
                read(&s.qubits, &gq, k),
                read(&s.qubits, &fq, k),
                read(&s.qubits, &uq, k),
                read(&s.qubits, &vq, k),
            );
            assert_eq!(g & 1, 1, "tick={t} shot={k}: G even");
            assert_eq!(f & 1, 1, "tick={t} shot={k}: F even");
            let mut rho = ((t - 1) & 1 == 1) ^ (((s.qubits[w.h[0].0 as usize] >> k) & 1) != 0);
            if w.log.len() >= 8 {
                rho ^= (((s.qubits[w.log[0].0 as usize] ^ s.qubits[w.log[4].0 as usize]) >> k) & 1) != 0;
            }
            let mut finv = 1usize;
            for _ in 0..r { finv = finv.wrapping_mul(2usize.wrapping_sub(f.wrapping_mul(finv))) & mask; }
            let signed_p = if rho { (!p_low).wrapping_add(1) & mask } else { p_low };
            let want = g.wrapping_mul(u).wrapping_add(signed_p).wrapping_mul(finv) & mask;
            assert_eq!(v, want, "stable page r={r} tick={t} shot={k} g={g} f={f} u={u} rho={rho}");
            checked += 1;
        }
        s.apply_iter(b.ops[bounds[t - 1]..bounds[t]].iter());
    }
    eprintln!("stable determinant page r={r} exact on {checked} tick/shot states");
}

#[test]
#[ignore]
fn lilypad_g_mask_boundary_rho_audit() {
    const R: usize = 3;
    let sch = sched_g();
    let ticks = env_usize("LILYPAD_TICKS", sch.s);
    let mut s0 = setup_with_capq(&sch, 13, false, false, 11);
    let sc = PScr::alloc_fwd(&mut s0.b, 27);
    let rho_keep = s0.b.alloc();
    let Setup { mut b, x, w, .. } = s0;
    init_g(&mut b, &w, &sch, &sc);
    let m = b.fresh_bits(ticks + 1);
    let mut starts = vec![b.ops.len()];
    let mut mids = vec![None];
    for t in 1..=ticks {
        let rho_before = rho_stable(&w, t - 1);
        step_core_g(&mut b, &w, t, &sch, &sc, &rho_before, sc.e, &[], None);
        if t % 2 == 0 {
            rho_before.xor_into(&mut b, rho_keep);
            b.begin();
            if t > 0 {
                fix_boundary(&mut b, &|f| w.af(t + 1, f), sch.c[t] - 1, sch.c[t + 1]);
            }
            fix_boundary(&mut b, &|f| w.bf(f), sch.c[t], sch.c[t + 1]);
            for &h in &w.h { b.cx(sc.sg, h); }
            inc_unctl(&mut b, &w.h, &sc.tmp);
            cap_logic(&mut b, &w, &sc);
            let prefix = b.end();
            b.play(&prefix, false);
            mids.push(Some(b.ops.len()));
            b.play(&prefix, true);
            rho_before.xor_into(&mut b, rho_keep);
        } else {
            mids.push(None);
        }
        halve_g(&mut b, &w, t, &sch, &sc);
        b.hmr_to(sc.e, m[t]);
        starts.push(b.ops.len());
    }

    let mut rng = Rng::new(env_usize("LILYPAD_SEED", 2) as u64);
    let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-g-mask-boundary-rho");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 { put(&mut s.qubits, &x, k, xs[k]); }
    s.apply_iter(b.ops[..starts[0]].iter());
    let mut n_before = 0usize;
    let mut n_stable = 0usize;
    let mut n_pre = 0usize;
    let mut total = 0usize;
    for t in 1..=ticks {
        if let Some(mid) = mids[t] {
            s.apply_iter(b.ops[starts[t - 1]..mid].iter());
            let gq: Vec<QubitId> = (0..R).map(|i| w.af(t + 1, i)).collect();
            let fq: Vec<QubitId> = (0..R).map(|i| w.bf(i)).collect();
            let uq: Vec<QubitId> = (0..R).map(|i| w.asig(t + 1, i)).collect();
            let vq: Vec<QubitId> = (0..R).map(|i| w.bsig(i)).collect();
            for k in 0..64 {
                let g = get_u(&s.qubits, &gq, k) as usize & 7;
                let f = get_u(&s.qubits, &fq, k) as usize & 7;
                let u = get_u(&s.qubits, &uq, k) as usize & 7;
                let v = get_u(&s.qubits, &vq, k) as usize & 7;
                let rb = ((s.qubits[rho_keep.0 as usize] >> k) & 1) != 0;
                let mut rs = (t & 1 == 1) ^ (((s.qubits[w.h[0].0 as usize] >> k) & 1) != 0);
                rs ^= (((s.qubits[w.log[0].0 as usize] ^ s.qubits[w.log[4].0 as usize]) >> k) & 1) != 0;
                let sigma = ((s.qubits[sc.sg.0 as usize] >> k) & 1) != 0;
                let rp = rs ^ sigma;
                let inv = (1usize..8).find(|z| (f * z) & 7 == 1).unwrap();
                let calc = |rho: bool| ((g * u + if rho { 1 } else { 7 }) * inv) & 7;
                n_before += usize::from(calc(rb) == v);
                n_stable += usize::from(calc(rs) == v);
                n_pre += usize::from(calc(rp) == v);
                total += 1;
                if t == 4 && matches!(k, 6 | 12) {
                    eprintln!("mask rho witness t={t} shot={k}: g={g} f={f} u={u} v={v} rb={rb} rs={rs} sigma={sigma} rp={rp} calc=({},{},{})", calc(rb), calc(rs), calc(rp));
                }
            }
            s.apply_iter(b.ops[mid..starts[t]].iter());
        } else {
            s.apply_iter(b.ops[starts[t - 1]..starts[t]].iter());
        }
    }
    eprintln!("mask-boundary rho audit: total={total} before={n_before} stable_t={n_stable} pre_swap_expr={n_pre}");
    assert!(n_before == total || n_stable == total || n_pre == total);
}

#[test]
#[ignore]
fn lilypad_g_reachable_borrowed_page_sources() {
    const R: usize = 3;
    const NV: usize = 8;
    let mut anf_rows = vec![];
    for bit in 0..R {
        let mut anf = vec![0u8; 1 << NV];
        for assignment in 0..1usize << NV {
            let g = 1 | (((assignment >> 0) & 3) << 1);
            let f = 1 | (((assignment >> 2) & 3) << 1);
            let u = (assignment >> 4) & 7;
            let rho = (assignment >> 7) & 1;
            let sign_p = if rho == 0 { 7 } else { 1 };
            let inv = (1usize..8).find(|z| (f * z) & 7 == 1).unwrap();
            let v = ((g * u + sign_p) * inv) & 7;
            anf[assignment] = ((v >> bit) & 1) as u8;
        }
        for k in 0..NV {
            for mask in 0..1usize << NV {
                if mask & (1 << k) != 0 { anf[mask] ^= anf[mask ^ (1 << k)]; }
            }
        }
        anf_rows.push(anf.into_iter().enumerate().filter_map(|(m, c)| (c != 0).then_some(m)).collect::<Vec<_>>());
    }

    let sch = sched_g();
    let ticks = env_usize("LILYPAD_TICKS", sch.s);
    let mut s0 = setup_with_capq(&sch, 13, false, false, 11);
    let sc = PScr::alloc_fwd(&mut s0.b, 27);
    let rho_tmp = s0.b.alloc();
    let dirty = s0.b.alloc_n(4);
    let Setup { mut b, x, w, .. } = s0;
    init_g(&mut b, &w, &sch, &sc);
    let m = b.fresh_bits(ticks + 1);
    let mut starts = vec![b.ops.len()];
    let mut page_mids = vec![None];
    let mut page_ends = vec![None];
    for t in 1..=ticks {
        let rho = rho_stable(&w, t - 1);
        step_core_g(&mut b, &w, t, &sch, &sc, &rho, sc.e, &[], None);
        if t % 2 == 0 {
            let g0 = w.af(t + 1, 0);
            let f0 = w.bf(0);
            let vars = [
                w.af(t + 1, 1),
                w.af(t + 1, 2),
                w.bf(1),
                w.bf(2),
                w.asig(t + 1, 0),
                w.asig(t + 1, 1),
                w.asig(t + 1, 2),
                rho_tmp,
            ];
            let emit = |b: &mut B, bit: usize, target: QubitId| {
                for &mask in &anf_rows[bit] {
                    let controls: Vec<(QubitId, bool)> = (0..NV)
                        .filter(|k| mask & (1 << k) != 0)
                        .map(|k| (vars[k], false))
                        .collect();
                    super::mask::mc_xor(b, &controls, target, &[], &dirty);
                }
            };
            b.x(g0);
            b.x(f0);
            rho.xor_into(&mut b, rho_tmp);
            emit(&mut b, 1, g0);
            emit(&mut b, 2, f0);
            rho.xor_into(&mut b, g0);
            rho.xor_into(&mut b, f0);
            page_mids.push(Some(b.ops.len()));
            rho.xor_into(&mut b, f0);
            rho.xor_into(&mut b, g0);
            emit(&mut b, 2, f0);
            emit(&mut b, 1, g0);
            rho.xor_into(&mut b, rho_tmp);
            b.x(f0);
            b.x(g0);
            page_ends.push(Some(b.ops.len()));
        } else {
            page_mids.push(None);
            page_ends.push(None);
        }
        halve_g(&mut b, &w, t, &sch, &sc);
        b.hmr_to(sc.e, m[t]);
        starts.push(b.ops.len());
    }

    let mut rng = Rng::new(env_usize("LILYPAD_SEED", 2) as u64);
    let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-g-reachable-borrowed-page");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
        for (j, q) in dirty.iter().enumerate() {
            if ((k * 0x35 + j * 0x17) >> (j + 1)) & 1 != 0 { s.qubits[q.0 as usize] |= 1u64 << k; }
        }
    }
    let dirty_before: Vec<u64> = dirty.iter().map(|q| s.qubits[q.0 as usize]).collect();
    s.apply_iter(b.ops[..starts[0]].iter());
    let mut checked = 0usize;
    for t in 1..=ticks {
        if let (Some(mid), Some(end)) = (page_mids[t], page_ends[t]) {
            s.apply_iter(b.ops[starts[t - 1]..mid].iter());
            for k in 0..64 {
                let mut rho = ((t - 1) & 1 == 1) ^ (((s.qubits[w.h[0].0 as usize] >> k) & 1) != 0);
                rho ^= (((s.qubits[w.log[0].0 as usize] ^ s.qubits[w.log[4].0 as usize]) >> k) & 1) != 0;
                let want1 = ((s.qubits[w.bsig(1).0 as usize] >> k) & 1) ^ u64::from(rho);
                let want2 = ((s.qubits[w.bsig(2).0 as usize] >> k) & 1) ^ u64::from(rho);
                assert_eq!((s.qubits[w.af(t + 1, 0).0 as usize] >> k) & 1, want1, "tick={t} shot={k} V1");
                assert_eq!((s.qubits[w.bf(0).0 as usize] >> k) & 1, want2, "tick={t} shot={k} V2");
                checked += 1;
            }
            s.apply_iter(b.ops[mid..end].iter());
            assert_eq!(s.qubits[rho_tmp.0 as usize], 0, "tick={t}: rho tmp");
            for (j, q) in dirty.iter().enumerate() {
                assert_eq!(s.qubits[q.0 as usize], dirty_before[j], "tick={t}: dirty {j}");
            }
            s.apply_iter(b.ops[end..starts[t]].iter());
        } else {
            s.apply_iter(b.ops[starts[t - 1]..starts[t]].iter());
        }
    }
    eprintln!("reachable borrowed page sources exact on {checked} even-tick/shot states");
}

#[test]
#[ignore]
fn lilypad_g_regen_check() {
    use super::frogstrip::SEC;
    let sch = sched_g();
    let qb = env_usize("LILYPAD_QB", 13);
    let ticks = env_usize("LILYPAD_TICKS", sch.s);
    let room = env_usize("LILYPAD_ROOM", 8);
    let prof = std::env::var("LILYPAD_SEC").is_ok();
    if prof {
        SEC.with(|s| *s.borrow_mut() = Some(Default::default()));
    }
    let mut s0 = setup_with_capq(&sch, qb, false, true, 11);
    let sc = PScr::alloc_inv_g(&mut s0.b, room);
    let external_dirty = s0.b.alloc_n(7);
    let g = GScr;
    let Setup { mut b, x, w, .. } = s0;
    init_g(&mut b, &w, &sch, &sc);
    if super::lilypad_g::test_page3_storage() {
        let rho0 = rho_stable(&w, 0);
        super::lilypad_g::page3_storage_xor(&mut b, &w, 1, &rho0, &external_dirty);
    }
    let mut bounds = vec![b.ops.len()];
    let mut inv_cost = 0.0;
    for t in 1..=ticks {
        let (p1, p3) = rec_regen_g(&mut b, &w, t, &sch, &sc, &g, None, &external_dirty);
        inv_cost += b.measure(&p1, true) + b.measure(&p3, true);
        b.play(&p1, false);
        b.play(&p3, false);
        bounds.push(b.ops.len());
    }
    eprintln!("Lilypad-G regen: inverse cost {inv_cost:.0} ({:.1}/tick), peak {}", inv_cost / ticks as f64, b.peak);
    if prof {
        let mm = SEC.with(|s| s.borrow_mut().take().unwrap());
        for (name, (sum, n)) in &mm {
            eprintln!("SEC {name:14} total {sum:>10.0} n {n:>5} avg {:>8.1}", sum / *n as f64);
        }
    }
    let mut rng = Rng::new(env_usize("LILYPAD_SEED", 2) as u64);
    let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-g-regen");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
    }
    let mut ms: Vec<Gm> = xs.iter().map(|&v| Gm::new(v)).collect();
    s.apply_iter(b.ops[..bounds[0]].iter());
    let mut scratch: Vec<QubitId> = [sc.e, sc.sg]
        .iter()
        .copied()
        .chain(sc.tmp.iter().copied())
        .chain(sc.pool.iter().copied())
        .collect();
    scratch.extend(&sc.d);
    scratch.extend(&sc.sp);
    let mut nbad = 0;
    for t in 1..=ticks {
        s.apply_iter(b.ops[bounds[t - 1]..bounds[t]].iter());
        for mm in &mut ms {
            mm.tick(t, &sch, qb);
        }
        nbad = check_tick_g(&w, &sch, t, &s.qubits, &ms, qb, true);
        let good: u64 = ms.iter().enumerate().filter(|(_, m)| !m.bad).map(|(k, _)| 1u64 << k).sum();
        for &q in &scratch {
            assert_eq!(s.qubits[q.0 as usize] & good, 0, "tick {t}: scratch q{} dirty", q.0);
        }
        assert_eq!(s.phase & good, 0, "tick {t}: phase");
    }
    eprintln!("Lilypad-G regeneration exact on {} / 64 shots", 64 - nbad);
}

#[test]
#[ignore]
fn lilypad_g_count() {
    use super::frogstrip::SEC;
    let sch = sched_g();
    let qb = env_usize("LILYPAD_QB", 13);
    let cap = env_usize("LILYPAD_CAP", 893) as u64;
    let prof = std::env::var("LILYPAD_SEC").is_ok();
    if prof {
        SEC.with(|s| *s.borrow_mut() = Some(Default::default()));
    }
    let Setup { mut b, y, x, mut w } = setup(&sch, qb, true, false);
    let g = GScr;
    let live_f = b.live + 2 + NT as u64;
    let room_f = cap.saturating_sub(live_f) as usize;
    let sc = PScr::alloc_fwd(&mut b, room_f);
    let div = b.new_division();
    let n0 = b.ops.len();
    let m = walk_forward_g(&mut b, &w, &sch, &sc, &g, Some(div));
    let n1 = b.ops.len();
    let adapter = endpoint_adapter_g(&mut b, &w, &sch, &sc);
    b.play(&adapter, false);
    let na = b.ops.len();
    b.play(&adapter, true);
    b.cx(w.h[HB - 2], w.h[HB - 1]);
    b.free(w.h[HB - 1]);
    sc.release(&mut b);
    b.acquire(w.h[HB - 1]);
    b.cx(w.h[HB - 2], w.h[HB - 1]);
    if super::lilypad_g::test_page3_storage() {
        let rho_end = rho_stable(&w, sch.s);
        super::lilypad_g::page3_storage_xor(&mut b, &w, sch.s + 1, &rho_end, &y);
    }
    w.q = b.alloc_n(qb);
    let live_i = b.live + 2 + inverse_d_len_g() as u64 + inverse_tmp_len_g() as u64 + SB as u64;
    let room_i = cap.saturating_sub(live_i) as usize;
    let sc = PScr::alloc_inv_g(&mut b, room_i);
    let ni0 = b.ops.len();
    walk_inverse_g(&mut b, &w, &sch, &sc, &g, &m, Some(div), &y);
    let n2 = b.ops.len();
    b.close_division(div);
    let ef = super::tests_chunked::expected_t(&b.ops[n0..n1]);
    let ei = super::tests_chunked::expected_t(&b.ops[ni0..n2]);
    eprintln!(
        "LILYPAD_G_COUNT W {} qb {qb} cap {cap}: fwd pool {room_f} inv pool {room_i} fwd {ef:.0} inv {ei:.0} peak {}",
        sch.w, b.peak
    );
    if prof {
        let mm = SEC.with(|s| s.borrow_mut().take().unwrap());
        for (name, (sum, n)) in &mm {
            eprintln!("SEC {name:18} total {sum:>10.0} n {n:>5} avg {:>8.1}", sum / *n as f64);
        }
    }
    let mut rng = Rng::new(env_usize("LILYPAD_SEED", 3) as u64);
    let xs: Vec<N> = if let Ok(path) = std::env::var("LILYPAD_G_XFILE") {
        let batch = env_usize("LILYPAD_G_BATCH", 0);
        std::fs::read_to_string(path)
            .unwrap()
            .lines()
            .filter(|line| !line.trim().is_empty())
            .skip(batch * 64)
            .take(64)
            .map(|line| N::from_str_radix(line.trim().trim_start_matches("0x"), 16).unwrap())
            .collect()
    } else {
        (0..64).map(|_| rand_x(&mut rng)).collect()
    };
    assert!(!xs.is_empty() && xs.len() <= 64);
    let ys: Vec<N> = (0..xs.len()).map(|_| rand_x(&mut rng)).collect();
    let xtag = std::env::var("LILYPAD_XOF_TAG").unwrap_or_else(|_| "lilypad-g-count".into());
    let mut xr = xof(xtag.as_bytes());
    let mut s = sim(&b, &mut xr);
    let mut xrf = xof(format!("{xtag}-forward").as_bytes());
    let mut sf = sim(&b, &mut xrf);
    let mut xra = xof(format!("{xtag}-adapter").as_bytes());
    let mut sa = sim(&b, &mut xra);
    for k in 0..xs.len() {
        put(&mut s.qubits, &x, k, xs[k]);
        put(&mut s.qubits, &y, k, ys[k]);
        put(&mut sf.qubits, &x, k, xs[k]);
        put(&mut sf.qubits, &y, k, ys[k]);
        put(&mut sa.qubits, &x, k, xs[k]);
        put(&mut sa.qubits, &y, k, ys[k]);
    }
    sf.apply_iter(b.ops[..n1].iter());
    sa.apply_iter(b.ops[..na].iter());
    s.apply_iter(b.ops.iter());
    let mut ms: Vec<Gm> = xs.iter().map(|&v| Gm::new(v)).collect();
    for t in 1..=sch.s {
        for mm in &mut ms {
            mm.tick(t, &sch, qb);
        }
    }
    let mut other: Vec<QubitId> = w.a[256..].to_vec();
    other.extend(&w.bb);
    other.extend(&w.q);
    other.extend(&w.h);
    other.extend(&w.log);
    let value_len = sch.c[sch.s + 1];
    let cofactor_len = sch.w - value_len;
    let fq: Vec<QubitId> = (0..value_len).map(|j| w.bf(j)).collect();
    let cfq: Vec<QubitId> = (0..cofactor_len).map(|j| w.asig(sch.s + 1, j)).collect();
    let key = w.bf(1);
    let pm = p();
    let endpoint_exp = sch.s - usize::from(HALF_COFACTOR_G);
    let two_s = N::from(2u64).pow_mod(N::from(endpoint_exp as u64), pm);
    let smod = |v: N| {
        if v.bit(TOP) {
            let a = (!v).wrapping_add(N::from(1u64)) % pm;
            if a == N::ZERO { N::ZERO } else { pm - a }
        } else {
            v % pm
        }
    };
    let mut clean = 0;
    let mut predicted = 0;
    let mut repaired = 0;
    for k in 0..xs.len() {
        let f = get_s(&sf.qubits, &fq, k);
        let cf = get_s(&sf.qubits, &cfq, k);
        let output_ok = smod(f).mul_mod(smod(cf), pm).mul_mod(xs[k], pm) == two_s;
        let key_neg = (sa.qubits[key.0 as usize] >> k) & 1 != 0;
        let acf = smod(get_s(&sa.qubits, &cfq, k));
        let adapter_output = acf.mul_mod(xs[k], pm);
        let adapter_relation_ok = adapter_output == if key_neg { pm - two_s } else { two_s };
        let mut adapter_keep = vec![false; sa.qubits.len()];
        for &q in y.iter().chain(cfq.iter()).chain(w.h.iter()).chain(w.log.iter()) {
            adapter_keep[q.0 as usize] = true;
        }
        adapter_keep[key.0 as usize] = true;
        let adapter_residue_ok = sa
            .qubits
            .iter()
            .enumerate()
            .all(|(i, row)| adapter_keep[i] || ((row >> k) & 1 == 0));
        let adapter_ok = adapter_relation_ok && adapter_residue_ok;
        let xok = get_s(&s.qubits, &x, k) & ((N::from(1u64) << 256) - N::from(1u64)) == xs[k];
        let yok = get_s(&s.qubits, &y, k) & ((N::from(1u64) << 256) - N::from(1u64)) == ys[k];
        let anc_ok = other.iter().all(|q| (s.qubits[q.0 as usize] >> k) & 1 == 0);
        let phase_ok = (s.phase >> k) & 1 == 0;
        let roundtrip_ok = xok && yok && anc_ok && phase_ok;
        let hsign_park_ok = ((sf.qubits[w.h[HB - 2].0 as usize] ^ sf.qubits[w.h[HB - 1].0 as usize]) >> k) & 1 == 0;
        let model_fail = ms[k].bad || ms[k].pm.g != N::ZERO;
        if model_fail {
            if output_ok && adapter_ok && roundtrip_ok
                && ms[k].pm.bad.as_ref().is_some_and(|reason| reason.starts_with("cap log overflow"))
            {
                // L4's repaired encoding intentionally rescues the benign
                // third-push subset that the pre-L4 predictor marks log3.
                repaired += 1;
            } else {
                predicted += 1;
                assert!(!output_ok || !adapter_ok || !roundtrip_ok, "shot {k}: predicted failure passed every gate check");
            }
        } else {
            clean += 1;
            assert!(hsign_park_ok, "shot {k}: endpoint h sign lane is not parkable");
            assert!(output_ok, "shot {k}: unexplained forward-output failure");
            assert!(adapter_ok, "shot {k}: unexplained adapter failure");
            assert!(
                roundtrip_ok,
                "shot {k}: unexplained round-trip/phase/ancilla failure xok={xok} yok={yok} anc_ok={anc_ok} phase_ok={phase_ok}"
            );
        }
    }
    eprintln!("Lilypad-G replay: {clean} clean exact, {predicted} predicted failures, {repaired} repaired cap cases, 0 unexplained");
}

#[test]
#[ignore]
fn lilypad_l2_negative_controls() {
    std::env::set_var("LILYPAD_CAPQ", "11");
    std::env::set_var("LILYPAD_K", "2");
    let rho_corpus = format!(
        "{}/../research/pdhd-892-handoff/probes/r8_combined/corpora/rho.txt",
        env!("CARGO_MANIFEST_DIR")
    );
    for mode in [1u8, 2, 3, 4, 5, 7] {
        if mode == 7 {
            std::env::set_var("LILYPAD_G_XFILE", &rho_corpus);
            std::env::set_var("LILYPAD_G_BATCH", "0");
        } else {
            std::env::remove_var("LILYPAD_G_XFILE");
            std::env::set_var("LILYPAD_SEED", format!("{}", 0x7200 + mode as usize));
        }
        super::lilypad::l2_test_neg(mode);
        let failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(lilypad_g_count));
        super::lilypad::l2_test_neg(0);
        assert!(failed.is_err(), "L2 negative control mode {mode} did not fire");
    }
    std::env::remove_var("LILYPAD_G_XFILE");
    std::env::remove_var("LILYPAD_G_BATCH");
}

#[test]
#[ignore]
fn lilypad_l4_negative_controls() {
    std::env::set_var("LILYPAD_CAPQ", "11");
    std::env::set_var("LILYPAD_K", "2");
    std::env::set_var(
        "LILYPAD_G_XFILE",
        format!(
            "{}/../research/pdhd-892-handoff/probes/r8_combined/corpora/cap1.txt",
            env!("CARGO_MANIFEST_DIR")
        ),
    );
    std::env::set_var("LILYPAD_G_BATCH", "0");
    for mode in [1u8, 2, 3] {
        super::lilypad::l4_test_neg(mode);
        let failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(lilypad_g_count));
        super::lilypad::l4_test_neg(0);
        assert!(failed.is_err(), "L4 negative control mode {mode} did not fire");
    }
    std::env::remove_var("LILYPAD_G_XFILE");
    std::env::remove_var("LILYPAD_G_BATCH");
}

#[test]
#[ignore]
fn lilypad_l5_rare_negative_controls() {
    std::env::set_var("LILYPAD_CAPQ", "11");
    std::env::set_var("LILYPAD_K", "2");
    let corpus = |name: &str| {
        format!(
            "{}/../research/pdhd-892-handoff/probes/r8_combined/corpora/{name}",
            env!("CARGO_MANIFEST_DIR")
        )
    };
    std::env::set_var("LILYPAD_G_BATCH", "0");

    std::env::set_var("LILYPAD_G_XFILE", corpus("mined.txt"));
    super::lilypad::l5_test_neg(1);
    let q11 = std::panic::catch_unwind(std::panic::AssertUnwindSafe(lilypad_g_count));
    super::lilypad::l5_test_neg(0);
    assert!(q11.is_err(), "L5 q11 core-offset control did not fire");

    std::env::set_var("LILYPAD_G_XFILE", corpus("open.txt"));
    super::lilypad::l5_test_neg(2);
    let c6cf1 = std::panic::catch_unwind(std::panic::AssertUnwindSafe(lilypad_g_count));
    super::lilypad::l5_test_neg(0);
    assert!(c6cf1.is_err(), "L5 C6 post-swap-flag control did not fire");

    std::env::set_var("LILYPAD_G_XFILE", corpus("rho.txt"));
    super::lilypad::l2_test_neg(7);
    let rhopub = std::panic::catch_unwind(std::panic::AssertUnwindSafe(lilypad_g_count));
    super::lilypad::l2_test_neg(0);
    assert!(rhopub.is_err(), "L5 public-rho proxy control did not fire");

    std::env::set_var("LILYPAD_G_XFILE", corpus("cap1.txt"));
    super::lilypad_g::g_test_neg(6);
    let noadrho = std::panic::catch_unwind(std::panic::AssertUnwindSafe(lilypad_g_count));
    super::lilypad_g::g_test_neg(0);
    assert!(noadrho.is_err(), "L5 no-adapter-rho control did not fire");

    std::env::remove_var("LILYPAD_G_XFILE");
    std::env::remove_var("LILYPAD_G_BATCH");
}

#[test]
#[ignore]
fn lilypad_g_endpoint_adapter() {
    let sch = sched_g();
    let qb = 13;
    let cap = env_usize("LILYPAD_CAP", 893) as u64;
    let Setup { mut b, y, x, w } = setup(&sch, qb, true, false);
    let g = GScr;
    let room = cap.saturating_sub(b.live + 2 + NT as u64) as usize;
    let sc = PScr::alloc_fwd(&mut b, room);
    let _m = walk_forward_g(&mut b, &w, &sch, &sc, &g, None);
    let adapter = endpoint_adapter_g(&mut b, &w, &sch, &sc);
    let n0 = b.ops.len();
    b.play(&adapter, false);
    let n1 = b.ops.len();
    let cost = super::tests_chunked::expected_t(&b.ops[n0..n1]);
    eprintln!("Lilypad-G endpoint adapter: expected T {cost:.0}, peak {}", b.peak);
    assert!(cost <= 1000.0, "adapter kill threshold exceeded: {cost}");
    let mut rng = Rng::new(0x61_ada7u64);
    let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let ys: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-g-adapter");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
        put(&mut s.qubits, &y, k, ys[k]);
    }
    s.apply_iter(b.ops.iter());
    let pmod = p();
    let endpoint_exp = sch.s - usize::from(HALF_COFACTOR_G);
    let two_s = N::from(2u64).pow_mod(N::from(endpoint_exp as u64), pmod);
    let inv: Vec<QubitId> = (0..sch.w - sch.c[sch.s + 1]).map(|j| w.asig(sch.s + 1, j)).collect();
    let key = w.bf(1);
    let mut ms: Vec<Gm> = xs.iter().map(|&v| Gm::new(v)).collect();
    for t in 1..=sch.s {
        for mm in &mut ms {
            mm.tick(t, &sch, qb);
        }
    }
    let mut exact = 0;
    for k in 0..64 {
        if ms[k].bad || ms[k].pm.g != N::ZERO {
            continue;
        }
        exact += 1;
        let c = get_s(&s.qubits, &inv, k);
        let cmod = if c.bit(TOP) {
            let a = (!c).wrapping_add(N::from(1u64)) % pmod;
            if a == N::ZERO { N::ZERO } else { pmod - a }
        } else {
            c % pmod
        };
        let got = cmod.mul_mod(xs[k], pmod);
        let neg = (s.qubits[key.0 as usize] >> k) & 1 != 0;
        let want = if neg { pmod - two_s } else { two_s };
        assert_eq!(got, want, "shot {k}: Lilypad-G endpoint relation");
        let mut keep = vec![false; s.qubits.len()];
        for &q in y.iter().chain(inv.iter()).chain(w.h.iter()).chain(w.log.iter()) {
            keep[q.0 as usize] = true;
        }
        keep[key.0 as usize] = true;
        for (i, row) in s.qubits.iter().enumerate() {
            if !keep[i] {
                assert_eq!((row >> k) & 1, 0, "shot {k}: adapter residue q{i}");
            }
        }
    }
    eprintln!("Lilypad-G endpoint adapter exact on {exact}/64 shots");
    assert!(exact >= 60);
}
