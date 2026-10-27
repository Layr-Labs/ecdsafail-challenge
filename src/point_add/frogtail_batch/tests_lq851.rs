//! Q851 page (V mod 32): exhaustive gate-level checks of the low-lane arithmetic and formulas of the inverse walk.
use super::*;
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};

fn xof(tag: &[u8]) -> sha3::Shake256Reader {
    let mut h = sha3::Shake256::default();
    h.update(tag);
    h.finalize_xof()
}

fn put(s: &mut [u64], qs: &[QubitId], shot: usize, v: u64) {
    for (k, q) in qs.iter().enumerate() {
        if (v >> k) & 1 == 1 {
            s[q.0 as usize] |= 1u64 << shot;
        } else {
            s[q.0 as usize] &= !(1u64 << shot);
        }
    }
}

fn get(s: &[u64], qs: &[QubitId], shot: usize) -> u64 {
    qs.iter().enumerate().fold(0, |v, (k, q)| v | (((s[q.0 as usize] >> shot) & 1) << k))
}

fn mix(x: u64) -> u64 {
    let mut z = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// Run `nrows` rows (64 per batch): `set` writes row inputs into a fresh state, `check` reads the final state.
fn run_rows(
    b: &B,
    tag: &str,
    nrows: usize,
    set: &dyn Fn(&mut [u64], usize, usize),
    check: &dyn Fn(&[u64], &[u64], usize, usize),
) {
    for batch in 0..nrows.div_ceil(64) {
        let mut xr = xof(format!("{tag}-{batch}").as_bytes());
        let mut s = Simulator::new(b.width() as usize, 1, &mut xr);
        for shot in 0..64 {
            let row = (batch * 64 + shot) % nrows;
            set(&mut s.qubits, shot, row);
        }
        let init = s.qubits.clone();
        s.apply_iter(b.ops.iter());
        assert_eq!(s.phase, 0, "{tag}: phase in batch {batch}");
        for shot in 0..64 {
            let row = (batch * 64 + shot) % nrows;
            check(&init, &s.qubits, shot, row);
        }
    }
}

#[test]
fn lq851_oracle_even_exhaustive() {
    for rho_mode in 0..3 {
        let mut b = B::new();
        let h = b.alloc_n(4);
        let gh = b.alloc_n(4);
        let u = b.alloc_n(4);
        let f = b.alloc_n(4);
        let rq = b.alloc();
        let dirty = b.alloc_n(6);
        let rho = match rho_mode {
            0 => PL::Q(rq),
            1 => PL::C(false),
            _ => PL::C(true),
        };
        b.begin();
        lq_oracle_even(&mut b, &h, &gh, &u, &f, rho, &dirty);
        let o = b.end();
        b.play(&o, false);
        let set = |s: &mut [u64], shot: usize, row: usize| {
            put(s, &gh, shot, row as u64 & 15);
            put(s, &u, shot, (row as u64 >> 4) & 15);
            put(s, &f, shot, (row as u64 >> 8) & 15);
            put(s, &[rq], shot, (row as u64 >> 12) & 1);
            put(s, &dirty, shot, mix(row as u64) & 63);
        };
        let check = |init: &[u64], fin: &[u64], shot: usize, row: usize| {
            let g = 2 * (row as u64 & 15);
            let uu = (row as u64 >> 4) & 15;
            let ff = 1 + 2 * ((row as u64 >> 8) & 15);
            let r = match rho {
                PL::Q(_) => (row >> 12) & 1 == 1,
                PL::C(v) => v,
            };
            let v = lq_ref_v(5, g, ff, uu, r);
            assert_eq!(v & 1, 1);
            assert_eq!(get(fin, &h, shot), v >> 1, "oracle row {row} rho_mode {rho_mode}");
            for qs in [&gh, &u, &f, &dirty] {
                assert_eq!(get(fin, qs, shot), get(init, qs, shot), "restore row {row}");
            }
            assert_eq!(get(fin, &[rq], shot), get(init, &[rq], shot));
        };
        run_rows(&b, "lq851-oracle", 1 << 13, &set, &check);
        // fill then empty: identity
        b.play(&o, true);
        let check0 = |init: &[u64], fin: &[u64], shot: usize, _row: usize| {
            assert_eq!(fin.iter().map(|w| (w >> shot) & 1).collect::<Vec<_>>(),
                       init.iter().map(|w| (w >> shot) & 1).collect::<Vec<_>>());
        };
        run_rows(&b, "lq851-oracle-rt", 1 << 13, &set, &check0);
    }
}

#[test]
fn lq851_codec_hi_exhaustive() {
    for ctl_mode in 0..2 {
        for rho_mode in 0..3 {
            let mut b = B::new();
            let q = b.alloc_n(4);
            let g = b.alloc_n(3);
            let f = b.alloc_n(4);
            let rq = b.alloc();
            let sg = b.alloc();
            let dirty = b.alloc_n(6);
            let rho = match rho_mode {
                0 => PL::Q(rq),
                1 => PL::C(false),
                _ => PL::C(true),
            };
            let ctls: Vec<QubitId> = if ctl_mode == 1 { vec![sg] } else { vec![] };
            lq_codec_hi(&mut b, &q, &g, &f, rho, &ctls, &dirty);
            let set = |s: &mut [u64], shot: usize, row: usize| {
                put(s, &q, shot, row as u64 & 15);
                put(s, &g, shot, (row as u64 >> 4) & 7);
                put(s, &f, shot, (row as u64 >> 7) & 15);
                put(s, &[rq], shot, (row as u64 >> 11) & 1);
                put(s, &[sg], shot, (row as u64 >> 12) & 1);
                put(s, &dirty, shot, mix(row as u64 + 77) & 63);
            };
            let check = |init: &[u64], fin: &[u64], shot: usize, row: usize| {
                let uh = row as u64 & 15;
                let gg = 1 + 2 * ((row as u64 >> 4) & 7);
                let ff = 1 + 2 * ((row as u64 >> 7) & 15);
                let r = match rho {
                    PL::Q(_) => (row >> 11) & 1 == 1,
                    PL::C(v) => v,
                };
                let on = ctl_mode == 0 || (row >> 12) & 1 == 1;
                let v = lq_ref_v(5, gg, ff, 2 * uh, r);
                assert_eq!(v & 1, 1);
                let want = if on { v >> 1 } else { uh };
                assert_eq!(get(fin, &q, shot), want, "codec row {row} ctl {ctl_mode} rho {rho_mode}");
                for qs in [&g, &f, &dirty] {
                    assert_eq!(get(fin, qs, shot), get(init, qs, shot), "restore row {row}");
                }
                assert_eq!(get(fin, &[rq, sg], shot), get(init, &[rq, sg], shot));
            };
            run_rows(&b, "lq851-codec", 1 << 13, &set, &check);
        }
    }
}

/// The step core: hosts <- V'_hi (post state), back to V_hi, the full cofactor add on hosts + stored lanes, hosts
/// cleared; stored lanes must hold the high part of V + (-1)^s U and every other lane must be restored.
#[test]
fn lq851_step_core_flow_exhaustive_low() {
    for sinv in [false, true] {
        let mut b2 = B::new();
        let hosts = b2.alloc_n(4);
        let hi = b2.alloc_n(3);
        let gh = b2.alloc_n(4); // G' lanes 1..4 (G' even)
        let u = b2.alloc_n(8);
        let f = b2.alloc_n(4); // F lanes 1..4
        let rq = b2.alloc();
        let e = b2.alloc();
        let dirty = b2.alloc_n(6);
        let negs = vec![e, rq];
        let rho = PL::Q(rq);
        b2.begin();
        lq_oracle_even(&mut b2, &hosts, &gh, &u[..4], &f, rho, &dirty);
        let o = b2.end();
        b2.play(&o, false);
        b2.begin();
        page_xor_sign(&mut b2, &hosts, &negs, sinv);
        ttk_add_hooked_t0s(&mut b2, &u[..5], &hosts, &negs, sinv, &[]);
        page_xor_sign(&mut b2, &hosts, &negs, sinv);
        let la = b2.end();
        b2.play(&la, true);
        let mut bc = hosts.clone();
        bc.extend(&hi);
        page_xor_sign(&mut b2, &bc, &negs, sinv);
        ttk_add_hooked_t0s(&mut b2, &u, &bc, &negs, sinv, &[]);
        page_xor_sign(&mut b2, &bc, &negs, sinv);
        b2.play(&o, true);
        // rows: G (pre, odd, low 5 bits), F odd low 5, U 8 bits, rho, e, stored V hi 3 bits
        let row_parts = |row: usize| {
            let x = mix(row as u64 * 3 + sinv as u64);
            let g = 1 + 2 * (x & 15);
            let ff = 1 + 2 * ((x >> 4) & 15);
            let uu = (x >> 8) & 255;
            let r = (x >> 16) & 1;
            let ee = (x >> 17) & 1;
            let vhi = (x >> 18) & 7;
            (g, ff, uu, r, ee, vhi, x >> 21)
        };
        let set = |s: &mut [u64], shot: usize, row: usize| {
            let (g, ff, uu, r, ee, vhi, dv) = row_parts(row);
            let sgn = (ee ^ r ^ sinv as u64) & 1;
            // value add done classically: G' = G + (-1)^s F
            let gp = if sgn == 0 { g.wrapping_add(ff) } else { g.wrapping_sub(ff) } & 31;
            assert_eq!(gp & 1, 0);
            put(s, &gh, shot, gp >> 1);
            put(s, &f, shot, ff >> 1);
            put(s, &u, shot, uu);
            put(s, &[rq], shot, r);
            put(s, &[e], shot, ee);
            put(s, &hi, shot, vhi);
            put(s, &dirty, shot, dv & 63);
        };
        let check = |init: &[u64], fin: &[u64], shot: usize, row: usize| {
            let (g, ff, uu, r, ee, vhi, _) = row_parts(row);
            let sgn = (ee ^ r ^ sinv as u64) & 1;
            let vlow = lq_ref_v(5, g, ff, uu & 31, r == 1);
            let v = vlow + 32 * vhi;
            let vn = if sgn == 0 { v.wrapping_add(uu) } else { v.wrapping_sub(uu) } & 255;
            assert_eq!(get(fin, &hosts, shot), 0, "hosts clean row {row} sinv {sinv}");
            assert_eq!(get(fin, &hi, shot), vn >> 5, "stored high row {row} sinv {sinv}");
            // post-step identity on the low lanes
            let gp = if sgn == 0 { g.wrapping_add(ff) } else { g.wrapping_sub(ff) } & 31;
            assert_eq!(vn & 31, lq_ref_v(5, gp, ff, uu & 31, r == 1), "identity row {row}");
            for qs in [&gh, &u, &f, &dirty] {
                assert_eq!(get(fin, qs, shot), get(init, qs, shot), "restore row {row}");
            }
            assert_eq!(get(fin, &[rq, e], shot), get(init, &[rq, e], shot));
        };
        run_rows(&b2, "lq851-step", 1 << 15, &set, &check);
    }
}

/// ANF formulas against the reference on random rows, with the shapes the walk uses (distinct lanes, U0 hosted,
/// sign-extended narrow frames, D_k with its control).
#[test]
fn lq851_anf_shapes() {
    for narrow in [5usize, 4, 3] {
        for (kind, u0h, g0, ctl) in [
            (LqKind::V, false, false, false),
            (LqKind::V, true, true, false),
            (LqKind::D, true, true, true),
            (LqKind::V, false, true, false),
        ] {
            for bit in 1..5usize {
                let mut b = B::new();
                let gl = b.alloc_n(4);
                let fl = b.alloc_n(4);
                let ul = b.alloc_n(5);
                let rq = b.alloc();
                let c = b.alloc();
                let t = b.alloc();
                let dirty = b.alloc_n(7);
                let lane = |j: usize| j.min(narrow - 1);
                let g: Vec<PL> = std::iter::once(PL::C(g0)).chain((1..5).map(|j| PL::Q(gl[lane(j) - 1]))).collect();
                let f: Vec<PL> = std::iter::once(PL::C(true)).chain((1..5).map(|j| PL::Q(fl[lane(j) - 1]))).collect();
                let mut u: Vec<PL> = (0..5).map(|s| if s == 0 && u0h { PL::C(false) } else { PL::Q(ul[s]) }).collect();
                if kind == LqKind::D {
                    for x in u.iter_mut().skip(bit) {
                        *x = PL::C(false);
                    }
                }
                lq_vr_xor(&mut b, 5, kind, bit, &g, &f, &u, PL::Q(rq), if ctl { Some(c) } else { None }, t, &dirty);
                let set = |s: &mut [u64], shot: usize, row: usize| {
                    let x = mix(row as u64 + 1000 * bit as u64);
                    put(s, &gl, shot, x & 15);
                    put(s, &fl, shot, (x >> 4) & 15);
                    put(s, &ul, shot, (x >> 8) & 31);
                    put(s, &[rq, c, t], shot, (x >> 13) & 7);
                    put(s, &dirty, shot, (x >> 16) & 127);
                };
                let check = |init: &[u64], fin: &[u64], shot: usize, row: usize| {
                    let x = mix(row as u64 + 1000 * bit as u64);
                    let val = |l: &[PL], words: &[u64]| -> u64 {
                        l.iter().enumerate().fold(0, |v, (k, p)| {
                            v | (match p {
                                PL::C(c) => *c as u64,
                                PL::Q(q) => (words[q.0 as usize] >> shot) & 1,
                            } << k)
                        })
                    };
                    let (gv, fv, uv) = (val(&g, init), val(&f, init), val(&u, init));
                    // the sign-extended G, F are the narrow signed values themselves
                    let mut want = lq_ref_v(5, gv, fv, uv, (x >> 13) & 1 == 1) >> bit & 1;
                    if kind == LqKind::D {
                        // D_k = V_k ^ U_k with the true U (U_k and above in their lanes)
                        let ufull = (0..5).fold(0u64, |v, s| {
                            v | (if s == 0 && u0h { 0 } else { (init[ul[s].0 as usize] >> shot) & 1 } << s)
                        });
                        want = (lq_ref_v(5, gv, fv, ufull, (x >> 13) & 1 == 1) ^ ufull) >> bit & 1;
                    }
                    let on = !ctl || (x >> 14) & 1 == 1;
                    let t0 = (x >> 15) & 1;
                    assert_eq!(get(fin, &[t], shot), t0 ^ (want & on as u64), "anf narrow {narrow} kind {kind:?} bit {bit} row {row}");
                    for qs in [&gl, &fl, &ul, &dirty] {
                        assert_eq!(get(fin, qs, shot), get(init, qs, shot));
                    }
                };
                run_rows(&b, "lq851-anf", 4096, &set, &check);
            }
        }
    }
}
