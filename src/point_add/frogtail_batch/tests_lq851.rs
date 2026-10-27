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
    for (n, g1_one) in [(4usize, false), (4, true), (5, true), (5, false)] {
        for rho_mode in 0..3 {
            let mut b = B::new();
            let h = b.alloc_n(n);
            let ngh = if g1_one { n - 1 } else { n };
            let gh = b.alloc_n(ngh);
            let u = b.alloc_n(n);
            let f = b.alloc_n(n);
            let rq = b.alloc();
            let dirty = b.alloc_n(6);
            let rho = match rho_mode {
                0 => PL::Q(rq),
                1 => PL::C(false),
                _ => PL::C(true),
            };
            b.begin();
            lq_oracle_even(&mut b, &h, &gh, &u, &f, rho, &dirty, g1_one);
            let o = b.end();
            b.play(&o, false);
            let m = (1u64 << n) - 1;
            let mg = (1u64 << ngh) - 1;
            let parts = |row: usize| {
                let x = row as u64;
                (x & mg, (x >> ngh) & m, (x >> (ngh + n)) & m, (x >> (ngh + 2 * n)) & 1)
            };
            let nrows = 1usize << (ngh + 2 * n + 1);
            let set = |s: &mut [u64], shot: usize, row: usize| {
                let (gg, uu, ff, rr) = parts(row);
                put(s, &gh, shot, gg);
                put(s, &u, shot, uu);
                put(s, &f, shot, ff);
                put(s, &[rq], shot, rr);
                put(s, &dirty, shot, mix(row as u64) & 63);
            };
            let check = |init: &[u64], fin: &[u64], shot: usize, row: usize| {
                let (gg, uu, ff, rr) = parts(row);
                let g = if g1_one { 2 + 4 * gg } else { 2 * gg };
                let r = match rho {
                    PL::Q(_) => rr == 1,
                    PL::C(v) => v,
                };
                let v = lq_ref_v(n + 1, g, 1 + 2 * ff, uu, r);
                assert_eq!(v & 1, 1);
                assert_eq!(get(fin, &h, shot), v >> 1, "oracle n {n} g1 {g1_one} row {row} rho_mode {rho_mode}");
                for qs in [&gh, &u, &f, &dirty] {
                    assert_eq!(get(fin, qs, shot), get(init, qs, shot), "restore row {row}");
                }
                assert_eq!(get(fin, &[rq], shot), get(init, &[rq], shot));
            };
            run_rows(&b, "lq851-oracle", nrows, &set, &check);
            b.play(&o, true);
            let check0 = |init: &[u64], fin: &[u64], shot: usize, _row: usize| {
                assert_eq!(
                    fin.iter().map(|w| (w >> shot) & 1).collect::<Vec<_>>(),
                    init.iter().map(|w| (w >> shot) & 1).collect::<Vec<_>>()
                );
            };
            run_rows(&b, "lq851-oracle-rt", nrows, &set, &check0);
        }
    }
}

#[test]
fn lq851_codec_hi_exhaustive() {
    for n in [4usize, 5] {
        for ctl_mode in 0..2 {
            for rho_mode in 0..3 {
                let mut b = B::new();
                let q = b.alloc_n(n);
                let g = b.alloc_n(n - 1);
                let f = b.alloc_n(n);
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
                let m = (1u64 << n) - 1;
                let parts = |row: usize| {
                    let x = row as u64;
                    (x & m, (x >> n) & (m >> 1), (x >> (2 * n - 1)) & m, (x >> (3 * n - 1)) & 1, (x >> (3 * n)) & 1)
                };
                let set = |s: &mut [u64], shot: usize, row: usize| {
                    let (qq, gg, ff, rr, ss) = parts(row);
                    put(s, &q, shot, qq);
                    put(s, &g, shot, gg);
                    put(s, &f, shot, ff);
                    put(s, &[rq], shot, rr);
                    put(s, &[sg], shot, ss);
                    put(s, &dirty, shot, mix(row as u64 + 77) & 63);
                };
                let check = |init: &[u64], fin: &[u64], shot: usize, row: usize| {
                    let (uh, gg, ff, rr, ss) = parts(row);
                    let r = match rho {
                        PL::Q(_) => rr == 1,
                        PL::C(v) => v,
                    };
                    let on = ctl_mode == 0 || ss == 1;
                    let v = lq_ref_v(n + 1, 1 + 2 * gg, 1 + 2 * ff, 2 * uh, r);
                    assert_eq!(v & 1, 1);
                    let want = if on { v >> 1 } else { uh };
                    assert_eq!(get(fin, &q, shot), want, "codec n {n} row {row} ctl {ctl_mode} rho {rho_mode}");
                    for qs in [&g, &f, &dirty] {
                        assert_eq!(get(fin, qs, shot), get(init, qs, shot), "restore row {row}");
                    }
                    assert_eq!(get(fin, &[rq, sg], shot), get(init, &[rq, sg], shot));
                };
                run_rows(&b, "lq851-codec", 1usize << (3 * n + 1), &set, &check);
            }
        }
    }
}

/// The step core: hosts <- V'_hi (post state), back to V_hi, the full cofactor add on hosts + stored lanes, hosts
/// cleared; stored lanes must hold the high part of V + (-1)^s U and every other lane must be restored. With
/// `g1_one` the digit rule is imposed (s = G1 ^ F1, so G' = 2 mod 4) and the G' lane 1 is not read.
#[test]
fn lq851_step_core_flow() {
    for (r, g1_one) in [(5usize, false), (5, true), (6, true)] {
        for sinv in [false, true] {
            let n = r - 1;
            let mut b2 = B::new();
            let hosts = b2.alloc_n(n);
            let hi = b2.alloc_n(3);
            let gh = b2.alloc_n(if g1_one { n - 1 } else { n });
            let u = b2.alloc_n(r + 3);
            let f = b2.alloc_n(n);
            let rq = b2.alloc();
            let e = b2.alloc();
            let dirty = b2.alloc_n(6);
            let negs = vec![e, rq];
            b2.begin();
            lq_oracle_even(&mut b2, &hosts, &gh, &u[..n], &f, PL::Q(rq), &dirty, g1_one);
            let o = b2.end();
            b2.play(&o, false);
            b2.begin();
            page_xor_sign(&mut b2, &hosts, &negs, sinv);
            ttk_add_hooked_t0s(&mut b2, &u[..r], &hosts, &negs, sinv, &[]);
            page_xor_sign(&mut b2, &hosts, &negs, sinv);
            let la = b2.end();
            b2.play(&la, true);
            let mut bc = hosts.clone();
            bc.extend(&hi);
            page_xor_sign(&mut b2, &bc, &negs, sinv);
            ttk_add_hooked_t0s(&mut b2, &u, &bc, &negs, sinv, &[]);
            page_xor_sign(&mut b2, &bc, &negs, sinv);
            b2.play(&o, true);
            let mr = (1u64 << r) - 1;
            let mw = (1u64 << (r + 3)) - 1;
            let row_parts = |row: usize| {
                let x = mix(row as u64 * 3 + sinv as u64 + 100 * r as u64);
                let g = 1 | (x & mr);
                let ff = 1 | ((x >> 8) & mr);
                let uu = (x >> 16) & mw;
                let rr = (x >> 26) & 1;
                let mut ee = (x >> 27) & 1;
                if g1_one {
                    // digit rule: s = e ^ rho ^ sinv = G1 ^ F1
                    ee = ((g >> 1) ^ (ff >> 1) ^ rr ^ sinv as u64) & 1;
                }
                let vhi = (x >> 28) & 7;
                (g, ff, uu, rr, ee, vhi, x >> 32)
            };
            let set = |s: &mut [u64], shot: usize, row: usize| {
                let (g, ff, uu, rr, ee, vhi, dv) = row_parts(row);
                let sgn = (ee ^ rr ^ sinv as u64) & 1;
                let gp = if sgn == 0 { g.wrapping_add(ff) } else { g.wrapping_sub(ff) } & mr;
                assert_eq!(gp & 1, 0);
                if g1_one {
                    assert_eq!(gp & 3, 2);
                    put(s, &gh, shot, gp >> 2);
                } else {
                    put(s, &gh, shot, gp >> 1);
                }
                put(s, &f, shot, ff >> 1);
                put(s, &u, shot, uu);
                put(s, &[rq], shot, rr);
                put(s, &[e], shot, ee);
                put(s, &hi, shot, vhi);
                put(s, &dirty, shot, dv & 63);
            };
            let check = |init: &[u64], fin: &[u64], shot: usize, row: usize| {
                let (g, ff, uu, rr, ee, vhi, _) = row_parts(row);
                let sgn = (ee ^ rr ^ sinv as u64) & 1;
                let vlow = lq_ref_v(r, g, ff, uu & mr, rr == 1);
                let v = vlow + (vhi << r);
                let vn = if sgn == 0 { v.wrapping_add(uu) } else { v.wrapping_sub(uu) } & mw;
                assert_eq!(get(fin, &hosts, shot), 0, "hosts clean r {r} row {row} sinv {sinv}");
                assert_eq!(get(fin, &hi, shot), vn >> r, "stored high r {r} row {row} sinv {sinv}");
                let gp = if sgn == 0 { g.wrapping_add(ff) } else { g.wrapping_sub(ff) } & mr;
                assert_eq!(vn & mr, lq_ref_v(r, gp, ff, uu & mr, rr == 1), "identity row {row}");
                for qs in [&gh, &u, &f, &dirty] {
                    assert_eq!(get(fin, qs, shot), get(init, qs, shot), "restore row {row}");
                }
                assert_eq!(get(fin, &[rq, e], shot), get(init, &[rq, e], shot));
            };
            run_rows(&b2, "lq851-step", 1 << 15, &set, &check);
        }
    }
}

/// ANF formulas against the reference on random rows, with the shapes the walk uses (distinct lanes, U0 hosted,
/// sign-extended narrow frames, D_k with its control, constant G1).
#[test]
fn lq851_anf_shapes() {
    for r in [5usize, 6] {
        for narrow in [r, 5, 4, 3] {
            for (kind, u0h, g0, ctl, g1c) in [
                (LqKind::V, false, false, false, false),
                (LqKind::V, false, false, false, true),
                (LqKind::V, true, true, false, false),
                (LqKind::D, true, true, true, false),
                (LqKind::V, false, true, false, false),
            ] {
                for bit in 1..r {
                    let mut b = B::new();
                    let gl = b.alloc_n(r - 1);
                    let fl = b.alloc_n(r - 1);
                    let ul = b.alloc_n(r);
                    let rq = b.alloc();
                    let c = b.alloc();
                    let t = b.alloc();
                    let dirty = b.alloc_n(8);
                    let lane = |j: usize| j.min(narrow - 1);
                    let g: Vec<PL> = std::iter::once(PL::C(g0))
                        .chain((1..r).map(|j| if j == 1 && g1c { PL::C(true) } else { PL::Q(gl[lane(j) - 1]) }))
                        .collect();
                    let f: Vec<PL> = std::iter::once(PL::C(true)).chain((1..r).map(|j| PL::Q(fl[lane(j) - 1]))).collect();
                    let mut u: Vec<PL> = (0..r).map(|s| if s == 0 && u0h { PL::C(false) } else { PL::Q(ul[s]) }).collect();
                    if kind == LqKind::D {
                        for x in u.iter_mut().skip(bit) {
                            *x = PL::C(false);
                        }
                    }
                    lq_vr_xor(&mut b, r, kind, bit, &g, &f, &u, PL::Q(rq), if ctl { Some(c) } else { None }, t, &dirty);
                    let seed = 1000 * bit as u64 + 77 * r as u64 + narrow as u64;
                    let set = |s: &mut [u64], shot: usize, row: usize| {
                        let x = mix(row as u64 + seed);
                        put(s, &gl, shot, x & 31);
                        put(s, &fl, shot, (x >> 5) & 31);
                        put(s, &ul, shot, (x >> 10) & 63);
                        put(s, &[rq, c, t], shot, (x >> 16) & 7);
                        put(s, &dirty, shot, (x >> 19) & 255);
                    };
                    let check = |init: &[u64], fin: &[u64], shot: usize, row: usize| {
                        let x = mix(row as u64 + seed);
                        let val = |l: &[PL], words: &[u64]| -> u64 {
                            l.iter().enumerate().fold(0, |v, (k, p)| {
                                v | (match p {
                                    PL::C(c) => *c as u64,
                                    PL::Q(q) => (words[q.0 as usize] >> shot) & 1,
                                } << k)
                            })
                        };
                        let (gv, fv) = (val(&g, init), val(&f, init));
                        let ufull = (0..r).fold(0u64, |v, s| {
                            v | (if s == 0 && u0h { 0 } else { (init[ul[s].0 as usize] >> shot) & 1 } << s)
                        });
                        let rr = (x >> 16) & 1 == 1;
                        let want = if kind == LqKind::D {
                            (lq_ref_v(r, gv, fv, ufull, rr) ^ ufull) >> bit & 1
                        } else {
                            lq_ref_v(r, gv, fv, val(&u, init), rr) >> bit & 1
                        };
                        let on = !ctl || (x >> 17) & 1 == 1;
                        let t0 = (x >> 18) & 1;
                        assert_eq!(get(fin, &[t], shot), t0 ^ (want & on as u64), "anf r {r} narrow {narrow} kind {kind:?} bit {bit} row {row}");
                        for qs in [&gl, &fl, &ul, &dirty] {
                            assert_eq!(get(fin, qs, shot), get(init, qs, shot));
                        }
                    };
                    run_rows(&b, "lq851-anf", 2048, &set, &check);
                }
            }
        }
    }
}

/// Q849 step core with V0, V1 virtual: hosts <- V'2.. (post state, G' = 2 mod 4), low add undone, full add with the
/// two-lane virtual carry, hosts cleared; for every page width used (6 on the narrow frames, 7).
#[test]
fn lq849_step_core_v1_virtual() {
    for re in [6usize, 7] {
        for sinv in [false, true] {
            for flip in [false, true] {
                let m = re - 2;
                let mut b2 = B::new();
                let hosts = b2.alloc_n(m);
                let hi = b2.alloc_n(3);
                let g2 = b2.alloc_n(m); // G' lanes 2..re-1
                let u = b2.alloc_n(re + 3);
                let f = b2.alloc_n(re - 1); // F lanes 1..re-1
                let rq = b2.alloc();
                let e = b2.alloc();
                let dirty = b2.alloc_n(8);
                let rho = ParityCtl { qs: vec![rq], flip };
                let negs = vec![e, rq];
                let sv = sinv;
                let k = flip ^ sv;
                let r = lq_fold(&mut b2, &rho);
                b2.begin();
                lq_oracle_even_z(&mut b2, &hosts, &g2, &u[..re - 1], &f, r, &dirty);
                let o = b2.end();
                lq_unfold(&mut b2, &rho);
                // fill
                lq_fold(&mut b2, &rho);
                b2.play(&o, false);
                lq_unfold(&mut b2, &rho);
                let c2 = |b: &mut B| lq_c2_xor(b, u[2], u[0], u[1], f[0], &rho, e, k, &dirty);
                b2.begin();
                page_xor_sign(&mut b2, &hosts, &negs, sv);
                ttk_add_hooked_t01v(&mut b2, &u[..re], &hosts, &c2, &[]);
                page_xor_sign(&mut b2, &hosts, &negs, sv);
                let la = b2.end();
                b2.play(&la, true);
                let mut bc = hosts.clone();
                bc.extend(&hi);
                page_xor_sign(&mut b2, &bc, &negs, sv);
                ttk_add_hooked_t01v(&mut b2, &u, &bc, &c2, &[]);
                page_xor_sign(&mut b2, &bc, &negs, sv);
                lq_fold(&mut b2, &rho);
                b2.play(&o, true);
                lq_unfold(&mut b2, &rho);
                let mr = (1u64 << re) - 1;
                let mw = (1u64 << (re + 3)) - 1;
                let row_parts = |row: usize| {
                    let x = mix(row as u64 * 7 + 13 * re as u64 + 2 * sv as u64 + flip as u64);
                    let g = 1 | (x & mr);
                    let ff = 1 | ((x >> 8) & mr);
                    let uu = (x >> 16) & mw;
                    let rl = (x >> 28) & 1; // lane value; rho = rl ^ flip
                    let rr = rl ^ flip as u64;
                    // digit rule: s = e ^ rho ^ (flip ^ sinv) ^ ... ; choose e so that s = G1 ^ F1
                    let ee = ((g >> 1) ^ (ff >> 1) ^ rl ^ sv as u64) & 1;
                    let vhi = (x >> 29) & 7;
                    (g, ff, uu, rl, rr, ee, vhi, x >> 32)
                };
                let set = |s: &mut [u64], shot: usize, row: usize| {
                    let (g, ff, uu, rl, _rr, ee, vhi, dv) = row_parts(row);
                    let sgn = (ee ^ rl ^ sv as u64) & 1;
                    let gp = if sgn == 0 { g.wrapping_add(ff) } else { g.wrapping_sub(ff) } & mr;
                    assert_eq!(gp & 3, 2);
                    put(s, &g2, shot, gp >> 2);
                    put(s, &f, shot, ff >> 1);
                    put(s, &u, shot, uu);
                    put(s, &[rq], shot, rl);
                    put(s, &[e], shot, ee);
                    put(s, &hi, shot, vhi);
                    put(s, &dirty, shot, dv & 255);
                };
                let check = |init: &[u64], fin: &[u64], shot: usize, row: usize| {
                    let (g, ff, uu, rl, rr, ee, vhi, _) = row_parts(row);
                    let sgn = (ee ^ rl ^ sv as u64) & 1;
                    let vlow = lq_ref_v(re, g, ff, uu & mr, rr == 1);
                    let v = vlow + (vhi << re);
                    let vn = if sgn == 0 { v.wrapping_add(uu) } else { v.wrapping_sub(uu) } & mw;
                    assert_eq!(get(fin, &hosts, shot), 0, "hosts clean re {re} row {row}");
                    assert_eq!(get(fin, &hi, shot), vn >> re, "stored high re {re} row {row} sinv {sv} flip {flip}");
                    let gp = if sgn == 0 { g.wrapping_add(ff) } else { g.wrapping_sub(ff) } & mr;
                    assert_eq!(vn & mr, lq_ref_v(re, gp, ff, uu & mr, rr == 1), "identity row {row}");
                    for qs in [&g2, &u, &f, &dirty] {
                        assert_eq!(get(fin, qs, shot), get(init, qs, shot), "restore row {row}");
                    }
                    assert_eq!(get(fin, &[rq, e], shot), get(init, &[rq, e], shot));
                };
                run_rows(&b2, "lq849-step", 1 << 15, &set, &check);
            }
        }
    }
}

/// The Q849 post-step oracle on every input (G' = 2 mod 4): h = V'2..V'(r-1).
#[test]
fn lq849_oracle_z_exhaustive() {
    for m in [4usize, 5] {
        let n = m + 1;
        for rho_mode in 0..3 {
            let mut b = B::new();
            let h = b.alloc_n(m);
            let g2 = b.alloc_n(m);
            let u = b.alloc_n(n);
            let f = b.alloc_n(n);
            let rq = b.alloc();
            let dirty = b.alloc_n(8);
            let rho = match rho_mode {
                0 => PL::Q(rq),
                1 => PL::C(false),
                _ => PL::C(true),
            };
            lq_oracle_even_z(&mut b, &h, &g2, &u, &f, rho, &dirty);
            let parts = |row: usize| {
                let x = row as u64;
                let mm = (1u64 << m) - 1;
                let nn = (1u64 << n) - 1;
                (x & mm, (x >> m) & nn, (x >> (m + n)) & nn, (x >> (m + 2 * n)) & 1)
            };
            let set = |s: &mut [u64], shot: usize, row: usize| {
                let (gg, uu, ff, rr) = parts(row);
                put(s, &g2, shot, gg);
                put(s, &u, shot, uu);
                put(s, &f, shot, ff);
                put(s, &[rq], shot, rr);
                put(s, &dirty, shot, mix(row as u64 + 5) & 255);
            };
            let check = |init: &[u64], fin: &[u64], shot: usize, row: usize| {
                let (gg, uu, ff, rr) = parts(row);
                let r = match rho {
                    PL::Q(_) => rr == 1,
                    PL::C(v) => v,
                };
                let v = lq_ref_v(n + 1, 2 + 4 * gg, 1 + 2 * ff, uu, r);
                assert_eq!(v & 1, 1);
                // V'1 is the linear form U0 ^ F1 ^ !rho
                assert_eq!((v >> 1) & 1, (uu & 1) ^ (ff & 1) ^ (!r) as u64);
                assert_eq!(get(fin, &h, shot), v >> 2, "oracle_z m {m} row {row} rho {rho_mode}");
                for qs in [&g2, &u, &f, &dirty] {
                    assert_eq!(get(fin, qs, shot), get(init, qs, shot), "restore row {row}");
                }
                assert_eq!(get(fin, &[rq], shot), get(init, &[rq], shot));
            };
            run_rows(&b, "lq849-oz", 1usize << (m + 2 * n + 1), &set, &check);
        }
    }
}

/// The narrow frames of the Q849 page: sign-extended G' and F lane lists through the V'2.. computation and the
/// in-place swap codec, against the reference on the sign-extended values; and the alias-tolerant add.
#[test]
fn lq849_narrow_frames() {
    for kv in 3usize..=7 {
        for ctl in [false, true] {
            let m = 5usize;
            let n = m + 1;
            let mut b = B::new();
            let h = b.alloc_n(m);
            let gl = b.alloc_n(kv - 2); // G' lanes 2..kv-1
            let u = b.alloc_n(n);
            let fl = b.alloc_n(kv - 1); // F lanes 1..kv-1
            let rq = b.alloc();
            let sg = b.alloc();
            let qq = b.alloc_n(n);
            let dirty = b.alloc_n(8);
            let lane = |j: usize| j.min(kv - 1);
            let g2: Vec<QubitId> = (2..n + 1).map(|j| gl[lane(j) - 2]).collect();
            let f: Vec<QubitId> = (1..n + 1).map(|j| fl[lane(j) - 1]).collect();
            lq_oracle_even_z(&mut b, &h, &g2, &u, &f, PL::Q(rq), &dirty);
            let gs: Vec<QubitId> = (1..n).map(|j| fl[lane(j) - 1]).collect();
            let ctls: Vec<QubitId> = if ctl { vec![sg] } else { vec![] };
            lq_codec_hi(&mut b, &qq, &gs, &f, PL::Q(rq), &ctls, &dirty);
            let sext = |v: u64, bits: usize, width: usize| -> u64 {
                let s = (v >> (bits - 1)) & 1;
                let mut x = v & ((1 << bits) - 1);
                if s == 1 {
                    x |= ((1u64 << width) - 1) & !((1u64 << bits) - 1);
                }
                x
            };
            let row = |r: usize| mix(r as u64 * 37 + kv as u64 * 5 + ctl as u64);
            let set = |s: &mut [u64], shot: usize, r: usize| {
                let x = row(r);
                put(s, &gl, shot, x & 63);
                put(s, &u, shot, (x >> 6) & 63);
                put(s, &fl, shot, (x >> 13) & 63);
                put(s, &[rq], shot, (x >> 20) & 1);
                put(s, &[sg], shot, (x >> 21) & 1);
                put(s, &qq, shot, (x >> 22) & 63);
                put(s, &dirty, shot, (x >> 29) & 255);
            };
            let check = |init: &[u64], fin: &[u64], shot: usize, r: usize| {
                let x = row(r);
                let rr = (x >> 20) & 1 == 1;
                let gw = n + 1;
                let gp = sext(2 + 4 * get(init, &gl, shot), kv, gw);
                let fv = sext(1 + 2 * get(init, &fl, shot), kv, gw);
                let v = lq_ref_v(gw, gp, fv, get(init, &u, shot), rr);
                assert_eq!(get(fin, &h, shot), v >> 2, "narrow z kv {kv} row {r}");
                let uh = get(init, &qq, shot);
                let on = !ctl || (x >> 21) & 1 == 1;
                let vv = lq_ref_v(gw, fv, fv, 2 * uh, rr);
                assert_eq!(get(fin, &qq, shot), if on { vv >> 1 } else { uh }, "narrow codec kv {kv} row {r}");
                for qs in [&gl, &u, &fl, &dirty] {
                    assert_eq!(get(fin, qs, shot), get(init, qs, shot), "restore kv {kv} row {r}");
                }
            };
            run_rows(&b, "lq849-narrow", 1 << 13, &set, &check);
        }
    }
}
