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
    for n in [2usize, 3, 4, 5] {
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

#[test]
fn carry_oracle_all_inputs() {
 for p in 2usize..=6 {
  let mut b=B::new();let u=b.alloc_n(p+1);let g=b.alloc_n(p);let f=b.alloc_n(p);let e=b.alloc();let rq=b.alloc();let target=b.alloc();let dirty=b.alloc_n(12);
  let rho=ParityCtl{qs:vec![rq],flip:false};
  carry_oracle(&mut b,&u,&g,&f,e,&rho,Some(target),&dirty);
  let mask=(1u64<<p)-1;
  let parts=|row:usize|{let x=row as u64;(x&((1<<(p+1))-1),(x>>(p+1))&((1<<(p-1))-1),(x>>(2*p))&mask,(x>>(3*p))&1,(x>>(3*p+1))&1)};
  let set=|s:&mut[u64],shot:usize,row:usize|{let(uu,gg,ff,ee,rr)=parts(row);put(s,&u,shot,uu);put(s,&g[1..],shot,gg);put(s,&f,shot,ff);put(s,&[e],shot,ee);put(s,&[rq],shot,rr);put(s,&dirty,shot,mix(row as u64)&4095);};
  let check=|init:&[u64],fin:&[u64],shot:usize,row:usize|{let(uu,gg,ff,ee,rr)=parts(row);let gp=2+4*gg;let fv=1+2*ff;let sign=1^ee^rr;let gv=if sign==0{gp.wrapping_sub(fv)}else{gp+fv};let v=lq_ref_v(p,gv,fv,uu,rr!=0);let tf=v^if sign!=0{mask}else{0};let carry=((tf&mask)+(uu&mask))>>p;assert_eq!(get(fin,&[target],shot),carry,"carry p{p} row{row}");for q in u.iter().chain(&g).chain(&f).chain([&e,&rq]).chain(&dirty){assert_eq!(get(fin,&[*q],shot),get(init,&[*q],shot),"restore p{p} row{row}");}};
  run_rows(&b,"carry-oracle",1<<(3*p+2),&set,&check);
  b.z_if(target,crate::circuit::NO_BIT);
  carry_oracle(&mut b,&u,&g,&f,e,&rho,None,&dirty);
  carry_oracle(&mut b,&u,&g,&f,e,&rho,Some(target),&dirty);
  let back=|init:&[u64],fin:&[u64],shot:usize,_row:usize|{for q in u.iter().chain(&g).chain(&f).chain([&e,&rq,&target]).chain(&dirty){assert_eq!(get(fin,&[*q],shot),get(init,&[*q],shot));}};
  run_rows(&b,"carry-oracle-phase",1<<(3*p+2),&set,&back);
 }
}

#[test]
fn value_bit_oracle_all_inputs() {
 for p in 2usize..=5 {for post in [false,true] {
  let mut b=B::new();let u=b.alloc_n(p+1);let gh=b.alloc_n(p-1);let f=b.alloc_n(p);let e=b.alloc();let rq=b.alloc();let target=b.alloc();let dirty=b.alloc_n(12);
  let rho=ParityCtl{qs:vec![rq],flip:false};
  value_bit_oracle(&mut b,&u,&gh,&f,e,&rho,Some(target),&dirty,post);
  let mask=(1u64<<p)-1;
  let parts=|row:usize|{let x=row as u64;(x&((1<<(p+1))-1),(x>>(p+1))&((1<<(p-1))-1),(x>>(2*p))&mask,(x>>(3*p))&1,(x>>(3*p+1))&1)};
  let set=|s:&mut[u64],shot:usize,row:usize|{let(uu,gg,ff,ee,rr)=parts(row);put(s,&u,shot,uu);put(s,&gh,shot,gg);put(s,&f,shot,ff);put(s,&[e],shot,ee);put(s,&[rq],shot,rr);put(s,&dirty,shot,mix(row as u64)&4095);};
  let check=|init:&[u64],fin:&[u64],shot:usize,row:usize|{let(uu,gg,ff,ee,rr)=parts(row);let gp=2+4*gg;let fv=1+2*ff;let sign=1^ee^rr;let gv=if post{gp}else if sign==0{gp.wrapping_sub(fv)}else{gp+fv};let v=lq_ref_v(p+1,gv,fv,uu,rr!=0);assert_eq!(get(fin,&[target],shot),(v>>p)&1,"value p{p} post{post} row{row}");for q in u.iter().chain(&gh).chain(&f).chain([&e,&rq]).chain(&dirty){assert_eq!(get(fin,&[*q],shot),get(init,&[*q],shot),"restore p{p} row{row}");}};
  run_rows(&b,"value-bit",1<<(3*p+2),&set,&check);
  b.z_if(target,crate::circuit::NO_BIT);
  value_bit_oracle(&mut b,&u,&gh,&f,e,&rho,None,&dirty,post);
  value_bit_oracle(&mut b,&u,&gh,&f,e,&rho,Some(target),&dirty,post);
  let back=|init:&[u64],fin:&[u64],shot:usize,_row:usize|{for q in u.iter().chain(&gh).chain(&f).chain([&e,&rq,&target]).chain(&dirty){assert_eq!(get(fin,&[*q],shot),get(init,&[*q],shot));}};
  run_rows(&b,"value-bit-phase",1<<(3*p+2),&set,&back);
 }}
}

#[test]
fn recycled_arithmetic_charts_all_inputs(){
 for p in 2usize..=5 {for kind in 0..3 {
  let mut b=B::new();let u=b.alloc_n(p+1);let g=b.alloc_n(p);let f=b.alloc_n(p);let e=b.alloc();let rq=b.alloc();let target=b.alloc();let dirty=b.alloc_n(12);
  let rho=ParityCtl{qs:vec![rq],flip:false};
  let oracle=|b:&mut B,tgt:Option<QubitId>|{if kind==2 {carry_oracle(b,&u,&g,&f,e,&rho,tgt,&dirty)}else{value_bit_oracle(b,&u,&g[1..],&f,e,&rho,tgt,&dirty,kind==1)}};
  if kind==2 {b.low_clean=vec![g[0]];}
  b.begin();oracle(&mut b,Some(target));let compute=b.end();
  b.low_clean.push(target);b.begin();oracle(&mut b,None);let phase=b.end();b.low_clean.clear();
  b.circuit_chart(compute.clone(),phase.clone(),target,crate::circuit::NO_BIT,0);
  b.circuit_chart(compute,phase,target,crate::circuit::NO_BIT,1);
  let mask=(1u64<<p)-1;
  let set=|s:&mut[u64],shot:usize,row:usize|{let x=row as u64;put(s,&u,shot,x&((1<<(p+1))-1));put(s,&g[1..],shot,(x>>(p+1))&((1<<(p-1))-1));put(s,&f,shot,(x>>(2*p))&mask);put(s,&[e],shot,(x>>(3*p))&1);put(s,&[rq],shot,(x>>(3*p+1))&1);put(s,&dirty,shot,mix(x)&4095);};
  let check=|init:&[u64],fin:&[u64],shot:usize,_row:usize|{for q in u.iter().chain(&g).chain(&f).chain([&e,&rq,&target]).chain(&dirty){assert_eq!(get(fin,&[*q],shot),get(init,&[*q],shot));}};
  run_rows(&b,"recycled-charts",1<<(3*p+2),&set,&check);
 }}
}

#[test]
fn signed_short_value_oracles_all_inputs(){
 for p in 3usize..=6 {for kv in 3..=p {for kind in 0..3 {
  let mut b=B::new();let u=b.alloc_n(p+1);let g0=b.alloc();let gh=b.alloc_n(kv-2);let fh=b.alloc_n(kv-1);let e=b.alloc();let rq=b.alloc();let target=b.alloc();let dirty=b.alloc_n(12);
  let g:Vec<_>=std::iter::once(g0).chain((0..p-1).map(|i|gh[i.min(gh.len()-1)])).collect();
  let f:Vec<_>=(0..p).map(|i|fh[i.min(fh.len()-1)]).collect();
  let rho=ParityCtl{qs:vec![rq],flip:false};
  let oracle=|b:&mut B,tgt:Option<QubitId>|{if kind==2{carry_oracle(b,&u,&g,&f,e,&rho,tgt,&dirty)}else{value_bit_oracle(b,&u,&g[1..],&f,e,&rho,tgt,&dirty,kind==1)}};
  if kind==2{b.low_clean=vec![g0];}
  b.begin();oracle(&mut b,Some(target));let compute=b.end();b.play(&compute,false);
  let mask=(1u64<<p)-1;
  let ext=|v:u64,n:usize,m:usize|{if v>>(n-1)&1==0{v}else{v|(((1u64<<m)-1)^((1u64<<n)-1))}};
  let parts=|row:usize|{let x=row as u64;(x&((1<<(p+1))-1),(x>>(p+1))&((1<<(kv-2))-1),(x>>(p+kv-1))&((1<<(kv-1))-1),(x>>(p+2*kv-2))&1,(x>>(p+2*kv-1))&1)};
  let set=|s:&mut[u64],shot:usize,row:usize|{let(uu,gg,ff,ee,rr)=parts(row);put(s,&u,shot,uu);put(s,&gh,shot,gg);put(s,&fh,shot,ff);put(s,&[e],shot,ee);put(s,&[rq],shot,rr);put(s,&dirty,shot,mix(row as u64)&4095);};
  let check=|init:&[u64],fin:&[u64],shot:usize,row:usize|{let(uu,gg,ff,ee,rr)=parts(row);let gp=2+4*ext(gg,kv-2,p-1);let fv=1+2*ext(ff,kv-1,p);let sign=1^ee^rr;let gv=if kind==1{gp}else if sign==0{gp.wrapping_sub(fv)}else{gp+fv};let v=lq_ref_v(p+1,gv,fv,uu,rr!=0);let want=if kind<2{v>>p&1}else{let tf=v^if sign!=0{mask}else{0};((tf&mask)+(uu&mask))>>p};assert_eq!(get(fin,&[target],shot),want,"signed p{p} kv{kv} kind{kind} row{row}");for q in u.iter().chain(&gh).chain(&fh).chain([&e,&rq,&g0]).chain(&dirty){assert_eq!(get(fin,&[*q],shot),get(init,&[*q],shot));}};
  run_rows(&b,"signed-value",1<<(p+2*kv),&set,&check);
  b.low_clean.push(target);b.begin();oracle(&mut b,None);let phase=b.end();b.low_clean.clear();
  b.circuit_chart(compute,phase,target,crate::circuit::NO_BIT,1);
  let back=|init:&[u64],fin:&[u64],shot:usize,_row:usize|{for q in u.iter().chain(&gh).chain(&fh).chain([&e,&rq,&g0,&target]).chain(&dirty){assert_eq!(get(fin,&[*q],shot),get(init,&[*q],shot));}};
  run_rows(&b,"signed-value-erase",1<<(p+2*kv),&set,&back);
 }}}
}

#[test]
fn cuccaro_incoming_receipts_all_inputs(){
 use super::super::chunked::{self,PairKey,Pair,AddRole};
 use crate::circuit::analyze_ops;
 for n in 3usize..=8{for room in [2,3]{
  let mut b=B::new();let a=b.alloc_n(n);let t=b.alloc_n(n);let cin=b.alloc();let pool=b.alloc_n(room);
  let key=PairKey{division:0,tick:1,role:AddRole::Cofactor};
  assert!(chunked::try_add_paired_cin(&mut b,&a,&t,ONE,None,Some(cin),&pool,Some(Pair::Forward(key))));
  let debts=b.take_chunk_debts(key,n,false,true);
  b.begin();chunked::add_with_debts(&mut b,&a,&t,ONE,cin,&[],debts);let back=b.end();b.play(&back,true);
  let(_,nb,_,_)=analyze_ops(b.ops.iter());let mask=(1u64<<n)-1;
  for batch in 0..(1usize<<(2*n+1)).div_ceil(64){
   let mut rng=xof(format!("cin-debts-{n}-{room}-{batch}").as_bytes());let mut sim=Simulator::new(b.width()as usize,nb as usize,&mut rng);
   for shot in 0..64{let row=(batch*64+shot)as u64;put(&mut sim.qubits,&a,shot,row&mask);put(&mut sim.qubits,&t,shot,row>>n&mask);put(&mut sim.qubits,&[cin],shot,row>>(2*n)&1);}
   let init=sim.qubits.clone();sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,init,"cin receipt restore n{n} room{room} batch{batch}");assert_eq!(sim.phase,0,"cin receipt phase n{n} room{room} batch{batch}");
  }
 }}
}

#[test]
fn crossing_swap_all_inputs() {
    for n in [2usize, 3, 4, 5] {
        for ctl_mode in 1..2 {
            for rho_mode in 0..3 {
                let mut b = B::new();
                let q = b.alloc_n(n);
                let g = b.alloc_n(n);
                let f = b.alloc_n(n);
                let rq = b.alloc();
                let sg = b.alloc();
                let dirty = b.alloc_n(6);
                let rho = match rho_mode {
                    0 => PL::Q(rq),
                    1 => PL::C(false),
                    _ => PL::C(true),
                };
                lq_codec_crossing_swap(&mut b,&q,&g,&f,rho,sg,&dirty,|b|{for i in 0..n{b.cswap(sg,g[i],f[i]);}});
                let m = (1u64 << n) - 1;
                let parts = |row: usize| {
                    let x = row as u64;
                    (x & m, (x >> n) & m, (x >> (2 * n)) & m, (x >> (3 * n)) & 1, (x >> (3 * n + 1)) & 1)
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
                    assert_eq!(get(fin,&g,shot),if on{ff}else{gg});
                    assert_eq!(get(fin,&f,shot),if on{gg}else{ff});
                    for qs in [&dirty] {
                        assert_eq!(get(fin, qs, shot), get(init, qs, shot), "restore row {row}");
                    }
                    assert_eq!(get(fin, &[rq, sg], shot), get(init, &[rq, sg], shot));
                };
                run_rows(&b, "lq851-codec", 1usize << (3 * n + 2), &set, &check);
            }
        }
    }
}

#[test]
fn value_bit_output_host_in_loan_list() {
 for p in 2usize..=5 {for post in [false,true] {
  let mut b=B::new();let u=b.alloc_n(p+1);let gh=b.alloc_n(p-1);let f=b.alloc_n(p);let e=b.alloc();let rq=b.alloc();let target=b.alloc();let dirty=b.alloc_n(12);
  let loans:Vec<_>=std::iter::once(target).chain(dirty.iter().copied()).collect();
  let rho=ParityCtl{qs:vec![rq],flip:false};
  value_bit_oracle(&mut b,&u,&gh,&f,e,&rho,Some(target),&loans,post);
  let mask=(1u64<<p)-1;
  let parts=|row:usize|{let x=row as u64;(x&((1<<(p+1))-1),(x>>(p+1))&((1<<(p-1))-1),(x>>(2*p))&mask,(x>>(3*p))&1,(x>>(3*p+1))&1)};
  let set=|s:&mut[u64],shot:usize,row:usize|{let(uu,gg,ff,ee,rr)=parts(row);put(s,&u,shot,uu);put(s,&gh,shot,gg);put(s,&f,shot,ff);put(s,&[e],shot,ee);put(s,&[rq],shot,rr);put(s,&dirty,shot,mix(row as u64)&4095);};
  let check=|init:&[u64],fin:&[u64],shot:usize,row:usize|{let(uu,gg,ff,ee,rr)=parts(row);let gp=2+4*gg;let fv=1+2*ff;let sign=1^ee^rr;let gv=if post{gp}else if sign==0{gp.wrapping_sub(fv)}else{gp+fv};let v=lq_ref_v(p+1,gv,fv,uu,rr!=0);assert_eq!(get(fin,&[target],shot),(v>>p)&1,"value p{p} post{post} row{row}");for q in u.iter().chain(&gh).chain(&f).chain([&e,&rq]).chain(&dirty){assert_eq!(get(fin,&[*q],shot),get(init,&[*q],shot),"restore p{p} row{row}");}};
  run_rows(&b,"value-bit",1<<(3*p+2),&set,&check);
  b.z_if(target,crate::circuit::NO_BIT);
  value_bit_oracle(&mut b,&u,&gh,&f,e,&rho,None,&loans,post);
  value_bit_oracle(&mut b,&u,&gh,&f,e,&rho,Some(target),&loans,post);
  let back=|init:&[u64],fin:&[u64],shot:usize,_row:usize|{for q in u.iter().chain(&gh).chain(&f).chain([&e,&rq,&target]).chain(&dirty){assert_eq!(get(fin,&[*q],shot),get(init,&[*q],shot));}};
  run_rows(&b,"value-bit-phase",1<<(3*p+2),&set,&back);
 }}
}

#[test]
fn post_top_bit_clean_loan_all_inputs(){
 for p in 2usize..=5 {for nc in 0..=2 {
  let mut b=B::new();let u=b.alloc_n(p+1);let gh=b.alloc_n(p-1);let f=b.alloc_n(p);let e=b.alloc();let rq=b.alloc();let host=b.alloc();let dirty=b.alloc_n(12);let clean=b.alloc_n(nc);
  let rho=ParityCtl{qs:vec![rq],flip:false};b.low_clean=clean.clone();
  value_bit_oracle(&mut b,&u,&gh,&f,e,&rho,Some(host),&dirty,true);
  post_top_delta(&mut b,&u,&gh,&f,&rho,&dirty);b.cx(host,u[p-1]);
  let mask=(1u64<<p)-1;
  let parts=|row:usize|{let x=row as u64;(x&((1<<(p+1))-1),(x>>(p+1))&((1<<(p-1))-1),(x>>(2*p))&mask,(x>>(3*p))&1)};
  let set=|s:&mut[u64],shot:usize,row:usize|{let(uu,gg,ff,rr)=parts(row);put(s,&u,shot,uu);put(s,&gh,shot,gg);put(s,&f,shot,ff);put(s,&[rq],shot,rr);put(s,&dirty,shot,mix(row as u64)&4095);};
  let check=|init:&[u64],fin:&[u64],shot:usize,row:usize|{let(uu,gg,ff,rr)=parts(row);let v=lq_ref_v(p+1,2+4*gg,1+2*ff,uu,rr!=0);
   assert_eq!(get(fin,&[host],shot),(v>>p)&1);assert_eq!(get(fin,&u,shot),uu&!(1<<(p-1)),"loan p{p} nc{nc} row{row}");
   for q in gh.iter().chain(&f).chain([&rq,&e]).chain(&dirty).chain(&clean){assert_eq!(get(fin,&[*q],shot),get(init,&[*q],shot));}
  };
  run_rows(&b,"post-top-clean-loan",1<<(3*p+1),&set,&check);
  b.cx(host,u[p-1]);post_top_delta(&mut b,&u,&gh,&f,&rho,&dirty);
  value_bit_oracle(&mut b,&u,&gh,&f,e,&rho,Some(host),&dirty,true);
  let restore=|init:&[u64],fin:&[u64],shot:usize,_row:usize|{for q in u.iter().chain(&gh).chain(&f).chain([&rq,&e,&host]).chain(&dirty).chain(&clean){assert_eq!(get(fin,&[*q],shot),get(init,&[*q],shot));}};
  run_rows(&b,"post-top-clean-loan-restore",1<<(3*p+1),&set,&restore);
 }}
}

#[test]
fn post_top_bit_clean_loan_signed_aliases(){
 let p=5usize;
 for nc in 0..=2 {
  let mut b=B::new();let u=b.alloc_n(p+1);let gs=b.alloc();let fs=b.alloc_n(2);let gh=vec![gs;p-1];let mut f=vec![fs[1];p];f[0]=fs[0];
  let e=b.alloc();let rq=b.alloc();let host=b.alloc();let dirty=b.alloc_n(12);let clean=b.alloc_n(nc);let rho=ParityCtl{qs:vec![rq],flip:false};b.low_clean=clean.clone();
  value_bit_oracle(&mut b,&u,&gh,&f,e,&rho,Some(host),&dirty,true);
  post_top_delta(&mut b,&u,&gh,&f,&rho,&dirty);b.cx(host,u[p-1]);
  let set=|s:&mut[u64],shot:usize,row:usize|{put(s,&u,shot,(row&63)as u64);put(s,&[gs],shot,((row>>6)&1)as u64);put(s,&fs,shot,((row>>7)&3)as u64);put(s,&[rq],shot,((row>>9)&1)as u64);put(s,&dirty,shot,mix(row as u64)&4095);};
  let check=|init:&[u64],fin:&[u64],shot:usize,row:usize|{
   let uu=(row&63)as u64;let gg=if row>>6&1!=0{15}else{0};let ff=((row>>7)&1)as u64+if row>>8&1!=0{30}else{0};let v=lq_ref_v(6,2+4*gg,1+2*ff,uu,row>>9&1!=0);
   assert_eq!(get(fin,&[host],shot),(v>>5)&1);assert_eq!(get(fin,&u,shot),uu&!16);
   for q in fs.iter().chain([&gs,&rq,&e]).chain(&dirty).chain(&clean){assert_eq!(get(fin,&[*q],shot),get(init,&[*q],shot));}
  };
  run_rows(&b,"signed-top-clean-loan",1024,&set,&check);
  b.cx(host,u[p-1]);post_top_delta(&mut b,&u,&gh,&f,&rho,&dirty);value_bit_oracle(&mut b,&u,&gh,&f,e,&rho,Some(host),&dirty,true);
  let check=|init:&[u64],fin:&[u64],shot:usize,_row:usize|{for q in u.iter().chain(&fs).chain([&gs,&rq,&e,&host]).chain(&dirty).chain(&clean){assert_eq!(get(fin,&[*q],shot),get(init,&[*q],shot));}};
  run_rows(&b,"signed-top-clean-loan-restore",1024,&set,&check);
 }
}

#[test]
fn hosted_post_bit_carry_all_inputs(){
 for p in 2usize..=5 {for nc in 0..=2 {
  let mut b=B::new();let u=b.alloc_n(p+1);let gh=b.alloc_n(p-1);let f=b.alloc_n(p);let e=b.alloc();let rq=b.alloc();let host=b.alloc();let target=b.alloc();let dirty=b.alloc_n(12);let clean=b.alloc_n(nc);b.low_clean=clean.clone();let rho=ParityCtl{qs:vec![rq],flip:false};
  value_bit_oracle(&mut b,&u,&gh,&f,e,&rho,Some(host),&dirty,true);
  carry_from_host_oracle(&mut b,&u,&gh,&f,e,&rho,host,Some(target),&dirty);
  let mask=(1u64<<p)-1;
  let parts=|row:usize|{let x=row as u64;(x&((1<<(p+1))-1),(x>>(p+1))&((1<<(p-1))-1),(x>>(2*p))&mask,(x>>(3*p))&1,(x>>(3*p+1))&1)};
  let set=|s:&mut[u64],shot:usize,row:usize|{let(uu,gg,ff,ee,rr)=parts(row);put(s,&u,shot,uu);put(s,&gh,shot,gg);put(s,&f,shot,ff);put(s,&[e],shot,ee);put(s,&[rq],shot,rr);put(s,&dirty,shot,mix(row as u64)&4095);};
  let check=|init:&[u64],fin:&[u64],shot:usize,row:usize|{let(uu,gg,ff,ee,rr)=parts(row);let gp=2+4*gg;let fv=1+2*ff;let sign=1^ee^rr;let gv=if sign==0{gp.wrapping_sub(fv)}else{gp+fv};let v=lq_ref_v(p,gv,fv,uu,rr!=0);let tf=v^if sign!=0{mask}else{0};let c=((tf&mask)+(uu&mask))>>p;
   assert_eq!(get(fin,&[target],shot),c);assert_eq!(get(fin,&[host],shot),(lq_ref_v(p+1,gp,fv,uu,rr!=0)>>p)&1);
   for q in u.iter().chain(&gh).chain(&f).chain([&e,&rq]).chain(&dirty).chain(&clean){assert_eq!(get(fin,&[*q],shot),get(init,&[*q],shot));}
  };
  run_rows(&b,"hosted-post-carry",1<<(3*p+2),&set,&check);
  b.z_if(target,crate::circuit::NO_BIT);carry_from_host_oracle(&mut b,&u,&gh,&f,e,&rho,host,None,&dirty);
  carry_from_host_oracle(&mut b,&u,&gh,&f,e,&rho,host,Some(target),&dirty);value_bit_oracle(&mut b,&u,&gh,&f,e,&rho,Some(host),&dirty,true);
  let back=|init:&[u64],fin:&[u64],shot:usize,_row:usize|{for q in u.iter().chain(&gh).chain(&f).chain([&e,&rq,&target,&host]).chain(&dirty).chain(&clean){assert_eq!(get(fin,&[*q],shot),get(init,&[*q],shot));}};
  run_rows(&b,"hosted-post-carry-phase",1<<(3*p+2),&set,&back);
 }}
}

#[test]
fn low_input_coordinate_hosts_suffix_exactly(){
 for p in 2usize..=5 {for nh in 1..=3.min(p-1) {for fused in [false,true] {
  let cut=p+1-nh;
  let mut b=B::new();let u=b.alloc_n(p+3);let gh=b.alloc_n(p-1);let f=b.alloc_n(p);let e=b.alloc();let rq=b.alloc();let ci=b.alloc();let vh=b.alloc_n(2);let dirty=b.alloc_n(12);let clean=b.alloc_n(2);let saved=b.alloc_n(nh-1);let rho=ParityCtl{qs:vec![rq],flip:false};
  let mut g=vec![ci];g.extend_from_slice(&gh[..cut-1]);b.low_clean=clean.clone();
  if fused{value_bit_oracle(&mut b,&u[..=cut],&gh[..cut-1],&f[..cut],e,&rho,Some(ci),&dirty,false);b.cx(u[cut],ci);}else{carry_oracle(&mut b,&u[..=cut],&g,&f[..cut],e,&rho,Some(ci),&dirty);}
  let mut aa=u[cut..].to_vec();for (j,&q) in saved.iter().enumerate(){b.cx(u[cut+j],q);aa[j]=q;}
  b.begin();let rp=lq_fold(&mut b,&rho);lq_codec_hi(&mut b,&u[..p],&gh,&f,rp,&[],&dirty);lq_unfold(&mut b,&rho);let tr=b.end();b.low_clean.clear();b.play(&tr,false);
  let hosts=u[cut-1..p].to_vec();if fused{b.cx(hosts[0],ci);}
  let add=|b:&mut B,aa:&[QubitId],tt:&[QubitId]|{
   for &q in tt{b.x(q);b.cx(e,q);b.cx(rq,q);}
   if tt.len()==1{b.cx(aa[0],tt[0]);b.cx(ci,tt[0]);}else{crate::point_add::frogtail_batch::chunked::add_with_debts(b,aa,tt,ONE,ci,&clean,vec![]);}
   for &q in tt{b.x(q);b.cx(e,q);b.cx(rq,q);}
  };
  b.begin();add(&mut b,&aa[..nh],&hosts);let lo=b.end();b.play(&lo,true);
  let mut tt=hosts;tt.extend_from_slice(&vh);add(&mut b,&aa,&tt);
  if fused{b.cx(u[cut-1],ci);}b.play(&tr,true);for (j,&q) in saved.iter().enumerate(){b.cx(u[cut+j],q);}
  b.low_clean=clean.clone();if fused{b.cx(u[cut],ci);value_bit_oracle(&mut b,&u[..=cut],&gh[..cut-1],&f[..cut],e,&rho,Some(ci),&dirty,false);}else{carry_oracle(&mut b,&u[..=cut],&g,&f[..cut],e,&rho,Some(ci),&dirty);}b.low_clean.clear();
  let mask=(1u64<<p)-1;let parts=|row:usize|{let x=if p==5{mix(row as u64)}else{row as u64};(x&((1<<(p+3))-1),(x>>(p+3))&((1<<(p-1))-1),(x>>(2*p+2))&mask,(x>>(3*p+2))&1,(x>>(3*p+3))&1,(x>>(3*p+4))&3)};
  let set=|s:&mut[u64],shot:usize,row:usize|{let(uu,gg,ff,ee,rr,hh)=parts(row);put(s,&u,shot,uu);put(s,&gh,shot,gg);put(s,&f,shot,ff);put(s,&[e],shot,ee);put(s,&[rq],shot,rr);put(s,&vh,shot,hh);put(s,&dirty,shot,mix(row as u64)&4095);};
  let check=|init:&[u64],fin:&[u64],shot:usize,row:usize|{let(uu,gg,ff,ee,rr,hh)=parts(row);let gp=2+4*gg;let fv=1+2*ff;let sign=1^ee^rr;let gv=if sign==0{gp.wrapping_sub(fv)}else{gp+fv};let vp=lq_ref_v(p+1,gv,fv,uu,rr!=0);let cm=(1<<cut)-1;let carry=((vp&cm)^if sign!=0{cm}else{0})+(uu&cm);let old=(hh<<nh)|((vp>>cut)&((1<<nh)-1));let hm=(1<<(nh+2))-1;let neg=if sign!=0{hm}else{0};let result=(((old^neg)+(uu>>cut)+(carry>>cut))&hm)^neg;
   assert_eq!(get(fin,&vh,shot),result>>nh,"p{p} nh{nh} row{row}");for q in u.iter().chain(&gh).chain(&f).chain([&e,&rq,&ci]).chain(&dirty).chain(&clean).chain(&saved){assert_eq!(get(fin,&[*q],shot),get(init,&[*q],shot),"restore p{p} nh{nh} row{row}");}
  };
  run_rows(&b,"input-coordinate-suffix",if p==5{65536}else{1<<(3*p+6)},&set,&check);
 }}}
}

#[test]
fn pooled_small_constant_additions_exact(){
 for n in 2usize..=5{for nc in 0usize..=2{for clean_n in [0usize,1,3,6]{for k in 1u64..1u64<<n{
  let mut b=B::new();let q=b.alloc_n(n);let ctl=b.alloc_n(nc);let clean=b.alloc_n(clean_n);let dirty=b.alloc_n(12);b.low_clean=clean.clone();
  b.begin();lq_add_const(&mut b,&q,k,&ctl,&dirty);let add=b.end();b.play(&add,false);
  let set=|s:&mut[u64],shot:usize,row:usize|{put(s,&q,shot,(row&((1<<n)-1))as u64);put(s,&ctl,shot,(row>>n)as u64);put(s,&dirty,shot,mix(row as u64)&4095);};
  let check=|init:&[u64],fin:&[u64],shot:usize,row:usize|{let old=(row&((1<<n)-1))as u64;let on=(row>>n)==(1<<nc)-1;assert_eq!(get(fin,&q,shot),(old+if on{k}else{0})&((1<<n)-1),"n{n} nc{nc} clean{clean_n} k{k} row{row}");for x in ctl.iter().chain(&clean).chain(&dirty){assert_eq!(get(fin,&[*x],shot),get(init,&[*x],shot));}};
  run_rows(&b,"pool-constant-add",1<<(n+nc),&set,&check);b.play(&add,true);
  let back=|init:&[u64],fin:&[u64],shot:usize,_row:usize|{for x in q.iter().chain(&ctl).chain(&clean).chain(&dirty){assert_eq!(get(fin,&[*x],shot),get(init,&[*x],shot));}};
  run_rows(&b,"pool-constant-add-undo",1<<(n+nc),&set,&back);
 }}}}
}

#[test]
fn low_incoming_add_all_inputs(){
 for n in 1usize..=6{for room in [0usize,1,2,5]{for controlled in [false,true]{
  let mut b=B::new();let a=b.alloc_n(n);let t=b.alloc_n(n);let ci=b.alloc();let ctl=b.alloc();let clean=b.alloc_n(room);b.low_clean=clean.clone();
  b.begin();low_add_cin(&mut b,&a,&t,ci,if controlled{ctl}else{ONE});let add=b.end();b.play(&add,false);
  let mask=(1u64<<n)-1;
  let set=|s:&mut[u64],shot:usize,row:usize|{let r=row as u64;put(s,&a,shot,r&mask);put(s,&t,shot,r>>n&mask);put(s,&[ci,ctl],shot,r>>(2*n));};
  let check=|init:&[u64],fin:&[u64],shot:usize,row:usize|{let r=row as u64;let on=!controlled||(r>>(2*n+1)&1)==1;let want=((r>>n&mask)+if on{(r&mask)+(r>>(2*n)&1)}else{0})&mask;assert_eq!(get(fin,&t,shot),want,"n{n} room{room} ctl{controlled} row{row}");for x in a.iter().chain([&ci,&ctl]).chain(&clean){assert_eq!(get(fin,&[*x],shot),get(init,&[*x],shot));}};
  run_rows(&b,"incoming-add",1<<(2*n+2),&set,&check);b.play(&add,true);
  let back=|init:&[u64],fin:&[u64],shot:usize,_row:usize|{for x in a.iter().chain(&t).chain([&ci,&ctl]).chain(&clean){assert_eq!(get(fin,&[*x],shot),get(init,&[*x],shot));}};
  run_rows(&b,"incoming-add-undo",1<<(2*n+2),&set,&back);
 }}}
}
