//! Tests: primitives on random inputs and the froghop-single traversal against the integer reference model.

use super::arith::*;
use super::builder::B;
use super::froghop_single::{mcx_dirty, Fh, Lay};
use super::refmodel::{self, N, St};
use crate::circuit::{analyze_ops, Op, QubitId};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};

pub struct Sim {
    pub q: Vec<u64>,
    pub phase: u64,
    pub tof: u64,
}

/// Run ops on 64 shots starting from `init` qubit words; returns final words, phase word, Toffoli count.
pub fn run(ops: &[Op], nq: usize, init: &dyn Fn(&mut Vec<u64>)) -> Sim {
    let (aq, nb, _, _) = analyze_ops(ops.iter());
    let nq = nq.max(aq as usize);
    let mut h = sha3::Shake256::default();
    h.update(b"froghop-test");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new(nq, (nb as usize).max(1), &mut xof);
    init(&mut s.qubits);
    s.apply_iter(ops.iter());
    Sim { q: s.qubits.clone(), phase: s.phase, tof: s.stats.toffoli_gates }
}

pub struct Rng(u64);
impl Rng {
    pub fn new(s: u64) -> Rng {
        Rng(s ^ 0x9E3779B97F4A7C15)
    }
    pub fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    pub fn below(&mut self, bits: usize) -> N {
        let mut v = N::ZERO;
        for i in 0..6 {
            v |= N::from(self.next()) << (64 * i);
        }
        if bits < 384 { v & ((N::from(1u64) << bits) - N::from(1u64)) } else { v }
    }
}

fn put(words: &mut [u64], qs: &[QubitId], shot: usize, val: &N) {
    for (i, &q) in qs.iter().enumerate() {
        if val.bit(i) {
            words[q.0 as usize] |= 1 << shot;
        } else {
            words[q.0 as usize] &= !(1 << shot);
        }
    }
}
fn get(words: &[u64], qs: &[QubitId], shot: usize) -> N {
    let mut v = N::ZERO;
    for (i, &q) in qs.iter().enumerate() {
        if (words[q.0 as usize] >> shot) & 1 == 1 {
            v |= N::from(1u64) << i;
        }
    }
    v
}
fn getb(words: &[u64], q: QubitId, shot: usize) -> u64 {
    (words[q.0 as usize] >> shot) & 1
}

#[test]
fn ladder_compare_and_cond_sub() {
    for &l in &[1usize, 2, 5, 17, 64] {
        let mut b = B::new();
        let t = b.alloc_n(l);
        let s = b.alloc_n(l);
        let c0 = b.alloc();
        let g = b.alloc();
        let x = b.alloc();
        let ru = up(&mut b, &t, &s, c0);
        let rd = down(&mut b, &t, &s, c0, Some(x));
        b.play(&ru, false);
        let ctop = s[l - 1];
        // x = [T >= S] & g
        b.x(ctop);
        b.and_c(g, ctop, x);
        b.x(ctop);
        b.play(&rd, false);
        let mut rng = Rng::new(l as u64);
        let mut tv = vec![];
        let mut sv = vec![];
        let mut gv = vec![];
        for _ in 0..64 {
            tv.push(rng.below(l));
            sv.push(if rng.next() % 3 == 0 { tv.last().unwrap().clone() } else { rng.below(l) });
            gv.push(rng.next() & 1);
        }
        let r = run(&b.ops, 0, &|w| {
            for k in 0..64 {
                put(w, &t, k, &tv[k]);
                put(w, &s, k, &sv[k]);
                if gv[k] == 1 {
                    w[g.0 as usize] |= 1 << k;
                }
            }
        });
        assert_eq!(r.phase, 0);
        for k in 0..64 {
            let ge = tv[k] >= sv[k];
            let xe = ge && gv[k] == 1;
            assert_eq!(getb(&r.q, x, k) == 1, xe, "x l={l} k={k}");
            let te = if xe { tv[k] - sv[k] } else { tv[k] };
            assert_eq!(get(&r.q, &t, k), te, "t l={l}");
            assert_eq!(get(&r.q, &s, k), sv[k]);
            assert_eq!(getb(&r.q, c0, k), 0);
        }
        assert_eq!(b.tof as usize, 3 * l + 1, "toffoli count");
    }
}

#[test]
fn ladder_coef_inverse() {
    // U^{-1}: (td, beta) -> (td + beta * S, 0) when [td + beta S >= S] == beta
    let l = 40;
    let mut b = B::new();
    let t = b.alloc_n(l);
    let s = b.alloc_n(l);
    let c0 = b.alloc();
    let be = b.alloc();
    let ep = b.alloc();
    let ru = up(&mut b, &t, &s, c0);
    let rd = down(&mut b, &t, &s, c0, Some(be));
    b.play(&rd, true);
    let ctop = s[l - 1];
    b.x(ctop);
    b.ccx(ep, ctop, be);
    b.x(ctop);
    b.play(&ru, true);
    let mut rng = Rng::new(5);
    let mut cases = vec![];
    for _ in 0..64 {
        let sv = rng.below(l - 2) | N::from(1u64);
        let tdv = rng.below(l - 1) % sv; // td < S
        let bit = rng.next() & 1;
        let epv = rng.next() & 1;
        cases.push((tdv, sv, bit * epv, epv));
    }
    let r = run(&b.ops, 0, &|w| {
        for (k, (tdv, sv, bit, epv)) in cases.iter().enumerate() {
            put(w, &t, k, tdv);
            put(w, &s, k, sv);
            if *bit == 1 {
                w[be.0 as usize] |= 1 << k;
            }
            if *epv == 1 {
                w[ep.0 as usize] |= 1 << k;
            }
        }
    });
    assert_eq!(r.phase, 0);
    for (k, (tdv, sv, bit, _)) in cases.iter().enumerate() {
        let te = if *bit == 1 { *tdv + *sv } else { *tdv };
        assert_eq!(get(&r.q, &t, k), te);
        assert_eq!(getb(&r.q, be, k), 0, "beta erased");
    }
}

#[test]
fn rotation_and_counters() {
    for &n in &[6usize, 7, 12, 31] {
        let mut b = B::new();
        let t = b.alloc_n(n);
        let k1 = b.alloc();
        let k2 = b.alloc();
        rot4_up(&mut b, k1, k2, &t);
        let mut rng = Rng::new(n as u64);
        let vals: Vec<N> = (0..64).map(|_| rng.below(n)).collect();
        let r = run(&b.ops, 0, &|w| {
            for k in 0..64 {
                put(w, &t, k, &vals[k]);
                if k & 1 == 1 {
                    w[k1.0 as usize] |= 1 << k;
                }
                if k & 2 == 2 {
                    w[k2.0 as usize] |= 1 << k;
                }
            }
        });
        for k in 0..64 {
            let e = (k & 3) as usize;
            let _ = e;
            let got = get(&r.q, &t, k);
            for i in 0..n {
                assert_eq!(got.bit(i), vals[k].bit((i + n - e) % n), "rot n={n} e={e}");
            }
        }
    }
    // counters
    let mut b = B::new();
    let c = b.alloc_n(5);
    let ct = b.alloc();
    let anc = b.alloc_n(4);
    inc(&mut b, ct, &c, &anc);
    let ct2 = b.alloc();
    dec(&mut b, ct2, &c, &anc);
    let r = run(&b.ops, 0, &|w| {
        for k in 0..64 {
            put(w, &c, k, &N::from((k % 32) as u64));
            if k & 1 == 1 {
                w[ct.0 as usize] |= 1 << k;
            }
            if k & 2 == 2 {
                w[ct2.0 as usize] |= 1 << k;
            }
        }
    });
    assert_eq!(r.phase, 0);
    for k in 0..64 {
        let e = ((k % 32) as i64 + (k & 1) as i64 - ((k >> 1) & 1) as i64).rem_euclid(32) as u64;
        assert_eq!(get(&r.q, &c, k), N::from(e));
        for &a in &anc {
            assert_eq!(getb(&r.q, a, k), 0);
        }
    }
}

#[test]
fn and_lits_and_mcx() {
    let mut b = B::new();
    let x = b.alloc_n(6);
    let out = b.alloc();
    let anc = b.alloc_n(4);
    let lits: Vec<(QubitId, bool)> = x.iter().enumerate().map(|(i, &q)| (q, i % 2 == 1)).collect();
    let rec = and_lits(&mut b, &lits, out, &anc);
    b.play(&rec, false);
    let t2 = b.alloc();
    b.cx(out, t2);
    b.play(&rec, true);
    let dirty = b.alloc_n(8);
    let t3 = b.alloc();
    mcx_dirty(&mut b, &x, t3, &dirty);
    let r = run(&b.ops, 0, &|w| {
        for k in 0..64 {
            put(w, &x, k, &N::from(k as u64));
            put(w, &dirty, k, &N::from((k * 37 % 256) as u64));
        }
    });
    assert_eq!(r.phase, 0);
    for k in 0..64 {
        let want = (0..6).all(|i| ((k >> i) & 1 == 1) != (i % 2 == 1));
        assert_eq!(getb(&r.q, t2, k) == 1, want);
        assert_eq!(getb(&r.q, out, k), 0);
        assert_eq!(getb(&r.q, t3, k) == 1, k == 63);
        assert_eq!(get(&r.q, &dirty, k), N::from((k * 37 % 256) as u64));
    }
}

pub fn test_layout() -> Lay {
    super::layout()
}

/// Read the circuit state of shot k into the reference-model shape (layout M, pi from the circuit).
fn read_state(w: &[u64], f: &Fh, lay: &Lay, mm: usize, k: usize) -> (N, N, N, N, u32, u8, Vec<u8>, bool, u32, u8, u8) {
    let wl = lay.w;
    let pi = get(w, &f.pi, k).as_limbs()[0] as u32;
    let td = get(w, &f.d[0..mm], k);
    let r = get(w, &f.d[mm..wl], k);
    let vf: Vec<QubitId> = (0..wl).map(|u| f.v[(u + pi as usize) % wl]).collect();
    let tv = get(w, &vf[0..mm], k);
    let rv = get(w, &vf[mm..wl], k);
    let ph = if getb(w, f.fo, k) == 1 { 0 } else if getb(w, f.fr, k) == 1 { 1 } else if getb(w, f.fd, k) == 1 { 2 } else { 3 };
    let dep = get(w, &f.dep, k).as_limbs()[0] as usize;
    let done = getb(w, f.fnn, k) == 1;
    let stk: Vec<u8> = (0..dep).rev().map(|i| getb(w, f.stk[i], k) as u8).collect();
    let cnt = if done { get(w, f.cnt(), k).as_limbs()[0] as u32 } else { 0 };
    (r, td, rv, tv, pi, ph, stk, done, cnt, getb(w, f.par, k) as u8, getb(w, f.f1, k) as u8)
}

#[test]
fn traversal_matches_model() {
    let lay = test_layout();
    let wl = lay.w;
    let mut b = B::new();
    let d = b.alloc_n(wl);
    let v = b.alloc_n(wl);
    let dirty = b.alloc_n(64);
    let mut f = Fh::alloc(&mut b, d, v, &lay, dirty.clone());
    let mut rng = Rng::new(42);
    let pp = refmodel::p();
    let mut models: Vec<St> = (0..64)
        .map(|_| {
            let mut x = rng.below(256) % pp;
            if x == N::ZERO {
                x = N::from(1u64);
            }
            St::new(x)
        })
        .collect();
    // V's r lanes hold x' at the initial layout
    let m0 = lay.m[0];
    let vlanes: Vec<QubitId> = f.v[m0 + 1..m0 + 257].to_vec(); // V starts rotated by pi = 1
    f.init(&mut b, &lay);
    let init_ops = b.ops.len();
    let nq = b.width() as usize;
    let mut sim_words = {
        let mods = models.clone();
        let dq = dirty.clone();
        let r = run(&b.ops[..init_ops], nq, &move |w| {
            for k in 0..64 {
                put(w, &vlanes, k, &mods[k].rv);
                put(w, &dq, k, &N::from((k * 7919) as u64));
            }
        });
        r.q
    };
    let mut tof = 0u64;
    for sigma in 0..lay.s {
        let mm = lay.m[sigma];
        // check state at slot start
        for k in 0..64 {
            let got = read_state(&sim_words, &f, &lay, mm, k);
            let m = &models[k];
            let want = (m.r, m.td, m.rv, m.tv, m.pi, if m.done { 3 } else { m.ph }, m.stk.clone(), m.done, m.cnt,
                        m.par, m.f1);
            assert_eq!(got, want, "slot {sigma} shot {k}");
        }
        let start = b.ops.len();
        f.slot(&mut b, &lay, sigma);
        let ops = b.ops[start..].to_vec();
        let words = sim_words.clone();
        let r = run(&ops, nq, &move |w| {
            w.copy_from_slice(&words);
        });
        assert_eq!(r.phase, 0, "phase after slot {sigma}");
        tof += r.tof;
        sim_words = r.q;
        for s in f.all_meta().iter().take(super::froghop_single::POOL) {
            assert_eq!(sim_words[s.0 as usize], 0, "scratch q{} dirty after slot {sigma}", s.0);
        }
        for m in models.iter_mut() {
            m.fwd_at(sigma);
        }
    }
    for k in 0..64 {
        let x = {
            let st = &models[k];
            st.result()
        };
        let _ = x;
        assert!(models[k].done);
    }
    eprintln!("traversal: {} slots, avg Toffoli/shot {} ({} per slot), qubits {}", lay.s, tof / 64,
              tof / 64 / lay.s as u64, b.width());
}

#[test]
fn forward_inverse_identity_batches() {
    let lay = test_layout();
    let wl = lay.w;
    for seed in 0..6u64 {
        let mut b = B::new();
        let d = b.alloc_n(wl);
        let v = b.alloc_n(wl);
        let dirty = b.alloc_n(64);
        let mut f = Fh::alloc(&mut b, d, v, &lay, dirty.clone());
        let m0 = lay.m[0];
        let vlanes: Vec<QubitId> = f.v[m0 + 1..m0 + 257].to_vec();
        let dl0 = f.d.clone();
        let vl0 = f.v.clone();
        let mut rng = Rng::new(1000 + seed);
        let pp = refmodel::p();
        let xs: Vec<N> = (0..64).map(|_| { let x = rng.below(256) % pp; if x == N::ZERO { N::from(1u64) } else { x } }).collect();
        let models: Vec<St> = xs.iter().map(|&x| St::new(x)).collect();
        f.init(&mut b, &lay);
        let maps = f.forward(&mut b, &lay);
        let mid = b.ops.len();
        let (dfin, vfin) = (f.d.clone(), f.v.clone());
        f.inverse(&mut b, &lay, &maps);
        f.init(&mut b, &lay); // X gates: undo the constants
        assert_eq!(f.d, dl0);
        assert_eq!(f.v, vl0);
        let nq = b.width() as usize;
        let mods = models.clone();
        let dq = dirty.clone();
        let vl = vlanes.clone();
        let r = run(&b.ops[..mid], nq, &|w| {
            for k in 0..64 {
                put(w, &vl, k, &mods[k].rv);
                put(w, &dq, k, &N::from((k * 7919) as u64));
            }
        });
        // after forward: check the final state against the model
        let mut ms = models.clone();
        for m in ms.iter_mut() { for sg in 0..lay.s { m.fwd_at(sg); } }
        let (dsave, vsave) = (f.d.clone(), f.v.clone());
        f.d = dfin.clone();
        f.v = vfin.clone();
        for k in 0..64 {
            let mm = lay.m[lay.s - 1];
            let got = read_state(&r.q, &f, &lay, mm, k);
            assert!(ms[k].done, "unfinished shot");
            assert_eq!(got.0, ms[k].r);
            assert_eq!(got.3, ms[k].tv);
            let _ = ms[k].result();
        }
        f.d = dsave;
        f.v = vsave;
        let r2 = run(&b.ops, nq, &|w| {
            for k in 0..64 {
                put(w, &vl, k, &mods[k].rv);
                put(w, &dq, k, &N::from((k * 7919) as u64));
            }
        });
        assert_eq!(r2.phase, 0, "phase after forward+inverse");
        for q in 0..nq {
            let want = if vl.iter().any(|x| x.0 as usize == q) || dq.iter().any(|x| x.0 as usize == q) { None } else { Some(0u64) };
            if let Some(z) = want { assert_eq!(r2.q[q], z, "qubit {q} not restored (seed {seed})"); }
        }
        for k in 0..64 {
            assert_eq!(get(&r2.q, &vl, k), mods[k].rv);
            assert_eq!(get(&r2.q, &dq, k), N::from((k * 7919) as u64));
        }
        eprintln!("seed {seed}: forward+inverse ok, tof/shot {}", r2.tof / 64);
    }
}

fn modp_n() -> N { refmodel::p() }

#[test]
fn modp_routines() {
    use super::modp::*;
    let pp = modp_n();
    let mut rng = Rng::new(77);
    let vals = |rng: &mut Rng| -> Vec<N> { (0..64).map(|_| { let v = rng.below(256) % pp; if v == N::ZERO { N::from(3u64) } else { v } }).collect() };
    // double / halve / ctrl_modadd / modsub / ctrl_neg
    let mut b = B::new();
    let z = b.alloc_n(256);
    let y = b.alloc_n(256);
    let ctl = b.alloc();
    let ms = Ms::alloc(&mut b);
    let mut zz = z.clone();
    let t0 = b.tof;
    mod_double(&mut b, &ms, &mut zz);
    let tdbl = b.tof - t0;
    let t0 = b.tof;
    ctrl_modadd(&mut b, &ms, &zz, &y, ctl);
    let tadd = b.tof - t0;
    let zv = vals(&mut rng);
    let yv = vals(&mut rng);
    let r = run(&b.ops, 0, &|w| {
        for k in 0..64 {
            put(w, &z, k, &zv[k]);
            put(w, &y, k, &yv[k]);
            if k % 3 != 0 { w[ctl.0 as usize] |= 1 << k; }
            w[ms.one.0 as usize] = 0; // set by the X in alloc
        }
    });
    assert_eq!(r.phase, 0);
    for k in 0..64 {
        let mut e = (zv[k] + zv[k]) % pp;
        if k % 3 != 0 { e = (e + yv[k]) % pp; }
        assert_eq!(get(&r.q, &zz, k), e, "double+add k={k}");
        assert_eq!(get(&r.q, &y, k), yv[k]);
        assert_eq!(getb(&r.q, ms.k, k), 0);
        for &q in &ms.s { assert_eq!(getb(&r.q, q, k), 0); }
    }
    eprintln!("mod_double {tdbl} T, ctrl_modadd {tadd} T");
    // negation and modsub, halving
    let mut b = B::new();
    let z = b.alloc_n(256);
    let y = b.alloc_n(256);
    let ctl = b.alloc();
    let ms = Ms::alloc(&mut b);
    ctrl_neg(&mut b, &ms, &z, ctl);
    modsub(&mut b, &ms, &z, &y);
    let mut zz = z.clone();
    mod_halve(&mut b, &ms, &mut zz);
    let r = run(&b.ops, 0, &|w| {
        for k in 0..64 {
            put(w, &z, k, &zv[k]);
            put(w, &y, k, &yv[k]);
            if k % 2 == 0 { w[ctl.0 as usize] |= 1 << k; }
        }
    });
    assert_eq!(r.phase, 0);
    let inv2 = (pp + N::from(1u64)) / N::from(2u64);
    for k in 0..64 {
        let mut e = if k % 2 == 0 { pp - zv[k] } else { zv[k] };
        e = (e + pp - yv[k]) % pp;
        e = e.mul_mod(inv2, pp);
        assert_eq!(get(&r.q, &zz, k), e, "neg/sub/halve k={k}");
        assert_eq!(getb(&r.q, ms.k, k), 0);
    }
}

#[test]
fn modp_product_and_mac() {
    use super::modp::*;
    let pp = modp_n();
    let mut rng = Rng::new(99);
    let vals = |rng: &mut Rng| -> Vec<N> { (0..64).map(|_| rng.below(256) % pp).collect() };
    let mut b = B::new();
    let a = b.alloc_n(256);
    let y = b.alloc_n(256);
    let z = b.alloc_n(256);
    let acc = b.alloc_n(256);
    let ms = Ms::alloc(&mut b);
    let mut zz = z.clone();
    let t0 = b.tof;
    product(&mut b, &ms, &mut zz, &a, &y);
    let tp = b.tof - t0;
    let mut yy = y.clone();
    let t0 = b.tof;
    mac(&mut b, &ms, &acc, &a, &mut yy);
    let tm = b.tof - t0;
    assert_eq!(yy, y);
    let av = vals(&mut rng);
    let yv = vals(&mut rng);
    let cv = vals(&mut rng);
    let r = run(&b.ops, 0, &|w| {
        for k in 0..64 {
            put(w, &a, k, &av[k]);
            put(w, &y, k, &yv[k]);
            put(w, &acc, k, &cv[k]);
        }
    });
    assert_eq!(r.phase, 0);
    for k in 0..64 {
        let e = av[k].mul_mod(yv[k], pp);
        assert_eq!(get(&r.q, &zz, k), e, "product k={k}");
        assert_eq!(get(&r.q, &acc, k), (cv[k] + e) % pp, "mac k={k}");
        assert_eq!(get(&r.q, &y, k), yv[k]);
        assert_eq!(get(&r.q, &a, k), av[k]);
    }
    eprintln!("product {tp} T, mac {tm} T");
}

#[test]
fn point_add_end_to_end() {
    use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
    let lay = super::layout();
    let mut b = B::new();
    let (xq, yq) = super::pointadd::point_add(&mut b, &lay);
    let ops = b.ops.clone();
    let (nq, _, _, regs) = analyze_ops(ops.iter());
    eprintln!("ops {} qubits {} peak {} emitted tof {}", ops.len(), nq, b.peak, b.tof);
    // curve
    let pp = refmodel::p();
    let to_u = |v: &N| -> ruint::aliases::U256 { ruint::aliases::U256::from_limbs(v.as_limbs()[0..4].try_into().unwrap()) };
    type U = ruint::aliases::U256;
    let hx = |h: &str| U::from_str_radix(h, 16).unwrap();
    let curve = WeierstrassEllipticCurve {
        modulus: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
        a: U::ZERO,
        b: U::from(7u64),
        gx: hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
        gy: hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
        order: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
    };
    let _ = &pp;
    let mut rng = Rng::new(2024);
    let mut cases = vec![];
    for _ in 0..64 {
        let k1 = to_u(&(rng.below(250) + N::from(1u64)));
        let k2 = to_u(&(rng.below(250) + N::from(1u64)));
        let t = curve.mul(curve.gx, curve.gy, k1);
        let o = curve.mul(curve.gx, curve.gy, k2);
        let e = curve.add(t.0, t.1, o.0, o.1);
        cases.push((t, o, e));
    }
    let mut h = sha3::Shake256::default();
    h.update(b"froghop-e2e");
    let mut xof = h.finalize_xof();
    let (_, nb, _, _) = analyze_ops(ops.iter());
    let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
    for (k, (t, o, _)) in cases.iter().enumerate() {
        sim.set_register(&regs[0], t.0, k);
        sim.set_register(&regs[1], t.1, k);
        sim.set_register(&regs[2], o.0, k);
        sim.set_register(&regs[3], o.1, k);
    }
    sim.apply_iter(ops.iter());
    let mut bad = 0;
    for (k, (_, _, e)) in cases.iter().enumerate() {
        let gx = sim.get_register(&regs[0], k);
        let gy = sim.get_register(&regs[1], k);
        if gx != e.0 || gy != e.1 { bad += 1; }
    }
    assert_eq!(sim.phase, 0, "phase garbage");
    let regq: std::collections::HashSet<u64> = xq.iter().chain(yq.iter()).map(|q| q.0).collect();
    for q in 0..nq {
        if !regq.contains(&q) { assert_eq!(sim.qubits[q as usize], 0, "ancilla garbage q{q}"); }
    }
    assert_eq!(bad, 0, "classical mismatches");
    eprintln!("end-to-end OK: avg Toffoli {}", sim.stats.toffoli_gates / 64);
}

#[test]
fn rot2_test() {
    for &n in &[6usize, 7, 12, 31] {
        let mut b = B::new();
        let t = b.alloc_n(n);
        let c = b.alloc();
        rot2_up(&mut b, c, &t);
        let mut rng = Rng::new(n as u64 + 9);
        let vals: Vec<N> = (0..64).map(|_| rng.below(n)).collect();
        let r = run(&b.ops, 0, &|w| {
            for k in 0..64 {
                put(w, &t, k, &vals[k]);
                if k & 1 == 1 { w[c.0 as usize] |= 1 << k; }
            }
        });
        for k in 0..64 {
            let e = if k & 1 == 1 { 2 } else { 0 };
            let got = get(&r.q, &t, k);
            for i in 0..n { assert_eq!(got.bit(i), vals[k].bit((i + n - e) % n), "rot2 n={n}"); }
        }
    }
}
