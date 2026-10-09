//! frogdrop tests: the 3-of-4 machine primitives, columns, traversal, product fold and end-to-end point addition.

use super::builder::B;
use super::frogdrop::*;
use super::frogdrop_sched::N;
use crate::circuit::{analyze_ops, Op};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};
use crate::circuit::QubitId;


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
    h.update(b"frogdrop-test");
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

fn put(w: &mut [u64], qs: &[QubitId], shot: usize, v: &N) {
    for (i, &q) in qs.iter().enumerate() {
        if v.bit(i) { w[q.0 as usize] |= 1 << shot } else { w[q.0 as usize] &= !(1 << shot) }
    }
}
fn get(w: &[u64], qs: &[QubitId], shot: usize) -> N {
    let mut v = N::ZERO;
    for (i, &q) in qs.iter().enumerate() {
        if (w[q.0 as usize] >> shot) & 1 == 1 {
            v |= N::from(1u64) << i;
        }
    }
    v
}
fn getb(w: &[u64], q: QubitId, shot: usize) -> u64 {
    (w[q.0 as usize] >> shot) & 1
}
fn mask(l: usize) -> N {
    (N::from(1u64) << l) - N::from(1u64)
}

#[test]
fn frogdrop_mul_odd_and_inverse() {
    for &(l, m, tail) in &[(8usize, 3usize, 40usize), (40, 12, 40), (130, 64, 40), (256, 128, 40), (257, 30, 40)] {
        let mut b = B::new();
        let x = b.alloc_n(l);
        let a = b.alloc_n(m);
        let c0 = b.alloc();
        let h = b.alloc();
        let anc = b.alloc_n(tail);
        let dirty_free: Vec<QubitId> = [c0, h].iter().cloned().chain(anc.iter().cloned()).collect();
        b.begin();
        mul_odd(&mut b, &x, &a, tail, c0, h, &anc);
        let rec = b.end();
        b.play(&rec, false);
        let t_mul = b.tof;
        let n_fwd = b.ops.len();
        b.play(&rec, true);
        let mut rng = Rng::new(l as u64 * 7 + m as u64);
        let xs: Vec<N> = (0..64).map(|_| rng.below(l)).collect();
        let as_: Vec<N> = (0..64).map(|_| rng.below(m) | N::from(1u64)).collect();
        let fwd = run(&b.ops[..n_fwd], b.width() as usize, &|w| {
            for s in 0..64 {
                put(w, &x, s, &xs[s]);
                put(w, &a, s, &as_[s]);
            }
        });
        let all = run(&b.ops, b.width() as usize, &|w| {
            for s in 0..64 {
                put(w, &x, s, &xs[s]);
                put(w, &a, s, &as_[s]);
            }
        });
        for s in 0..64 {
            let want = xs[s].wrapping_mul(as_[s]) & mask(l);
            assert_eq!(get(&fwd.q, &x, s), want, "mul l={l} m={m} shot {s}");
            assert_eq!(get(&fwd.q, &a, s), as_[s]);
            for &q in &dirty_free {
                assert_eq!((fwd.q[q.0 as usize] >> s) & 1, 0, "scratch dirty");
            }
            assert_eq!(get(&all.q, &x, s), xs[s], "inverse l={l} m={m}");
        }
        assert_eq!(fwd.phase, 0);
        eprintln!("mul_odd L={l} M={m} tail={tail}: {t_mul} Toffoli ({:.2}/lane-add, L*(M+tail) = {})", t_mul as f64 /
                  ((l as f64) * ((m + tail).min(l) as f64)), l * (m + tail).min(l));
    }
}

#[test]
fn frogdrop_mul_odd_masked() {
    for &(l, m, tail, wlo, whi) in &[(40usize, 8usize, 12usize, 20usize, 34usize), (256, 64, 40, 150, 210), (256, 128, 40, 100, 170)] {
        let mut b = B::new();
        let x = b.alloc_n(l);
        let a = b.alloc_n(m);
        let bvn = 9;
        let bv = b.alloc_n(bvn);
        let sc = MulScr { c0: b.alloc(), f: b.alloc(), t: b.alloc(), zeros: b.alloc_n(tail), pre: b.alloc_n(bvn - 1),
                          e: b.alloc(), epre: b.alloc_n(bvn - 1), g: b.alloc(), dirty: vec![] };
        let t0 = b.tof;
        mul_odd_masked(&mut b, &x, &a, tail, &bv, wlo, whi, &sc);
        let tm = b.tof - t0;
        let mut rng = Rng::new(l as u64 * 31 + m as u64);
        let mut cs = vec![];
        for _ in 0..64 {
            let beta = wlo + (rng.next() as usize) % (whi - wlo);
            let xv = rng.below(l); // lanes >= beta: arbitrary other data
            let av = rng.below(m) | N::from(1u64);
            cs.push((beta, xv, av));
        }
        let r = run(&b.ops, b.width() as usize, &|w| {
            for (k, (beta, xv, av)) in cs.iter().enumerate() {
                put(w, &x, k, xv);
                put(w, &a, k, av);
                put(w, &bv, k, &N::from(*beta as u64));
            }
        });
        assert_eq!(r.phase, 0);
        for (k, (beta, xv, av)) in cs.iter().enumerate() {
            let lowm = mask(*beta);
            let want = ((xv & lowm).wrapping_mul(*av) & lowm) | (*xv & !lowm);
            assert_eq!(get(&r.q, &x, k), want, "l={l} m={m} beta={beta} shot {k}");
            assert_eq!(get(&r.q, &a, k), *av);
            for &q in [sc.c0, sc.f, sc.t, sc.e, sc.g].iter().chain(sc.zeros.iter()).chain(sc.pre.iter()).chain(sc.epre.iter()) {
                assert_eq!((r.q[q.0 as usize] >> k) & 1, 0, "scratch q{} dirty, shot {k}", q.0);
            }
        }
        let plain = {
            let mut b2 = B::new();
            let x2 = b2.alloc_n(whi);
            let a2 = b2.alloc_n(m);
            let anc = b2.alloc_n(tail);
            let c0 = b2.alloc();
            let h = b2.alloc();
            mul_odd(&mut b2, &x2, &a2, tail, c0, h, &anc);
            b2.tof
        };
        eprintln!("masked mul L<={whi} M={m} window [{wlo},{whi}) ({} lanes): {tm} Toffoli vs unmasked {plain} at L={whi} (+{:.0}%)",
                  whi - wlo, 100.0 * (tm as f64 / plain as f64 - 1.0));
    }
}

#[test]
fn frogdrop_mul_odd_frame_and_rot() {
    for &(n, top, llo, m, tail) in &[(48usize, 44usize, 20usize, 6usize, 10usize), (280, 280, 100, 128, 40), (280, 270, 120, 64, 40)] {
        let mut b = B::new();
        let v = b.alloc_n(n);
        let a = b.alloc_n(m);
        let lsbv = b.alloc_n(9);
        let (c0, h, e, g) = (b.alloc(), b.alloc(), b.alloc(), b.alloc());
        let anc = b.alloc_n(tail);
        let epre = b.alloc_n(8);
        let t0 = b.tof;
        mul_odd_frame(&mut b, &v, top, llo, &lsbv, &a, tail, c0, h, &anc, e, &epre, g, &[]);
        let tm = b.tof - t0;
        // rotation round trip on top
        let t1 = b.tof;
        rot_by(&mut b, &v, &lsbv, false);
        rot_by(&mut b, &v, &lsbv, true);
        let trot = (b.tof - t1) / 2;
        let mut rng = Rng::new(n as u64 + top as u64 * 7);
        let cs: Vec<(usize, N, N)> = (0..64).map(|_| {
            let lsb = llo + (rng.next() as usize) % (top - 1 - llo);
            (lsb, rng.below(n), rng.below(m) | N::from(1u64))
        }).collect();
        let r = run(&b.ops, b.width() as usize, &|w| {
            for (k, (lsb, vv, av)) in cs.iter().enumerate() {
                put(w, &v, k, vv); put(w, &a, k, av); put(w, &lsbv, k, &N::from(*lsb as u64));
            }
        });
        assert_eq!(r.phase, 0);
        for (k, (lsb, vv, av)) in cs.iter().enumerate() {
            let w = top - lsb;
            let xv = (*vv >> *lsb) & mask(w);
            let prod = xv.wrapping_mul(*av) & mask(w);
            let keep = !(mask(w) << *lsb) & mask(n);
            let want = (*vv & keep) | (prod << *lsb);
            assert_eq!(get(&r.q, &v, k), want, "frame mul n={n} top={top} lsb={lsb} shot {k}");
            for &q in [c0, h, e, g].iter().chain(anc.iter()).chain(epre.iter()) {
                assert_eq!((r.q[q.0 as usize] >> k) & 1, 0, "scratch dirty");
            }
        }
        eprintln!("frame mul top={top} llo={llo} M={m}: {tm} Toffoli; ring rotation by a 9-bit amount over {n} lanes: {trot}");
    }
}

fn pval() -> N {
    super::frogdrop_sched::p()
}

#[test]
fn frogdrop_shift_and_p_minus() {
    let n = 290usize;
    let (clo, chi) = (180usize, 288usize);
    let tail = 40usize;
    for mode in 0..3 {
        let mut b = B::new();
        let v = b.alloc_n(n);
        let cutv = b.alloc_n(9);
        let amt = b.alloc_n(5);
        let (f, tmp, g, one) = (b.alloc(), b.alloc(), b.alloc(), b.alloc());
        let pre = b.alloc_n(8);
        let anc = b.alloc_n(tail + 12);
        let dpool = b.alloc_n(64);
        let t0 = b.tof;
        match mode {
            0 => shift_region(&mut b, &v, &cutv, clo, chi, &amt, true, f, &pre, tmp, g, &[]),
            1 => shift_region(&mut b, &v, &cutv, clo, chi, &amt, false, f, &pre, tmp, g, &[]),
            _ => p_minus(&mut b, &v, &cutv, clo, chi, tail, &anc, one, f, &pre, tmp, &dpool),
        }
        let tc = b.tof - t0;
        let mut rng = Rng::new(77 + mode as u64);
        let cs: Vec<(usize, usize, N)> = (0..64).map(|_| {
            let cut = clo + (rng.next() as usize) % (chi - clo + 1);
            let s = (rng.next() as usize) % 20;
            let mut vv = rng.below(n);
            // region content: up needs top s lanes of [0,cut) zero; down needs low s lanes zero
            if mode == 0 { vv = vv & !(mask(s) << (cut - s)); }
            if mode == 1 { vv = vv & !mask(s); }
            // p - Z: the map's W = Z X <= p (lanes of the region above 256 are 0)
            if mode == 2 { vv = (vv & !mask(cut)) | (rng.below(256) % pval()); }
            (cut, s, vv)
        }).collect();
        let r = run(&b.ops, b.width() as usize, &|w| {
            for (k, (cut, s, vv)) in cs.iter().enumerate() {
                put(w, &v, k, vv); put(w, &cutv, k, &N::from(*cut as u64)); put(w, &amt, k, &N::from(*s as u64));
            }
        });
        assert_eq!(r.phase, 0);
        for (k, (cut, s, vv)) in cs.iter().enumerate() {
            let reg = *vv & mask(*cut);
            let rest = *vv & !mask(*cut) & mask(n);
            let want_reg = match mode {
                0 => (reg << *s) & mask(*cut),
                1 => reg >> *s,
                _ => (pval().wrapping_sub(reg)) & mask(*cut),
            };
            assert_eq!(get(&r.q, &v, k), want_reg | rest, "mode {mode} cut {cut} s {s} shot {k}");
            for &q in [f, tmp, g, one].iter().chain(pre.iter()).chain(anc.iter()) {
                assert_eq!((r.q[q.0 as usize] >> k) & 1, 0, "scratch dirty mode {mode}");
            }
        }
        eprintln!("mode {} ({}): {tc} Toffoli over window [{clo},{chi}]", mode, ["shift up", "shift down", "p - Z"][mode]);
    }
}

fn blen(x: &N) -> usize { x.bit_len() }
fn v2n(x: &N) -> usize { x.trailing_zeros() }
fn rev_into(w: &mut [u64], lanes: &[QubitId], shot: usize, val: &N) {
    // val's bit k at lanes[n-1-k]
    let n = lanes.len();
    let rl: Vec<QubitId> = (0..n).map(|k| lanes[n - 1 - k]).collect();
    put(w, &rl, shot, val);
}
fn rev_get(w: &[u64], lanes: &[QubitId], shot: usize, nbits: usize) -> N {
    let n = lanes.len();
    let rl: Vec<QubitId> = (0..nbits).map(|k| lanes[n - 1 - k]).collect();
    get(w, &rl, shot)
}

/// Random Euclid map instances (Z, X, Y, y), mixing phase 1 (Z = r_j, X = t_{j+1}, Y = t_j) and phase 2
/// (Z = t_j, X = r_{j+1}, Y = r_j).
fn map_cases(seed: u64, k: usize) -> Vec<(N, N, N, N)> {
    let p = pval();
    let mut rng = Rng::new(seed);
    let mut out = vec![];
    while out.len() < k {
        let mut x = rng.below(256) % p;
        if x.is_zero() { continue; }
        if x > p >> 1 { x = p - x; }
        let (mut r, mut t) = (vec![p, x], vec![N::ZERO, N::from(1u64)]);
        while !r[r.len() - 1].is_zero() {
            let n = r.len();
            let q = r[n - 2] / r[n - 1];
            let rn = r[n - 2] - q * r[n - 1];
            let tn = t[n - 2] + q * t[n - 1];
            r.push(rn); t.push(tn);
        }
        let nn = r.len() - 1; // r[nn] = 0
        let j = 1 + (rng.next() as usize) % (nn - 2);
        let phase2 = blen(&r[j - 1]) <= blen(&t[j - 1]);
        if phase2 {
            out.push((t[j], r[j + 1], r[j], t[j + 1]));
        } else {
            out.push((r[j], t[j + 1], t[j], r[j + 1]));
        }
    }
    out
}

#[test]
fn frogdrop_map_full() {
    let n = 285usize;
    let nq = 150usize;
    let tail = 40usize;
    let cs = map_cases(1234, 64);
    let cuts: Vec<usize> = cs.iter().map(|(_, x, y, _)| n - blen(x).max(blen(y))).collect();
    let par = MapPar { clo: *cuts.iter().min().unwrap(), chi: *cuts.iter().max().unwrap(),
                       m: cs.iter().map(|(_, x, y, _)| blen(x).max(blen(y))).max().unwrap(),
                       tail, emax: 28 };
    let mut b = B::new();
    let ring = b.alloc_n(n);
    let q = b.alloc_n(nq);
    let cutv = b.alloc_n(9);
    let sc = MapScr { c0: b.alloc(), h: b.alloc(), e: b.alloc(), g: b.alloc(), f: b.alloc(), tmp: b.alloc(),
                      one: b.alloc(), anc: b.alloc_n(tail + 12), pre: b.alloc_n(8), ez: b.alloc_n(5),
                      epre: b.alloc_n(4), dirty: b.alloc_n(64) };
    map(&mut b, &ring, &q, &cutv, &par, &sc);
    let tm = b.tof;
    let r = run(&b.ops, b.width() as usize, &|w| {
        for (k, (z, x, y, _)) in cs.iter().enumerate() {
            put(w, &ring[..cuts[k]], k, z);
            rev_into(w, &ring[cuts[k]..], k, y);
            put(w, &q, k, x);
            put(w, &cutv, k, &N::from(cuts[k] as u64));
        }
    });
    assert_eq!(r.phase, 0);
    for (k, (z, x, y, yn)) in cs.iter().enumerate() {
        let _ = z;
        assert_eq!(get(&r.q, &ring[..cuts[k]], k), *yn, "ring bottom (y) shot {k} cut {}", cuts[k]);
        assert_eq!(rev_get(&r.q, &ring[cuts[k]..], k, n - cuts[k]), *x, "ring top (X) shot {k}");
        assert_eq!(get(&r.q, &q, k), *y, "Q (Y) shot {k}");
        for &qq in [sc.c0, sc.h, sc.e, sc.g, sc.f, sc.tmp, sc.one].iter().chain(sc.anc.iter()).chain(sc.pre.iter())
            .chain(sc.ez.iter()).chain(sc.epre.iter()) {
            assert_eq!((r.q[qq.0 as usize] >> k) & 1, 0, "scratch q{} dirty shot {k}", qq.0);
        }
    }
    eprintln!("map: {tm} Toffoli for 64 mixed shots, cut window [{}, {}], m = {}", par.clo, par.chi, par.m);
}

#[test]
fn frogdrop_map_stages() {
    let n = 285usize; let nq = 150usize; let tail = 40usize;
    let cs = map_cases(1234, 64);
    let cuts: Vec<usize> = cs.iter().map(|(_, x, y, _)| n - blen(x).max(blen(y))).collect();
    let par = MapPar { clo: *cuts.iter().min().unwrap(), chi: *cuts.iter().max().unwrap(),
                       m: cs.iter().map(|(_, x, y, _)| blen(x).max(blen(y))).max().unwrap(), tail, emax: 28 };
    let p = pval();
    for upto in 1..=14 {
        let mut b = B::new();
        let ring = b.alloc_n(n); let q = b.alloc_n(nq); let cutv = b.alloc_n(9);
        let sc = MapScr { c0: b.alloc(), h: b.alloc(), e: b.alloc(), g: b.alloc(), f: b.alloc(), tmp: b.alloc(),
                          one: b.alloc(), anc: b.alloc_n(tail + 12), pre: b.alloc_n(8), ez: b.alloc_n(5),
                          epre: b.alloc_n(4), dirty: b.alloc_n(64) };
        map_upto(&mut b, &ring, &q, &Cut::reg(&cutv), &par, &sc, upto);
        let r = run(&b.ops, b.width() as usize, &|w| {
            for (k, (z, x, y, _)) in cs.iter().enumerate() {
                put(w, &ring[..cuts[k]], k, z); rev_into(w, &ring[cuts[k]..], k, y); put(w, &q, k, x);
                put(w, &cutv, k, &N::from(cuts[k] as u64));
            }
        });
        let mut bad = 0;
        for (k, (z, x, y, yn)) in cs.iter().enumerate() {
            let cut = cuts[k];
            let m = mask(cut);
            let (ex, ey) = (v2n(x), v2n(y));
            let zx = (z.wrapping_mul(*x)) & m;
            let pz = p.wrapping_sub(zx) & m;
            let bot = get(&r.q, &ring[..cut], k);
            let qv = get(&r.q, &q, k);
            let ezv = get(&r.q, &sc.ez, k);
            let xodd = *x >> ex; let yodd = *y >> ey;
            let (wb, wq, we) = match upto {
                1 => (*z, *x, N::from(ex as u64)),
                2 => (*z, xodd, N::from(ex as u64)),
                3 => ((*z << ex) & m, xodd, N::from(ex as u64)),
                4 => (zx, xodd, N::from(ex as u64)),
                5 => (zx, *x, N::from(ex as u64)),
                6 => (zx, *x, N::ZERO),
                7 => (pz, *x, N::ZERO),
                8 => (pz, *y, N::ZERO),
                9 => (pz, *y, N::from(ey as u64)),
                10 => (pz, yodd, N::from(ey as u64)),
                11 => ((*yn << ey) & m, yodd, N::from(ey as u64)),
                12 => (*yn, yodd, N::from(ey as u64)),
                13 => (*yn, *y, N::from(ey as u64)),
                _ => (*yn, *y, N::ZERO),
            };
            if bot != wb || qv != wq || ezv != we {
                if bad < 2 {
                    eprintln!("stage {upto} shot {k} cut {cut} ex {ex} ey {ey}: bottom ok {} q ok {} ez ok {} (ez got {ezv})",
                              bot == wb, qv == wq, ezv == we);
                }
                bad += 1;
            }
        }
        eprintln!("stage {upto}: {bad}/64 wrong");
        if bad > 0 { break; }
    }
}

#[test]
fn frogdrop_dstep_and_inverse() {
    let n = 285usize; let nq = 150usize; let qbn = 24usize;
    let p = pval();
    // 64 (X, Y, q, Xout) cases: half phase-2 DV (X = r_{j-1}, Y = r_j), half phase-1 CO via D^-1 checks
    let mut rng = Rng::new(99);
    let mut cs = vec![];
    while cs.len() < 64 {
        let mut x = rng.below(256) % p;
        if x.is_zero() { continue; }
        if x > p >> 1 { x = p - x; }
        let (mut r, mut t) = (vec![p, x], vec![N::ZERO, N::from(1u64)]);
        while !r[r.len() - 1].is_zero() {
            let k = r.len();
            let qq = r[k - 2] / r[k - 1];
            let rn = r[k - 2] - qq * r[k - 1]; let tn = t[k - 2] + qq * t[k - 1];
            r.push(rn); t.push(tn);
        }
        let nn = r.len() - 1;
        let j = 1 + (rng.next() as usize) % (nn - 2);
        let qq = r[j - 1] / r[j];
        if blen(&qq) > qbn { continue; }
        let phase2 = cs.len() % 2 == 0;
        if (phase2 && blen(&r[j - 1]) > 140) || (!phase2 && blen(&t[j + 1]) > 140) { continue; }
        if cs.len() % 2 == 0 {
            cs.push((r[j - 1], r[j], qq, r[j + 1], false)); // D: X = r_{j-1} -> r_{j+1}
        } else {
            cs.push((t[j + 1], t[j], qq, t[j - 1], true)); // D on (t_{j+1}, t_j) gives q, t_{j-1}
        }
    }
    // D's cut: region = bl(Y) + qb lanes, so the borrow read at the region top covers every Y 2^k
    let cuts: Vec<usize> = cs.iter().map(|(_, y, _, _, _)| n - blen(y) - qbn).collect();
    let (clo, chi) = (*cuts.iter().min().unwrap(), *cuts.iter().max().unwrap());
    let mut b = B::new();
    let ring = b.alloc_n(n); let q = b.alloc_n(nq); let cutv = b.alloc_n(9); let qb = b.alloc_n(qbn);
    let zeros = b.alloc_n(80); let (c0, tmp) = (b.alloc(), b.alloc()); let pre = b.alloc_n(8);
    b.begin();
    dstep(&mut b, &ring, &q, &cutv, clo, chi, &qb, &zeros, c0, tmp, &pre, &[]);
    let rec = b.end();
    b.play(&rec, false);
    let td = b.tof;
    let nfwd = b.ops.len();
    b.play(&rec, true);
    let zs: Vec<N> = (0..64).map(|_| rng.below(100)).collect();
    let init = |w: &mut Vec<u64>| {
        for (k, (x, y, _, _, _)) in cs.iter().enumerate() {
            put(w, &ring[..cuts[k]], k, &(zs[k] & mask(cuts[k])));
            rev_into(w, &ring[cuts[k]..], k, x);
            put(w, &q, k, y);
            put(w, &cutv, k, &N::from(cuts[k] as u64));
        }
    };
    let rf = run(&b.ops[..nfwd], b.width() as usize, &init);
    let ra = run(&b.ops, b.width() as usize, &init);
    assert_eq!(rf.phase, 0);
    for (k, (x, y, qq, xo, _)) in cs.iter().enumerate() {
        assert_eq!(get(&rf.q, &qb, k), *qq, "q shot {k}");
        assert_eq!(rev_get(&rf.q, &ring[cuts[k]..], k, n - cuts[k]), *xo, "X out shot {k}");
        assert_eq!(get(&rf.q, &ring[..cuts[k]], k), zs[k] & mask(cuts[k]), "Z untouched shot {k}");
        assert_eq!(get(&rf.q, &q, k), *y);
        assert_eq!(rev_get(&ra.q, &ring[cuts[k]..], k, n - cuts[k]), *x, "inverse restores X shot {k}");
        assert_eq!(get(&ra.q, &qb, k), N::ZERO);
        for &qq2 in [c0, tmp].iter().chain(zeros.iter()).chain(pre.iter()) {
            assert_eq!((rf.q[qq2.0 as usize] >> k) & 1, 0, "scratch");
        }
    }
    eprintln!("D (24 bits): {td} Toffoli, cut window [{clo},{chi}]");
}

#[test]
fn frogdrop_pipeline() {
    let (k, kp, qb, tot) = (30usize, 32usize, 24usize, 80usize);
    let p = pval();
    let mut rng = Rng::new(4242);
    let mut cs = vec![];
    while cs.len() < 64 {
        let mut x = rng.below(256) % p;
        if x.is_zero() { continue; }
        if x > p >> 1 { x = p - x; }
        let (mut r, mut t) = (vec![p, x], vec![N::ZERO, N::from(1u64)]);
        while !r[r.len() - 1].is_zero() {
            let n = r.len();
            let qq = r[n - 2] / r[n - 1];
            let rn = r[n - 2] - qq * r[n - 1]; let tn = t[n - 2] + qq * t[n - 1];
            r.push(rn); t.push(tn);
        }
        let nn = r.len() - 1;
        let j = 1 + (rng.next() as usize) % (nn - 2);
        let phase2 = blen(&r[j - 1]) <= blen(&t[j - 1]);
        let (z, y) = if phase2 { (t[j], r[j]) } else { (r[j], t[j]) };
        let sz = blen(&z);
        let zh = z >> (sz - k);
        let sy = blen(&y).saturating_sub(kp);
        let yh = y >> sy;
        let e = 256 - (sz - k) - sy;
        if e > tot { continue; }
        let zodd = zh | N::from(1u64);
        let fh = ((N::from(1u64) << e) - N::from(1u64)) / zodd;
        let rfin = ((N::from(1u64) << e) - N::from(1u64)) % zodd;
        let q0 = fh / yh; let rho = fh % yh;
        if blen(&q0) > qb { continue; }
        cs.push((zh, yh, tot - e, q0, rho, rfin));
    }
    let mut b = B::new();
    let zh = b.alloc_n(k); let yh = b.alloc_n(kp); let startv = b.alloc_n(7);
    let ps = PScr { r: b.alloc_n(k + 1), rho: b.alloc_n(kp + 1), q0: b.alloc_n(qb), f: b.alloc(), g: b.alloc(),
                    c0: b.alloc(), zero: b.alloc(), one: b.alloc(), spre: b.alloc_n(6), tmp: b.alloc(), dirty: vec![] };
    b.x(ps.one);
    b.begin();
    let (rf, rhof) = pipeline(&mut b, &zh, &yh, &startv, tot, qb, &ps);
    let rec = b.end();
    b.play(&rec, false);
    let tp = b.tof;
    let nf = b.ops.len();
    b.play(&rec, true);
    let init = |w: &mut Vec<u64>| {
        for (s, (zv, yv, st, _, _, _)) in cs.iter().enumerate() {
            put(w, &zh, s, zv); put(w, &yh, s, yv); put(w, &startv, s, &N::from(*st as u64));
        }
    };
    let rfw = run(&b.ops[..nf], b.width() as usize, &init);
    let rall = run(&b.ops, b.width() as usize, &init);
    assert_eq!(rfw.phase, 0);
    for (s, (_, _, _, q0, rho, rfin)) in cs.iter().enumerate() {
        assert_eq!(get(&rfw.q, &ps.q0, s), *q0, "q0 shot {s}");
        assert_eq!(get(&rfw.q, &rhof, s), *rho, "rho shot {s}");
        assert_eq!(get(&rfw.q, &rf, s), *rfin, "R shot {s}");
        for &q in [ps.f, ps.g, ps.c0, ps.zero, ps.tmp].iter().chain(ps.spre.iter()) {
            assert_eq!((rfw.q[q.0 as usize] >> s) & 1, 0, "scratch dirty shot {s}");
        }
        for &q in ps.r.iter().chain(ps.rho.iter()).chain(ps.q0.iter()) {
            assert_eq!((rall.q[q.0 as usize] >> s) & 1, 0, "un-P leaves garbage shot {s}");
        }
    }
    eprintln!("pipeline P (K={k}, KP={kp}, QB={qb}, {tot} steps): {tp} Toffoli");
}

fn euclid_seq(x: N) -> (Vec<N>, Vec<N>) {
    let p = pval();
    let (mut r, mut t) = (vec![p, x], vec![N::ZERO, N::from(1u64)]);
    while !r[r.len() - 1].is_zero() {
        let n = r.len();
        let qq = r[n - 2] / r[n - 1];
        let rn = r[n - 2] - qq * r[n - 1]; let tn = t[n - 2] + qq * t[n - 1];
        r.push(rn); t.push(tn);
    }
    (r, t)
}

/// classical frogdrop machine: state (ph, j); column kinds HR step / HT step / switch (no step)
#[derive(Clone, Copy, PartialEq, Debug)]
enum Kd { Hr, Ht, Sw }

fn fd_kind(r: &[N], ph: u8, j: usize, l0: usize) -> Kd {
    if ph == 1 { Kd::Ht } else if blen(&r[j]) <= l0 { Kd::Sw } else { Kd::Hr }
}

fn fd_next(kd: Kd, j: usize) -> (u8, usize) {
    match kd { Kd::Hr => (0, j + 1), Kd::Ht => (1, j + 1), Kd::Sw => (1, j) }
}

/// (bottom, Q, top) register values of state (ph, j)
fn fd_regs(r: &[N], t: &[N], ph: u8, j: usize) -> (N, N, N) {
    if ph == 0 { (r[j], t[j - 1], t[j]) } else { (t[j], r[j - 1], r[j]) }
}

struct ColRig {
    b: B,
    fd: super::frogdrop_col::Fd,
    sc: super::frogdrop_col::ColScr,
    dirty: Vec<QubitId>,
    sy0: Vec<QubitId>,
}

fn col_rig(n: usize, nq: usize, kp: usize, qb: usize, tail: usize) -> ColRig {
    use super::frogdrop_col::*;
    let sw = super::pointadd_frogdrop::SW;
    let mut b = B::new();
    let fd = Fd { ring: b.alloc_n(n), q: b.alloc_n(nq), sy: b.alloc_n(sw), sx: b.alloc_n(sw), ph: b.alloc(),
                  cnt: b.alloc_n(7) };
    let dirty = b.alloc_n(64);
    let ps = PScr { r: vec![], rho: b.alloc_n(kp + 1), q0: b.alloc_n(qb), f: b.alloc(), g: b.alloc(), c0: b.alloc(),
                    zero: b.alloc(), one: b.alloc(), spre: b.alloc_n(6), tmp: b.alloc(), dirty: vec![] };
    let ms = MapScr { c0: b.alloc(), h: b.alloc(), e: b.alloc(), g: b.alloc(), f: b.alloc(), tmp: b.alloc(),
                      one: b.alloc(), anc: b.alloc_n(tail + 12), pre: b.alloc_n(8), ez: b.alloc_n(5),
                      epre: b.alloc_n(4), dirty: b.alloc_n(64) };
    let sc = ColScr { sz: b.alloc_n(9), cmpc: b.alloc(),
                      bq: b.alloc(), sw: b.alloc(), g: b.alloc(), act: b.alloc(), c0: b.alloc(), tmp: b.alloc(), tmp2: b.alloc(),
                      f: b.alloc(), one: b.alloc(), pre: b.alloc_n(8), opre: b.alloc_n(8), anc: b.alloc_n(tail + 12),
                      zeros: b.alloc_n(40), ps, ms, dirty: dirty.clone() };
    let sy0 = fd.sy.clone();
    ColRig { b, fd, sc, dirty, sy0 }
}

/// Run `cols` unified columns on 64 shots given as (euclid seq, start ph, start j); check every register.
fn run_cols(shots: &[((Vec<N>, Vec<N>), u8, usize)], cols: usize, l0: usize, nq: usize) {
    use super::frogdrop_col::*;
    let (n, k, kp, qb, tot, tail) = (289usize, 30usize, 32usize, 24usize, 86usize, 40usize);
    let mut rig = col_rig(n, nq, kp, qb, tail);
    let mut st: Vec<(u8, usize)> = shots.iter().map(|(_, ph, j)| (*ph, *j)).collect();
    let mut total = 0u64;
    for c in 0..cols {
        let mut cp = ColPar { n, nq, h: n - 257, k, kp, qb, tot, sz: (999, 0), sy: (999, 0), smax: (999, 0), m: 0,
                              tail, emax: 28, hr: false, ht: false, sw: false, l0, swl: (0, 0), dn: false, fin: false,
                              nomap: false, tt: false };
        let mut kinds = [0usize; 3];
        for (s, ((r, t), _, _)) in shots.iter().enumerate() {
            let (ph, j) = st[s];
            let kd = fd_kind(r, ph, j, l0);
            let (bz, by, mx) = match kd {
                Kd::Hr => { cp.hr = true; kinds[0] += 1; (blen(&r[j]), blen(&t[j]), blen(&t[j + 1]).max(blen(&t[j]))) }
                Kd::Ht => { cp.ht = true; kinds[1] += 1; (blen(&t[j]), blen(&r[j]), blen(&r[j + 1]).max(blen(&r[j]))) }
                Kd::Sw => {
                    cp.sw = true; kinds[2] += 1;
                    cp.swl.0 = cp.swl.0.max(blen(&r[j]).max(blen(&t[j - 1])));
                    cp.swl.1 = cp.swl.1.max(blen(&r[j - 1]).max(blen(&t[j])));
                    (blen(&r[j]), blen(&t[j]), blen(&r[j]).max(blen(&t[j])))
                }
            };
            cp.sz = (cp.sz.0.min(bz), cp.sz.1.max(bz));
            cp.sy = (cp.sy.0.min(by), cp.sy.1.max(by));
            cp.smax = (cp.smax.0.min(mx), cp.smax.1.max(mx));
            cp.m = cp.m.max(mx);
            st[s] = fd_next(kd, j);
        }
        let t0 = rig.b.tof;
        column(&mut rig.b, &mut rig.fd, &cp, &rig.sc);
        total += rig.b.tof - t0;
        eprintln!("column {c}: {} Toffoli, kinds HR/HT/SW {:?}, sz {:?} sy {:?} smax {:?} m {} swl {:?}",
                  rig.b.tof - t0, kinds, cp.sz, cp.sy, cp.smax, cp.m, cp.swl);
    }
    eprintln!("total {total} Toffoli over {cols} columns, peak qubits of the rig {}", rig.b.width());
    let (ring, q, sy0, fd, sc, dirty) = (&rig.fd.ring, &rig.fd.q, &rig.sy0, &rig.fd, &rig.sc, &rig.dirty);
    let dvals: Vec<N> = (0..64).map(|s| N::from(0x9e3779b97f4a7c15u64.wrapping_mul(s as u64 + 1))).collect();
    let r = run(&rig.b.ops, rig.b.width() as usize, &|w| {
        for (s, ((rr, tt), ph, j)) in shots.iter().enumerate() {
            let (bot, qv, top) = fd_regs(rr, tt, *ph, *j);
            put(w, &ring[..257], s, &bot);
            for i in 0..blen(&top) { if top.bit(i) { w[ring[n - 1 - i].0 as usize] |= 1 << s; } }
            put(w, q, s, &qv);
            put(w, sy0, s, &N::from(blen(&top) as u64));
            if *ph == 1 { w[fd.ph.0 as usize] |= 1 << s; }
            put(w, dirty, s, &dvals[s]);
        }
        w[sc.ps.one.0 as usize] = 0;
    });
    assert_eq!(r.phase, 0, "phase garbage");
    for (s, ((rr, tt), _, _)) in shots.iter().enumerate() {
        let (ph, j) = st[s];
        let (bot, x, y) = fd_regs(rr, tt, ph, j);
        let mut bad = vec![];
        for l in 0..n {
            let want = if l < 257 && bot.bit(l) { 1 } else if l >= n - blen(&y) && y.bit(n - 1 - l) { 1 } else { 0 };
            if (r.q[ring[l].0 as usize] >> s) & 1 != want { bad.push(l); }
        }
        assert!(bad.is_empty(), "shot {s} (end ph {ph} j {j}): ring lanes wrong {:?}", &bad[..bad.len().min(8)]);
        assert_eq!(get(&r.q, q, s), x, "shot {s}: Q");
        assert_eq!(get(&r.q, &fd.sy, s), N::from(blen(&y) as u64), "shot {s}: sy");
        assert_eq!(get(&r.q, &fd.sx, s), N::ZERO, "shot {s}: sx");
        assert_eq!((r.q[fd.ph.0 as usize] >> s) & 1, ph as u64, "shot {s}: ph");
        assert_eq!(get(&r.q, dirty, s), dvals[s], "shot {s}: dirty");
        let mut scr: Vec<QubitId> = vec![sc.cmpc, sc.bq, sc.sw, sc.g, sc.act, sc.c0, sc.tmp, sc.tmp2, sc.f,
                                         sc.one];
        for v in [&sc.sz, &sc.pre, &sc.opre, &sc.anc, &sc.zeros, &sc.ps.rho, &sc.ps.q0,
                  &sc.ps.spre, &sc.ms.anc, &sc.ms.pre, &sc.ms.ez, &sc.ms.epre] { scr.extend(v.iter()); }
        scr.extend([sc.ps.f, sc.ps.g, sc.ps.c0, sc.ps.zero, sc.ps.tmp, sc.ms.c0, sc.ms.h, sc.ms.e, sc.ms.g, sc.ms.f,
                    sc.ms.tmp, sc.ms.one]);
        for &qq in &scr { assert_eq!((r.q[qq.0 as usize] >> s) & 1, 0, "shot {s}: scratch q{} dirty", qq.0); }
    }
}

fn rand_shots(seed: u64, mut pick: impl FnMut(&mut Rng, &(Vec<N>, Vec<N>)) -> Option<(u8, usize)>)
    -> Vec<((Vec<N>, Vec<N>), u8, usize)> {
    let p = pval();
    let mut rng = Rng::new(seed);
    let mut shots = vec![];
    while shots.len() < 64 {
        let mut x = rng.below(256) % p;
        if x.is_zero() { continue; }
        if x > p >> 1 { x = p - x; }
        let seq = euclid_seq(x);
        if let Some((ph, j)) = pick(&mut rng, &seq) { shots.push((seq, ph, j)); }
    }
    shots
}

#[test]
fn frogdrop_hr_columns() {
    let cols: usize = std::env::var("FROGDROP_COLS").ok().and_then(|s| s.parse().ok()).unwrap_or(6);
    let shots = rand_shots(777, |_, _| Some((0, 1)));
    run_cols(&shots, cols, 0, 150);
}

#[test]
fn frogdrop_ht_columns() {
    let cols: usize = std::env::var("FROGDROP_COLS").ok().and_then(|s| s.parse().ok()).unwrap_or(4);
    let shots = rand_shots(901, |rng, (r, t)| {
        let nn = r.len() - 1;
        let cross = (1..nn).find(|&j| blen(&r[j - 1]) <= blen(&t[j - 1])).unwrap();
        if cross + 1 + cols + 2 >= nn { return None; }
        let hi = nn - 2 - cols;
        Some((1, cross + 1 + (rng.next() as usize) % (hi - cross)))
    });
    run_cols(&shots, cols, 0, 150);
}

/// shots start 0..4 HR steps before their switch (first j with bl(r_j) <= l0) and run through it
#[test]
fn frogdrop_switch_columns() {
    let cols: usize = std::env::var("FROGDROP_COLS").ok().and_then(|s| s.parse().ok()).unwrap_or(7);
    let l0: usize = std::env::var("FROGDROP_L0").ok().and_then(|s| s.parse().ok()).unwrap_or(120);
    let nq: usize = std::env::var("FROGDROP_NQ").ok().and_then(|s| s.parse().ok()).unwrap_or(150);
    let shots = rand_shots(4242, |rng, (r, _)| {
        let jsw = (1..r.len()).find(|&j| blen(&r[j]) <= l0).unwrap();
        Some((0, jsw.saturating_sub((rng.next() as usize) % 5).max(1)))
    });
    run_cols(&shots, cols, l0, nq);
}

/// Full traversal: 64 shots from HR(1) through the switch, the end of Euclid (done idling) and the end fix.
#[test]
fn frogdrop_traversal() {
    use super::frogdrop_col::*;
    let l0: usize = std::env::var("FROGDROP_L0").ok().and_then(|s| s.parse().ok()).unwrap_or(120);
    let nq: usize = std::env::var("FROGDROP_NQ").ok().and_then(|s| s.parse().ok()).unwrap_or(150);
    let seed: u64 = std::env::var("FROGDROP_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(31337);
    let n: usize = std::env::var("FROGDROP_N").ok().and_then(|s| s.parse().ok()).unwrap_or(289);
    let (k, kp, qb, tot, tail) = (30usize, 32usize, 24usize, 86usize, 40usize);
    let shots = rand_shots(seed, |_, _| Some((0, 1)));
    let lens: Vec<usize> = shots.iter().map(|((r, _), _, _)| r.len() - 1).collect(); // N (r[N] = 0)
    let cols = lens.iter().map(|nn| nn - 1).max().unwrap();
    eprintln!("Euclid lengths {}..{}, columns {cols}", lens.iter().min().unwrap(), lens.iter().max().unwrap());
    // model state per shot: (ph, j, done, cnt, a0)
    let mut st: Vec<(u8, usize, bool, usize, bool)> = vec![(0, 1, false, 0, false); 64];
    let mut rig = col_rig(n, nq, kp, qb, tail);
    let base = ColPar { n, nq, h: n - 257, k, kp, qb, tot, sz: (999, 0), sy: (999, 0), smax: (999, 0), m: 0, tail,
                        emax: 28, hr: false, ht: false, sw: false, l0, swl: (0, 0), dn: false, fin: false,
                        nomap: false, tt: false };
    let mut total = 0u64;
    for c in 0..cols {
        let mut cp = base.clone();
        let mut kinds = [0usize; 4];
        for (s, ((r, t), _, _)) in shots.iter().enumerate() {
            let nn = lens[s];
            let (ph, j, done, cnt, a0) = st[s];
            let rr = r[nn - 2];
            let (bz, by, mx);
            if done {
                cp.dn = true; kinds[3] += 1;
                if a0 { bz = blen(&t[nn - 1]); by = 1; mx = blen(&rr); } else { bz = blen(&t[nn - 2]); by = blen(&rr); mx = blen(&rr); }
                st[s] = (ph, j, true, cnt + 1, !a0);
            } else {
                let kd = fd_kind(r, ph, j, l0);
                match kd {
                    Kd::Hr => { cp.hr = true; kinds[0] += 1; bz = blen(&r[j]); by = blen(&t[j]); mx = blen(&t[j + 1]).max(blen(&t[j])); }
                    Kd::Ht => { cp.ht = true; kinds[1] += 1; bz = blen(&t[j]); by = blen(&r[j]); mx = blen(&r[j + 1]).max(blen(&r[j])); }
                    Kd::Sw => {
                        cp.sw = true; kinds[2] += 1;
                        cp.swl.0 = cp.swl.0.max(blen(&r[j]).max(blen(&t[j - 1])));
                        cp.swl.1 = cp.swl.1.max(blen(&r[j - 1]).max(blen(&t[j])));
                        bz = blen(&r[j]); by = blen(&t[j]); mx = blen(&r[j]).max(blen(&t[j]));
                    }
                }
                let (ph2, j2) = fd_next(kd, j);
                if kd == Kd::Ht && j2 == nn - 1 { cp.fin = true; st[s] = (ph2, j2, true, 0, true); } else { st[s] = (ph2, j2, false, 0, false); }
            }
            cp.sz = (cp.sz.0.min(bz), cp.sz.1.max(bz));
            cp.sy = (cp.sy.0.min(by), cp.sy.1.max(by));
            cp.smax = (cp.smax.0.min(mx), cp.smax.1.max(mx));
            cp.m = cp.m.max(mx);
        }
        let t0 = rig.b.tof;
        column(&mut rig.b, &mut rig.fd, &cp, &rig.sc);
        total += rig.b.tof - t0;
        if c % 10 == 0 || kinds[2] > 0 && kinds[2] == 64 || c + 3 > cols {
            eprintln!("column {c}: {} T, HR/HT/SW/idle {:?}, sz {:?} sy {:?} smax {:?}", rig.b.tof - t0, kinds, cp.sz, cp.sy, cp.smax);
        }
    }
    // end fix: B0 shots (odd idle count) map back to A0; then the last middle clears R
    let mut cpb = base.clone();
    let mut nb0 = 0;
    for (s, ((r, t), _, _)) in shots.iter().enumerate() {
        let (_, _, done, _, a0) = st[s];
        assert!(done);
        let nn = lens[s];
        if !a0 {
            nb0 += 1;
            let mx = blen(&r[nn - 2]);
            cpb.smax = (cpb.smax.0.min(mx), cpb.smax.1.max(mx));
            cpb.m = cpb.m.max(mx);
            let _ = t;
        }
    }
    if let Ok(v) = std::env::var("FROGDROP_B0") {
        let w: Vec<usize> = v.split(',').map(|x| x.parse().unwrap()).collect();
        cpb.smax = (w[0], w[1]);
        cpb.m = w[1];
    }
    let mut cpl = base.clone();
    cpl.ht = true;
    cpl.nomap = true;
    for (s, ((_, t), _, _)) in shots.iter().enumerate() {
        let bz = blen(&t[lens[s] - 1]);
        cpl.sz = (cpl.sz.0.min(bz), cpl.sz.1.max(bz));
    }
    cpl.sy = (1, 1);
    let t0 = rig.b.tof;
    let scc = rig.sc.clone();
    traversal_end(&mut rig.b, &mut rig.fd, if nb0 > 0 { Some(&cpb) } else { None }, &cpl, &|_| scc.clone());
    total += rig.b.tof - t0;
    eprintln!("end: {} T ({nb0} B0 shots); traversal total {total} T over {cols} columns", rig.b.tof - t0);
    let (ring, q, sy0, fd, sc) = (&rig.fd.ring, &rig.fd.q, &rig.sy0, &rig.fd, &rig.sc);
    let r = run(&rig.b.ops, rig.b.width() as usize, &|w| {
        for (s, ((rr, tt), _, _)) in shots.iter().enumerate() {
            put(w, &ring[..257], s, &rr[1]);
            w[ring[n - 1].0 as usize] |= 1 << s;
            put(w, sy0, s, &N::from(1u64));
            let _ = tt;
        }
        w[sc.ps.one.0 as usize] = 0;
    });
    assert_eq!(r.phase, 0, "phase garbage");
    let mut nbad = 0;
    for (s, ((_, tt), _, _)) in shots.iter().enumerate() {
        let nn = lens[s];
        let z = tt[nn - 1];
        let mut bad = vec![];
        for l in 0..n {
            let want = if l < 257 && z.bit(l) { 1 } else if l == n - 1 { 1 } else { 0 };
            if (r.q[ring[l].0 as usize] >> s) & 1 != want { bad.push(l); }
        }
        let ok = bad.is_empty() && get(&r.q, q, s) == N::ZERO && get(&r.q, &fd.sy, s) == N::from(1u64)
            && get(&r.q, &fd.sx, s) == N::ZERO && (r.q[fd.ph.0 as usize] >> s) & 1 == 1
            && get(&r.q, &fd.cnt, s) == N::from((cols - (nn - 1) + 1) as u64);
        let mut scr: Vec<QubitId> = vec![sc.cmpc, sc.bq, sc.sw, sc.g, sc.act, sc.c0, sc.tmp, sc.tmp2, sc.f, sc.one];
        for v in [&sc.sz, &sc.pre, &sc.opre, &sc.anc, &sc.zeros, &sc.ps.rho, &sc.ps.q0] {
            scr.extend(v.iter());
        }
        let sok = scr.iter().all(|qq| (r.q[qq.0 as usize] >> s) & 1 == 0);
        if !(ok && sok) {
            if nbad < 4 {
                eprintln!("shot {s} (N {nn}): ring bad {:?}, Q {} sy {} ph {} done {} cnt {} (want {}), scratch ok {sok}",
                          &bad[..bad.len().min(8)], get(&r.q, q, s), get(&r.q, &fd.sy, s), (r.q[fd.ph.0 as usize] >> s) & 1,
                          0, get(&r.q, &fd.cnt, s), cols - (nn - 1) + 1);
            }
            nbad += 1;
        }
    }
    assert_eq!(nbad, 0, "{nbad}/64 shots wrong");
}

/// Schedule envelopes: build from FROGDROP_M shots with margins FROGDROP_DS/FROGDROP_DC/FROGDROP_DCOLS, validate on FROGDROP_V fresh shots;
/// writes the schedule to FROGDROP_OUT if set.
#[test]
#[ignore = "tool: run with --ignored and FROGDROP_* settings"]
fn frogdrop_sched_gen() {
    use super::frogdrop_sched::*;
    let env = |k: &str, d: usize| std::env::var(k).ok().and_then(|s| s.parse().ok()).unwrap_or(d);
    let (m, v, ds, dc, dcols, dw) = (env("FROGDROP_M", 20000), env("FROGDROP_V", 20000), env("FROGDROP_DS", 0), env("FROGDROP_DC", 0),
                                     env("FROGDROP_DCOLS", 0), env("FROGDROP_DW", 0));
    let t0 = std::time::Instant::now();
    let shots: Vec<Shot> = sample(m, 11).into_iter().map(|x| shot(x, L0)).collect();
    eprintln!("{m} shots in {:?}", t0.elapsed());
    let sc = envelope(&shots, ds, dc, dcols, dw);
    let qn = shots.iter().flat_map(|s| s.recs.iter().map(|r| r.qn)).max().unwrap();
    eprintln!("columns {}, Q need {qn}, b0 {:?} lsz {:?}", sc.cols.len(), sc.b0, sc.lsz);
    let fresh: Vec<Shot> = sample(v, 12345).into_iter().map(|x| shot(x, L0)).collect();
    let mut fails = std::collections::BTreeMap::<String, usize>::new();
    let mut nf = 0;
    for s in &fresh {
        if let Some(why) = check(s, &sc) {
            nf += 1;
            let key: String = why.split(':').next().unwrap().chars().take(12).collect();
            *fails.entry(key).or_default() += 1;
            if nf <= 5 { eprintln!("  fail: {why}"); }
        }
    }
    let qnf = fresh.iter().flat_map(|s| s.recs.iter().map(|r| r.qn)).max().unwrap();
    eprintln!("fresh {v}: {nf} outside ({:.2e}/shot), fresh Q need {qnf}; by kind {:?}", nf as f64 / v as f64, fails);
    if let Ok(path) = std::env::var("FROGDROP_OUT") {
        std::fs::write(&path, to_text(&sc)).unwrap();
        eprintln!("wrote {path}");
    }
}

/// Q need tail: per-shot max Q value bits over FROGDROP_V shots.
#[test]
#[ignore = "tool: run with --ignored and FROGDROP_* settings"]
fn frogdrop_qneed_tail() {
    use super::frogdrop_sched::*;
    let v = std::env::var("FROGDROP_V").ok().and_then(|s| s.parse().ok()).unwrap_or(1000000usize);
    let l0 = std::env::var("FROGDROP_L0").ok().and_then(|s| s.parse().ok()).unwrap_or(L0);
    let mut h = std::collections::BTreeMap::<usize, usize>::new();
    for x in sample(v, 777) {
        let s = shot(x, l0);
        let q = s.recs.iter().map(|r| r.qn).max().unwrap();
        *h.entry(q).or_default() += 1;
    }
    let mut tail = 0usize;
    let mut rows = vec![];
    for (&k, &c) in h.iter().rev() {
        tail += c;
        rows.push(format!("P(qn >= {k}) = {:.2e}", tail as f64 / v as f64));
        if rows.len() >= 10 { break; }
    }
    eprintln!("L0 {l0}: {}", rows.join(", "));
}

/// Windowed quotient estimate (as the column computes it) over FROGDROP_V shots: failures q0 - b != q, q0 >= 2^QB,
/// e > TOT. Uses FROGDROP_K / FROGDROP_KP.
#[test]
#[ignore = "tool: run with --ignored and FROGDROP_* settings"]
fn frogdrop_est_rate() {
    use super::frogdrop_sched::*;
    use super::frogdrop_sched::p;
    let env = |k: &str, d: usize| std::env::var(k).ok().and_then(|s| s.parse().ok()).unwrap_or(d);
    let (v, k, kp, qb, tot) = (env("FROGDROP_V", 100000), env("FROGDROP_K", 30), env("FROGDROP_KP", 32), env("FROGDROP_QB", 24),
                               env("FROGDROP_TOT", 86));
    let seed = env("FROGDROP_SEED", 99) as u64;
    let pp = p();
    let one = N::from(1u64);
    let (mut dec, mut bad, mut qover, mut eover) = (0u64, 0u64, 0u64, 0u64);
    let mut badq = std::collections::BTreeMap::<usize, u64>::new();
    for xr in sample(v, seed) {
        let (mut r, mut t) = (vec![pp, xr], vec![N::ZERO, one]);
        while !r[r.len() - 1].is_zero() {
            let n = r.len();
            let q = r[n - 2] / r[n - 1];
            let rn = r[n - 2] - q * r[n - 1];
            let tn = t[n - 2] + q * t[n - 1];
            r.push(rn);
            t.push(tn);
        }
        let nn = r.len() - 1;
        let mut ph = 0;
        for j in 1..nn - 1 {
            if ph == 0 && r[j].bit_len() <= L0 { ph = 1; }
            let q = r[j - 1] / r[j];
            let (z, x, y) = if ph == 0 { (r[j], t[j - 1], t[j]) } else { (t[j], r[j + 1], r[j]) };
            let (sz, sy) = (z.bit_len(), y.bit_len());
            let zh = (z >> (sz - k)) | one;
            let (yh, xh) = if sy >= kp { (y >> (sy - kp), x >> (sy - kp)) } else { (y << (kp - sy), x << (kp - sy)) };
            let e = 256 + k + kp - sz - sy;
            dec += 1;
            if e > tot { eover += 1; continue; }
            let fh = ((one << e) - one) / zh;
            let (q0, rho) = (fh / yh, fh % yh);
            if q0 >= (one << qb) { qover += 1; continue; }
            let b = if rho < xh { one } else { N::ZERO };
            if q0 - b != q {
                bad += 1;
                *badq.entry(q.bit_len()).or_default() += 1;
            }
        }
    }
    eprintln!("K {k} KP {kp} QB {qb} TOT {tot}: {dec} decisions over {v} shots: wrong {bad} ({:.2e}/shot), q0 over {qover} \
               ({:.2e}/shot), e over {eover}; wrong by bl(q) {:?}", bad as f64 / v as f64, qover as f64 / v as f64, badq);
}

/// The real traversal (pointadd_frogdrop::trav_forward with sched_frogdrop.txt) on 64 random shots: end state per shot.
#[test]
fn frogdrop_traversal_sched() {
    use super::frogdrop_sched::{sample, shot, from_text};
    let seed: u64 = std::env::var("FROGDROP_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(5);
    let xs = sample(64, seed);
    let ncols = from_text(super::pointadd_frogdrop::SCHED_FROGDROP).cols.len();
    let mut b = B::new();
    let xq = b.alloc_n(256);
    let dirty = b.alloc_n(256);
    let t = super::pointadd_frogdrop::trav_forward(&mut b, &xq, &dirty);
    eprintln!("trav_forward: {} T, {} ops, peak {}", b.tof, b.ops.len(), b.peak);
    let dv: Vec<N> = (0..64).map(|s| N::from(0x9e3779b97f4a7c15u64.wrapping_mul(s as u64 + 3))).collect();
    let r = run(&b.ops, b.width() as usize, &|w| {
        for s in 0..64 {
            put(w, &xq, s, &xs[s]);
            put(w, &dirty, s, &dv[s]);
        }
    });
    assert_eq!(r.phase, 0, "phase garbage");
    let mut nbad = 0;
    for s in 0..64 {
        let (rr, tt) = euclid_seq(xs[s]);
        let nn = rr.len() - 1;
        let sh = shot(xs[s], super::frogdrop_sched::L0);
        assert_eq!(sh.recs.len(), nn - 1);
        let want_t = tt[nn - 1];
        let ok_t = get(&r.q, &t.fd.ring[0..255], s) == want_t;
        let mut cl: Vec<QubitId> = t.fd.cnt[0..6].to_vec();
        cl.push(t.fd.ring[255]); // the counter's top bit is parked in ring lane 255
        let cnt = get(&r.q, &cl, s);
        let ok_c = cnt == N::from((ncols - (nn - 1) + 1) as u64);
        let ok_d = get(&r.q, &dirty, s) == dv[s];
        let mut zero_ok = true;
        for &q in t.fd.ring[256..].iter().chain(t.fd.q.iter()).chain(t.fd.sy.iter()).chain(t.fd.sx.iter())
            .chain([t.fd.ph, t.fd.cnt[6]].iter()).chain(t.pool.iter()) {
            if (r.q[q.0 as usize] >> s) & 1 != 0 { zero_ok = false; }
        }
        if !(ok_t && ok_c && ok_d && zero_ok) {
            if nbad < 4 { eprintln!("shot {s} (N {nn}): t ok {ok_t} cnt {cnt} (want {}) dirty ok {ok_d} zeros ok {zero_ok}", ncols - (nn - 1) + 1); }
            nbad += 1;
        }
    }
    assert_eq!(nbad, 0, "{nbad}/64 shots wrong");
}

/// Debug: the real schedule's first FROGDROP_C columns on 64 shots; per-shot register check vs the model.
#[test]
#[ignore = "tool: run with --ignored and FROGDROP_* settings"]
fn frogdrop_sched_prefix() {
    use super::frogdrop_col::*;
    use super::frogdrop_sched::{sample, shot, Kind, L0};
    use super::pointadd_frogdrop::*;
    let seed: u64 = std::env::var("FROGDROP_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(5);
    let ncol: usize = std::env::var("FROGDROP_C").ok().and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut xs = sample(64, seed);
    if let Ok(v) = std::env::var("FROGDROP_XS") {
        for (i, h) in v.split(',').enumerate() {
            xs[i] = N::from_str_radix(h.trim_start_matches("0x"), 16).unwrap();
        }
    }
    let (cols, _, _) = col_pars(&super::frogdrop_sched::from_text(SCHED_FROGDROP));
    let mut b = B::new();
    let xq = b.alloc_n(256);
    let dirty = b.alloc_n(256);
    let mut ring = xq.clone();
    ring.extend(b.alloc_n(N - 256));
    let mut fd = Fd { ring, q: b.alloc_n(NQ), sy: b.alloc_n(SW), sx: b.alloc_n(SW), ph: b.alloc(), cnt: b.alloc_n(CNTB) };
    let pool = b.alloc_n(pool_size(KP, QB, SW));
    b.x(fd.ring[N - 1]);
    b.x(fd.sy[0]);
    for cp in &cols[..ncol] {
        let sc = ColScr::carve(&pool, &fd.sx, &dirty, KP, QB, TAIL);
        column(&mut b, &mut fd, cp, &sc);
    }
    let endm: usize = std::env::var("FROGDROP_END").ok().and_then(|s| s.parse().ok()).unwrap_or(0);
    if endm > 0 {
        let (_, b0, last) = col_pars(&super::frogdrop_sched::from_text(SCHED_FROGDROP));
        let carve = |sx: &[QubitId]| ColScr::carve(&pool, sx, &dirty, KP, QB, TAIL);
        traversal_end(&mut b, &mut fd, if endm == 1 { b0.as_ref() } else { None }, &last, &carve);
        let r = run(&b.ops, b.width() as usize, &|w| {
            for s in 0..64 { put(w, &xq, s, &xs[s]); }
        });
        let mut bad = vec![];
        for s in 0..64 {
            let (rr, tt) = euclid_seq(xs[s]);
            let nn = rr.len() - 1;
            let idle = ncol - (nn - 1);
            let ok_t = get(&r.q, &fd.ring[0..256], s) == tt[nn - 1];
            let ok_q = get(&r.q, &fd.q, s) == N::ZERO;
            let ok_top = (r.q[fd.ring[N - 1].0 as usize] >> s) & 1 == 1;
            let ok_sy = get(&r.q, &fd.sy, s) == N::from(1u64);
            let ok_p = pool.iter().all(|q| (r.q[q.0 as usize] >> s) & 1 == 0);
            if !(ok_t && ok_q && ok_top && ok_sy && ok_p) {
                bad.push((s, idle % 2, blen(&rr[nn - 2]), ok_t, ok_q, ok_top, ok_sy, ok_p));
            }
        }
        eprintln!("END: phase {:#x}; bad (shot, idle parity, bl R, t, Q, top, sy, pool) {:?}", r.phase, bad);
        return;
    }
    let r = run(&b.ops, b.width() as usize, &|w| {
        for s in 0..64 { put(w, &xq, s, &xs[s]); }
    });
    let mut bad = vec![];
    for s in 0..64 {
        let (rr, tt) = euclid_seq(xs[s]);
        let sh = shot(xs[s], L0);
        let nn = rr.len() - 1;
        let (mut ph, mut j) = (0u8, 1usize);
        let (bot, qv, top, cnt);
        if ncol < sh.recs.len() {
            for c in 0..ncol {
                match sh.recs[c].kind { Kind::Hr => j += 1, Kind::Ht => j += 1, Kind::Sw => ph = 1, Kind::Idle => {} }
            }
            let v = fd_regs(&rr, &tt, ph, j);
            bot = v.0; qv = v.1; top = v.2; cnt = 0usize;
        } else {
            let idle = ncol - sh.recs.len();
            if idle % 2 == 0 { bot = tt[nn - 1]; qv = rr[nn - 2]; top = N::from(1u64); }
            else { bot = tt[nn - 2]; qv = N::from(1u64); top = rr[nn - 2]; }
            ph = 1; cnt = idle + 1;
        }
        let mut badl = 0;
        for l in 0..N {
            let want = if l < 257 && bot.bit(l) { 1 } else if l >= N - blen(&top) && top.bit(N - 1 - l) { 1 } else { 0 };
            if (r.q[fd.ring[l].0 as usize] >> s) & 1 != want { badl += 1; }
        }
        let fl = [badl == 0, get(&r.q, &fd.q, s) == qv, get(&r.q, &fd.sy, s) == N::from(blen(&top) as u64),
            (r.q[fd.ph.0 as usize] >> s) & 1 == ph as u64, true,
            get(&r.q, &fd.cnt, s) == N::from(cnt as u64), get(&r.q, &fd.sx, s) == N::ZERO,
            pool.iter().all(|q| (r.q[q.0 as usize] >> s) & 1 == 0)];
        if fl.iter().any(|x| !x) {
            let dirty_pool: Vec<usize> = (0..pool.len()).filter(|&i| (r.q[pool[i].0 as usize] >> s) & 1 == 1).collect();
            if bad.len() < 3 { eprintln!("shot {s}: ring/Q/sy/ph/done/cnt/sx/pool {:?} dirty pool idx {:?}", fl, dirty_pool); }
            bad.push((s, nn, badl));
        }
    }
    eprintln!("C={ncol}: phase {:#x}; bad shots {:?}", r.phase, bad);
}

/// Nonce predictor: build the frogdrop circuit, hash it as eval_circuit does (Fiat-Shamir), derive the 9024 test
/// shots and evaluate the classical failure predicate of both divisions. Then scan FROGDROP_SCAN alternative nonces
/// (the final X X pair's qubit) and report the clean ones.
#[test]
#[ignore = "tool: run with --ignored and FROGDROP_* settings"]
fn frogdrop_predict_nonce() {
    use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
    use super::frogdrop_sched::{from_text, predict};
    use super::pointadd_frogdrop::*;
    use sha3::digest::{ExtendableOutput, Update, XofReader};
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
    let scan: usize = std::env::var("FROGDROP_SCAN").ok().and_then(|s| s.parse().ok()).unwrap_or(0);
    let mut b = B::new();
    let _ = point_add(&mut b);
    let ops = std::mem::take(&mut b.ops);
    let width = b.width();
    eprintln!("built {} ops, width {width}", ops.len());
    let l = ops.len();
    let mut pre = sha3::Shake256::default();
    pre.update(b"quantum_ecc-fiat-shamir-v2");
    pre.update(&(l as u64).to_le_bytes());
    let upd = |h: &mut sha3::Shake256, op: &crate::circuit::Op| {
        h.update(&[op.kind as u8]);
        h.update(&op.q_control2.0.to_le_bytes());
        h.update(&op.q_control1.0.to_le_bytes());
        h.update(&op.q_target.0.to_le_bytes());
        h.update(&op.c_target.0.to_le_bytes());
        h.update(&op.c_condition.0.to_le_bytes());
        h.update(&op.r_target.0.to_le_bytes());
    };
    for op in &ops[..l - 2] { upd(&mut pre, op); }
    let tail = ops[l - 2];
    drop(ops);
    let sched = from_text(SCHED_FROGDROP);
    let pp = super::frogdrop_sched::p();
    let to_n = |u: U| -> N { let mut v = N::ZERO; for (i, &w) in u.as_limbs().iter().enumerate() { v |= N::from(w) << (64 * i); } v };
    let pred = |x: N| predict(x, &sched, K, KP, QB, TOT, NQ, EMAX);
    let half = std::env::var("FROGDROP_SHOTS").ok().and_then(|s| s.parse().ok()).unwrap_or(9024usize);
    let mut clean = vec![];
    for nonce in 0..(scan.max(1) as u64) {
        let q = if scan == 0 { tail.q_target.0 } else { nonce };
        if q >= width { break; }
        let mut h = pre.clone();
        let mut op = tail;
        op.q_target = crate::circuit::QubitId(q);
        upd(&mut h, &op);
        upd(&mut h, &op);
        let mut xof = h.finalize_xof();
        let mut fails = std::collections::BTreeMap::<&str, usize>::new();
        let mut n = 0;
        for _ in 0..half {
            let mut rb = [[0u8; 32]; 2];
            xof.read(&mut rb[0]);
            xof.read(&mut rb[1]);
            let k1 = U::from_le_bytes(rb[0]);
            let k2 = U::from_le_bytes(rb[1]);
            let t = curve.mul(curve.gx, curve.gy, k1);
            let o = curve.mul(curve.gx, curve.gy, k2);
            if t.0 == o.0 || (t.0.is_zero() && t.1.is_zero()) || (o.0.is_zero() && o.1.is_zero()) { continue; }
            let e = curve.add(t.0, t.1, o.0, o.1);
            n += 1;
            let (x1, x2, x3) = (to_n(t.0), to_n(o.0), to_n(e.0));
            let d1 = if x1 >= x2 { x1 - x2 } else { x1 + pp - x2 };
            let d2 = if x3 >= x2 { x3 - x2 } else { x3 + pp - x2 };
            if std::env::var("FROGDROP_DUMP").ok().and_then(|v| v.parse::<usize>().ok()) == Some(n - 1) {
                eprintln!("DUMP shot {}: x1' {:#x} x2' {:#x}", n - 1, d1, d2);
            }
            for d in [d1, d2] {
                if let Some(why) = pred(d) { *fails.entry(why).or_default() += 1; }
            }
        }
        let nf: usize = fails.values().sum();
        eprintln!("nonce qubit {q}: {n} shots, failing divisions {nf} {:?}", fails);
        if nf == 0 { clean.push(q); }
    }
    eprintln!("clean nonces: {:?}", clean);
}

#[test]
#[ignore = "tool: run with --ignored and FROGDROP_* settings"]
fn frogdrop_debug_rec() {
    use super::frogdrop_sched::*;
    let x = N::from_str_radix(std::env::var("FROGDROP_X1").unwrap().trim_start_matches("0x"), 16).unwrap();
    let c0: usize = std::env::var("FROGDROP_C").ok().and_then(|s| s.parse().ok()).unwrap_or(85);
    let s = shot(x, L0);
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(&from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    let (rr, tt) = euclid_seq(x);
    for c in c0.saturating_sub(2)..c0 + 2 {
        let r = s.rec(c);
        let e = &cols[c];
        eprintln!("col {c}: {:?}\n   env hr {} ht {} sw {} dn {} fin {} sz {:?} sy {:?} smax {:?} m {} swl {:?}", r, e.hr, e.ht,
                  e.sw, e.dn, e.fin, e.sz, e.sy, e.smax, e.m, e.swl);
    }
    let mut j = 1; let mut ph = 0;
    for c in 0..c0 { match s.recs[c].kind { Kind::Hr | Kind::Ht => j += 1, Kind::Sw => ph = 1, _ => {} } }
    let q = rr[j - 1] / rr[j];
    eprintln!("at col {c0}: ph {ph} j {j} q {} bl(r_j) {} bl(t_j) {} v2 r_j+1 {} v2 t_j+1 {} v2 r_j {} v2 t_j {}", q, rr[j].bit_len(),
              tt[j].bit_len(), rr[j + 1].trailing_zeros(), tt[j + 1].trailing_zeros(), rr[j].trailing_zeros(), tt[j].trailing_zeros());
}

/// Classical failure rate of the full predicate (per traversal input) for ring sizes FROGDROP_NR (comma list).
#[test]
#[ignore = "tool: run with --ignored and FROGDROP_* settings"]
fn frogdrop_pred_rate() {
    use super::frogdrop_sched::{from_text, predict_n, sample};
    use super::pointadd_frogdrop::*;
    let v: usize = std::env::var("FROGDROP_V").ok().and_then(|s| s.parse().ok()).unwrap_or(200000);
    let nrs: Vec<usize> = std::env::var("FROGDROP_NR").unwrap_or("288".into()).split(',').map(|x| x.parse().unwrap()).collect();
    let sched = from_text(SCHED_FROGDROP);
    let xs = sample(v, 4321);
    for nr in nrs {
        let mut f = std::collections::BTreeMap::<&str, usize>::new();
        for x in &xs {
            if let Some(w) = predict_n(*x, &sched, K, KP, QB, TOT, NQ, EMAX, nr) { *f.entry(w).or_default() += 1; }
        }
        let tot: usize = f.values().sum();
        eprintln!("ring {nr}: {tot}/{v} fail ({:.2e}/input, lambda ~{:.3} over 18048) {:?}", tot as f64 / v as f64,
                  tot as f64 / v as f64 * 18048.0, f);
    }
}

#[test]
fn modp_fold_dirty_carry() {
    use super::modp_frogdrop::{add_small, Ms, C};
    for &(lo, k) in &[(0usize, C), (4usize, C - 1)] {
        let mut b = B::new();
        let t = b.alloc_n(256);
        let g = b.alloc_n(256);
        let ctl = b.alloc();
        let ms = Ms::alloc(&mut b);
        add_small(&mut b, &ms, &t, lo, Some(ctl), k, &g);
        let mut rng = Rng::new(lo as u64 + 77);
        let mut tv: Vec<N> = vec![];
        let mut gv: Vec<N> = vec![];
        for s in 0..64 {
            let mut x = rng.below(256);
            // force long carry runs into both borrowed increments, but keep bits 41 and 63 clear (no truncation)
            if s % 2 == 0 { for j in 0..41 { x |= N::from(1u64) << j; } }
            if s % 4 == 0 { for j in 32..63 { x |= N::from(1u64) << j; } }
            let c41: N = N::from(1u64) << 41;
            let c63: N = N::from(1u64) << 63;
            x &= !c41;
            x &= !c63;
            tv.push(x);
            gv.push(rng.below(256));
        }
        let (tv2, gv2, t2, g2) = (tv.clone(), gv.clone(), t.clone(), g.clone());
        let width = b.width() as usize;
        let r = run(&b.ops, width, &move |w| {
            for s in 0..64 {
                put(w, &t2, s, &tv2[s]);
                put(w, &g2, s, &gv2[s]);
                if s % 3 != 2 { w[ctl.0 as usize] |= 1 << s; }
            }
        });
        let m256 = (N::from(1u64) << 256) - N::from(1u64);
        for s in 0..64 {
            let c = s % 3 != 2;
            let want = (tv[s] + if c { N::from(k) } else { N::ZERO }) & m256;
            assert_eq!(get(&r.q, &t, s), want, "fold lo {lo} shot {s}");
            assert_eq!(get(&r.q, &g, s), gv[s], "dirty restored");
            assert_eq!(getb(&r.q, ctl, s), c as u64, "ctrl restored");
        }
        assert_eq!(r.phase, 0);
        for s in 0..64 { assert_eq!(getb(&r.q, ms.k, s), 0); }
        eprintln!("fold lo {lo}: ok ({} T)", b.tof);
    }
}

#[test]
fn frogdrop_point_add_end_to_end() {
    use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
    let mut b = B::new();
    let (xq, yq) = super::pointadd_frogdrop::point_add(&mut b);
    let ops = std::mem::take(&mut b.ops);
    let (nq, _, _, regs) = crate::circuit::analyze_ops(ops.iter());
    eprintln!("ops {} qubits {} peak {} emitted tof {}", ops.len(), nq, b.peak, b.tof);
    // curve
    let pp = super::frogdrop_sched::p();
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
    let mut rng = Rng::new(std::env::var("FROGDROP_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(2024));
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
    h.update(b"frogdrop-e2e");
    let mut xof = h.finalize_xof();
    let (_, nb, _, _) = crate::circuit::analyze_ops(ops.iter());
    let mut sim = crate::sim::Simulator::new(nq as usize, nb as usize, &mut xof);
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
        if gx != e.0 || gy != e.1 { bad += 1; eprintln!("shot {k} wrong"); }
    }
    eprintln!("phase {:#x}, bad {bad}", sim.phase);
    assert_eq!(sim.phase, 0, "phase garbage");
    let regq: std::collections::HashSet<u64> = xq.iter().chain(yq.iter()).map(|q| q.0).collect();
    for q in 0..nq {
        if !regq.contains(&q) { assert_eq!(sim.qubits[q as usize], 0, "ancilla garbage q{q}"); }
    }
    assert_eq!(bad, 0, "classical mismatches");
    eprintln!("frogdrop end-to-end OK: avg Toffoli {}", sim.stats.toffoli_gates / 64);
}

#[test]
fn modp_ctrl_modadd_and_product() {
    use super::modp_frogdrop::{ctrl_modadd, product, Ms};
    let pp = super::frogdrop_sched::p();
    let m256 = (N::from(1u64) << 256) - N::from(1u64);
    // z += ctl y mod p on lazy (non-canonical, < 2^256) operands, with carry-heavy edge cases
    {
        let mut b = B::new();
        let z = b.alloc_n(256);
        let y = b.alloc_n(256);
        let ctl = b.alloc();
        let d = b.alloc();
        let ms = Ms::alloc(&mut b);
        ctrl_modadd(&mut b, &ms, &z, &y, ctl, d);
        let mut rng = Rng::new(31);
        let (mut zv, mut yv) = (vec![], vec![]);
        for s in 0..64 {
            let (mut a, mut c) = (rng.below(256), rng.below(256));
            // carry-heavy cases (not adversarial to the 32-lane erase compare, which errs w.p. 2^-32)
            if s % 8 == 0 { a |= (N::from(1u64) << 120) - N::from(1u64); }
            if s % 8 == 1 { c = m256 - N::from(3u64); }
            if s % 8 == 2 { c = a; }
            zv.push(a);
            yv.push(c);
        }
        let (zv2, yv2, z2, y2) = (zv.clone(), yv.clone(), z.clone(), y.clone());
        let width = b.width() as usize;
        let r = run(&b.ops, width, &move |w| {
            for s in 0..64 {
                put(w, &z2, s, &zv2[s]);
                put(w, &y2, s, &yv2[s]);
                if s % 3 != 2 { w[ctl.0 as usize] |= 1 << s; }
                if s % 2 == 0 { w[d.0 as usize] |= 1 << s; }
            }
        });
        for s in 0..64 {
            let c = s % 3 != 2;
            let want = (zv[s] + if c { yv[s] } else { N::ZERO }) % pp;
            assert_eq!(get(&r.q, &z, s) % pp, want, "ctrl_modadd shot {s}");
            assert_eq!(get(&r.q, &y, s), yv[s], "y restored");
            assert_eq!(getb(&r.q, ctl, s), c as u64);
            assert_eq!(getb(&r.q, d, s), (s % 2 == 0) as u64, "dirty restored");
            assert_eq!(getb(&r.q, ms.k, s), 0, "flag clean");
        }
        assert_eq!(r.phase, 0);
        eprintln!("ctrl_modadd: ok ({} T)", b.tof);
    }
    // z = a y mod p
    {
        let mut b = B::new();
        let z = b.alloc_n(256);
        let a = b.alloc_n(255);
        let y = b.alloc_n(256);
        let ms = Ms::alloc(&mut b);
        let mut zz = z.clone();
        product(&mut b, &ms, &mut zz, &a, &y);
        let mut rng = Rng::new(77);
        let (mut av, mut yv) = (vec![], vec![]);
        for _ in 0..64 {
            av.push(rng.below(255));
            yv.push(rng.below(256) % pp);
        }
        let (av2, yv2, a2, y2) = (av.clone(), yv.clone(), a.clone(), y.clone());
        let width = b.width() as usize;
        let r = run(&b.ops, width, &move |w| {
            for s in 0..64 {
                put(w, &a2, s, &av2[s]);
                put(w, &y2, s, &yv2[s]);
            }
        });
        for s in 0..64 {
            assert_eq!(get(&r.q, &zz, s) % pp, av[s].mul_mod(yv[s], pp), "product shot {s}");
            assert_eq!(get(&r.q, &a, s), av[s]);
            assert_eq!(get(&r.q, &y, s), yv[s]);
            assert_eq!(getb(&r.q, ms.k, s), 0);
        }
        assert_eq!(r.phase, 0);
        eprintln!("product: ok ({} T)", b.tof);
    }
}

/// Flag-free modular add: exhaustive on small moduli 2^n - c (all z < p, all y >= c, ctl, both borrowed qubits).
#[test]
fn modp_nf_exhaustive_small() {
    use super::modp_frogdrop::ctrl_modadd_nf;
    for &(n, c) in &[(5usize, 1u64), (6, 3), (6, 4), (7, 5), (7, 2)] {
        let p = (1u64 << n) - c;
        let mut b = B::new();
        let z = b.alloc_n(n);
        let y = b.alloc_n(n);
        let ctl = b.alloc();
        let d = b.alloc();
        let g = b.alloc();
        ctrl_modadd_nf(&mut b, &z, &y, ctl, d, g, c);
        let width = b.width() as usize;
        let mut cases: Vec<(u64, u64, u64, u64, u64)> = vec![];
        for zv in 0..p {
            for yv in c..(1u64 << n) {
                for bits in 0..8u64 {
                    cases.push((zv, yv, bits & 1, (bits >> 1) & 1, (bits >> 2) & 1));
                }
            }
        }
        let mut checked = 0usize;
        for chunk in cases.chunks(64) {
            let ch = chunk.to_vec();
            let (z2, y2) = (z.clone(), y.clone());
            let r = run(&b.ops, width, &move |w| {
                for (s, &(zv, yv, cv, dv, gv)) in ch.iter().enumerate() {
                    put(w, &z2, s, &N::from(zv));
                    put(w, &y2, s, &N::from(yv));
                    if cv == 1 { w[ctl.0 as usize] |= 1 << s; }
                    if dv == 1 { w[d.0 as usize] |= 1 << s; }
                    if gv == 1 { w[g.0 as usize] |= 1 << s; }
                }
            });
            assert_eq!(r.phase & if chunk.len() == 64 { u64::MAX } else { (1u64 << chunk.len()) - 1 }, 0,
                       "phase n {n} c {c}");
            for (s, &(zv, yv, cv, dv, gv)) in chunk.iter().enumerate() {
                let sum = zv + cv * yv;
                let want = if sum >> n != 0 { sum - (1u64 << n) + c } else { sum };
                let got = get(&r.q, &z, s);
                assert_eq!(got, N::from(want), "n {n} c {c}: z {zv} y {yv} ctl {cv} d {dv} g {gv}");
                assert_eq!(get(&r.q, &y, s), N::from(yv), "y restored");
                assert_eq!(getb(&r.q, ctl, s), cv);
                assert_eq!(getb(&r.q, d, s), dv);
                assert_eq!(getb(&r.q, g, s), gv);
                checked += 1;
            }
        }
        eprintln!("nf modadd n {n} c {c}: {checked} cases ok ({} T)", b.tof);
    }
}

/// Flag-free modular add and product at 256 bits against the reference, borrowed qubits restored, no garbage.
#[test]
fn modp_nf_256() {
    use super::modp_frogdrop::{ctrl_modadd_nf, product_nf, C};
    let pp = super::frogdrop_sched::p();
    let m256 = (N::from(1u64) << 256) - N::from(1u64);
    {
        let mut b = B::new();
        let z = b.alloc_n(256);
        let y = b.alloc_n(256);
        let ctl = b.alloc();
        let d = b.alloc();
        let g = b.alloc();
        ctrl_modadd_nf(&mut b, &z, &y, ctl, d, g, C);
        let mut rng = Rng::new(4242);
        let (mut zv, mut yv) = (vec![], vec![]);
        for s in 0..64 {
            let (mut a, mut c) = (rng.below(256) % pp, rng.below(256) % pp);
            if s % 8 == 0 { a = N::ZERO; }
            if s % 8 == 1 { a = pp - N::from(1u64); }
            if s % 8 == 2 { c = pp - N::from(1u64); }
            if s % 8 == 3 { c = N::from(C); }
            if s % 8 == 4 { a = pp - c; }
            if s % 8 == 5 { if c > N::from(1u64) && c - N::from(1u64) < pp { a = pp - c + N::from(1u64); } }
            if s % 8 == 6 { a = (N::from(1u64) << 255) | ((N::from(1u64) << 200) - N::from(1u64)); a %= pp; }
            zv.push(a);
            yv.push(c);
        }
        let (zv2, yv2, z2, y2) = (zv.clone(), yv.clone(), z.clone(), y.clone());
        let width = b.width() as usize;
        let r = run(&b.ops, width, &move |w| {
            for s in 0..64 {
                put(w, &z2, s, &zv2[s]);
                put(w, &y2, s, &yv2[s]);
                if s % 3 != 2 { w[ctl.0 as usize] |= 1 << s; }
                if s % 2 == 0 { w[d.0 as usize] |= 1 << s; }
                if s % 5 < 2 { w[g.0 as usize] |= 1 << s; }
            }
        });
        for s in 0..64 {
            let c = s % 3 != 2;
            let sum = zv[s] + if c { yv[s] } else { N::ZERO };
            let want = if sum > m256 { (sum - m256 - N::from(1u64)) + N::from(C) } else { sum };
            assert_eq!(get(&r.q, &z, s), want, "nf modadd shot {s}");
            assert_eq!(get(&r.q, &y, s), yv[s], "y restored");
            assert_eq!(getb(&r.q, ctl, s), c as u64);
            assert_eq!(getb(&r.q, d, s), (s % 2 == 0) as u64);
            assert_eq!(getb(&r.q, g, s), (s % 5 < 2) as u64);
        }
        assert_eq!(r.phase, 0);
        eprintln!("ctrl_modadd_nf 256: ok ({} T)", b.tof);
    }
    {
        let mut b = B::new();
        let z = b.alloc_n(256);
        let a = b.alloc_n(255);
        let y = b.alloc_n(256);
        let mut zz = z.clone();
        product_nf(&mut b, &mut zz, &a, &y);
        let mut rng = Rng::new(99);
        let (mut av, mut yv) = (vec![], vec![]);
        for s in 0..64 {
            let mut x = rng.below(255);
            if s == 0 { x = N::ZERO; }
            if s == 1 { x = N::from(1u64); }
            if s == 2 { x = (N::from(1u64) << 255) - N::from(1u64); }
            av.push(x);
            yv.push(rng.below(256) % pp);
        }
        let (av2, yv2, a2, y2) = (av.clone(), yv.clone(), a.clone(), y.clone());
        let width = b.width() as usize;
        let r = run(&b.ops, width, &move |w| {
            for s in 0..64 {
                put(w, &a2, s, &av2[s]);
                put(w, &y2, s, &yv2[s]);
            }
        });
        for s in 0..64 {
            assert_eq!(get(&r.q, &zz, s) % pp, av[s].mul_mod(yv[s], pp), "product_nf shot {s}");
            assert_eq!(get(&r.q, &a, s), av[s]);
            assert_eq!(get(&r.q, &y, s), yv[s]);
        }
        assert_eq!(r.phase, 0);
        eprintln!("product_nf: ok ({} T, peak {} = 767 + 0 scratch)", b.tof, b.peak);
        assert_eq!(b.peak, 767);
    }
}
