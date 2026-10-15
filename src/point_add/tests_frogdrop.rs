//! frogdrop tests: the 3-of-4 machine primitives, columns, traversal, product fold and end-to-end point addition.

use super::builder::B;
use super::frogdrop::*;
use super::frogdrop_sched::N;
#[cfg(all(target_os = "linux", nonce_openssl))]
#[path = "tests_nonce_openssl.rs"]
mod nonce_openssl;
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
                      epre: b.alloc_n(4), dirty: b.alloc_n(64), andc: b.alloc_n(4) };
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
                          epre: b.alloc_n(4), dirty: b.alloc_n(64), andc: b.alloc_n(4) };
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
fn d1_map_281_switch_delayed_handoff() {
    use super::frogdrop_sched::{shot, Kind, L0};
    let n = 281usize;
    let nq = 128usize;
    let mut rng = Rng::new(0xd1_698_281);
    let mut cases: Vec<(Kind, N, N, N, N)> = vec![];
    let mut counts = [0usize; 4];
    for _ in 0..10000 {
        if counts.iter().all(|&v| v >= 16) { break; }
        let x = rng.below(255).max(N::from(1u64));
        let (r, t) = euclid_seq(x);
        let sh = shot(x, L0);
        let mut j = 1usize;
        for rec in sh.recs {
            let (bucket, vals) = match rec.kind {
                Kind::Sw => (0, Some((t[j - 1], r[j], t[j], r[j - 1]))),
                Kind::Dl => (1, Some((t[j + 1], r[j], t[j], r[j + 1]))),
                Kind::Dq => (2, Some((t[j], r[j + 1], r[j], t[j + 1]))),
                Kind::Hr => (3, Some((r[j], t[j + 1], t[j], r[j + 1]))),
                _ => (4, None),
            };
            if let Some((z, xv, y, yn)) = vals {
                let m = blen(&xv).max(blen(&y));
                if bucket < 4 && counts[bucket] < 16 && m <= nq && v2n(&xv) <= 24 && v2n(&y) <= 24
                    && blen(&z) <= n - m && blen(&yn) <= n - m {
                    cases.push((rec.kind, z, xv, y, yn));
                    counts[bucket] += 1;
                }
            }
            match rec.kind {
                Kind::Hr | Kind::Ht | Kind::Dq => j += 1,
                _ => {}
            }
        }
    }
    assert_eq!(counts, [16; 4], "coverage: switch, delayed, handoff, ordinary");
    let cuts: Vec<usize> = cases.iter().map(|(_, _, x, y, _)| n - blen(x).max(blen(y))).collect();
    let par = MapPar { clo: *cuts.iter().min().unwrap(), chi: *cuts.iter().max().unwrap(),
                       m: n - *cuts.iter().min().unwrap(), tail: 40, emax: 24 };
    let mut b = B::new();
    let ring = b.alloc_n(n); let q = b.alloc_n(nq); let cutv = b.alloc_n(8);
    let sc = MapScr { c0: b.alloc(), h: b.alloc(), e: b.alloc(), g: b.alloc(), f: b.alloc(), tmp: b.alloc(),
                      one: b.alloc(), anc: b.alloc_n(52), pre: b.alloc_n(8), ez: b.alloc_n(5),
                      epre: b.alloc_n(4), dirty: b.alloc_n(64), andc: b.alloc_n(4) };
    b.begin(); mapf(&mut b, &ring, &q, &Cut { v: cutv.clone(), a: n as isize, neg: true }, &par, &sc);
    let record = b.end();
    b.play(&record, false);
    let forward = b.ops.len();
    b.play(&record, true);
    let initial = |w: &mut Vec<u64>| {
        let mut noise = Rng::new(0xd1_698_999);
        for &lane in &sc.dirty { w[lane.0 as usize] = noise.next(); }
        for (k, (_, z, x, y, _)) in cases.iter().enumerate() {
            put(w, &ring[..cuts[k]], k, z);
            rev_into(w, &ring[cuts[k]..], k, y);
            put(w, &q, k, x);
            put(w, &cutv, k, &N::from((n - cuts[k]) as u64));
        }
    };
    let f = run(&b.ops[..forward], b.width() as usize, &initial);
    assert_eq!(f.phase, 0);
    for (k, (_, _, x, y, yn)) in cases.iter().enumerate() {
        assert_eq!(get(&f.q, &ring[..cuts[k]], k), *yn, "map output shot {k}");
        assert_eq!(rev_get(&f.q, &ring[cuts[k]..], k, n - cuts[k]), *x, "map top shot {k}");
        assert_eq!(get(&f.q, &q, k), *y, "map Q shot {k}");
    }
    let both = run(&b.ops, b.width() as usize, &initial);
    let mut input = vec![0u64; b.width() as usize]; initial(&mut input);
    assert_eq!(both.phase, 0);
    assert_eq!(both.q, input, "full forward/inverse state including dirty passengers");
    eprintln!("D1_MAP281_PASS cases={counts:?} width={} forward_t={} ops={forward}", b.width(), f.tof);
}

#[test]
fn d2_ordinary_map_extension_exact() {
    use super::frogdrop_col::{map_stage, ColScr, Fd};
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    let cp = &cols[0];
    assert!(!cp.sw && cp.emax == 22 && cp.n == 277);
    let mut b = B::new();
    let ring = b.alloc_n(cp.n);
    let payload = b.alloc_n(259);
    let q = b.alloc_n(128);
    let sy = b.alloc_n(8);
    let sx = b.alloc_n(8);
    let ph = b.alloc();
    let pool = b.alloc_n(13);
    assert_eq!(b.width(), 694);
    let fd = Fd { ring: ring.clone(), q: q.clone(), sy: sy.clone(), sx: sx.clone(), ph,
                  cnt: q[121..].to_vec() };
    let sc = ColScr::carve_col(&pool, &fd.sx, &payload, cp.kp, cp.qb, cp.tail, cp.sz.1 > 255);
    let record = map_stage(&mut b, &fd, cp, &sc);
    b.play(&record, false);
    let forward = b.ops.len();
    b.play(&record, true);
    let p = pval();
    let mut input = vec![0u64; b.width() as usize];
    let mut rng = Rng::new(0xd2_697_280);
    for &lane in &payload { input[lane.0 as usize] = rng.next(); }
    let mut cases = Vec::new();
    for lane in 0..64 {
        let (x, y, z) = match lane % 4 {
            0 => (N::from(1u64), N::from(1u64), N::from(1 + lane as u64)),
            1 => (N::from(2u64), N::from(1u64), N::from(1 + lane as u64)),
            2 => (N::from(1u64), N::from(2u64), N::from(1 + 2 * lane as u64)),
            _ => (N::from(3u64), N::from(2u64), N::from(1 + 2 * lane as u64)),
        };
        let cut = cp.n - blen(&x).max(blen(&y));
        put(&mut input, &ring[..cut], lane, &z);
        rev_into(&mut input, &ring[cut..], lane, &y);
        put(&mut input, &q, lane, &x);
        put(&mut input, &sy, lane, &N::from(blen(&y) as u64));
        cases.push((cut, x, y, (p - z * x) / y));
    }
    let f = run(&b.ops[..forward], b.width() as usize, &|q| *q = input.clone());
    assert_eq!(f.phase, 0);
    for (lane, (cut, x, y, want)) in cases.iter().enumerate() {
        assert_eq!(get(&f.q, &ring[..*cut], lane), *want, "map bottom shot {lane}");
        assert_eq!(rev_get(&f.q, &ring[*cut..], lane, cp.n - *cut), *x, "map top shot {lane}");
        assert_eq!(get(&f.q, &q, lane), *y, "map Q shot {lane}");
    }
    let both = run(&b.ops, b.width() as usize, &|q| *q = input.clone());
    assert_eq!(both.phase, 0);
    assert_eq!(both.q, input, "forward/inverse, scratch, and dirty passengers");
    eprintln!("D2_MAP_EXTENSION_PASS shots=64 width={} forward_ops={forward}", b.width());
}

#[test]
fn d3_b0_two_lane_extension_controlled_replay() {
    use super::frogdrop_col::{map_stage, ColScr, Fd};
    let (_, b0, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    let cp = b0.expect("B0 column");
    assert_eq!((cp.n, cp.emax, cp.m, cp.sz), (277, 22, 28, (0, 0)));
    let mut b = B::new();
    let ring = b.alloc_n(cp.n);
    let payload = b.alloc_n(259);
    let q = b.alloc_n(128);
    let sy = b.alloc_n(8);
    let sx = b.alloc_n(8);
    let ph = b.alloc();
    let pool = b.alloc_n(13);
    assert_eq!(b.width(), 694);
    let fd = Fd { ring: ring.clone(), q: q.clone(), sy: sy.clone(), sx, ph,
                  cnt: q[121..].to_vec() };
    let sc = ColScr::carve_col(&pool, &fd.sx, &payload, cp.kp, cp.qb, cp.tail, false);
    b.allow_booth = false;
    let record = map_stage(&mut b, &fd, &cp, &sc);
    b.play_ctrl(&record, sc.sw, sc.g);
    let forward = b.ops.len();
    let inverse = super::frogdrop_col::rec(&mut b, |b| b.play(&record, true));
    b.play_ctrl(&inverse, sc.sw, sc.g);
    let mut input = vec![0u64; b.width() as usize];
    let mut rng = Rng::new(0xd3_b0_278);
    let active = 0x55aa_33cc_f00f_0ff0u64;
    input[sc.sw.0 as usize] = active;
    input[ph.0 as usize] = u64::MAX;
    for &lane in &payload { input[lane.0 as usize] = rng.next(); }
    let p = pval();
    let mut cases = Vec::new();
    for lane in 0..64 {
        let x = N::from(1 + lane as u64 % 23);
        let y = N::from(1u64);
        let z = N::from(1 + (3 * lane) as u64);
        let cut = cp.n - blen(&x).max(blen(&y));
        put(&mut input, &ring[..cut], lane, &z);
        rev_into(&mut input, &ring[cut..], lane, &y);
        put(&mut input, &q, lane, &x);
        put(&mut input, &sy, lane, &N::from(blen(&y) as u64));
        cases.push((cut, x, y, (p - z * x) / y));
    }
    let out = run(&b.ops[..forward], b.width() as usize, &|w| *w = input.clone());
    assert_eq!(out.phase, 0);
    for (lane, (cut, x, y, want)) in cases.iter().enumerate() {
        if (active >> lane) & 1 == 1 {
            assert_eq!(get(&out.q, &ring[..*cut], lane), *want, "active B0 bottom {lane}");
            assert_eq!(rev_get(&out.q, &ring[*cut..], lane, cp.n - *cut), *x, "active B0 top {lane}");
            assert_eq!(get(&out.q, &q, lane), *y, "active B0 Q {lane}");
        } else {
            for i in 0..b.width() as usize {
                assert_eq!((out.q[i] >> lane) & 1, (input[i] >> lane) & 1,
                           "inactive B0 passenger shot {lane} q{i}");
            }
        }
    }
    let both = run(&b.ops, b.width() as usize, &|w| *w = input.clone());
    assert_eq!(both.phase, 0);
    assert_eq!(both.q, input, "controlled B0 forward/inverse cleanup");
    eprintln!("D3_B0_MAP_PASS shots=64 width={} forward_ops={forward}", b.width());
}

#[test]
fn d4_n278_map_extension_forward_inverse_phase() {
    d2_ordinary_map_extension_exact();
    d3_b0_two_lane_extension_controlled_replay();
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
    let ring = b.alloc_n(n);
    let q = b.alloc_n(nq);
    let cnt = q[nq - 7..].to_vec();
    let fd = Fd { ring, q, sy: b.alloc_n(sw), sx: b.alloc_n(sw), ph: b.alloc(), cnt };
    let dirty = b.alloc_n(64);
    let ps = PScr { r: vec![], rho: b.alloc_n(kp + 1), q0: b.alloc_n(qb), f: b.alloc(), g: b.alloc(), c0: b.alloc(),
                    zero: b.alloc(), one: b.alloc(), spre: b.alloc_n(6), tmp: b.alloc(), dirty: vec![] };
    let ms = MapScr { c0: b.alloc(), h: b.alloc(), e: b.alloc(), g: b.alloc(), f: b.alloc(), tmp: b.alloc(),
                      one: b.alloc(), anc: b.alloc_n(tail + 12), pre: b.alloc_n(8), ez: b.alloc_n(5),
                      epre: b.alloc_n(4), dirty: b.alloc_n(64), andc: b.alloc_n(4) };
    let mut sc = ColScr { sz: b.alloc_n(9), cmpc: b.alloc(),
                      bq: b.alloc(), sw: b.alloc(), g: b.alloc(), act: b.alloc(), c0: b.alloc(), tmp: b.alloc(), tmp2: b.alloc(),
                      f: b.alloc(), one: b.alloc(), pre: b.alloc_n(8), opre: b.alloc_n(8), anc: b.alloc_n(tail + 12),
                      zeros: b.alloc_n(40), u: b.alloc_n(8), u2: b.alloc_n(8), js: b.alloc(), qsets: qsubsets(qb), tq: b.alloc(), ps, ms,
                      dirty: dirty.clone(), rho_clean: vec![], slim: vec![], gx: vec![] };
    sc.slim = vec![sc.bq, sc.cmpc, sc.f, sc.g, sc.c0, b.alloc(), b.alloc(), sc.js, b.alloc()];
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
                              nomap: false, tt: false, pht: false, psy: (0, 0), xw: 0, psw: false, cntw: 7, cntmax: 127, col: usize::MAX,
                              dl: false, dq: false, dlr: 0 };
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
                        nomap: false, tt: false, pht: false, psy: (0, 0), xw: 0, psw: false, cntw: 7, cntmax: 127, col: usize::MAX,
                        dl: false, dq: false, dlr: 0 };
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
    let qq = b.alloc_n(NQ); let cnt = if std::env::var("CNT_SEP").is_ok() { b.alloc_n(CNTB) } else { qq[NQ - CNTB..].to_vec() };
    let mut fd = Fd { ring, q: qq, sy: b.alloc_n(SW), sx: b.alloc_n(SW), ph: b.alloc(), cnt };
    let pool = b.alloc_n(pool_size(KP, QB, SW));
    b.x(fd.ring[N - 1]);
    b.x(fd.sy[0]);
    for cp in &cols[..ncol] {
        let sc = ColScr::carve_col(&pool, &fd.sx, &dirty, KP, QB, TAIL, cp.sz.1 > 255);
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
                match sh.recs[c].kind { Kind::Hr => j += 1, Kind::Ht => j += 1, Kind::Sw => ph = 1, Kind::Idle => {},
                                        Kind::Dl => ph = 1, Kind::Dq => j += 1 }
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
        let fl = [badl == 0, get(&r.q, &fd.q[..if std::env::var("CNT_SEP").is_ok() { NQ } else { NQ - CNTB }], s) == qv, get(&r.q, &fd.sy, s) == N::from(blen(&top) as u64),
            (r.q[fd.ph.0 as usize] >> s) & 1 == ph as u64, true,
            get(&r.q, &fd.cnt, s) == N::from(cnt as u64), get(&r.q, &fd.sx, s) == N::ZERO,
            pool.iter().all(|q| (r.q[q.0 as usize] >> s) & 1 == 0)];
        if fl.iter().any(|x| !x) {
            let dirty_pool: Vec<usize> = (0..pool.len()).filter(|&i| (r.q[pool[i].0 as usize] >> s) & 1 == 1).collect();
            if bad.len() < 3 { eprintln!("shot {s}: ring/Q/sy/ph/done/cnt/sx/pool {:?} dirty pool idx {:?} cnt {} want {} dn {}", fl, dirty_pool,
                get(&r.q, &fd.cnt, s), cnt, 0); }
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
    for c in 0..c0 { match s.recs[c].kind { Kind::Hr | Kind::Ht => j += 1, Kind::Sw => ph = 1, Kind::Dl => ph = 1,
                                            Kind::Dq => j += 1, _ => {} } }
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


/// Controlled add with logical-AND carries on the top lanes: every split of the lanes, against the plain ripple.
#[test]
fn frogdrop_cadd_and() {
    for &(n, nt) in &[(1usize, 0usize), (3, 2), (6, 3), (9, 4), (12, 0)] {
        for k in 0..=n + 1 {
            let mut b = B::new();
            let t = b.alloc_n(n);
            let s = b.alloc_n(n);
            let tl = b.alloc_n(nt);
            let g = b.alloc();
            let c0 = b.alloc();
            let h = b.alloc();
            let anc = b.alloc_n(nt.max(1));
            let andc = b.alloc_n(k);
            cadd_tail_and(&mut b, g, &t, &s, &tl, c0, h, &anc, &andc);
            let mut rng = Rng::new((n * 31 + k) as u64);
            let mut cases = vec![];
            for _ in 0..64 {
                cases.push((rng.below(n), rng.below(n), rng.below(nt.max(1)), rng.next() & 1));
            }
            let (t2, s2, tl2, cs) = (t.clone(), s.clone(), tl.clone(), cases.clone());
            let r = run(&b.ops, b.width() as usize, &move |w| {
                for (sh, (tv, sv, lv, gv)) in cs.iter().enumerate() {
                    put(w, &t2, sh, tv);
                    put(w, &s2, sh, sv);
                    if nt > 0 { put(w, &tl2, sh, lv); }
                    if *gv == 1 { w[g.0 as usize] |= 1 << sh; }
                }
            });
            assert_eq!(r.phase, 0, "phase n {n} k {k}");
            for (sh, (tv, sv, lv, gv)) in cases.iter().enumerate() {
                let full = tv.clone() + (lv.clone() << n) + if *gv == 1 { sv.clone() } else { N::ZERO };
                let m = mask(n + nt);
                let want = full & m;
                let got = get(&r.q, &t, sh) + (if nt > 0 { get(&r.q, &tl, sh) << n } else { N::ZERO });
                assert_eq!(got, want, "n {n} nt {nt} k {k} shot {sh}");
                assert_eq!(get(&r.q, &s, sh), *sv);
                for &q in andc.iter().chain([c0, h].iter()).chain(anc.iter()) { assert_eq!(getb(&r.q, q, sh), 0); }
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ payload tests

/// classical payload model: per level j (1..=last) the pre-digit (d, W) and the post-transition W_{j+1};
/// W two's complement mod 2^384.
struct PlModel {
    d_pre: Vec<N>,
    w_pre: Vec<N>,
    w_next: Vec<N>,
    last: usize,
}

fn pl_model(r: &[N], t: &[N], dy: N) -> PlModel {
    let nn = r.len() - 1;
    let last = nn - 1;
    let mut d = dy;
    let mut w = N::ZERO;
    let mut m = PlModel { d_pre: vec![N::ZERO; last + 2], w_pre: vec![N::ZERO; last + 2], w_next: vec![N::ZERO; last + 2], last };
    for j in 1..=last {
        m.d_pre[j] = d;
        m.w_pre[j] = w;
        let e = d / r[j];
        d -= e * r[j];
        let wpost = w.wrapping_add(e.wrapping_mul(t[j]));
        let q = r[j - 1] / r[j];
        let wn = q.wrapping_mul(t[j]).wrapping_add(!wpost);
        m.w_next[j] = wn;
        w = wn;
    }
    assert!(d.is_zero());
    m.d_pre[last + 1] = N::ZERO;
    m.w_pre[last + 1] = w;
    m
}

/// payload lanes of the pre form at level j (region [258 - bl(t_j), 259)) or the offset form after level j's
/// transition (offset bit at lane bl(r_j)).
fn pl_lanes_pre(d: &N, w: &N, btj: usize) -> Vec<u8> {
    let np = super::payload::NP;
    let b = np - 1 - btj;
    (0..np).map(|l| if l < b { d.bit(l) as u8 } else { w.bit(np - 1 - l) as u8 }).collect()
}
fn pl_lanes_off(d: &N, wn: &N, brj: usize) -> Vec<u8> {
    let np = super::payload::NP;
    let u = wn.wrapping_add(N::from(1u64) << (np - 1 - brj));
    (0..np).map(|l| if l < brj { d.bit(l) as u8 } else { u.bit(np - 1 - l) as u8 }).collect()
}

/// Full traversal with the payload on 64 shots (rig scratch): checks every Euclid register and the payload after
/// FROGDROP_COLS columns (default: through the end).
#[test]
fn frogdrop_traversal_pl() {
    use super::frogdrop_col::*;
    use super::payload::*;
    let l0 = super::frogdrop_sched::L0;
    let nq: usize = std::env::var("FROGDROP_NQ").ok().and_then(|s| s.parse().ok()).unwrap_or(150);
    let seed: u64 = std::env::var("FROGDROP_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(31337);
    let n: usize = 289;
    let (k, kp, qb, tot, tail) = (30usize, 32usize, 24usize, 86usize, 40usize);
    let shots = rand_shots(seed, |_, _| Some((0, 1)));
    let lens: Vec<usize> = shots.iter().map(|((r, _), _, _)| r.len() - 1).collect();
    let cols = lens.iter().map(|nn| nn - 1).max().unwrap();
    let upto: usize = std::env::var("FROGDROP_COLS").ok().and_then(|s| s.parse().ok()).unwrap_or(usize::MAX);
    let mut rng = Rng::new(seed ^ 0x5555);
    let p = pval();
    let dys: Vec<N> = (0..64).map(|_| rng.below(256) % p).collect();
    let models: Vec<PlModel> = shots.iter().enumerate().map(|(s, ((r, t), _, _))| pl_model(r, t, dys[s])).collect();
    let mut st: Vec<(u8, usize, bool, usize, bool)> = vec![(0, 1, false, 0, false); 64];
    // payload form per shot: (offset?, level j)
    let mut pf: Vec<(bool, usize)> = vec![(false, 1); 64];
    let mut rig = col_rig(n, nq, kp, qb, tail);
    let pl = PlCol { p: rig.b.alloc_n(NP), free: rig.b.alloc_n(54), mid_hr: rig.b.alloc_n(5), mid_ht: rig.b.alloc_n(4),
                     dirty: rig.fd.ring[260..].to_vec(),
                     obs: if std::env::var("PL_DBG_OBS").is_ok() { rig.b.alloc_n(400) } else { vec![] } };
    let base = ColPar { n, nq, h: n - 257, k, kp, qb, tot, sz: (999, 0), sy: (999, 0), smax: (999, 0), m: 0, tail,
                        emax: 28, hr: false, ht: false, sw: false, l0, swl: (0, 0), dn: false, fin: false,
                        nomap: false, tt: false, pht: false, psy: (0, 0), xw: 0, psw: false, cntw: 7, cntmax: 127, col: usize::MAX,
                        dl: false, dq: false, dlr: 0 };
    let mut total = 0u64;
    let mut prev: Option<ColPar> = None;
    let ncols = cols.min(upto);
    for c in 0..ncols {
        let mut cp = base.clone();
        if let Some(pc) = &prev {
            cp.pht = pc.ht;
            cp.psy = pc.sy;
        }
        let mut kinds = [0usize; 4];
        for (s, ((r, t), _, _)) in shots.iter().enumerate() {
            let nn = lens[s];
            let (ph, j, done, cnt, a0) = st[s];
            if pf[s].0 { pf[s] = (false, pf[s].1 + 1); } // deferred HT narrowing at this column's start
            let rr = r[nn - 2];
            let (bz, by, mx);
            if done {
                cp.dn = true; kinds[3] += 1;
                if a0 { bz = blen(&t[nn - 1]); by = 1; mx = blen(&rr); } else { bz = blen(&t[nn - 2]); by = blen(&rr); mx = blen(&rr); }
                st[s] = (ph, j, true, cnt + 1, !a0);
            } else {
                let kd = fd_kind(r, ph, j, l0);
                match kd {
                    Kd::Hr => { cp.hr = true; kinds[0] += 1; bz = blen(&r[j]); by = blen(&t[j]); mx = blen(&t[j + 1]).max(blen(&t[j]));
                                pf[s] = (false, j + 1); }
                    Kd::Ht => { cp.ht = true; kinds[1] += 1; bz = blen(&t[j]); by = blen(&r[j]); mx = blen(&r[j + 1]).max(blen(&r[j]));
                                pf[s] = (true, j); }
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
        let upto_stage: usize = std::env::var("FROGDROP_UPTO").ok().and_then(|s| s.parse().ok()).unwrap_or(99);
        let plo = if std::env::var("PL_OFF").is_ok() { None } else { Some(&pl) };
        if c + 1 == ncols && upto_stage < 99 {
            column_upto(&mut rig.b, &mut rig.fd, &cp, &rig.sc, upto_stage, plo);
        } else {
            column_pl(&mut rig.b, &mut rig.fd, &cp, &rig.sc, plo);
        }
        total += rig.b.tof - t0;
        if c % 10 == 0 || c + 3 > cols {
            eprintln!("column {c}: {} T, HR/HT/SW/idle {:?}, sz {:?} sy {:?} smax {:?}", rig.b.tof - t0, kinds, cp.sz, cp.sy, cp.smax);
        }
        prev = Some(cp);
    }
    let full = ncols == cols;
    if full {
        let mut cpb = base.clone();
        let mut nb0 = 0;
        for (s, ((r, _), _, _)) in shots.iter().enumerate() {
            let (_, _, done, _, a0) = st[s];
            assert!(done);
            if !a0 {
                nb0 += 1;
                let mx = blen(&r[lens[s] - 2]);
                cpb.smax = (cpb.smax.0.min(mx), cpb.smax.1.max(mx));
                cpb.m = cpb.m.max(mx);
            }
        }
        let mut cpl = base.clone();
        cpl.ht = true;
        cpl.nomap = true;
        let pc = prev.clone().unwrap();
        cpl.pht = pc.ht;
        cpl.psy = pc.sy;
        for (s, ((_, t), _, _)) in shots.iter().enumerate() {
            let bz = blen(&t[lens[s] - 1]);
            cpl.sz = (cpl.sz.0.min(bz), cpl.sz.1.max(bz));
            if pf[s].0 { pf[s] = (false, pf[s].1 + 1); }
        }
        cpl.sy = (1, 1);
        let t0 = rig.b.tof;
        let scc = rig.sc.clone();
        traversal_end_pl(&mut rig.b, &mut rig.fd, if nb0 > 0 { Some(&cpb) } else { None }, &cpl, &|_| scc.clone(), Some(&pl));
        total += rig.b.tof - t0;
        eprintln!("end: {} T; traversal total {total} T over {cols} columns", rig.b.tof - t0);
    } else {
        eprintln!("stopped after {ncols} columns, {total} T");
    }
    let (ring, sy0, fd, sc) = (&rig.fd.ring, &rig.sy0, &rig.fd, &rig.sc);
    let r = run(&rig.b.ops, rig.b.width() as usize, &|w| {
        for (s, ((rr, _), _, _)) in shots.iter().enumerate() {
            put(w, &ring[..257], s, &rr[1]);
            w[ring[n - 1].0 as usize] |= 1 << s;
            put(w, sy0, s, &N::from(1u64));
            put(w, &pl.p[..256], s, &dys[s]);
        }
        w[sc.ps.one.0 as usize] = 0;
    });
    assert_eq!(r.phase, 0, "phase garbage");
    let mut nbad = 0;
    for (s, ((rr, tt), _, _)) in shots.iter().enumerate() {
        let m = &models[s];
        let want: Vec<u8> = if full {
            // after the end column: offset form of W_{last+1} with offset bit at lane bl(r_last) = 1
            pl_lanes_off(&N::ZERO, &m.w_pre[m.last + 1], 1)
        } else {
            let (off, j) = pf[s];
            if off { pl_lanes_off(&m.d_pre[j + 1], &m.w_next[j], blen(&rr[j])) }
            else { pl_lanes_pre(&m.d_pre[j], &m.w_pre[j], blen(&tt[j])) }
        };
        let got: Vec<u8> = pl.p.iter().map(|qq| ((r.q[qq.0 as usize] >> s) & 1) as u8).collect();
        let bad: Vec<usize> = (0..NP).filter(|&l| got[l] != want[l]).collect();
        if !full && std::env::var("FROGDROP_UPTO").is_err() {
            let (ph, j, done, _, _) = st[s];
            if !done {
                let (bot, x, y) = fd_regs(rr, tt, ph, j);
                let mut ebad = vec![];
                for l in 0..n {
                    let wnt = if l < 257 && bot.bit(l) { 1 } else if l >= n - blen(&y) && y.bit(n - 1 - l) { 1 } else { 0 };
                    if (r.q[ring[l].0 as usize] >> s) & 1 != wnt { ebad.push(l); }
                }
                if !ebad.is_empty() || get(&r.q, &rig.fd.q, s) != x {
                    eprintln!("shot {s}: EUCLID wrong: ring lanes {:?} Q ok {}", &ebad[..ebad.len().min(8)], get(&r.q, &rig.fd.q, s) == x);
                }
            }
        }
        let mut scr: Vec<QubitId> = pl.free.clone();
        scr.extend(&pl.mid_hr);
        scr.extend(&pl.mid_ht);
        scr.extend(&fd.sx);
        scr.extend(&sc.ps.rho);
        scr.extend(&sc.ps.q0);
        let dirty_scr: Vec<u32> = scr.iter().filter(|qq| (r.q[qq.0 as usize] >> s) & 1 == 1).map(|qq| qq.0 as u32).collect();
        let only: Option<usize> = std::env::var("FROGDROP_SHOT").ok().and_then(|x| x.parse().ok());
        if (!bad.is_empty() || !dirty_scr.is_empty()) && only.map_or(true, |o| o == s) {
            if nbad < 6 || only.is_some() {
                eprintln!("shot {s} (N {}, form {:?}, st {:?}): payload lanes wrong {:?} (of {}), dirty scratch {:?}",
                          lens[s], pf[s], st[s], &bad[..bad.len().min(12)], bad.len(), &dirty_scr[..dirty_scr.len().min(8)]);
                let j = pf[s].1;
                if j >= 1 && j < m.last {
                    let e = m.d_pre[j] / rr[j];
                    let q = rr[j - 1] / rr[j];
                    eprintln!("   t_j {:x} r_j {:x} d_pre {:x} r_jm1 {:x} r_jp1 {:x}", tt[j], rr[j], m.d_pre[j], rr[j - 1], rr[j + 1]);
                    eprintln!("   level {j}: bl r_j {} bl t_j {} bl t_j+1 {} bl r_j-1 {} q {} e {} Wpre {:x} Wnext {:x}",
                              blen(&rr[j]), blen(&tt[j]), blen(&tt[j + 1]), blen(&rr[j - 1]), q, e, m.w_pre[j], m.w_next[j]);
                    let gs: String = got.iter().rev().map(|x| char::from(b'0' + x)).collect();
                    let ws: String = want.iter().rev().map(|x| char::from(b'0' + x)).collect();
                    eprintln!("   got  (lane 258..0) {gs}\n   want (lane 258..0) {ws}");
                    if !pl.obs.is_empty() {
                        let ob: String = pl.obs.iter().map(|qq| char::from(b'0' + ((r.q[qq.0 as usize] >> s) & 1) as u8)).collect();
                        eprintln!("   obs {ob}");
                        eprintln!("   r_j+1 {:x}", rr[j + 1]);
                    }
                }
            }
            nbad += 1;
        }
    }
    eprintln!("PAYLOAD_TRAVERSAL nbad {nbad}/64, total T {total}, width {}", rig.b.width());
    assert_eq!(nbad, 0, "{nbad}/64 shots wrong");
}

/// trans_one with the coarse mask: t (positions k..) += g * s where the source carries garbage far above.
#[test]
fn payload_trans_one_masked() {
    use super::payload::*;
    let mut rng = Rng::new(99);
    for trial in 0..8 {
        let k = (rng.next() % 26) as usize;
        let mut b = B::new();
        let p = b.alloc_n(NP);
        let src = b.alloc_n(300);
        let sy = b.alloc_n(8);
        let qk = b.alloc();
        let act = b.alloc();
        let g = b.alloc();
        let c0 = b.alloc();
        let tmp = b.alloc();
        let dirty = b.alloc_n(8);
        let t: Vec<QubitId> = (k..NP).map(|pos| wl(&p, pos)).collect();
        let s: Vec<QubitId> = src[..NP - k].to_vec();
        let amax = 7;
        let sub = trial % 2 == 1;
        b.begin();
        trans_one(&mut b, &t, &s, k, sub, vec![(qk, false), (act, false)], Some((&sy[4..], amax)), g, c0, &[tmp], &dirty);
        let rec = b.end();
        b.play(&rec, false);
        // per shot: br = bl(r) in [1,118], bt = bl(t) with br + bt <= 257; U < 2^(259-br); source = |t| < 2^bt, garbage from lane >= bt + 31
        let mut cases = vec![];
        for _ in 0..64 {
            let br = 1 + (rng.next() % 118) as usize;
            let bt = (257 - br).min(256) - (rng.next() % 20) as usize;
            let w = 259 - br;
            let tv = rng.below(bt) | (N::from(1u64) << (bt - 1));
            // keep U + tv*2^k < 2^w and U >= tv*2^k for sub
            let lim = N::from(1u64) << w;
            let add = tv << k;
            if add >= lim >> 1 { cases.push(None); continue; }
            let u = if sub { add + rng.below(w - 1) % (lim - add - add) } else { rng.below(w - 1) % (lim - add) };
            let d = rng.below(br);
            let garb = rng.below(300) & !((N::from(1u64) << (288 - br)) - N::from(1u64));
            cases.push(Some((br, bt, u, d, tv, garb)));
        }
        let r = run(&b.ops, b.width() as usize, &|wv| {
            for (sh, c) in cases.iter().enumerate() {
                if let Some((br, _bt, u, d, tv, garb)) = c {
                    for l in 0..NP { let bit = if l < *br { d.bit(l) } else { u.bit(NP - 1 - l) }; if bit { wv[p[l].0 as usize] |= 1 << sh; } }
                    put(wv, &src, sh, &(*tv | *garb));
                    put(wv, &sy, sh, &N::from(*br as u64));
                    wv[qk.0 as usize] |= 1 << sh;
                    wv[act.0 as usize] |= 1 << sh;
                }
            }
        });
        let mut bad = 0;
        for (sh, c) in cases.iter().enumerate() {
            if let Some((br, _bt, u, d, tv, _garb)) = c {
                let u2 = if sub { *u - (*tv << k) } else { *u + (*tv << k) };
                let ok = (0..NP).all(|l| { let bit = if l < *br { d.bit(l) } else { u2.bit(NP - 1 - l) };
                                              ((r.q[p[l].0 as usize] >> sh) & 1 == 1) == bit });
                if !ok { bad += 1; }
            }
        }
        assert_eq!(r.phase, 0);
        eprintln!("trial {trial} k {k} sub {sub}: bad {bad}");
        assert_eq!(bad, 0);
    }
}

#[test]
fn d2_payload_guard_280_exact() {
    use super::payload::{trans_one_guard, wl, NP};
    let mut b = B::new();
    b.cancel_simple_pairs = false;
    b.cancel_commuting_pairs = false;
    let p = b.alloc_n(NP);
    let src = b.alloc_n(NP - 1);
    let sy = b.alloc_n(8);
    let qk = b.alloc();
    let act = b.alloc();
    let g = b.alloc();
    let c0 = b.alloc();
    let tmp = b.alloc();
    let dirty = b.alloc_n(16);
    let t: Vec<QubitId> = (1..NP).map(|pos| wl(&p, pos)).collect();
    b.begin();
    trans_one_guard(&mut b, &t, &src, 1, false, vec![(qk, false), (act, false)],
                    Some((&sy[4..], 8)), g, c0, &[tmp], &dirty, 264);
    let recipe = b.end();
    b.play(&recipe, false);
    let forward = b.ops.clone();
    b.play(&recipe, true);
    let roundtrip = b.ops.clone();
    let mut input = vec![0u64; b.width() as usize];
    let mut rng = Rng::new(0xd2_280_105);
    for &q in &dirty { input[q.0 as usize] = rng.next(); }
    let mut want = input.clone();
    for lane in 0..64 {
        let (pv, sv, size, on) = if lane == 0 {
            (N::ZERO, N::from(1u64) << 152, 127usize, true)
        } else {
            (rng.below(NP), rng.below(NP - 1), [1, 16, 31, 64, 96, 112, 127, 128][lane % 8],
             lane % 3 != 0)
        };
        put(&mut input, &p, lane, &pv);
        put(&mut input, &src, lane, &sv);
        put(&mut input, &sy, lane, &N::from(size as u64));
        put(&mut want, &p, lane, &pv);
        put(&mut want, &src, lane, &sv);
        put(&mut want, &sy, lane, &N::from(size as u64));
        if on {
            input[qk.0 as usize] |= 1u64 << lane; input[act.0 as usize] |= 1u64 << lane;
            want[qk.0 as usize] |= 1u64 << lane; want[act.0 as usize] |= 1u64 << lane;
        }
        let mut tv = N::ZERO;
        for i in 0..NP - 1 { if pv.bit(NP - 2 - i) { tv |= N::from(1u64) << i; } }
        let sum = tv + sv;
        for i in 0..NP - 1 {
            let pos = i + 1;
            let allowed = on && (size >> 4) < ((264isize - pos as isize).div_euclid(16) + 1).max(0) as usize;
            let bit = if allowed { sum.bit(i) } else { tv.bit(i) };
            let wire = p[NP - 1 - pos].0 as usize;
            if bit { want[wire] |= 1u64 << lane; } else { want[wire] &= !(1u64 << lane); }
        }
    }
    let got = run(&forward, input.len(), &|q| *q = input.clone());
    if got.q != want {
        let bad: Vec<_> = (0..want.len()).filter(|&i| got.q[i] != want[i])
            .take(12).map(|i| (i, got.q[i] ^ want[i])).collect();
        panic!("guarded add first wrong wire/lane-mask {bad:?}");
    }
    assert_eq!(got.phase, 0);
    let back = run(&roundtrip, input.len(), &|q| *q = input.clone());
    assert_eq!(back.q, input, "recorded forward and inverse restore every wire");
    assert_eq!(back.phase, 0);
    eprintln!("D2_PAYLOAD_GUARD_PASS width={} shots=64 forward_ops={}", b.width(), forward.len());
}

/// HT transition as in col_trans_ht: U += q0 |t| (k = 0..24), U -= bq |t|, ring-sourced with garbage.
#[test]
fn payload_trans_ht_unit() {
    use super::payload::*;
    let mut rng = Rng::new(7);
    let mut b = B::new();
    let p = b.alloc_n(NP);
    let ring = b.alloc_n(289);
    let sy = b.alloc_n(8);
    let q0 = b.alloc_n(24);
    let bq = b.alloc();
    let act = b.alloc();
    let g = b.alloc();
    let c0 = b.alloc();
    let tmp = b.alloc();
    let dirty = ring[260..].to_vec();
    let amax = 7;
    b.begin();
    trans_q0(&mut b, &p, &q0, None, &[(act, false)], &ring, NP, Some((&sy[4..], amax)), g, c0, &[tmp], &dirty);
    let t: Vec<QubitId> = (0..NP).map(|pos| wl(&p, pos)).collect();
    trans_one(&mut b, &t, &ring[..NP], 0, true, vec![(bq, false), (act, false)], Some((&sy[4..], amax)), g, c0, &[tmp], &dirty);
    let rec = b.end();
    b.play(&rec, false);
    let mut cases = vec![];
    while cases.len() < 64 {
        let br = 1 + (rng.next() % 118) as usize;
        let bt = (257 - br).min(256) - (rng.next() % 10) as usize;
        let w = 259 - br;
        let tv = rng.below(bt) | (N::from(1u64) << (bt - 1));
        let lim = N::from(1u64) << (w - 1);
        if tv >= lim { continue; }
        let qmax = (lim / tv).to::<u64>().min(1 << 23);
        if qmax < 2 { continue; }
        let q = (rng.next() % (qmax - 1)) + 1;
        let bqv = rng.next() & 1;
        let q0v = q + bqv;
        // U0 so that U0 + q0 t < 2^w, U0 + q0 t - bq t >= 0 ... U0 in [0, 2^w - (q0+1) t)
        let room = (N::from(1u64) << w) - N::from(q0v + 1) * tv;
        let u0 = rng.below(w) % room;
        let d = rng.below(br);
        let rv = rng.below(br.min(140)); // ring top value r_{j+1} < 2^br
        cases.push((br, bt, u0, d, tv, q0v, bqv, rv));
    }
    let r = run(&b.ops, b.width() as usize, &|wv| {
        for (sh, c) in cases.iter().enumerate() {
            let (br, _bt, u, d, tv, q0v, bqv, rv) = c;
            for l in 0..NP { let bit = if l < *br { d.bit(l) } else { u.bit(NP - 1 - l) }; if bit { wv[p[l].0 as usize] |= 1 << sh; } }
            put(wv, &ring[..257], sh, tv);
            for i in 0..rv.bit_len() { if rv.bit(i) { wv[ring[288 - i].0 as usize] |= 1 << sh; } }
            put(wv, &sy, sh, &N::from(*br as u64));
            put(wv, &q0, sh, &N::from(*q0v));
            if *bqv == 1 { wv[bq.0 as usize] |= 1 << sh; }
            wv[act.0 as usize] |= 1 << sh;
        }
    });
    let mut bad = 0;
    for (sh, c) in cases.iter().enumerate() {
        let (br, _bt, u, d, tv, q0v, bqv, _rv) = c;
        let u2 = *u + N::from(*q0v) * *tv - N::from(*bqv) * *tv;
        let ok = (0..NP).all(|l| { let bit = if l < *br { d.bit(l) } else { u2.bit(NP - 1 - l) };
                                      ((r.q[p[l].0 as usize] >> sh) & 1 == 1) == bit });
        if !ok { bad += 1; if bad < 4 { eprintln!("shot {sh}: br {br} q0 {q0v} bq {bqv}"); } }
    }
    assert_eq!(r.phase, 0);
    eprintln!("HT trans unit: bad {bad}/64");
    assert_eq!(bad, 0);
}

/// ht_exact_trans on one HT state replicated over 64 shots (FROGDROP_HT="t r rm1 W(hex, 384-bit two's complement) e").
#[test]
fn payload_ht_exact_unit() {
    use super::frogdrop_col::*;
    use super::payload::*;
    let spec = std::env::var("FROGDROP_HT").unwrap_or_default();
    if spec.is_empty() { return; }
    let v: Vec<N> = spec.split_whitespace().map(|x| N::from_str_radix(x, 16).unwrap()).collect();
    let (tj, rj, rjm1, wpost) = (v[0], v[1], v[2], v[3]);
    let n = 289usize;
    let nq = 150usize;
    let mut b = B::new();
    let qq = b.alloc_n(nq); let cnt = qq[nq - 7..].to_vec();
    let fd = Fd { ring: b.alloc_n(n), q: qq, sy: b.alloc_n(8), sx: b.alloc_n(8), ph: b.alloc(), cnt };
    let p = b.alloc_n(NP);
    let free = b.alloc_n(62);
    let act = b.alloc();
    let szreg = b.alloc_n(9);
    let ds = DigScr { e: free[0..26].to_vec(), sa: szreg.clone(), sb: fd.sy.clone(), sv: free[35], fa: free[36],
                      g: free[37], c0: free[38], tmp: free[39..41].to_vec(), pre1: free[41..49].to_vec(),
                      pre2: free[49..57].to_vec(), zeros: free[57..61].to_vec(), dirty: fd.ring[260..].to_vec() , smin: 0 };
    let szlo: usize = std::env::var("FROGDROP_SZLO").ok().and_then(|x| x.parse().ok()).unwrap_or(117);
    let cp = ColPar { n, nq, h: n - 257, k: 30, kp: 32, qb: 24, tot: 86, sz: (szlo, 200), sy: (72, 138), smax: (1, 1), m: 0,
                      tail: 40, emax: 28, hr: true, ht: true, sw: false, l0: 118, swl: (0, 0), dn: false, fin: false,
                      nomap: false, tt: false, pht: false, psy: (0, 0), xw: 0, psw: false, cntw: 7, cntmax: 127, col: usize::MAX,
                      dl: false, dq: false, dlr: 0 };
    let dirty = fd.ring[260..].to_vec();
    b.begin();
    ht_exact_trans(&mut b, &fd, &cp, &szreg, &p, act, &ds, &dirty);
    let rec = b.end();
    b.play(&rec, false);
    let br = rj.bit_len();
    let w = 259 - br;
    let one = N::from(1u64);
    let u0 = (one << (w - 1)).wrapping_sub(wpost).wrapping_sub(one);
    let q = rjm1 / rj;
    let r = run(&b.ops, b.width() as usize, &|wv| {
        for sh in 0..64 {
            put(wv, &fd.ring[..257], sh, &tj);
            for i in 0..rjm1.bit_len() { if rjm1.bit(i) { wv[fd.ring[n - 1 - i].0 as usize] |= 1 << sh; } }
            put(wv, &fd.q, sh, &rj);
            put(wv, &fd.sy, sh, &N::from(br as u64));
            put(wv, &szreg, sh, &N::from(tj.bit_len() as u64));
            for l in br..NP { if u0.bit(NP - 1 - l) { wv[p[l].0 as usize] |= 1 << sh; } }
            wv[act.0 as usize] |= 1 << sh;
        }
    });
    let u1 = u0 + q * tj;
    let got: N = (0..w).fold(N::ZERO, |acc, i| if (r.q[p[NP - 1 - i].0 as usize] & 1) == 1 { acc | (one << i) } else { acc });
    let dl: Vec<usize> = (0..br).filter(|&l| r.q[p[l].0 as usize] & 1 == 1).collect();
    eprintln!("q {q} want U {:x}\n got U {:x}\n d lanes set {:?} phase {}", u1, got, dl, r.phase);
    let xg: N = (0..200).fold(N::ZERO, |acc, i| if (r.q[fd.ring[n - 1 - i].0 as usize] & 1) == 1 { acc | (one << i) } else { acc });
    eprintln!("X after {:x} (want {:x})", xg, rjm1);
    let scr: Vec<usize> = free.iter().enumerate().filter(|(_, qq)| r.q[qq.0 as usize] & 1 == 1).map(|(i, _)| i).collect();
    eprintln!("dirty scratch idx {:?}", scr);
}

/// Production traversal (schedule + pool) with the payload: 64 sampled shots, checks the Euclid outputs and the final
/// payload (offset form of W_{last+1}, offset bit at lane 1) for every shot the classical predictor accepts.
#[test]
fn frogdrop_traversal_sched_pl() {
    use super::frogdrop_sched::{sample, from_text};
    use super::pointadd_frogdrop::*;
    use super::payload::NP;
    b2_bake_pred_knobs();
    let seed: u64 = std::env::var("FROGDROP_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(5);
    // agent_lowq_quot QUOT_TRAV_XS=x1,x2,..: those inputs (hex) cycled over the 64 shots, every shot checked
    let given: Option<Vec<N>> = std::env::var("QUOT_TRAV_XS").ok()
        .map(|v| v.split(',').map(|x| N::from_str_radix(x.trim(), 16).unwrap()).collect());
    let xs = match &given { Some(g) => (0..64).map(|s| g[s % g.len()]).collect(), None => sample(64, seed) };
    let mut rng = Rng::new(seed ^ 0x77);
    let p = pval();
    let dys: Vec<N> = (0..64).map(|_| rng.below(256) % p).collect();
    let sc = from_text(SCHED_FROGDROP);
    let ncols = sc.cols.len();
    let mut b = B::new();
    let xq = b.alloc_n(256);
    let pl = b.alloc_n(NP);
    let none = std::env::var("PL_NONE").is_ok();
    let t = trav_forward_pl(&mut b, &xq, &pl, if none { None } else { Some(&pl) });
    eprintln!("trav_forward_pl: {} T, {} ops, peak {}", b.tof, b.ops.len(), b.peak);
    let r = run(&b.ops, b.width() as usize, &|w| {
        for s in 0..64 {
            put(w, &xq, s, &xs[s]);
            put(w, &pl[..256], s, &dys[s]);
        }
    });
    eprintln!("phase word {:#x}", r.phase);
    let mut nbad = 0;
    let mut nskip = 0;
    let mut skipped_mask = 0u64;
    for s in 0..64 {
        if given.is_none() && super::frogdrop_sched::predict_n(xs[s], &sc, 24, KP, QB, TOT, NQ, EMAX, N).is_some() { nskip += 1; continue; }
        // (given inputs: the ring's own predictor at K24 precision)
        if given.is_some() && super::frogdrop_sched::predict_n(xs[s], &sc, 24, KP, QB, TOT, NQ, EMAX, N).is_some() {
            nskip += 1;
            skipped_mask |= 1u64 << s;
            continue;
        }
        let (rr, tt) = euclid_seq(xs[s]);
        let nn = rr.len() - 1;
        let ok_t = get(&r.q, &t.fd.ring[0..256], s) == tt[nn - 1];
        let ok_c = get(&r.q, &t.fd.cnt, s) == N::from((ncols - (nn - 1) + 1) as u64)
            && get(&r.q, &t.fd.q[..26], s) == rr[nn - 2];
        let mut zero_ok = true;
        for &q in t.fd.ring[256..].iter().chain(t.fd.q[26..NQ - 7].iter()).chain(t.fd.sy.iter()).chain(t.fd.sx.iter())
            .chain([t.fd.ph].iter()).chain(t.pool.iter()) {
            if (r.q[q.0 as usize] >> s) & 1 != 0 { zero_ok = false; }
        }
        let m = pl_model(&rr, &tt, dys[s]);
        let want = pl_lanes_off(&N::ZERO, &m.w_pre[m.last + 1], 1);
        let got: Vec<u8> = pl.iter().map(|qq| ((r.q[qq.0 as usize] >> s) & 1) as u8).collect();
        let bad: Vec<usize> = if none { vec![] } else { (0..NP).filter(|&l| got[l] != want[l]).collect() };
        if !(ok_t && ok_c && zero_ok && bad.is_empty()) {
            if nbad < 6 { eprintln!("shot {s} (N {nn}): t {ok_t} cnt {ok_c} zeros {zero_ok} payload bad {:?} (of {})", &bad[..bad.len().min(10)], bad.len());
                let nz: Vec<String> = [("ring256", t.fd.ring[256..].to_vec()), ("q26", t.fd.q[26..NQ - 7].to_vec()), ("sy", t.fd.sy.clone()),
                    ("sx", t.fd.sx.clone()), ("ph", vec![t.fd.ph]), ("pool", t.pool.clone())].iter()
                    .filter(|(_, v)| get(&r.q, v, s) != N::ZERO).map(|(nm, v)| format!("{nm}={:x}", get(&r.q, v, s))).collect();
                eprintln!("   cnt {} want {} R {:x} want {:x} nonzero {:?}", get(&r.q, &t.fd.cnt, s), ncols - (nn - 1) + 1,
                    get(&r.q, &t.fd.q[..26], s), rr[nn - 2], nz); }
            nbad += 1;
        }
    }
    eprintln!("SCHED_PL nbad {nbad}/{} (predictor-skipped {nskip})", 64 - nskip);
    eprintln!("checked-shot phase word {:#x}", r.phase & !skipped_mask);
    assert_eq!(r.phase & !skipped_mask, 0, "phase garbage");
    assert_eq!(nbad, 0);
}

/// Stream-decode an ops file written by the builder's exact stream (QECCOPSZ framing) in chunks.
fn stream_ops(path: &std::path::Path, mut each: impl FnMut(&[Op])) -> u64 {
    use std::io::Read;
    use crate::circuit::{OperationType as K, BitId, RegisterId};
    let mut f = std::fs::File::open(path).unwrap();
    let mut hdr = [0u8; 16];
    f.read_exact(&mut hdr).unwrap();
    assert_eq!(&hdr[..8], b"QECCOPSZ");
    let n = u64::from_le_bytes(hdr[8..].try_into().unwrap());
    let mut dec = zstd::stream::read::Decoder::new(f).unwrap();
    let kinds = [K::Neg, K::Register, K::AppendToRegister, K::BitInvert, K::BitStore0, K::BitStore1, K::X, K::Z, K::CX,
                 K::CZ, K::Swap, K::R, K::Hmr, K::CCX, K::CCZ, K::PushCondition, K::PopCondition, K::DebugPrint];
    let chunk = 1usize << 20;
    let mut buf = vec![0u8; 56 * chunk];
    let mut done = 0u64;
    let rd = |b: &[u8], o: usize| u64::from_le_bytes(b[o..o + 8].try_into().unwrap());
    while done < n {
        let m = ((n - done) as usize).min(chunk);
        dec.read_exact(&mut buf[..56 * m]).unwrap();
        let ops: Vec<Op> = (0..m).map(|i| {
            let r = &buf[56 * i..56 * i + 56];
            let k = u32::from_le_bytes(r[0..4].try_into().unwrap()) as usize;
            Op { kind: kinds[k], q_control2: QubitId(rd(r, 8)), q_control1: QubitId(rd(r, 16)), q_target: QubitId(rd(r, 24)),
                 c_target: BitId(rd(r, 32)), c_condition: BitId(rd(r, 40)), r_target: RegisterId(rd(r, 48)) }
        }).collect();
        each(&ops);
        done += m as u64;
    }
    n
}

/// One-pass streamed prefix hash for the v2 hunt. QECCOPSZ's count is in its
/// header; each 56-byte record contributes its low kind byte and six u64s.
/// Keep the final two records outside the prefix for a control/target scan.
fn p3_stream_prefix(path: &std::path::Path) -> (usize, u64, sha3::Shake256, Op) {
    use std::io::Read;
    use crate::circuit::{BitId, OperationType as K, RegisterId};
    let mut file = std::fs::File::open(path).unwrap();
    let mut hdr = [0u8; 16];
    file.read_exact(&mut hdr).unwrap();
    assert_eq!(&hdr[..8], b"QECCOPSZ");
    let count = u64::from_le_bytes(hdr[8..].try_into().unwrap()) as usize;
    let mut decoder = zstd::stream::read::Decoder::new(file).unwrap();
    let kinds = [K::Neg, K::Register, K::AppendToRegister, K::BitInvert, K::BitStore0, K::BitStore1,
                 K::X, K::Z, K::CX, K::CZ, K::Swap, K::R, K::Hmr, K::CCX, K::CCZ,
                 K::PushCondition, K::PopCondition, K::DebugPrint];
    let get = |r: &[u8], o: usize| u64::from_le_bytes(r[o..o + 8].try_into().unwrap());
    let mut pre = sha3::Shake256::default();
    pre.update(b"quantum_ecc-fiat-shamir-v2");
    pre.update(&(count as u64).to_le_bytes());
    let chunk = 1usize << 15;
    let mut raw = vec![0u8; 56 * chunk];
    let mut hashed = vec![0u8; 49 * chunk];
    let mut seen = 0usize;
    let mut width = 0u64;
    let mut tail = None;
    while seen < count {
        let m = (count - seen).min(chunk);
        decoder.read_exact(&mut raw[..56 * m]).unwrap();
        let mut hm = 0usize;
        for i in 0..m {
            let r = &raw[56 * i..56 * (i + 1)];
            let kind = u32::from_le_bytes(r[..4].try_into().unwrap()) as usize;
            assert!(kind < kinds.len());
            let q = [get(r, 8), get(r, 16), get(r, 24)];
            for &v in &q { if v != u64::MAX && v < (1 << 40) { width = width.max(v + 1); } }
            if seen + i < count - 2 {
                hashed[49 * hm] = kind as u8;
                hashed[49 * hm + 1..49 * (hm + 1)].copy_from_slice(&r[8..56]);
                hm += 1;
            } else if seen + i == count - 2 {
                tail = Some(Op { kind: kinds[kind], q_control2: QubitId(q[0]), q_control1: QubitId(q[1]),
                                 q_target: QubitId(q[2]), c_target: BitId(get(r, 32)),
                                 c_condition: BitId(get(r, 40)), r_target: RegisterId(get(r, 48)) });
            }
        }
        pre.update(&hashed[..49 * hm]);
        seen += m;
    }
    (count, width, pre, tail.unwrap())
}

#[test]
#[ignore = "requires D1_PREFIX_A and D1_PREFIX_B full streams"]
fn d1_nonce_prefix_fixed() {
    use sha3::digest::XofReader;
    let a = std::env::var("D1_PREFIX_A").expect("first stream path");
    let b = std::env::var("D1_PREFIX_B").expect("second stream path");
    let (na, wa, pa, ta) = p3_stream_prefix(std::path::Path::new(&a));
    let (nb, wb, pb, tb) = p3_stream_prefix(std::path::Path::new(&b));
    let mut ha = [0u8; 32]; let mut hb = [0u8; 32];
    pa.finalize_xof().read(&mut ha);
    pb.finalize_xof().read(&mut hb);
    assert_eq!((na, wa), (nb, wb), "count and width");
    assert_eq!(ha, hb, "all operation bytes before the last two nonce gates");
    assert_eq!(ta.kind, crate::circuit::OperationType::CX);
    assert_eq!(tb.kind, crate::circuit::OperationType::CX);
    assert_eq!(ta.q_control1, tb.q_control1);
    eprintln!("D1_PREFIX_PASS ops={na} width={wa} ctrl={} targets=({}, {})",
        ta.q_control1.0, ta.q_target.0, tb.q_target.0);
}

/// End-to-end payload-division point addition on 64 random point pairs (streamed build + streamed simulation):
/// classical result, phase and every ancilla.
#[test]
fn payload_point_add_end_to_end() {
    use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
    use crate::circuit::{QubitOrBit, BitId};
    let path = std::env::temp_dir().join(format!("pl_e2e_{}.bin", std::process::id()));
    std::env::set_var("LOWQ_EXACT_STREAM_PATH", &path);
    let mut b = B::new();
    std::env::remove_var("LOWQ_EXACT_STREAM_PATH");
    let (xq, yq) = super::pointadd_frogdrop::point_add_pl(&mut b);
    let nops = b.finish_stream().unwrap();
    let nq = b.width() as usize;
    eprintln!("ops {nops} width {nq} peak {} emitted tof {}", b.peak, b.tof);
    type U = ruint::aliases::U256;
    let to_u = |v: &N| -> U { U::from_limbs(v.as_limbs()[0..4].try_into().unwrap()) };
    let hx = |h: &str| U::from_str_radix(h, 16).unwrap();
    let curve = WeierstrassEllipticCurve {
        modulus: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
        a: U::ZERO, b: U::from(7u64),
        gx: hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
        gy: hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
        order: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
    };
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
    let regs: Vec<Vec<QubitOrBit>> = vec![
        xq.iter().map(|&q| QubitOrBit::Qubit(q)).collect(),
        yq.iter().map(|&q| QubitOrBit::Qubit(q)).collect(),
        (0..256).map(|i| QubitOrBit::Bit(BitId(1 + 2 * 1000 + i as u64))).collect(),
        (0..256).map(|i| QubitOrBit::Bit(BitId(1 + 3 * 1000 + i as u64))).collect(),
    ];
    let mut h = sha3::Shake256::default();
    h.update(b"frogdrop-e2e");
    let mut xof = h.finalize_xof();
    let mut sim = crate::sim::Simulator::new(nq, 20000, &mut xof);
    for (k, (t, o, _)) in cases.iter().enumerate() {
        sim.set_register(&regs[0], t.0, k);
        sim.set_register(&regs[1], t.1, k);
        sim.set_register(&regs[2], o.0, k);
        sim.set_register(&regs[3], o.1, k);
    }
    stream_ops(&path, |ops| sim.apply_iter(ops.iter()));
    let _ = std::fs::remove_file(&path);
    let mut bad = 0;
    for (k, (_, _, e)) in cases.iter().enumerate() {
        let gx = sim.get_register(&regs[0], k);
        let gy = sim.get_register(&regs[1], k);
        if gx != e.0 || gy != e.1 { bad += 1; if bad < 5 { eprintln!("shot {k} wrong (x ok {}, y ok {})", gx == e.0, gy == e.1); } }
    }
    let regq: std::collections::HashSet<u64> = xq.iter().chain(yq.iter()).map(|q| q.0).collect();
    let anc: Vec<usize> = (0..nq).filter(|&q| !regq.contains(&(q as u64)) && sim.qubits[q] != 0).collect();
    eprintln!("PL_E2E phase {:#x}, bad {bad}/64, ancilla garbage {:?}, avg Toffoli {}", sim.phase, &anc[..anc.len().min(10)],
              sim.stats.toffoli_gates / 64);
    assert_eq!(sim.phase, 0, "phase garbage");
    assert!(anc.is_empty(), "ancilla garbage");
    assert_eq!(bad, 0, "classical mismatches");
}

/// Diagnostic checkpoint replay on a previously emitted stream. D2_TRACE_CKS is the
/// comma-separated sequence of physical-op offsets printed by FROGDROP_CK.
#[test]
#[ignore = "explicit D2_TRACE_OPSFILE and D2_TRACE_CKS required"]
fn d2_full_stage_trace() {
    use crate::circuit::{BitId, QubitOrBit};
    type U = ruint::aliases::U256;
    let hx = |v: &str| U::from_str_radix(v, 16).unwrap();
    let marks: Vec<u64> = std::env::var("D2_TRACE_CKS").unwrap().split(',')
        .map(|s| s.trim().parse().unwrap()).collect();
    assert!(marks.windows(2).all(|p| p[0] < p[1]));
    let path = std::path::PathBuf::from(std::env::var("D2_TRACE_OPSFILE").unwrap());
    let regs: Vec<Vec<QubitOrBit>> = vec![
        (0..256).map(|i| QubitOrBit::Qubit(QubitId(i))).collect(),
        (256..512).map(|i| QubitOrBit::Qubit(QubitId(i))).collect(),
        (0..256).map(|i| QubitOrBit::Bit(BitId(2001 + i))).collect(),
        (0..256).map(|i| QubitOrBit::Bit(BitId(3001 + i))).collect(),
    ];
    let mut h = sha3::Shake256::default();
    h.update(b"d2-full-stage-trace");
    let mut xof = h.finalize_xof();
    let mut sim = Simulator::new(697, 2_500_000, &mut xof);
    let values = [
        hx("ac7de7e4273cdc5db0db68b3bfbc63918bf75431937b73ba3efc0f169c42e9f9"),
        hx("f1da94ae86fe9b5e1192c3c3e0ca01d90157d50e032ed8ca082fa7b4444d9799"),
        hx("e4c833d785501264ffb5069f194b96d1b0727d32a6b060cbd9a4cd617b862ec"),
        hx("50428abcc3b1743a9d73525e113bc7eba645647b69c6d6f4666be0d224779f5d"),
    ];
    for shot in 0..64 { for (reg, value) in regs.iter().zip(values) { sim.set_register(reg, value, shot); } }
    let lam_ids: Vec<QubitId> = (0..256).map(|i| QubitId(514 - i)).collect();
    let dxp = N::from_str_radix("7617d889c38491d85280744f0d98670173be5c8b95c8538727f917ff2a9b0bb7", 16).unwrap();
    let product = N::from_str_radix("44f9bbc9f1eb6cf119dd26918dbe80d6a6c4ce9c6f5213e26c19ced3d296c79a", 16).unwrap();
    let (rr, tt) = euclid_seq(dxp);
    let pm = pl_model(&rr, &tt, product);
    let want_payload = pl_lanes_off(&N::ZERO, &pm.w_next[pm.last], 1);
    let mut seen = 0u64;
    let mut at = 0usize;
    let mut carry: Vec<Op> = Vec::new();
    let dump = |sim: &Simulator<'_, _>, n: u64, label: usize| {
        eprintln!("D2_STAGE label={label} ops={n} x={:x} y={:x} lam={:x} phase={}",
            sim.get_register(&regs[0], 0), sim.get_register(&regs[1], 0),
            get(&sim.qubits, &lam_ids, 0), sim.phase & 1);
        if label == 4 {
            let bad: Vec<usize> = (0..259).filter(|&i| (sim.qubits[256 + i] & 1) as u8 != want_payload[i]).collect();
            eprintln!("D2_STAGE pre-T4 payload_bad={} lanes={:?}", bad.len(), &bad[..bad.len().min(24)]);
        }
    };
    let total = stream_ops(&path, |ops| {
        use crate::circuit::OperationType as K;
        carry.extend_from_slice(ops);
        loop {
            let limit = if at < marks.len() { ((marks[at] - seen) as usize).min(carry.len()) }
                        else { carry.len() };
            let (mut depth, mut cut) = (0i64, 0usize);
            for (i, op) in carry[..limit].iter().enumerate() {
                match op.kind { K::PushCondition => depth += 1, K::PopCondition => depth -= 1, _ => {} }
                assert!(depth >= 0);
                if depth == 0 { cut = i + 1; }
            }
            if cut == 0 { break; }
            sim.apply_iter(carry[..cut].iter());
            carry.drain(..cut);
            seen += cut as u64;
            if at < marks.len() && seen == marks[at] { dump(&sim, seen, at); at += 1; }
            if carry.is_empty() { break; }
        }
    });
    assert_eq!(at, marks.len());
    assert!(carry.is_empty(), "unbalanced condition stack at stream end");
    assert_eq!(seen, total);
    dump(&sim, total, at);
}

// Test-only transcription of midg::stage1_v's 24-bit reciprocal decision rule.
// This is deliberately separate from the production schedule predictor.
fn p3_over(w: N, z: N, k: usize) -> bool {
    let one = N::from(1u64);
    let sz = z.bit_len();
    let s = sz - k;
    let zh = (z >> s) | one;
    let f = ((one << (256 - s)) - one) / zh;
    let u = 257usize.saturating_sub(sz + super::midg::TC);
    (w >> u) > (f >> u)
}

fn p3_gtest(ph: u8, j: usize, r: &[N], t: &[N], k: usize, qb: usize) -> bool {
    let (z, y) = if ph == 0 { (r[j], t[j]) } else { (t[j], r[j]) };
    let bb = 258isize - z.bit_len() as isize - y.bit_len() as isize;
    if ph == 0 {
        let mut w = t[j - 1];
        for kb in (0..qb).rev() {
            if kb as isize >= bb { continue; }
            let trial = w + (y << kb);
            if !p3_over(trial, z, k) { w = trial; }
        }
        w == t[j + 1]
    } else {
        let mut q = r[j - 1] / r[j];
        let mut x = r[j - 1];
        for kb in 0..qb {
            if kb as isize >= bb {
                if q.bit(kb) { return false; }
                continue;
            }
            if q.bit(kb) { x -= y << kb; }
            if !p3_over(x + (y << kb), z, k) { q ^= N::from(1u64) << kb; }
        }
        q.is_zero() && x == r[j + 1]
    }
}

fn p3_diag_division(name: &str, shot_index: usize, x: N, sc: &super::frogdrop_sched::Sched) {
    use super::frogdrop_sched::{check, predict_n, shot, Kind, L0};
    use super::pointadd_frogdrop::{EMAX, KP, N, NQ, QB, TOT};
    let old = predict_n(x, sc, 22, KP, QB, TOT, NQ, EMAX, N);
    let actual = predict_n(x, sc, 24, KP, QB, TOT, NQ, EMAX, N);
    let trace = shot(x, L0);
    eprintln!("P3_DIAG shot={shot_index} division={name} input=0x{x:x} old={old:?} v2={actual:?} envelope={:?} columns={} qneed_max={} end_qneed={}",
        check(&trace, sc), trace.recs.len(), trace.recs.iter().map(|rec| rec.qn).max().unwrap_or(0), trace.br);
    let one = N::from(1u64);
    let (mut r, mut t) = (vec![super::frogdrop_sched::p(), x], vec![N::ZERO, one]);
    while !r.last().unwrap().is_zero() {
        let len = r.len();
        let q = r[len - 2] / r[len - 1];
        r.push(r[len - 2] - q * r[len - 1]);
        t.push(t[len - 2] + q * t[len - 1]);
    }
    let nn = r.len() - 1;
    let mut j = 1usize;
    for (c, rec) in trace.recs.iter().enumerate() {
        let ph = match rec.kind {
            Kind::Hr | Kind::Dl => 0,
            Kind::Ht => 1,
            Kind::Sw => { continue; }
            Kind::Dq => { j += 1; continue; }
            Kind::Idle => continue,
        };
        let q = r[j - 1] / r[j];
        let q0 = q >= (one << QB);
        let (old_g, new_g) = if j + 1 < nn {
            (p3_gtest(ph, j, &r, &t, 22, QB), p3_gtest(ph, j, &r, &t, 24, QB))
        } else { (true, true) };
        if q0 || !old_g || !new_g {
            eprintln!("P3_STEP shot={shot_index} division={name} col={c} j={j} kind={:?} q_bits={} q0={} gtest_k22={} gtest_k24={} z_bits={} y_bits={}",
                rec.kind, q.bit_len(), q0, old_g, new_g,
                if ph == 0 { r[j].bit_len() } else { t[j].bit_len() },
                if ph == 0 { t[j].bit_len() } else { r[j].bit_len() });
        }
        if rec.kind != Kind::Dl { j += 1; }
    }
    for j in 1..nn {
        if r[j].bit_len() <= L0 && r[j - 1].bit_len() > L0 {
            let q = r[j - 1] / r[j];
            let ybl = if super::frogdrop_sched::dl_enabled() && r[j].bit_len() > t[j].bit_len() {
                t[j].bit_len()
            } else { r[j].bit_len() };
            let demand = ybl as isize + q.bit_len() as isize - 129;
            eprintln!("P3_CROSS shot={shot_index} division={name} j={j} y_bits={ybl} q_bits={} reserve_demand={demand} reserve={}",
                q.bit_len(), super::midg::park_reserve());
        }
    }
}

/// Nonce predictor for the payload shell (streamed build): Fiat-Shamir hash as eval_circuit, 9024 shots, base
/// classical predicate on both divisions (dx and dx'); FROGDROP_SCAN = number of nonce qubits to scan (0: built nonce).
#[test]
#[ignore = "tool: run with --ignored and FROGDROP_* settings"]
fn payload_predict_nonce() {
    payload_predict_nonce_impl(false);
}

/// The emitted 698-wire Scheme G frame uses a 24-bit reciprocal head and
/// sx[2], sx[4] as remainder lanes with physical K22 ring geometry. This test changes only the
/// classical oracle; it cannot affect the circuit builder or its stream.
#[test]
#[ignore = "tool: run with --ignored and FROGDROP_* settings"]
fn payload_predict_nonce_v2() {
    payload_predict_nonce_impl(true);
}

/// Full physical emission without retaining the billion-op vector in memory.
#[test]
#[ignore = "explicit B2_EMIT_STREAM_PATH in WSL home required"]
fn b2_emit_stream() {
    let path = std::env::var("B2_EMIT_STREAM_PATH").expect("B2_EMIT_STREAM_PATH required");
    assert!(!std::path::Path::new(&path).exists(), "new stream path required");
    std::env::set_var("LOWQ_EXACT_STREAM_PATH", &path);
    let ops = super::build();
    std::env::remove_var("LOWQ_EXACT_STREAM_PATH");
    assert!(ops.is_empty(), "streaming build must not retain ops");
    eprintln!("B2_EMITTED path={path}");
}

/// Full physical emission without retaining the billion-op vector in memory.
#[test]
#[ignore = "explicit D2_EMIT_STREAM_PATH in WSL home required"]
fn d2_emit_stream() {
    let path = std::env::var("D2_EMIT_STREAM_PATH").expect("D2_EMIT_STREAM_PATH required");
    assert!(!std::path::Path::new(&path).exists(), "new stream path required");
    std::env::set_var("LOWQ_EXACT_STREAM_PATH", &path);
    let mut b = B::new();
    std::env::remove_var("LOWQ_EXACT_STREAM_PATH");
    b.global_cancel = true;
    let _ = super::pointadd_frogdrop::point_add_pl(&mut b);
    let count = b.finish_stream().expect("stream enabled");
    eprintln!("D2_EMITTED peak={} width={} toffoli={} ops={} path={}",
              b.peak, b.width(), b.tof, count, path);
    assert_eq!((b.peak, b.width()), (697, 697));
}

/// D3 direct stream emission with the compile-time nonce of the graded 697 source.
#[test]
#[ignore = "explicit D3_EMIT_STREAM_PATH in WSL home required"]
fn d3_emit_stream() {
    let path = std::env::var("D3_EMIT_STREAM_PATH").expect("D3_EMIT_STREAM_PATH required");
    assert!(!std::path::Path::new(&path).exists(), "new stream path required");
    std::env::set_var("LOWQ_EXACT_STREAM_PATH", &path);
    let mut b = B::new();
    std::env::remove_var("LOWQ_EXACT_STREAM_PATH");
    b.global_cancel = true;
    let _ = super::pointadd_frogdrop::point_add_pl(&mut b);
    let count = b.finish_stream().expect("stream enabled");
    eprintln!("D3_EMITTED peak={} width={} toffoli={} ops={} path={}",
              b.peak, b.width(), b.tof, count, path);
    assert_eq!((b.peak, b.width()), (696, 696));
}

/// D4 direct stream emission with the compile-time nonce fixed at 181.
#[test]
#[ignore = "explicit D4_EMIT_STREAM_PATH in WSL home required"]
fn d4_emit_stream() {
    assert_eq!(super::NONCE, 181);
    let path = std::env::var("D4_EMIT_STREAM_PATH").expect("D4_EMIT_STREAM_PATH required");
    assert!(!std::path::Path::new(&path).exists(), "new stream path required");
    std::env::set_var("LOWQ_EXACT_STREAM_PATH", &path);
    let mut b = B::new();
    std::env::remove_var("LOWQ_EXACT_STREAM_PATH");
    b.global_cancel = true;
    let _ = super::pointadd_frogdrop::point_add_pl(&mut b);
    let count = b.finish_stream().expect("stream enabled");
    eprintln!("D4_EMITTED peak={} width={} toffoli={} ops={} path={}",
              b.peak, b.width(), b.tof, count, path);
    assert_eq!((b.peak, b.width()), (695, 695));
}

#[test]
#[ignore = "explicit D5_EMIT_STREAM_PATH in WSL home required"]
fn d5_emit_stream() {
    assert_eq!(super::NONCE, 181);
    let path = std::env::var("D5_EMIT_STREAM_PATH").expect("D5_EMIT_STREAM_PATH required");
    assert!(!std::path::Path::new(&path).exists(), "new stream path required");
    std::env::set_var("LOWQ_EXACT_STREAM_PATH", &path);
    let mut b = B::new();
    std::env::remove_var("LOWQ_EXACT_STREAM_PATH");
    b.global_cancel = true;
    let _ = super::pointadd_frogdrop::point_add_pl(&mut b);
    let count = b.finish_stream().expect("stream enabled");
    eprintln!("D5_EMITTED peak={} width={} toffoli={} ops={} path={}",
              b.peak, b.width(), b.tof, count, path);
    assert_eq!((b.peak, b.width()), (694, 694));
}

fn payload_predict_nonce_impl(precision24: bool) {
    use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
    use super::frogdrop_sched::{from_text, predict, predict_n, predict_n_geometry};
    use super::pointadd_frogdrop::*;
    use sha3::digest::{ExtendableOutput, Update, XofReader};
    type U = ruint::aliases::U256;
    // B2 paired census: bind each stream to its physical ring and exact
    // source geometry, while both streams retain the same 24-bit precision.
    let b2_ring = std::env::var("B2_PRED_RING").ok().map(|v| v.parse::<usize>().expect("B2_PRED_RING"));
    if let Some(nring) = b2_ring {
        assert!(precision24 && matches!(nring, 261 | 262 | 263));
        super::bake_knobs();
        std::env::set_var("QUOT_CUTS_NONCROSS", match nring { 263 => "10,20", 262 => "9,18", 261 => "8,16", _ => unreachable!() });
        std::env::set_var("QUOT_PRED_SPLITK", (nring - 259).to_string());
        let rs: usize = std::env::var("QUOT_RES_S").unwrap().parse().unwrap();
        let ytop = usize::from(std::env::var("LANE_S5_YTOP").as_deref() == Ok("1"));
        std::env::set_var("QUOT_PRED_RES_S", (rs + ytop).to_string());
        std::env::set_var("QUOT_PRED_SWCHK", "exact");
        std::env::set_var("QUOT_PRED_DLCHK", "exact");
    }
    let hx = |h: &str| U::from_str_radix(h, 16).unwrap();
    let curve = WeierstrassEllipticCurve {
        modulus: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
        a: U::ZERO, b: U::from(7u64),
        gx: hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
        gy: hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
        order: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
    };
    #[cfg(all(target_os = "linux", nonce_openssl))]
    let fast_curve = nonce_openssl::Curve::new();
    let scan: usize = std::env::var("FROGDROP_SCAN").ok().and_then(|s| s.parse().ok()).unwrap_or(0);
    // FROGDROP_OPSFILE: hash an existing ops file (e.g. a graded build) instead of building
    let opsfile = std::env::var("FROGDROP_OPSFILE").ok();
    let path = match &opsfile { Some(f) => std::path::PathBuf::from(f),
                                None => std::env::temp_dir().join(format!("pl_pred_{}.bin", std::process::id())) };
    let fast_prefix = if precision24 && opsfile.is_some() { Some(p3_stream_prefix(&path)) } else { None };
    let (l, width) = if let Some((n, w, _, _)) = &fast_prefix { (*n, *w) } else if opsfile.is_some() {
        let mut n = 0usize;
        let mut w = 0u64;
        stream_ops(&path, |ops| { for op in ops { n += 1; for q in [op.q_target.0, op.q_control1.0, op.q_control2.0] {
            if q != u64::MAX && q < 1 << 40 { w = w.max(q + 1); } } } });
        (n, w)
    } else {
        std::env::set_var("LOWQ_EXACT_STREAM_PATH", &path);
        let mut b = B::new();
        std::env::remove_var("LOWQ_EXACT_STREAM_PATH");
        let _ = point_add_pl(&mut b);
        let l = b.finish_stream().unwrap() as usize;
        eprintln!("built {l} ops, width {}, peak {}, emitted T {}", b.width(), b.peak, b.tof);
        (l, b.width())
    };
    let upd = |h: &mut sha3::Shake256, op: &crate::circuit::Op| {
        h.update(&[op.kind as u8]);
        h.update(&op.q_control2.0.to_le_bytes());
        h.update(&op.q_control1.0.to_le_bytes());
        h.update(&op.q_target.0.to_le_bytes());
        h.update(&op.c_target.0.to_le_bytes());
        h.update(&op.c_condition.0.to_le_bytes());
        h.update(&op.r_target.0.to_le_bytes());
    };
    let (pre, tail) = if let Some((_, _, pre, tail)) = fast_prefix { (pre, tail) } else {
        let mut pre = sha3::Shake256::default();
        pre.update(b"quantum_ecc-fiat-shamir-v2");
        pre.update(&(l as u64).to_le_bytes());
        let mut seen = 0usize;
        let mut tail = None;
        stream_ops(&path, |ops| {
            for op in ops {
                if seen < l - 2 { upd(&mut pre, op); } else if tail.is_none() { tail = Some(*op); }
                seen += 1;
            }
        });
        (pre, tail.unwrap())
    };
    if opsfile.is_none() { let _ = std::fs::remove_file(&path); }
    let sched = from_text(SCHED_FROGDROP);
    let pp = super::frogdrop_sched::p();
    let to_n = |u: U| -> N { let mut v = N::ZERO; for (i, &w) in u.as_limbs().iter().enumerate() { v |= N::from(w) << (64 * i); } v };
    let baseline = std::env::var_os("FROGDROP_PRED_BASELINE").is_some();
    let pred = |x: N| if precision24 {
        if baseline { predict_n_geometry(x, &sched, 24, 24, 24, 83, 128, 28, 282, 9, 0) }
        else { predict_n(x, &sched, 24, KP, QB, TOT, NQ, EMAX, b2_ring.unwrap_or(N)) }
    } else {
        predict(x, &sched, K, KP, QB, TOT, NQ, EMAX)
    };
    if precision24 { eprintln!("D2_PRED_GEOMETRY baseline={baseline} precision=24 physical_k={} ring={} qb={} emax={} reserve={} ordinary_extra={}",
        if baseline { 23 } else { b2_ring.unwrap_or(N) - 259 }, if baseline { 282 } else { b2_ring.unwrap_or(N) },
        if baseline { 24 } else { QB }, if baseline { 28 } else { EMAX },
        if baseline { 9 } else { super::midg::park_reserve() }, if baseline { 0 } else { (257 + EMAX).saturating_sub(N) }); }
    // the (fixed) done-counter probe bug: a shot's first idle column c read its counter (Q lane nq - cnt) in the map's
    // bl(X) probe (bound m_c) or the stage-1.5 bl(Q) probe (bound psy_c)
    let (cpars, _, _) = col_pars(&sched);
    let counter_probe_hit = |x: N| -> bool {
        let sh = super::frogdrop_sched::shot(x, super::frogdrop_sched::L0);
        let c = sh.recs.len();
        if c >= cpars.len() { return false; }
        let ctop = NQ - CNTB;
        cpars[c].m > ctop || (cpars[c].pht && cpars[c].psy.1.min(128) > ctop)
    };
    let mut clean = vec![];
    let mut clean_pairs = vec![];
    let diag_shots: std::collections::BTreeSet<usize> = std::env::var("FROGDROP_DIAG_SHOTS")
        .ok().map(|v| v.split(',').map(|s| s.trim().parse().unwrap()).collect()).unwrap_or_default();
    let shots: usize = std::env::var("D2_DIAG_SHOTS")
        .ok().and_then(|v| v.parse().ok()).unwrap_or(9024);
    let scan0: u64 = std::env::var("FROGDROP_SCAN0").ok().and_then(|s| s.parse().ok()).unwrap_or(0);
    // FROGDROP_CTRLS: controls of a CX CX nonce pair (the built tail must be a CX pair); every (ctrl, target)
    let ctrls: Vec<Option<u64>> = match std::env::var("FROGDROP_CTRLS") {
        Ok(v) => v.split(',').map(|x| Some(x.trim().parse::<u64>().unwrap())).collect(),
        Err(_) => vec![None],
    };
    if ctrls[0].is_some() { assert_eq!(tail.kind, crate::circuit::OperationType::CX, "FROGDROP_CTRLS needs a CX pair"); }
    for ctrl in ctrls {
    for nonce in scan0..(scan.max(1) as u64) {
        let q = if scan == 0 { tail.q_target.0 } else { nonce };
        if q >= width { break; }
        if ctrl == Some(q) { continue; }
        let mut h = pre.clone();
        let mut op = tail;
        op.q_target = crate::circuit::QubitId(q);
        if let Some(c) = ctrl { op.q_control1 = crate::circuit::QubitId(c); }
        upd(&mut h, &op);
        upd(&mut h, &op);
        let mut xof = h.finalize_xof();
        let mut fails = std::collections::BTreeMap::<&str, usize>::new();
        let mut cbs: Vec<usize> = vec![];
        let mut failed_shots = std::collections::BTreeSet::new();
        let mut failed_batches = std::collections::BTreeMap::<usize, &str>::new();
        let mut n = 0;
        for _ in 0..shots {
            let mut rb = [[0u8; 32]; 2];
            xof.read(&mut rb[0]);
            xof.read(&mut rb[1]);
            #[cfg(all(target_os = "linux", nonce_openssl))]
            let points = fast_curve.points(&rb);
            #[cfg(not(all(target_os = "linux", nonce_openssl)))]
            let points = {
                let t = curve.mul(curve.gx, curve.gy, U::from_le_bytes(rb[0]));
                let o = curve.mul(curve.gx, curve.gy, U::from_le_bytes(rb[1]));
                if t.0 == o.0 || (t.0.is_zero() && t.1.is_zero()) || (o.0.is_zero() && o.1.is_zero()) { None }
                else { Some([t, o, curve.add(t.0, t.1, o.0, o.1)]) }
            };
            let Some([t, o, e]) = points else { continue; };
            // Compare the optimized enumerator to the inherited model on the
            // first two accepted shots of each stream.
            #[cfg(all(target_os = "linux", nonce_openssl))]
            if n < 2 {
                let gt = curve.mul(curve.gx, curve.gy, U::from_le_bytes(rb[0]));
                let go = curve.mul(curve.gx, curve.gy, U::from_le_bytes(rb[1]));
                assert_eq!(t, gt, "dx input point");
                assert_eq!(o, go, "other input point");
                assert_eq!(e, curve.add(gt.0, gt.1, go.0, go.1), "sum input point");
            }
            n += 1;
            let (x1, x2, x3) = (to_n(t.0), to_n(o.0), to_n(e.0));
            let d1 = if x1 >= x2 { x1 - x2 } else { x1 + pp - x2 };
            let d2 = if x3 >= x2 { x3 - x2 } else { x3 + pp - x2 };
            if diag_shots.contains(&(n - 1)) {
                eprintln!("D2_DIAG_POINT shot={} x1={:x} y1={:x} x2={:x} y2={:x} x3={:x} y3={:x}",
                          n - 1, t.0, t.1, o.0, o.1, e.0, e.1);
                p3_diag_division("dx", n - 1, d1, &sched);
                p3_diag_division("dx_prime", n - 1, d2, &sched);
            }
            let mut cb = false;
            for (division, d) in [("dx", d1), ("dx_prime", d2)] {
                if let Some(why) = pred(d) {
                    *fails.entry(why).or_default() += 1;
                    failed_shots.insert(n - 1);
                    failed_batches.entry((n - 1) / 64).or_insert(why);
                    if scan == 0 { eprintln!("predicted failing shot {} {division} ({why})", n - 1); }
                }
                cb |= counter_probe_hit(d);
            }
            if cb { *fails.entry("counter-probe(fixed)").or_default() += 1; if cbs.len() < 12 { cbs.push(n - 1); } }
            // scanning: a nonce with one failing division is out
            if scan > 0 && std::env::var("FROGDROP_SCANALL").is_err()
                && fails.iter().any(|(k, v)| !k.starts_with("counter") && *v > 0) { break; }
        }
        let nf: usize = fails.iter().filter(|(k, _)| !k.starts_with("counter")).map(|(_, v)| v).sum();
        let mut batch_kinds = std::collections::BTreeMap::<&str, usize>::new();
        for &why in failed_batches.values() { *batch_kinds.entry(why).or_default() += 1; }
        eprintln!("nonce qubit {q}: {n} shots, failing divisions {nf} {:?}; counter-probe shots {:?}; ctrl {:?}", fails, cbs,
                  ctrl);
        eprintln!("D1_BATCH nonce={q} failing_shots={} failing_batches={} kinds={:?}",
            failed_shots.len(), failed_batches.len(), batch_kinds);
        if scan == 0 { eprintln!("predicted failing-shot set: {:?}", failed_shots); }
        if nf == 0 { clean.push(q); clean_pairs.push((ctrl, q)); }
    }
    }
    eprintln!("clean nonces: {:?}", clean);
    if precision24 { eprintln!("v2 clean ctrl/target pairs: {:?}", clean_pairs); }
}

#[test]
#[ignore = "tool"]
fn sched_qn_debug() {
    use super::frogdrop_sched::*;
    let shots: Vec<(N, Shot)> = sample(20000, 11).into_iter().map(|x| (x, shot(x, L0))).collect();
    let mut shown = 0;
    for (x, s) in &shots {
        for (c, r) in s.recs.iter().enumerate() {
            if r.qn > 128 && shown < 6 {
                shown += 1;
                let prev = if c > 0 { format!("{:?}", s.recs[c - 1].kind) } else { "-".into() };
                eprintln!("x {:x} col {c} kind {:?} prev {prev} qn {} sz {} sy {} xw {}", x, r.kind, r.qn, r.sz, r.sy, r.xw);
            }
        }
    }
}

/// Stage-3 study: windowed-estimate failures per traversal input with the raw Yh (built machine) vs a virtual-odd
/// Yh | 1 in the quotient step (needed by the parity erase q_k = par(rho) ^ par(R) ^ g). FROGDROP_YODD_N inputs.
#[test]
#[ignore]
fn yodd_estimate_study() {
    use super::frogdrop_sched::{p, sample};
    use super::pointadd_frogdrop::{K, KP, QB, TOT};
    let n: usize = std::env::var("FROGDROP_YODD_N").ok().and_then(|s| s.parse().ok()).unwrap_or(20000);
    let th = 8;
    let res: Vec<[usize; 6]> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..th).map(|ti| sc.spawn(move || {
            let pp = p();
            let one = N::from(1u64);
            let mut c = [0usize; 6]; // inputs, cols, fail raw, fail odd, inputs fail raw, inputs fail odd
            for xr in sample(n / th, 4242 + ti as u64) {
                let (mut r, mut t) = (vec![pp, xr], vec![N::ZERO, one]);
                while !r[r.len() - 1].is_zero() {
                    let m = r.len();
                    let q = r[m - 2] / r[m - 1];
                    let rn = r[m - 2] - q * r[m - 1];
                    let tn = t[m - 2] + q * t[m - 1];
                    r.push(rn);
                    t.push(tn);
                }
                let nn = r.len() - 1;
                let (mut fr, mut fo) = (0, 0);
                for j in 1..nn {
                    let q = r[j - 1] / r[j];
                    // HR while t_j < 2^128 (r-rule switch), then HT
                    let ht = t[j].bit_len() > super::frogdrop_sched::L0;
                    let (z, x, y) = if !ht { (r[j], t[j - 1], t[j]) } else { (t[j], r[j + 1], r[j]) };
                    let (sz, sy) = (z.bit_len(), y.bit_len());
                    if sz < K || sz + sy > 256 + K + KP { continue; }
                    let zh = (z >> (sz - K)) | one;
                    let (yh, xh) = if sy >= KP { (y >> (sy - KP), x >> (sy - KP)) } else { (y << (KP - sy), x << (KP - sy)) };
                    let e = 256 + K + KP - sz - sy;
                    if e > TOT { continue; }
                    let fh = ((one << e) - one) / zh;
                    c[1] += 1;
                    for (odd, f) in [(false, &mut fr), (true, &mut fo)] {
                        let yd = if odd { yh | one } else { yh };
                        let (q0, rho) = (fh / yd, fh % yd);
                        if q0 >= (one << QB) { *f += 1; continue; }
                        let b = if rho < xh { one } else { N::ZERO };
                        if q0 < b || q0 - b != q { *f += 1; }
                    }
                }
                c[0] += 1;
                c[2] += fr;
                c[3] += fo;
                c[4] += (fr > 0) as usize;
                c[5] += (fo > 0) as usize;
            }
            c
        })).collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut s = [0usize; 6];
    for c in res { for i in 0..6 { s[i] += c[i]; } }
    eprintln!("inputs {} cols {} | col fails raw {} odd {} | inputs failing raw {} odd {}", s[0], s[1], s[2], s[3], s[4], s[5]);
}

/// Stage 3': subset-storage P with a virtual-odd Yd. head + tail_a stores mask a of q0 = floor(F / (Yh|1)); the
/// switch tail_a^-1 + tail_b stores mask b; tail_b^-1 + head^-1 is clean. Both carry modes, production widths.
#[test]
fn pipeline_subset_switch() {
    use super::pointadd_frogdrop::{K, KP, TOT};
    let (k, kp, qb, tot) = (K, KP, 26usize, TOT);
    let soff = tot as i64 - 256 - k as i64 - kp as i64;
    let p = pval();
    let one = N::from(1u64);
    let mut rng = Rng::new(777);
    let mut cs = vec![];
    while cs.len() < 64 {
        let mut x = rng.below(256) % p;
        if x.is_zero() { continue; }
        if x > p >> 1 { x = p - x; }
        let (mut r, mut t) = (vec![p, x], vec![N::ZERO, one]);
        while !r[r.len() - 1].is_zero() {
            let n = r.len();
            let qq = r[n - 2] / r[n - 1];
            let rn = r[n - 2] - qq * r[n - 1]; let tn = t[n - 2] + qq * t[n - 1];
            r.push(rn); t.push(tn);
        }
        let nn = r.len() - 1;
        let j = 1 + (rng.next() as usize) % (nn - 2);
        let ht = blen(&t[j]) > 128;
        let (z, y) = if ht { (t[j], r[j]) } else { (r[j], t[j]) };
        let (sz, sy) = (blen(&z), blen(&y));
        if sz < k { continue; }
        let zh = z >> (sz - k);
        let yh = if sy >= kp { y >> (sy - kp) } else { y << (kp - sy) };
        let e = 256 + k + kp - sz - sy;
        if e > tot + k - 1 { continue; }
        let zd = zh | one;
        let yd = yh | one;
        let fh = ((one << e) - one) / zd;
        let rfin = ((one << e) - one) % zd;
        let (q0, rho) = (fh / yd, fh % yd);
        if blen(&q0) > qb { continue; }
        cs.push((zh, yh, sz + sy, q0, rho, rfin));
    }
    let mask_a: Vec<bool> = (0..qb).map(|i| i >= 13).collect();
    let mask_b: Vec<bool> = (0..qb).map(|i| i < 13).collect();
    for ncar in [0usize, 8] {
        let mut b = B::new();
        let zh = b.alloc_n(k); let yh = b.alloc_n(kp); let startv = b.alloc_n(9);
        let ps = PScr { r: b.alloc_n(k + 1), rho: b.alloc_n(kp + 1), q0: b.alloc_n(qb), f: b.alloc(), g: b.alloc(),
                        c0: b.alloc(), zero: b.alloc(), one: b.alloc(), spre: b.alloc_n(6), tmp: b.alloc(), dirty: vec![] };
        let carries = b.alloc_n(ncar);
        let tq = ps.f; // as in the column: P's f lane is clean at every quotient step
        let (head, tails, swp, rf, rhof) = pipeline_subset(&mut b, &zh, &yh, &startv, soff, tot, qb, &ps, &carries,
                                                           &[mask_a.clone(), mask_b.clone()], tq, 0);
        b.play(&head, false);
        b.play(&tails[0], false);
        let n1 = b.ops.len();
        let t1 = b.tof;
        b.play(&swp[0].0, true);
        b.play(&swp[0].1, false);
        let n2 = b.ops.len();
        let tsw = b.tof - t1;
        b.play(&tails[1], true);
        b.play(&head, true);
        let init = |w: &mut Vec<u64>| {
            for (s, (zv, yv, st, _, _, _)) in cs.iter().enumerate() {
                put(w, &zh, s, zv); put(w, &yh, s, yv); put(w, &startv, s, &N::from(*st as u64));
            }
        };
        let w = b.width() as usize;
        let r1 = run(&b.ops[..n1], w, &init);
        let r2 = run(&b.ops[..n2], w, &init);
        let r3 = run(&b.ops, w, &init);
        for (rr, m) in [(&r1, &mask_a), (&r2, &mask_b)] {
            assert_eq!(rr.phase, 0);
            for (s, (_, _, _, q0, rho, rfin)) in cs.iter().enumerate() {
                let want = (0..qb).fold(N::ZERO, |acc, i| if m[i] && q0.bit(i) { acc | (one << i) } else { acc });
                assert_eq!(get(&rr.q, &ps.q0, s), want, "stored q0 shot {s} carries {ncar}");
                assert_eq!(get(&rr.q, &rhof, s), *rho, "rho shot {s}");
                assert_eq!(get(&rr.q, &rf, s), *rfin, "R shot {s}");
                for &q in [ps.f, ps.g, ps.c0, ps.zero, ps.tmp, tq].iter().chain(ps.spre.iter()).chain(carries.iter()) {
                    assert_eq!((rr.q[q.0 as usize] >> s) & 1, 0, "scratch dirty shot {s}");
                }
            }
        }
        assert_eq!(r3.phase, 0);
        for s in 0..cs.len() {
            for &q in ps.r.iter().chain(ps.rho.iter()).chain(ps.q0.iter()) {
                assert_eq!((r3.q[q.0 as usize] >> s) & 1, 0, "un-P leaves garbage shot {s}");
            }
        }
        eprintln!("subset P carries {ncar}: P {t1} T, switch {tsw} T");
    }
}

/// Failure hunt: one production payload traversal build, FROGDROP_BATCHES batches of 64 random (x', dy) on 8 threads
/// (batch seeds FROGDROP_SEED0 + i). Prints every failing input (Euclid output, counter, zeros, payload, phase).
#[test]
#[ignore = "tool"]
fn frogdrop_traversal_hunt() {
    use super::frogdrop_sched::{sample, from_text, predict};
    use super::pointadd_frogdrop::*;
    use super::payload::NP;
    let nbatch: u64 = std::env::var("FROGDROP_BATCHES").ok().and_then(|s| s.parse().ok()).unwrap_or(16);
    let seed0: u64 = std::env::var("FROGDROP_SEED0").ok().and_then(|s| s.parse().ok()).unwrap_or(1000);
    let sc = from_text(SCHED_FROGDROP);
    let ncols = sc.cols.len();
    let mut b = B::new();
    let xq = b.alloc_n(256);
    let pl = b.alloc_n(NP);
    let t = trav_forward_pl(&mut b, &xq, &pl, Some(&pl));
    eprintln!("hunt build: {} T, {} ops, peak {}", b.tof, b.ops.len(), b.peak);
    let width = b.width() as usize;
    let ops = &b.ops;
    let t = &t;
    let pl = &pl;
    let xq = &xq;
    let sc = &sc;
    let next = std::sync::atomic::AtomicU64::new(0);
    let total_bad = std::sync::atomic::AtomicU64::new(0);
    std::thread::scope(|scope| {
        for _ in 0..8 {
            scope.spawn(|| loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                if i >= nbatch { break; }
                let seed = seed0 + i;
                // FROGDROP_HITS: only inputs that finish while the next column's probe bounds reach the counter lanes
                let xs = if std::env::var("FROGDROP_HITS").is_ok() {
                    let (cpars, _, _) = col_pars(sc);
                    let ctop = NQ - CNTB;
                    let mut v = vec![];
                    let mut k = 0u64;
                    while v.len() < 64 {
                        for x in sample(4096, seed * 1_000_003 + k) {
                            let sh = super::frogdrop_sched::shot(x, super::frogdrop_sched::L0);
                            let c = sh.recs.len();
                            if c < cpars.len() && (cpars[c].m > ctop || (cpars[c].pht && cpars[c].psy.1.min(128) > ctop))
                                && predict(x, sc, K, KP, QB, TOT, NQ, EMAX).is_none() && v.len() < 64 {
                                v.push(x);
                            }
                        }
                        k += 1;
                    }
                    v
                } else if let Ok(f) = std::env::var("FROGDROP_XFILE") {
                    // crafted inputs (hex, one per line): batch i takes lines 64 i .. 64 i + 64 (cyclic)
                    let all: Vec<N> = std::fs::read_to_string(&f).unwrap().lines().filter(|l| !l.trim().is_empty())
                        .map(|l| N::from_str_radix(l.trim(), 16).unwrap()).collect();
                    (0..64).map(|s| all[((seed - seed0) as usize * 64 + s) % all.len()]).collect()
                } else { sample(64, seed) };
                let mut rng = Rng::new(seed ^ 0x77);
                let p = pval();
                let dys: Vec<N> = (0..64).map(|_| rng.below(256) % p).collect();
                // per-batch measurement randomness
                let (aq, nb, _, _) = analyze_ops(ops.iter());
                let mut h = sha3::Shake256::default();
                h.update(b"frogdrop-hunt");
                h.update(&seed.to_le_bytes());
                let mut xof = h.finalize_xof();
                let mut sim = Simulator::new(width.max(aq as usize), (nb as usize).max(1), &mut xof);
                for s in 0..64 {
                    put(&mut sim.qubits, xq, s, &xs[s]);
                    put(&mut sim.qubits, &pl[..256], s, &dys[s]);
                }
                sim.apply_iter(ops.iter());
                let q = &sim.qubits;
                let mut nbad = 0;
                for s in 0..64 {
                    let pr = predict(xs[s], sc, K, KP, QB, TOT, NQ, EMAX);
                    let (rr, tt) = euclid_seq(xs[s]);
                    let nn = rr.len() - 1;
                    let ok_t = get(q, &t.fd.ring[0..256], s) == tt[nn - 1];
                    let ok_c = get(q, &t.fd.cnt, s) == N::from((ncols - (nn - 1) + 1) as u64)
                        && get(q, &t.fd.q[..26], s) == rr[nn - 2];
                    let mut zero_ok = true;
                    for &qq in t.fd.ring[256..].iter().chain(t.fd.q[26..NQ - 7].iter()).chain(t.fd.sy.iter())
                        .chain(t.fd.sx.iter()).chain([t.fd.ph].iter()).chain(t.pool.iter()) {
                        if (q[qq.0 as usize] >> s) & 1 != 0 { zero_ok = false; }
                    }
                    let m = pl_model(&rr, &tt, dys[s]);
                    let want = pl_lanes_off(&N::ZERO, &m.w_pre[m.last + 1], 1);
                    let nbadl = (0..NP).filter(|&l| (((q[pl[l].0 as usize] >> s) & 1) as u8) != want[l]).count();
                    let ph = (sim.phase >> s) & 1;
                    if !(ok_t && ok_c && zero_ok && nbadl == 0 && ph == 0) {
                        nbad += 1;
                        eprintln!("HUNT_FAIL seed {seed} shot {s} pred {:?} N {nn} t {ok_t} cnt {ok_c} zeros {zero_ok} payload_bad {nbadl} phase {ph} x {:x} dy {:x}",
                                  pr, xs[s], dys[s]);
                    }
                }
                total_bad.fetch_add(nbad, std::sync::atomic::Ordering::SeqCst);
                eprintln!("batch {seed}: {nbad} bad");
            });
        }
    });
    eprintln!("HUNT total bad {} of {} inputs", total_bad.load(std::sync::atomic::Ordering::SeqCst), nbatch * 64);
}

/// Column trace of one traversal input FROGDROP_X (hex) with payload dy FROGDROP_DY (hex) on 64 shots (different
/// measurement randomness): after every column, compares ring / Q / sy / ph with the schedule model and prints the
/// first deviating column per shot.
#[test]
#[ignore = "tool"]
fn frogdrop_col_trace() {
    super::bake_knobs();
    let hx = |v: &str| N::from_str_radix(v, 16).unwrap();
    let x = hx(&std::env::var("FROGDROP_X").unwrap());
    let dy = std::env::var("FROGDROP_DY").map(|v| hx(&v)).unwrap_or(N::ZERO);
    frogdrop_col_trace_impl(x, dy, false);
}

#[test]
fn d2_hr_digit_n280_packed() {
    let x = N::from_str_radix("70dddacfd33a34f528cce40d9366cd7cf10fa69c8f34abae2728b07a2e4b56e0", 16).unwrap();
    let dy = N::from_str_radix("103a92ea7a3771100adee61ee4d5f0a16324cad0b737e2f9e3c27ba78ac13969", 16).unwrap();
    frogdrop_col_trace_impl(x, dy, true);
}

#[test]
fn d4_n278_all_columns_euclid_payload_phase() {
    super::bake_knobs();
    let x = N::from_str_radix("70dddacfd33a34f528cce40d9366cd7cf10fa69c8f34abae2728b07a2e4b56e0", 16).unwrap();
    let dy = N::from_str_radix("564b1a76853d2295410e7ccd2aa128c52f84c1e577ab7011b206b43d4e9a70cb", 16).unwrap();
    frogdrop_col_trace_impl(x, dy, true);
}

#[test]
fn d4b_crossing_need7_direct_packed_phase() {
    super::bake_knobs();
    let x = N::from_str_radix("2b03ed9a1b8d6e0625a255ae3b009377d73ea64897d74b1bac0e5c49268ed892", 16).unwrap();
    let dy = N::from_str_radix("564b1a76853d2295410e7ccd2aa128c52f84c1e577ab7011b206b43d4e9a70cb", 16).unwrap();
    frogdrop_col_trace_impl(x, dy, true);
}

#[test]
fn d4b_crossing_need7_delayed_packed_phase() {
    super::bake_knobs();
    let x = N::from_str_radix("41503e271d244acabe765b13f678020499663b6c02c0fe7df23126d857c5944d", 16).unwrap();
    let dy = N::from_str_radix("564b1a76853d2295410e7ccd2aa128c52f84c1e577ab7011b206b43d4e9a70cb", 16).unwrap();
    frogdrop_col_trace_impl(x, dy, true);
}

#[test]
fn d4b_crossing_sy128_packed_phase() {
    super::bake_knobs();
    let x = N::from_str_radix("2dee75a73b9cc49e585d2c7a00bfae7af560d875df450d944ef3b26ce701f330", 16).unwrap();
    let dy = N::from_str_radix("564b1a76853d2295410e7ccd2aa128c52f84c1e577ab7011b206b43d4e9a70cb", 16).unwrap();
    frogdrop_col_trace_impl(x, dy, true);
}

fn b2_bake_pred_knobs() {
    super::bake_knobs();
    std::env::set_var("QUOT_PRED_SPLITK", "3");
    std::env::set_var("QUOT_PRED_RES_S", "6"); // five lanes and the exact Y-top slot
    std::env::set_var("QUOT_PRED_SWCHK", "exact");
    std::env::set_var("QUOT_PRED_DLCHK", "exact");
}

/// B3: V-time size order and paired vacancy on the source predictor recurrence.
/// A direct switch's entry `Rec.sy` is the prior X size; stage 2 replaces it
/// with bl(Q)=bl(r_j) before V, so inspect that actual V-time pair here.
#[test]
#[ignore = "explicit B3_PRED_N finite predictor screen"]
fn b3_predictor_size_order_x128() {
    use super::frogdrop_sched::{from_text, predict_n, sample, shot, Kind, L0};
    use super::pointadd_frogdrop::{SCHED_FROGDROP, KP, QB, TOT, NQ, EMAX, N};
    super::bake_knobs();
    std::env::set_var("QUOT_PRED_SPLITK", "2");
    std::env::set_var("QUOT_PRED_RES_S", "6");
    std::env::set_var("QUOT_PRED_SWCHK", "exact");
    std::env::set_var("QUOT_PRED_DLCHK", "exact");
    let sc = from_text(SCHED_FROGDROP);
    let (cpars, _, _) = super::pointadd_frogdrop::col_pars(&sc);
    let limit = std::env::var("B3_PRED_N").ok().and_then(|v| v.parse().ok()).unwrap_or(100_000);
    let mut plays = 0usize;
    let mut occupied = 0usize;
    let mut clean = std::collections::BTreeMap::<&str, String>::new();
    for x in sample(limit, 0xB3678) {
        let sh = shot(x, L0);
        let (r, t) = euclid_seq(x);
        let mut j = 1usize;
        let mut hits = vec![];
        for (col, rec) in sh.recs.iter().enumerate() {
            match rec.kind {
                Kind::Hr | Kind::Ht | Kind::Dl => {
                    let sz = if rec.kind == Kind::Ht { blen(&t[j]) } else { blen(&r[j]) };
                    let sy = if rec.kind == Kind::Ht { blen(&r[j]) } else { blen(&t[j]) };
                    assert!(sz >= sy && sz + sy <= 257, "V order x={x:x} col={col} kind={:?} sz={sz} sy={sy}", rec.kind);
                    plays += 1;
                    let g = 257 - sz - sy;
                    let cp = &cpars[col];
                    let mt = (cp.n - cp.sz.0 - cp.h + 1).min(cp.nq.max(cp.xw) + 1);
                    let kmax = 258usize.saturating_sub(cp.sz.0 + cp.sy.0).min(23).min(mt);
                    let cross = cp.sw || cp.dl || cp.dq || cp.psw;
                    let cuts = if cross { vec![1, 3, 7, 15] } else { vec![8, 16] };
                    let mut bd = vec![0];
                    bd.extend(cuts.into_iter().filter(|&b| b < kmax));
                    bd.push(kmax);
                    let q = r[j - 1] / r[j];
                    for w in bd.windows(2) {
                        for b in w[0]..w[1].min(23) {
                            if q.bit(b) && sy + b - w[0] == 128 {
                                occupied += 1;
                                assert!(g <= 15 && (g & 16) == 0);
                                hits.push((col, rec.kind, sz, sy, g, b, w[0], w[1]));
                            }
                        }
                    }
                }
                _ => {}
            }
            if matches!(rec.kind, Kind::Hr | Kind::Ht | Kind::Dq) { j += 1; }
        }
        if !hits.is_empty() && predict_n(x, &sc, 24, KP, QB, TOT, NQ, EMAX, N).is_none() {
            for h in hits {
                let kind = match h.1 { Kind::Hr => "HR", Kind::Ht => "HT", Kind::Dl => "DL", _ => unreachable!() };
                clean.entry(kind).or_insert_with(|| format!("x={x:x} col={} sz={} sy={} g={} b={} chunk=[{},{}]", h.0,h.2,h.3,h.4,h.5,h.6,h.7));
            }
        }
    }
    eprintln!("B3_PRED_SIZE inputs={limit} plays={plays} x128_occupied={occupied} clean_fixtures={clean:?}");
    assert!(occupied > 0 && !clean.is_empty());
}

/// B3: predictor-clean HT stage-5 logical park fixtures at physical K2.
#[test]
#[ignore = "explicit B3_STAGE5_N finite fixture search"]
fn b3_find_stage5_clean_fixtures() {
    use super::frogdrop_sched::{from_text, predict_n, sample, shot, Kind, L0};
    use super::pointadd_frogdrop::{SCHED_FROGDROP, KP, QB, TOT, NQ, EMAX, N};
    super::bake_knobs();
    std::env::set_var("QUOT_PRED_SPLITK", "2");
    std::env::set_var("QUOT_PRED_RES_S", "6");
    std::env::set_var("QUOT_PRED_SWCHK", "exact");
    std::env::set_var("QUOT_PRED_DLCHK", "exact");
    let sc = from_text(SCHED_FROGDROP);
    if let Ok(hx) = std::env::var("FROGDROP_X") {
        let x = N::from_str_radix(&hx, 16).unwrap();
        eprintln!("B3_STAGE5_PROBE x={x:x} verdict={:?}", predict_n(x, &sc, 24, KP, QB, TOT, NQ, EMAX, N));
    }
    let limit = std::env::var("B3_STAGE5_N").ok().and_then(|v| v.parse().ok()).unwrap_or(1_000_000);
    let mut found = std::collections::BTreeMap::<usize, String>::new();
    for (i, x) in sample(limit, 0xB357A6E5).into_iter().enumerate() {
        let sh = shot(x, L0);
        let (r, _) = euclid_seq(x);
        let mut j = 1usize;
        let mut hits = vec![];
        for (col, rec) in sh.recs.iter().enumerate() {
            if rec.kind == Kind::Ht {
                let sy = blen(&r[j]);
                let q = r[j - 1] / r[j];
                for b in 2..blen(&q).min(23) {
                    if q.bit(b) {
                        let pos = sy + b - 2;
                        if (128..=134).contains(&pos) {
                            hits.push((pos, col, sy, b));
                        }
                    }
                }
            }
            if matches!(rec.kind, Kind::Hr | Kind::Ht | Kind::Dq) { j += 1; }
        }
        if hits.is_empty() || predict_n(x, &sc, 24, KP, QB, TOT, NQ, EMAX, N).is_some() { continue; }
        for (pos, col, sy, b) in hits {
            found.entry(pos).or_insert_with(|| format!("x={x:x} col={col} sy={sy} b={b}"));
        }
        if found.len() == 7 {
            eprintln!("B3_STAGE5_CLEAN screened={} found={found:?}", i + 1);
            return;
        }
    }
    eprintln!("B3_STAGE5_CLEAN screened={limit} found={found:?}");
    assert_eq!(found.len(), 7, "not enough clean K2 stage-5 fixtures");
}

#[test]
#[ignore = "explicit B3_FIXTURE_N finite fixture search"]
fn b3_find_first_ht_and_chunk_cut_fixtures() {
    use super::frogdrop_sched::{shot, predict_n, from_text, sample, Kind, L0};
    use super::pointadd_frogdrop::{SCHED_FROGDROP, KP, QB, TOT, NQ, EMAX, N};
    super::bake_knobs();
    std::env::set_var("QUOT_PRED_SPLITK", "2");
    std::env::set_var("QUOT_PRED_RES_S", "6");
    std::env::set_var("QUOT_PRED_SWCHK", "exact");
    std::env::set_var("QUOT_PRED_DLCHK", "exact");
    let sc = from_text(SCHED_FROGDROP);
    let mut found = std::collections::BTreeMap::<&str, String>::new();
    let limit = std::env::var("B3_FIXTURE_N").ok().and_then(|v| v.parse().ok()).unwrap_or(250_000);
    for x in sample(limit, 0xB3678C08) {
        let sh = shot(x, L0);
        let (rr, _) = euclid_seq(x);
        let mut j = 1usize;
        let mut kinds = Vec::new();
        for (col, rec) in sh.recs.iter().enumerate() {
            if rec.kind == Kind::Ht && col > 0 && sh.recs[col - 1].kind == Kind::Sw && rec.sz < 128 {
                kinds.push(("first_ht_t_lt128", col));
            }
            if matches!(rec.kind, Kind::Hr | Kind::Ht) && j + 1 < rr.len() {
                let q = rr[j - 1] / rr[j];
                if q.bit(8) { kinds.push(("cut_8", col)); }
                if q.bit(16) { kinds.push(("cut_16", col)); }
            }
            if matches!(rec.kind, Kind::Hr | Kind::Ht | Kind::Dq) { j += 1; }
        }
        if !kinds.is_empty() && predict_n(x, &sc, 24, KP, QB, TOT, NQ, EMAX, N).is_none() {
            for (kind, col) in kinds { found.entry(kind).or_insert_with(|| format!("x={x:x} col={col}")); }
            if found.len() == 3 { break; }
        }
    }
    eprintln!("B3_FIRST_HT_CUT_FIXTURES clean={found:?} sample_limit={limit}");
    assert_eq!(found.len(), 3, "missing model-clean first HT or K2 chunk-cut fixture");
}

/// Find model-clean set quotient bits at the fifth reserve lane and Y-top boundary.
#[test]
#[ignore = "explicit B2_FIXTURE_N sample budget"]
fn b2_find_stage5_park_fixtures() {
    use super::frogdrop_sched::{shot, Kind, L0};
    b2_bake_pred_knobs();
    let sc = super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP);
    let mut found = std::collections::BTreeMap::<usize, String>::new();
    let limit = std::env::var("B2_FIXTURE_N").ok().and_then(|v| v.parse().ok()).unwrap_or(1_000_000);
    for x in super::frogdrop_sched::sample(limit, 5) {
        let sh = shot(x, L0);
        let (rr, _) = euclid_seq(x);
        let mut j = 1usize;
        let mut hits = Vec::new();
        for rec in &sh.recs {
            if matches!(rec.kind, Kind::Ht) && j + 1 < rr.len() {
                let q = rr[j - 1] / rr[j];
                hits.extend((3..blen(&q)).filter(|&kb| q.bit(kb))
                    .map(|kb| rec.sy.min(128) + kb - 3).filter(|pos| (128..=134).contains(pos)));
            }
            if matches!(rec.kind, Kind::Hr | Kind::Ht | Kind::Dq) { j += 1; }
        }
        if !hits.is_empty()
            && super::frogdrop_sched::predict_n(x, &sc, 24, 24, 23, 83, 128, 31, 262).is_none() {
            for pos in hits { found.entry(pos).or_insert_with(|| format!("{x:x}")); }
            if found.len() == 7 { break; }
        }
    }
    eprintln!("B2_STAGE5_PARK_FIXTURES clean={found:?} sample_limit={limit}");
    assert_eq!(found.len(), 7, "missing model-clean K3 park boundary fixture");
}

#[test]
#[ignore = "explicit FROGDROP_X hex fixture"]
fn b2_packed_x_phase() {
    super::bake_knobs();
    let x = N::from_str_radix(&std::env::var("FROGDROP_X").expect("hex fixture"), 16).unwrap();
    let dy = N::from_str_radix("564b1a76853d2295410e7ccd2aa128c52f84c1e577ab7011b206b43d4e9a70cb", 16).unwrap();
    frogdrop_col_trace_impl(x, dy, true);
}

#[test]
#[ignore = "explicit B2_FIXTURE_N sample budget"]
fn b2_find_first_ht_and_chunk_cut_fixtures() {
    use super::frogdrop_sched::{shot, Kind, L0};
    b2_bake_pred_knobs();
    let sc = super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP);
    let mut found = std::collections::BTreeMap::<&str, String>::new();
    let limit = std::env::var("B2_FIXTURE_N").ok().and_then(|v| v.parse().ok()).unwrap_or(1_000_000);
    for x in super::frogdrop_sched::sample(limit, 9) {
        let sh = shot(x, L0);
        let (rr, _) = euclid_seq(x);
        let mut j = 1usize;
        let mut kinds = Vec::new();
        for (col, rec) in sh.recs.iter().enumerate() {
            if matches!(rec.kind, Kind::Ht) && col > 0 && sh.recs[col - 1].kind == Kind::Sw
                && rec.sz < 128 { kinds.push(("first_ht_t_lt128", col)); }
            if matches!(rec.kind, Kind::Hr | Kind::Ht) && j + 1 < rr.len() {
                let q = rr[j - 1] / rr[j];
                if q.bit(9) { kinds.push(("cut_9", col)); }
                if q.bit(18) { kinds.push(("cut_18", col)); }
            }
            if matches!(rec.kind, Kind::Hr | Kind::Ht | Kind::Dq) { j += 1; }
        }
        if !kinds.is_empty()
            && super::frogdrop_sched::predict_n(x, &sc, 24, 24, 23, 83, 128, 31, 262).is_none() {
            for (kind, col) in kinds { found.entry(kind).or_insert_with(|| format!("x={x:x} col={col}")); }
            if found.len() == 3 { break; }
        }
    }
    eprintln!("B2_FIRST_HT_CHUNK_FIXTURES clean={found:?} sample_limit={limit}");
    assert_eq!(found.len(), 3, "missing model-clean first-HT or chunk-cut fixture");
}

pub(crate) fn frogdrop_col_trace_impl(x: N, dy: N, varied: bool) {
    use super::frogdrop_sched::{from_text, shot, Kind, L0};
    use super::frogdrop_col::{column_pl, pool_size, ColScr, Fd};
    use super::pointadd_frogdrop::*;
    use super::payload::NP;
    let mut payload_rng = Rng::new(0xd2_697_24);
    let dys: Vec<N> = (0..64).map(|s| if varied && s > 0 {
        payload_rng.below(256) % super::frogdrop_sched::p()
    } else { dy }).collect();
    let sh = shot(x, L0);
    let (rr, tt) = euclid_seq(x);
    let nn = rr.len() - 1;
    eprintln!("TRACE x {:x}: N {nn}, predictor {:?}", x,
              super::frogdrop_sched::predict(x, &from_text(SCHED_FROGDROP), K, KP, QB, TOT, NQ, EMAX));
    let mut b = B::new();
    if std::env::var_os("D2_NOOPT").is_some() {
        b.cancel_simple_pairs = false;
        b.cancel_commuting_pairs = false;
    }
    let xq = b.alloc_n(256);
    let pl = b.alloc_n(NP);
    let mut ring: Vec<QubitId> = xq.to_vec();
    ring.extend(b.alloc_n(N - 256));
    let q = b.alloc_n(NQ);
    let cnt = q[NQ - CNTB..].to_vec();
    let mut fd = Fd { ring, q, sy: b.alloc_n(SW), sx: b.alloc_n(SW), ph: b.alloc(), cnt };
    let pool = b.alloc_n(pool_size(KP, QB, SW));
    b.x(fd.ring[N - 1]);
    b.x(fd.sy[0]);
    let (cols, _b0, _last) = col_pars(&from_text(SCHED_FROGDROP));
    let plc = pl_col(&pl, &fd, &pool);
    let mut bounds = vec![(b.ops.len(), fd.sy.clone())];
    let stop_col: usize = std::env::var("FROGDROP_STOPCOL").ok().and_then(|v| v.parse().ok()).unwrap_or(usize::MAX);
    let stop_stage: usize = std::env::var("FROGDROP_STOPSTAGE").ok().and_then(|v| v.parse().ok()).unwrap_or(99);
    let trace_cols: usize = std::env::var("FROGDROP_TRACE_COLS").ok().and_then(|v| v.parse().ok()).unwrap_or(cols.len());
    for (ci, cp) in cols.iter().enumerate() {
        let sc = ColScr::carve_col(&pool, &fd.sx, &pl, KP, QB, TAIL, cp.sz.1 > 255);
        if ci == stop_col {
            super::frogdrop_col::column_upto(&mut b, &mut fd, cp, &sc, stop_stage, Some(&plc));
            // dump the state of shot 0 after the partial column and stop
            let (aq, nb, _, _) = analyze_ops(b.ops.iter());
            let mut h = sha3::Shake256::default();
            h.update(b"frogdrop-trace");
            let mut xof = h.finalize_xof();
            let mut sim = Simulator::new((b.width() as usize).max(aq as usize), (nb as usize).max(1), &mut xof);
            for s in 0..64 { put(&mut sim.qubits, &xq, s, &x); put(&mut sim.qubits, &pl[..256], s, &dys[s]); }
            if std::env::var_os("D2_WATCH_STAGE5").is_some() {
                let marks = super::frogdrop_col::MARKS.with(|m| m.borrow().clone());
                let mut start = 0;
                for (i, (_, st)) in marks.iter().enumerate() { if *st == 0 { start = i; } }
                let a = marks[start..].iter().find(|(_, st)| *st == 4).unwrap().0;
                let z = marks[start..].iter().find(|(_, st)| *st == 5).unwrap().0;
                sim.apply_iter(b.ops[..a].iter());
                let watched = pl[105].0 as usize;
                for i in a..z {
                    let before = sim.qubits[watched] & 1;
                    let ctl = (sim.qubits[sc.g.0 as usize] & 1, sim.qubits[fd.sx[7].0 as usize] & 1,
                               sim.qubits[fd.ph.0 as usize] & 1, sim.qubits[sc.sw.0 as usize] & 1);
                    sim.apply_iter(b.ops[i..i + 1].iter());
                    if sim.qubits[watched] & 1 != before {
                        eprintln!("D2_WATCH_STAGE5 op={i} {:?} act_c_ph_sw={ctl:?} payload105 {}->{}",
                                  b.ops[i], before, sim.qubits[watched] & 1);
                    }
                }
                sim.apply_iter(b.ops[z..].iter());
            } else if std::env::var_os("QUOT_PL_WATCH").is_some() {
                // agent_lowq_quot: payload lanes changed per mark segment of this column (FD_MARK=1)
                let marks = super::frogdrop_col::MARKS.with(|m| m.borrow().clone());
                let c0 = bounds.last().unwrap().0;
                sim.apply_iter(b.ops[..c0].iter());
                let snap = |qs: &[u64]| -> Vec<u64> { pl.iter().map(|q| qs[q.0 as usize]).collect() };
                let mut prev = snap(&sim.qubits);
                let mut pos = c0;
                let mut segs: Vec<(usize, usize)> = marks.iter().filter(|(o, _)| *o >= c0).copied().collect();
                segs.push((b.ops.len(), 99999));
                let mut last_st = 0;
                for (o, st) in segs {
                    sim.apply_iter(b.ops[pos..o].iter());
                    pos = o;
                    let cur = snap(&sim.qubits);
                    let nl = (0..pl.len()).filter(|&i| cur[i] != prev[i]).count();
                    let shots: u64 = (0..pl.len()).fold(0, |a, i| a | (cur[i] ^ prev[i]));
                    if nl > 0 {
                        eprintln!("PLWATCH marks {last_st}->{st} (op {o}): {nl} payload lanes changed, shots {:016x}", shots);
                    }
                    // the Euclid state is shot-independent (one x): a lane split across shots outside the payload
                    let plset: std::collections::BTreeSet<u64> = pl.iter().map(|q| q.0 as u64).collect();
                    let mixed: Vec<usize> = (0..sim.qubits.len()).filter(|&i| !plset.contains(&(i as u64))
                        && sim.qubits[i] != 0 && sim.qubits[i] != u64::MAX).collect();
                    if !mixed.is_empty() {
                        eprintln!("PLWATCH mixed after mark {st} (op {o}): {} lanes {:?}", mixed.len(), &mixed[..mixed.len().min(20)]);
                    }
                    if std::env::var_os("QUOT_WATCH_POOL").is_some() {
                        let pv: Vec<u64> = pool.iter().map(|q| sim.qubits[q.0 as usize] & 1).collect();
                        let ccnt = get(&sim.qubits, &fd.cnt, 0);
                        eprintln!("POOLWATCH mark {st}: pool(shot0) {:?} ph {} cnt {} sx {:x} sy {:x}", pv,
                                  sim.qubits[fd.ph.0 as usize] & 1, ccnt, get(&sim.qubits, &fd.sx, 0), get(&sim.qubits, &fd.sy, 0));
                    }
                    last_st = st;
                    prev = cur;
                }
            } else { sim.apply_iter(b.ops.iter()); }
            let g = |v: &[QubitId]| get(&sim.qubits, v, 0);
            let mut tp = N::ZERO;
            for m in 0..N { if (sim.qubits[fd.ring[N - 1 - m].0 as usize] & 1) == 1 { tp |= N::from(1u64) << m; } }
            eprintln!("STOP col {ci} stage {stop_stage} cp {{hr {} ht {} sw {} dn {} fin {} sz {:?} sy {:?} smax {:?} m {} xw {} pht {} psw {}}}",
                      cp.hr, cp.ht, cp.sw, cp.dn, cp.fin, cp.sz, cp.sy, cp.smax, cp.m, cp.xw, cp.pht, cp.psw);
            eprintln!("  ring bottom {:x}", g(&fd.ring[..160]));
            eprintln!("  ring reversed-from-top {:x}", tp);
            eprintln!("  Q {:x}  sy {:x} sx {:x} ph {}", g(&fd.q), g(&fd.sy), g(&fd.sx), sim.qubits[fd.ph.0 as usize] & 1);
            eprintln!("  payload low64 {:x} lane11 {}", g(&pl[..64]), sim.qubits[pl[11].0 as usize] & 1);
            let nz: Vec<usize> = (0..pool.len()).filter(|&i| sim.qubits[pool[i].0 as usize] & 1 == 1).collect();
            eprintln!("  pool nonzero idx {:?}  phase {:#x}", nz, sim.phase);
            eprintln!("  model: t[N-1] {:x} t[N-2] {:x} R {:x}", tt[nn - 1], tt[nn - 2], rr[nn - 2]);
            if let Ok(path) = std::env::var("FROGDROP_DUMPSTATE") {
                let bits: String = (0..b.width() as usize).map(|i| if sim.qubits[i] & 1 == 1 { '1' } else { '0' }).collect();
                std::fs::write(&path, bits).unwrap();
            }
            return;
        }
        column_pl(&mut b, &mut fd, cp, &sc, Some(&plc));
        bounds.push((b.ops.len(), fd.sy.clone()));
        if ci + 1 >= trace_cols { break; }
    }
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let mut h = sha3::Shake256::default();
    h.update(b"frogdrop-trace");
    let mut xof = h.finalize_xof();
    let mut sim = Simulator::new((b.width() as usize).max(aq as usize), (nb as usize).max(1), &mut xof);
    for s in 0..64 {
        put(&mut sim.qubits, &xq, s, &x);
        put(&mut sim.qubits, &pl[..256], s, &dys[s]);
    }
    sim.apply_iter(b.ops[..bounds[0].0].iter());
    let mut first_bad = vec![usize::MAX; 64];
    let mut soft_pl = vec![usize::MAX; 64];
    let (mut ph, mut j) = (0u8, 1usize);
    let mut idle = 0usize;
    let payload_model = if std::env::var_os("D2_TRACE_PAYLOAD").is_some() || varied {
        Some(pl_model(&rr, &tt, dys[0]))
    } else { None };
    let payload_models = if varied { Some(dys.iter().map(|&d| pl_model(&rr, &tt, d)).collect::<Vec<_>>()) }
                         else { None };
    let mut payload_form = (false, 1usize);
    let mut payload_first_bad = None;
    let mut prior_phase = sim.phase;
    let d3_owner_col: usize = std::env::var("D3_TRACE_OWNER_COL").ok().and_then(|v| v.parse().ok()).unwrap_or(8);
    for c in 0..bounds.len() - 1 {
        if std::env::var("D2_TRACE_STAGECOL").ok().and_then(|v| v.parse::<usize>().ok()) == Some(c) {
            let lane = std::env::var("D2_TRACE_STAGELANE").ok().and_then(|v| v.parse::<usize>().ok()).unwrap_or(217);
            let marks = super::frogdrop_col::MARKS.with(|m| m.borrow().clone());
            let mut at = bounds[c].0;
            let mut d3_narrow_before: Option<Vec<u64>> = None;
            for &(off, stage) in marks.iter().filter(|(off, _)| *off >= bounds[c].0 && *off <= bounds[c + 1].0) {
                if std::env::var_os("D3_AUDIT_ANDU").is_some() && ([811, 802, 9].contains(&stage) || (901..=924).contains(&stage)) {
                    let mut mismatches = 0usize;
                    let mut checked = 0usize;
                    for i in at..off {
                        let op = &b.ops[i];
                        if op.kind == crate::circuit::OperationType::Hmr {
                            if let Some(cz) = b.ops.get(i + 1).filter(|next| next.kind == crate::circuit::OperationType::CZ
                                    && next.c_condition == op.c_target) {
                                let t = sim.qubits[op.q_target.0 as usize];
                                let a = sim.qubits[cz.q_control1.0 as usize];
                                let bb = sim.qubits[cz.q_target.0 as usize];
                                let wrong = t ^ (a & bb);
                                checked += 1;
                                if wrong != 0 {
                                    mismatches += 1;
                                    if mismatches <= 16 { eprintln!("D3_ANDU_BAD stage={stage} op={i} target={} controls=({}, {}) wrong={wrong:#018x}",
                                        op.q_target.0, cz.q_control1.0, cz.q_target.0); }
                                }
                            }
                        }
                        sim.apply_iter(std::iter::once(op));
                    }
                    eprintln!("D3_ANDU_AUDIT stage={stage} checked={checked} mismatches={mismatches}");
                } else { sim.apply_iter(b.ops[at..off].iter()); }
                at = off;
                if std::env::var_os("D3_TRACE_PHASE").is_some() {
                    if stage == 811 { d3_narrow_before = Some(sim.qubits.clone()); }
                    if stage == 816 {
                        if let Some(before) = &d3_narrow_before {
                            let changed: Vec<_> = before.iter().zip(&sim.qubits).enumerate()
                                .filter_map(|(i, (a, b))| if a != b { Some(i) } else { None }).collect();
                            let non_payload: Vec<_> = changed.iter().copied()
                                .filter(|&i| !pl.iter().any(|q| q.0 as usize == i)).collect();
                            let low_payload: Vec<_> = changed.iter().copied()
                                .filter(|&i| pl[..64].iter().any(|q| q.0 as usize == i)).collect();
                            eprintln!("D3_NARROW_CHANGE total={} changed={changed:?} non_payload={non_payload:?} low_payload={low_payload:?}", changed.len());
                        }
                    }
                }
                let sx_live: Vec<(usize, u64)> = fd.sx.iter().enumerate()
                    .map(|(i, q)| (i, sim.qubits[q.0 as usize]))
                    .filter(|(_, word)| *word != 0).collect();
                let sz_live: Vec<(usize, u64)> = pool[..8].iter().enumerate()
                    .map(|(i, q)| (i, sim.qubits[q.0 as usize]))
                    .filter(|(_, word)| *word != 0).collect();
                eprintln!("D2_STAGE_PAYLOAD col={c} stage={stage} lane={lane} bit={} value={:x} phase={} sx_live={sx_live:?} sz_live={sz_live:?}",
                          sim.qubits[pl[lane].0 as usize] & 1, get(&sim.qubits, &pl[..256], 0), sim.phase);
                if (1501..=1505).contains(&stage) {
                    eprintln!("D5_PARK_STATE col={c} stage={stage} ring19={:#018x} sx1={:#018x} act={:#018x} ph={:#018x} qlow={:x}",
                        sim.qubits[fd.ring[19].0 as usize], sim.qubits[fd.sx[1].0 as usize],
                        sim.qubits[pool[8].0 as usize], sim.qubits[fd.ph.0 as usize],
                        get(&sim.qubits, &fd.q[..24], 0));
                }
                if c == d3_owner_col { eprintln!("D3_OLD_SX stage={stage} value={:x} high7={:#018x}",
                    get(&sim.qubits, &fd.sy, 0), sim.qubits[fd.sy[7].0 as usize]); }
                if c == d3_owner_col && [1402,1404,1405,1403].contains(&stage) { eprintln!("D3_COMPARE_STATE stage={stage} qlow={:x} q11={:#018x} c0={:#018x} pzero={:#018x} act={:#018x} sy={:x}",
                    get(&sim.qubits, &fd.q[..16], 0), sim.qubits[fd.q[11].0 as usize],
                    sim.qubits[pool[11].0 as usize], sim.qubits[pool[10].0 as usize], sim.qubits[pool[12].0 as usize], get(&sim.qubits, &fd.sx, 0)); }
                if c == d3_owner_col && [8, 901, 904, 914, 917, 921, 9, 1400, 1402, 1403].contains(&stage) {
                    let mut top = N::ZERO;
                    for k in 0..256 { if sim.qubits[fd.ring[fd.ring.len()-1-k].0 as usize] & 1 != 0 { top |= N::from(1u64) << k; } }
                    eprintln!("D3_MAP_STATE stage={stage} bottom={:x} top={:x} q={:x} sy={:x} sx={:x} pool1={:#x} want_t={:x}",
                        get(&sim.qubits, &fd.ring[..160], 0), top, get(&sim.qubits, &fd.q, 0),
                        get(&sim.qubits, &fd.sy, 0), get(&sim.qubits, &fd.sx, 0), sim.qubits[pool[1].0 as usize], tt[j+1]);
                }
                if let Some(pm) = &payload_model {
                    let e = pm.d_pre[j] / rr[j];
                    let wpost = pm.w_pre[j].wrapping_add(e.wrapping_mul(tt[j]));
                    let want = if stage == 2 { Some(pl_lanes_off(&pm.d_pre[j + 1], &!wpost, blen(&rr[j]))) }
                               else if (1000..1100).contains(&stage) {
                                   let kk = stage - 1000;
                                   let qpart = (rr[j - 1] / rr[j]) & ((N::from(1u64) << (kk + 1)) - N::from(1u64));
                                   let wn = qpart.wrapping_mul(tt[j]).wrapping_add(!wpost);
                                   Some(pl_lanes_off(&pm.d_pre[j + 1], &wn, blen(&rr[j])))
                               }
                               else if stage == 4 { Some(pl_lanes_off(&pm.d_pre[j + 1], &pm.w_next[j], blen(&rr[j]))) }
                               else if stage == 8 { Some(pl_lanes_pre(&pm.d_pre[j + 1], &pm.w_pre[j + 1], blen(&tt[j + 1]))) }
                               else { None };
                    if let Some(want) = want {
                        let bad: Vec<usize> = (0..pl.len()).filter(|&i| ((sim.qubits[pl[i].0 as usize] & 1) as u8) != want[i]).collect();
                        eprintln!("D2_STAGE_MODEL col={c} stage={stage} bad={:?} total={} want_lane={}",
                                  &bad[..bad.len().min(16)], bad.len(), want[lane]);
                    }
                }
            }
            sim.apply_iter(b.ops[at..bounds[c + 1].0].iter());
        } else if std::env::var_os("D4B_PARK_AUDIT").is_some() {
            let windows = super::midg::D4B_WINDOWS.with(|w| w.borrow().clone());
            let mut at = bounds[c].0;
            for &(start, end, kind, act) in windows.iter().filter(|w| w.0 >= bounds[c].0 && w.1 <= bounds[c + 1].0) {
                assert!(at <= start && start <= end && end <= bounds[c + 1].0);
                sim.apply_iter(b.ops[at..start].iter());
                let active = sim.qubits[act.0 as usize];
                let mut touched = vec![false; b.width() as usize];
                for op in &b.ops[start..end] {
                    for q in [op.q_target.0, op.q_control1.0, op.q_control2.0] {
                        if (q as usize) < touched.len() { touched[q as usize] = true; }
                    }
                }
                let fixed = |bank: &[QubitId]| -> (Vec<usize>, Vec<usize>) {
                    let mut z = vec![];
                    let mut o = vec![];
                    for (i, q) in bank.iter().enumerate() {
                        let qi = q.0 as usize;
                        if touched[qi] { continue; }
                        let bits = sim.qubits[qi] & active;
                        if bits == 0 { z.push(i); }
                        if bits == active { o.push(i); }
                    }
                    (z, o)
                };
                if active != 0 {
                    let (rz, ro) = fixed(&fd.ring);
                    let (pz, po) = fixed(&pl);
                    let (qz, qo) = fixed(&fd.q);
                    let (syz, syo) = fixed(&fd.sy);
                    let (sxz, sxo) = fixed(&fd.sx);
                    let (poolz, poolo) = fixed(&pool);
                    eprintln!("D4B_WINDOW col={c} kind={kind} start={start} end={end} active={active:#018x} ring0={rz:?} ring1={ro:?} payload0={pz:?} payload1={po:?} Q0={qz:?} Q1={qo:?} sy0={syz:?} sy1={syo:?} sx0={sxz:?} sx1={sxo:?} pool0={poolz:?} pool1={poolo:?}");
                }
                sim.apply_iter(b.ops[start..end].iter());
                at = end;
            }
            sim.apply_iter(b.ops[at..bounds[c + 1].0].iter());
        } else { sim.apply_iter(b.ops[bounds[c].0..bounds[c + 1].0].iter()); }
        if std::env::var_os("D3_TRACE_PHASE").is_some() && sim.phase != prior_phase {
            eprintln!("D3_PHASE column={c} before={prior_phase} after={}", sim.phase);
        }
        prior_phase = sim.phase;
        // model state after column c
        let rec = sh.rec(c);
        // A delayed no-step Dq keeps the offset form for one more column;
        // its HT narrow gate is explicitly suppressed until the next column.
        if payload_form.0 && rec.kind != Kind::Dq { payload_form = (false, payload_form.1 + 1); }
        let mut first_ht = false;
        let mut after_dl = false;
        match rec.kind {
            Kind::Hr => { j += 1; payload_form = (false, j); },
            Kind::Ht => { payload_form = (true, j); j += 1; },
            Kind::Sw => { ph = 1; first_ht = true; }
            Kind::Dl => { ph = 1; after_dl = true; payload_form = (true, j); }
            Kind::Dq => j += 1,
            Kind::Idle => idle += 1,
        }
        if let Some(pm) = &payload_model {
            let (off, pj) = payload_form;
            if payload_first_bad.is_none() && pj <= pm.last {
                let want = if off { pl_lanes_off(&pm.d_pre[pj + 1], &pm.w_next[pj], blen(&rr[pj])) }
                           else { pl_lanes_pre(&pm.d_pre[pj], &pm.w_pre[pj], blen(&tt[pj])) };
                let bad: Vec<usize> = (0..pl.len()).filter(|&i| ((sim.qubits[pl[i].0 as usize] & 1) as u8) != want[i]).collect();
                if !bad.is_empty() {
                    payload_first_bad = Some(c);
                    eprintln!("D2_PAYLOAD_BAD column={c} kind={:?} form={payload_form:?} lanes={:?} total={}",
                              rec.kind, &bad[..bad.len().min(16)], bad.len());
                }
            }
        }
        if let Some(models) = &payload_models {
            let (off, pj) = payload_form;
            for s in 0..64 {
                let pm = &models[s];
                if pj > pm.last { continue; }
                let want = if off { pl_lanes_off(&pm.d_pre[pj + 1], &pm.w_next[pj], blen(&rr[pj])) }
                           else { pl_lanes_pre(&pm.d_pre[pj], &pm.w_pre[pj], blen(&tt[pj])) };
                let bad: Vec<usize> = (0..pl.len()).filter(|&i| ((sim.qubits[pl[i].0 as usize] >> s) & 1) as u8 != want[i]).collect();
                if std::env::var_os("QUOT_D4_SOFT").is_some() {
                    if !bad.is_empty() && soft_pl[s] == usize::MAX {
                        soft_pl[s] = c;
                        eprintln!("SOFT payload shot={s} col={c} kind={:?} nbad {} first_bad={:?}", rec.kind, bad.len(),
                                  &bad[..bad.len().min(12)]);
                    }
                    continue;
                }
                assert!(bad.is_empty(), "d2 packed payload shot={s} col={c} kind={:?} first_bad={:?}",
                        rec.kind, &bad[..bad.len().min(12)]);
            }
        }
        let done = c + 1 >= sh.recs.len();
        let (z, qv, top) = if done {
            // idle columns completed after the last step (agent_lowq_quot: less the controlled-map columns, whose map
            // a done shot skips)
            let k = c + 1 - sh.recs.len() - super::frogdrop_col::map_ctrl_skipped_by(sh.recs.len() - 1, c);
            let r_ = rr[nn - 2];
            if k % 2 == 0 { (tt[nn - 1], r_, N::from(1u64)) } else { (tt[nn - 2], N::from(1u64), r_) }
        } else if ph == 0 {
            (rr[j], tt[j - 1], tt[j])
        } else if first_ht {
            (tt[j], rr[j], rr[j - 1])
        } else if after_dl {
            // a delayed shot after its crossing column: bottom t_j, Q r_j, top r_{j+1}, sw = 1
            (tt[j], rr[j], rr[j + 1])
        } else {
            (tt[j], rr[j - 1], rr[j])
        };
        let _ = idle;
        let mut want_ring = vec![0u8; N];
        for i in 0..256 { want_ring[i] = z.bit(i) as u8; }
        for m in 0..top.bit_len() { want_ring[N - 1 - m] = top.bit(m) as u8; }
        for s in 0..64 {
            if first_bad[s] != usize::MAX { continue; }
            let gr: Vec<u8> = fd.ring.iter().map(|qq| ((sim.qubits[qq.0 as usize] >> s) & 1) as u8).collect();
            let ok_ring = gr == want_ring;
            let qlow = if done { get(&sim.qubits, &fd.q[..NQ - CNTB], s) } else { get(&sim.qubits, &fd.q, s) };
            let ok_q = qlow == qv;
            let syv = get(&sim.qubits, &bounds[c + 1].1, s);
            let ok_sy = syv == N::from(top.bit_len() as u64);
            let phv = (sim.qubits[fd.ph.0 as usize] >> s) & 1;
            let ok_ph = done || phv == ph as u64;
            let swq = pool[super::frogdrop_col::SZB];
            let pz = pool.iter().all(|qq| (sim.qubits[qq.0 as usize] >> s) & 1 == (after_dl && *qq == swq) as u64);
            if !(ok_ring && ok_q && ok_sy && ok_ph && pz) {
                first_bad[s] = c;
                if std::env::var_os("QUOT_D4_SOFT").is_some() {
                    let qq = if j >= 1 && j < rr.len() && rr[j] != N::ZERO { rr[j - 1] / rr[j] } else { N::ZERO };
                    let pnz: Vec<usize> = (0..pool.len()).filter(|&i| (sim.qubits[pool[i].0 as usize] >> s) & 1 == 1).collect();
                    let sxv = get(&sim.qubits, &fd.sx, s);
                    eprintln!("SOFTSTATE shot {s} col {c} rec {:?} j {j} ph {ph} q(r_{{j-1}}/r_j) bl {} pool nz {:?} sx {:x}", rec,
                              qq.bit_len(), pnz, sxv);
                }
                if s < 4 {
                    let bad_ring: Vec<usize> = (0..N).filter(|&i| gr[i] != want_ring[i]).collect();
                    eprintln!("shot {s}: first bad column {c} kind {:?} (rec {:?}) ring {ok_ring} q {ok_q} sy {ok_sy} ({} want {}) ph {ok_ph} pool0 {pz}; bad ring lanes {:?}",
                              rec.kind, rec, syv, top.bit_len(), &bad_ring[..bad_ring.len().min(12)]);
                    eprintln!("   q got {:x} want {:x}", qlow, qv);
                    let bot = get(&sim.qubits, &fd.ring[..257], s);
                    let mut tp = N::ZERO;
                    for m in 0..(N - 257) { if gr[N - 1 - m] == 1 { tp |= N::from(1u64) << m; } }
                    eprintln!("   ring[..257] {:x} (want {:x}); top 31 lanes {:x} (want top {:x}); j {j} ph {ph}", bot, z, tp, top);
                    let idx = |v: &N| (0..rr.len()).find(|&i| rr[i] == *v).map(|i| format!("r{i}"))
                        .or((0..tt.len()).find(|&i| tt[i] == *v).map(|i| format!("t{i}"))).unwrap_or("?".into());
                    eprintln!("   q is {}, bottom is {}", idx(&qlow), idx(&bot));
                }
            }
        }
    }
    let mut hist = std::collections::BTreeMap::new();
    for &c in &first_bad { *hist.entry(c).or_insert(0) += 1; }
    eprintln!("TRACE first-bad histogram (column -> shots): {:?}", hist);
    if payload_model.is_some() { eprintln!("D2_PAYLOAD_FIRST_BAD {payload_first_bad:?}"); }
    if varied {
        assert!(first_bad.iter().all(|&c| c == usize::MAX), "d2 packed Euclid state");
        assert_eq!(sim.phase, 0, "d2 packed phase");
        eprintln!("D2_HR_DIGIT_N280_PACKED_PASS shots=64 columns={} arbitrary_payload=true phase=0", bounds.len() - 1);
    }
}

/// End-to-end hunt: one streamed point-add build, FROGDROP_BATCHES batches of 64 random point pairs on 8 threads
/// (batch seeds FROGDROP_SEED0 + i, own measurement randomness). Prints failing pairs; totals at the end.
#[test]
#[ignore = "tool"]
fn payload_e2e_hunt() {
    use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
    use crate::circuit::{QubitOrBit, BitId};
    let nbatch: u64 = std::env::var("FROGDROP_BATCHES").ok().and_then(|s| s.parse().ok()).unwrap_or(16);
    let seed0: u64 = std::env::var("FROGDROP_SEED0").ok().and_then(|s| s.parse().ok()).unwrap_or(5000);
    let path = std::env::temp_dir().join(format!("pl_e2eh_{}.bin", std::process::id()));
    std::env::set_var("LOWQ_EXACT_STREAM_PATH", &path);
    let mut b = B::new();
    std::env::remove_var("LOWQ_EXACT_STREAM_PATH");
    let (xq, yq) = super::pointadd_frogdrop::point_add_pl(&mut b);
    let nops = b.finish_stream().unwrap();
    let nq = b.width() as usize;
    let nbits = (b.bits_end() as usize).max(20000);
    eprintln!("E2EH ops {nops} width {nq} peak {} emitted tof {} bits {nbits}", b.peak, b.tof);
    type U = ruint::aliases::U256;
    let to_u = |v: &N| -> U { U::from_limbs(v.as_limbs()[0..4].try_into().unwrap()) };
    let hx = |h: &str| U::from_str_radix(h, 16).unwrap();
    let curve = WeierstrassEllipticCurve {
        modulus: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
        a: U::ZERO, b: U::from(7u64),
        gx: hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
        gy: hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
        order: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
    };
    let regs: Vec<Vec<QubitOrBit>> = vec![
        xq.iter().map(|&q| QubitOrBit::Qubit(q)).collect(),
        yq.iter().map(|&q| QubitOrBit::Qubit(q)).collect(),
        (0..256).map(|i| QubitOrBit::Bit(BitId(1 + 2 * 1000 + i as u64))).collect(),
        (0..256).map(|i| QubitOrBit::Bit(BitId(1 + 3 * 1000 + i as u64))).collect(),
    ];
    let regq: std::collections::HashSet<u64> = xq.iter().chain(yq.iter()).map(|q| q.0).collect();
    // FROGDROP_FS: the evaluator's own 9024 Fiat-Shamir shots of this build (built nonce), in batches of 64
    let fs_cases: Option<Vec<((U, U), (U, U), (U, U))>> = if std::env::var("FROGDROP_FS").is_ok() {
        use sha3::digest::{ExtendableOutput, Update, XofReader};
        let l = nops as usize;
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
        let mut seen = 0usize;
        stream_ops(&path, |ops| { for op in ops { if seen < l { upd(&mut pre, op); } seen += 1; } });
        let mut xof = pre.finalize_xof();
        let mut v = vec![];
        for _ in 0..9024 {
            let mut rb = [[0u8; 32]; 2];
            xof.read(&mut rb[0]);
            xof.read(&mut rb[1]);
            let t = curve.mul(curve.gx, curve.gy, U::from_le_bytes(rb[0]));
            let o = curve.mul(curve.gx, curve.gy, U::from_le_bytes(rb[1]));
            let e = curve.add(t.0, t.1, o.0, o.1);
            v.push((t, o, e));
        }
        eprintln!("E2EH FS mode: {} shots", v.len());
        Some(v)
    } else { None };
    let fs_cases = &fs_cases;
    let nbatch = if fs_cases.is_some() { 141 } else { nbatch };
    let next = std::sync::atomic::AtomicU64::new(0);
    let tot_bad = std::sync::atomic::AtomicU64::new(0);
    let tot_ph = std::sync::atomic::AtomicU64::new(0);
    let tot_anc = std::sync::atomic::AtomicU64::new(0);
    let tot_tof = std::sync::atomic::AtomicU64::new(0);
    std::thread::scope(|scope| {
        for _ in 0..8 {
            scope.spawn(|| loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                if i >= nbatch { break; }
                let seed = seed0 + i;
                let mut rng = Rng::new(seed);
                let mut cases = vec![];
                if let Some(fc) = fs_cases { cases = fc[(i as usize) * 64..(i as usize) * 64 + 64].to_vec(); }
                while cases.len() < 64 {
                    let k1 = to_u(&(rng.below(250) + N::from(1u64)));
                    let k2 = to_u(&(rng.below(250) + N::from(1u64)));
                    let t = curve.mul(curve.gx, curve.gy, k1);
                    let o = curve.mul(curve.gx, curve.gy, k2);
                    let e = curve.add(t.0, t.1, o.0, o.1);
                    cases.push((t, o, e));
                }
                let mut h = sha3::Shake256::default();
                h.update(b"frogdrop-e2eh");
                h.update(&seed.to_le_bytes());
                let mut xof = h.finalize_xof();
                let mut sim = crate::sim::Simulator::new(nq, nbits, &mut xof);
                for (k, (t, o, _)) in cases.iter().enumerate() {
                    sim.set_register(&regs[0], t.0, k);
                    sim.set_register(&regs[1], t.1, k);
                    sim.set_register(&regs[2], o.0, k);
                    sim.set_register(&regs[3], o.1, k);
                }
                // the simulator's condition stack is local to one apply_iter call: cut chunks only at depth 0
                {
                    use crate::circuit::OperationType as K;
                    let mut carry: Vec<crate::circuit::Op> = vec![];
                    stream_ops(&path, |ops| {
                        carry.extend_from_slice(ops);
                        let (mut depth, mut cut) = (0i64, 0usize);
                        for (i, op) in carry.iter().enumerate() {
                            match op.kind { K::PushCondition => depth += 1, K::PopCondition => depth -= 1, _ => {} }
                            if depth == 0 { cut = i + 1; }
                        }
                        sim.apply_iter(carry[..cut].iter());
                        carry.drain(..cut);
                    });
                    assert!(carry.is_empty(), "unbalanced conditions at stream end");
                }
                let mut bad = 0u64;
                let mut ancm = 0u64;
                for q in 0..nq { if !regq.contains(&(q as u64)) { ancm |= sim.qubits[q]; } }
                for (k, (t, o, e)) in cases.iter().enumerate() {
                    let gx = sim.get_register(&regs[0], k);
                    let gy = sim.get_register(&regs[1], k);
                    let pk = (sim.phase >> k) & 1;
                    let ak = (ancm >> k) & 1;
                    if gx != e.0 || gy != e.1 || pk != 0 || ak != 0 {
                        bad += 1;
                        eprintln!("E2EH_FAIL seed {seed} batch {i} shot {k} (fs index {}) x_ok", i as usize * 64 + k);
                        eprintln!("   x_ok {} y_ok {} phase {pk} anc {ak} t ({:x},{:x}) o ({:x},{:x})",
                                  gx == e.0, gy == e.1, t.0, t.1, o.0, o.1);
                    }
                }
                tot_bad.fetch_add(bad, std::sync::atomic::Ordering::SeqCst);
                tot_ph.fetch_add(sim.phase.count_ones() as u64, std::sync::atomic::Ordering::SeqCst);
                tot_anc.fetch_add(ancm.count_ones() as u64, std::sync::atomic::Ordering::SeqCst);
                tot_tof.fetch_add(sim.stats.toffoli_gates, std::sync::atomic::Ordering::SeqCst);
                eprintln!("e2e batch {seed}: {bad} bad (executed toffoli {})", sim.stats.toffoli_gates);
            });
        }
    });
    let _ = std::fs::remove_file(&path);
    let tt = tot_tof.load(std::sync::atomic::Ordering::SeqCst);
    eprintln!("E2EH executed toffoli total {tt} over {} shots: avg {:.3}", nbatch * 64, tt as f64 / (nbatch * 64) as f64);
    eprintln!("E2EH total bad {} (phase {}, ancilla {}) of {} shots", tot_bad.load(std::sync::atomic::Ordering::SeqCst),
              tot_ph.load(std::sync::atomic::Ordering::SeqCst), tot_anc.load(std::sync::atomic::Ordering::SeqCst), nbatch * 64);
}

/// Debug: traversal forward then its inverse (no payload) on 64 random x; every lane must return to the input and
/// the phase must be zero. FROGDROP_RT_PL=1: forward with payload, inverse with payload.
#[test]
#[ignore = "tool"]
fn frogdrop_roundtrip_dbg() {
    use super::frogdrop_sched::sample;
    use super::pointadd_frogdrop::*;
    use super::payload::NP;
    let seed: u64 = std::env::var("FROGDROP_SEED0").ok().and_then(|s| s.parse().ok()).unwrap_or(1000);
    let withpl = std::env::var("FROGDROP_RT_PL").is_ok();
    let mut b = B::new();
    let xq = b.alloc_n(256);
    let pl = b.alloc_n(NP);
    let t = trav_forward_pl(&mut b, &xq, &pl, if withpl { Some(&pl) } else { None });
    let mid = b.ops.len();
    let mix = std::env::var("FROGDROP_RT_MIX").is_ok();
    trav_inverse_pl(&mut b, t, &pl, if withpl && !mix { Some(&pl) } else { None });
    eprintln!("rt build: {} T, {} ops (forward {}), peak {}", b.tof, b.ops.len(), mid, b.peak);
    let width = b.width() as usize;
    let xs = sample(64, seed);
    let mut rng = Rng::new(seed ^ 0x77);
    let p = pval();
    let dys: Vec<N> = (0..64).map(|_| rng.below(256) % p).collect();
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let mut h = sha3::Shake256::default();
    h.update(b"frogdrop-rt");
    h.update(&seed.to_le_bytes());
    let mut xof = h.finalize_xof();
    let mut sim = Simulator::new(width.max(aq as usize), (nb as usize).max(1), &mut xof);
    for s in 0..64 {
        put(&mut sim.qubits, &xq, s, &xs[s]);
        put(&mut sim.qubits, &pl[..256], s, &dys[s]);
    }
    let stop: usize = std::env::var("FROGDROP_RT_STOP").ok().and_then(|s| s.parse().ok()).unwrap_or(usize::MAX);
    if stop < b.ops.len() { sim.apply_iter(b.ops[..stop].iter()); } else { sim.apply_iter(b.ops.iter()); }
    let q = &sim.qubits;
    let mut nbad = 0;
    let mut dirty_lanes = std::collections::BTreeMap::new();
    for s in 0..64 {
        let ok_x = get(q, &xq, s) == xs[s];
        let ok_p = mix || get(q, &pl[..256], s) == dys[s];
        let mut z = 0;
        for l in 0..width {
            let qq = QubitId(l as u64);
            if xq.contains(&qq) || pl[..256].contains(&qq) || (mix && pl.contains(&qq)) { continue; }
            if (q[l] >> s) & 1 != 0 { z += 1; *dirty_lanes.entry(l).or_insert(0) += 1; }
        }
        let ph = (sim.phase >> s) & 1;
        if !(ok_x && ok_p && z == 0 && ph == 0) { nbad += 1; if nbad <= 4 { eprintln!("RT_FAIL shot {s} x {ok_x} pl {ok_p} dirty {z} phase {ph}"); } }
    }
    let top: Vec<_> = dirty_lanes.iter().take(40).collect();
    eprintln!("RT bad {nbad} of 64; dirty lanes (lane: shots) {:?}", top);
}
#[path = "tests_q731_zero_parking.rs"]
mod q731_zero_parking;

#[path = "tests_q730_ring286_k28.rs"]
mod q730_ring286_k28;

/// sub700b: the HT restoring division (ht_div_rec) kept (not undone), q into 24 lanes F: F = floor(X/Y), X = X mod Y.
#[test]
#[ignore = "tool"]
fn sub700b_ht_div_unit() {
    use super::frogdrop_col::{ColPar, Fd};
    use super::payload::{ht_div_rec, DigScr};
    let n = 282usize; let nq = 128usize;
    let alt: usize = std::env::var("SUB700B_ALT").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    let mut b = B::new();
    let ring = b.alloc_n(n);
    let q = b.alloc_n(nq);
    let cnt = q[nq - 7..].to_vec();
    let fd = Fd { ring: ring.clone(), q: q.clone(), sy: b.alloc_n(8), sx: b.alloc_n(8), ph: b.alloc(), cnt };
    let sz = b.alloc_n(8);
    let f = b.alloc_n(24);
    let lanes = b.alloc_n(9);
    let act = b.alloc();
    let dirty = b.alloc_n(259);
    let (bqt, t2, pg, pc0, pzero, pf, mz, sa8, _x) = (lanes[0], lanes[1], lanes[2], lanes[3], lanes[4], lanes[5], lanes[6], lanes[7], lanes[8]);
    let ds = if alt == 0 {
        DigScr { e: f.clone(), sa: { let mut v = sz.clone(); v.push(sa8); v }, sb: fd.sy.clone(), sv: bqt, fa: t2, g: pg, c0: pc0,
                 tmp: vec![pzero, pf], pre1: vec![], pre2: vec![], zeros: vec![mz], dirty: dirty.clone() , smin: 0 }
    } else {
        DigScr { e: f.clone(), sa: { let mut v = sz.clone(); v.push(sa8); v }, sb: fd.sy.clone(), sv: bqt, fa: t2, g: pg, c0: pc0,
                 tmp: vec![pzero, pf], pre1: vec![], pre2: vec![], zeros: vec![mz, lanes[8]], dirty: dirty.clone() , smin: 0 }
    };
    // HT shots: Z = t_j, X = r_{j-1}, Y = r_j with bl(r_j) <= 128
    let shots = if let Ok(xh) = std::env::var("SUB700B_X") {
        let x = N::from_str_radix(&xh, 16).unwrap();
        let jj: usize = std::env::var("SUB700B_J").unwrap().parse().unwrap();
        let seq = euclid_seq(x);
        (0..64).map(|_| (seq.clone(), 1u8, jj)).collect::<Vec<_>>()
    } else { rand_shots(4711, |rng, (r, t)| {
        let nn = r.len() - 1;
        let js: Vec<usize> = (2..nn - 1).filter(|&j| blen(&r[j]) <= 128 && blen(&r[j]) >= 54 && blen(&t[j]) >= 101 && blen(&t[j]) <= 196).collect();
        if js.is_empty() { return None; }
        Some((1, js[(rng.next() as usize) % js.len()]))
    }) };
    let mut cp = ColPar { n, nq, h: n - 257, k: 23, kp: 24, qb: 26, tot: 83, sz: (999, 0), sy: (999, 0), smax: (1, 128), m: 128,
                          tail: 40, emax: 28, hr: false, ht: true, sw: false, l0: 128, swl: (0, 0), dn: false, fin: false,
                          nomap: false, tt: false, pht: false, psy: (0, 0), xw: 0, psw: false, cntw: 7, cntmax: 127, col: usize::MAX,
                          dl: false, dq: false, dlr: 0 };
    for ((r, t), _, j) in &shots {
        let (zb, yb, xb) = (blen(&t[*j]), blen(&r[*j]), blen(&r[*j - 1]));
        cp.sz = (cp.sz.0.min(zb), cp.sz.1.max(zb)); cp.sy = (cp.sy.0.min(yb), cp.sy.1.max(yb)); cp.xw = cp.xw.max(xb);
    }
    if let Ok(v) = std::env::var("SUB700B_XW") { cp.xw = v.parse().unwrap(); cp.sz.0 = cp.sz.0.min(101); }
    if std::env::var("SUB700B_COL69").is_ok() { cp.sz = (101, 196); cp.sy = (54, 156); cp.xw = 156; }
    eprintln!("cp sz {:?} sy {:?} xw {}", cp.sz, cp.sy, cp.xw);
    let div = ht_div_rec(&mut b, &fd, &cp, &sz, &dirty, act, &ds);
    b.play(&div, false);
    let dv: Vec<N> = (0..64).map(|s| N::from(0x9e3779b97f4a7c15u64.wrapping_mul(s as u64 + 7))).collect();
    let rres = run(&b.ops, b.width() as usize, &|w| {
        for (s, ((r, t), _, j)) in shots.iter().enumerate() {
            put(w, &ring[..257], s, &t[*j]);
            let x = r[*j - 1];
            for i in 0..blen(&x) { if x.bit(i) { w[ring[n - 1 - i].0 as usize] |= 1 << s; } }
            put(w, &q, s, &r[*j]);
            put(w, &fd.sy, s, &N::from(blen(&r[*j]) as u64));
            put(w, &sz, s, &N::from(blen(&t[*j]) as u64));
            w[act.0 as usize] |= 1 << s;
            put(w, &dirty, s, &dv[s]);
        }
    });
    let mut bad = 0;
    for (s, ((r, t), _, j)) in shots.iter().enumerate() {
        let qq = r[*j - 1] / r[*j];
        let fv = get(&rres.q, &f, s);
        let mut xv = N::ZERO;
        let xl = n - blen(&t[*j]) - 25;
        for i in 0..xl { if (rres.q[ring[n - 1 - i].0 as usize] >> s) & 1 == 1 { xv |= N::from(1u64) << i; } }
        let zok = get(&rres.q, &ring[..n - xl], s) == t[*j];
        let clean = lanes.iter().all(|l| (rres.q[l.0 as usize] >> s) & 1 == 0);
        let ok = fv == qq && xv == r[*j + 1] && zok && clean && get(&rres.q, &dirty, s) == dv[s];
        if !ok {
            bad += 1;
            if bad < 6 { eprintln!("shot {s}: q {} F {} X ok {} Z ok {} clean {} sz {} sy {}", qq, fv, xv == r[*j + 1], zok, clean, blen(&t[*j]), blen(&r[*j])); }
        }
    }
    eprintln!("SUB700B_HTDIV bad {bad}/64 phase {:#x}", rres.phase);
}

/// sub700b: the HT division with the real carve and mid2 roles, on one shot state (SUB700B_X, SUB700B_J), column-69
/// ranges.
#[test]
#[ignore = "tool"]
fn sub700b_ht_div_carve() {
    use super::frogdrop_col::{pool_size, ColPar, ColScr, Fd};
    use super::payload::{ht_div_rec, NP};
    use super::pointadd_frogdrop::*;
    let n = N; let nq = NQ;
    let mut b = B::new();
    let xq = b.alloc_n(256);
    let pl = b.alloc_n(NP);
    let mut ring: Vec<QubitId> = xq.to_vec();
    ring.extend(b.alloc_n(N - 256));
    let q = b.alloc_n(NQ);
    let cnt = q[NQ - CNTB..].to_vec();
    let mut fd = Fd { ring: ring.clone(), q: q.clone(), sy: b.alloc_n(SW), sx: b.alloc_n(SW), ph: b.alloc(), cnt };
    if std::env::var("SUB700B_SWAPSYSX").is_ok() { std::mem::swap(&mut fd.sy, &mut fd.sx); }
    let pool = b.alloc_n(pool_size(KP, QB, SW));
    let sc = ColScr::carve_col(&pool, &fd.sx, &pl, KP, QB, TAIL, false);
    let ro = super::mid2::roles(&sc, TOT, KP);
    let ds = super::mid2::ht_ds(&fd, &sc, &ro);
    let cp = ColPar { n, nq, h: n - 257, k: K, kp: KP, qb: 24, tot: TOT, sz: (101, 196), sy: (54, 156), smax: (1, 128), m: 128,
                      tail: TAIL, emax: EMAX, hr: false, ht: true, sw: true, l0: 128, swl: (0, 0), dn: false, fin: false,
                      nomap: false, tt: false, pht: false, psy: (0, 0), xw: 156, psw: false, cntw: 7, cntmax: 127, col: usize::MAX,
                      dl: false, dq: false, dlr: 0 };
    let x = N::from_str_radix(&std::env::var("SUB700B_X").unwrap(), 16).unwrap();
    let jj: usize = std::env::var("SUB700B_J").unwrap().parse().unwrap();
    let (r, t) = euclid_seq(x);
    {
        let ids = |v: &[QubitId]| v.iter().map(|x| x.0.to_string()).collect::<Vec<_>>().join(",");
        eprintln!("UNITROLES sz {} sy {} sx {} sw {} F {} act {} bqt {} t2 {} mz {}", ids(&sc.sz), ids(&fd.sy), ids(&fd.sx), sc.sw.0,
                  ids(&ro.f), ro.act.0, ro.bqt.0, ro.t2.0, ro.mz.0);
    }
    let div = ht_div_rec(&mut b, &fd, &cp, &sc.sz, &sc.dirty, sc.sw, &ds);
    eprintln!("UNITDIV {:?}", super::mid2::ghash(&div));
    b.play(&div, false);
    let loaded: Option<Vec<u8>> = std::env::var("SUB700B_LOADSTATE").ok().map(|p| std::fs::read(p).unwrap());
    let rres = run(&b.ops, b.width() as usize, &|w| {
        if let Some(st) = &loaded {
            for (i, &c) in st.iter().enumerate() { if c == b'1' { w[i] = u64::MAX; } }
            w[sc.sw.0 as usize] = u64::MAX;
            return;
        }
        for s in 0..64 {
            put(w, &ring[..257], s, &t[jj]);
            let xv = r[jj - 1];
            for i in 0..blen(&xv) { if xv.bit(i) { w[ring[n - 1 - i].0 as usize] |= 1 << s; } }
            put(w, &q, s, &r[jj]);
            put(w, &fd.sy, s, &N::from(blen(&r[jj]) as u64));
            put(w, &sc.sz, s, &N::from(blen(&t[jj]) as u64));
            w[sc.sw.0 as usize] |= 1 << s;
            w[fd.ph.0 as usize] |= 1 << s;
            if std::env::var("SUB700B_DIRTYRAND").is_ok() {
                let mut rng = Rng::new(s as u64 * 7919 + 13);
                let v = rng.below(256);
                put(w, &pl[..256], s, &v);
                for l in 256..pl.len() { if rng.next() & 1 == 1 { w[pl[l].0 as usize] |= 1 << s; } }
            }
        }
    });
    let qq = r[jj - 1] / r[jj];
    let fv = get(&rres.q, &ro.f, 0);
    let nz: Vec<usize> = (0..pool.len()).filter(|&i| rres.q[pool[i].0 as usize] & 1 == 1).collect();
    eprintln!("SUB700B_CARVE q {} F {} pool nonzero {:?} sx {:x} phase {:#x}", qq, fv, nz, get(&rres.q, &fd.sx, 0), rres.phase);
}

/// Lane census (FD_MARK): one traversal build; per column stage, the pool and spare-size lanes its ops touch.
/// Prints per stage the max count over columns (and the column), plus per-column totals in FD_CENSUS_OUT (json).
#[test]
#[ignore = "tool"]
fn sub700b_lane_census() {
    use super::pointadd_frogdrop::*;
    use super::payload::NP;
    use super::frogdrop_col::{MARKS, COLSX};
    std::env::set_var("FD_MARK", "1");
    let mut b = B::new();
    let xq = b.alloc_n(256);
    let pl = b.alloc_n(NP);
    let t = trav_forward_pl(&mut b, &xq, &pl, Some(&pl));
    eprintln!("census build: {} T, {} ops, peak {}", b.tof, b.ops.len(), b.peak);
    let marks = MARKS.with(|m| m.borrow().clone());
    let colsx = COLSX.with(|m| m.borrow().clone());
    let pool: std::collections::HashMap<u64, usize> = t.pool.iter().enumerate().map(|(i, q)| (q.0, i)).collect();
    // column boundaries: marks with stage 0
    let mut out = String::from("[");
    let mut col = 0usize;
    let mut first = true;
    let mut i = 0;
    while i < marks.len() {
        if marks[i].1 != 0 { i += 1; continue; }
        let sx: std::collections::HashMap<u64, usize> = colsx[col].iter().enumerate().map(|(i, q)| (q.0, i)).collect();
        let mut j = i;
        loop {
            let a = marks[j].0;
            let z = if j + 1 < marks.len() { marks[j + 1].0 } else { b.ops.len() };
            let st = marks[j].1;
            let mut pu = std::collections::BTreeSet::new();
            let mut su = std::collections::BTreeSet::new();
            for op in &b.ops[a..z] {
                for qq in [op.q_control2, op.q_control1, op.q_target] {
                    if let Some(&pi) = pool.get(&qq.0) { pu.insert(pi); }
                    if let Some(&si) = sx.get(&qq.0) { su.insert(si); }
                }
            }
            if !first { out.push(','); }
            first = false;
            out.push_str(&format!("{{\"c\":{},\"s\":{},\"ops\":{},\"pool\":{:?},\"sx\":{:?}}}", col, st, z - a,
                                  pu.iter().collect::<Vec<_>>(), su.iter().collect::<Vec<_>>()));
            j += 1;
            if j >= marks.len() || marks[j].1 == 0 { break; }
        }
        col += 1;
        i = j;
    }
    out.push(']');
    std::fs::write(std::env::var("FD_CENSUS_OUT").unwrap_or("/tmp/census.json".into()), out).unwrap();
    eprintln!("census: {} columns", col);
}

/// Value-level census (FD_MARK): one traversal on 64 random inputs; per column stage, the most pool + spare-size
/// lanes nonzero (on any shot) at one instant, and which. Writes FD_CENSUS_OUT (json lines: c, s, occ, lanes).
#[test]
#[ignore = "tool"]
fn sub700b_value_census() {
    use super::pointadd_frogdrop::*;
    use super::payload::NP;
    use super::frogdrop_col::{MARKS, COLSX};
    use super::frogdrop_sched::sample;
    use crate::circuit::OperationType as OT;
    use sha3::digest::XofReader;
    std::env::set_var("FD_MARK", "1");
    let seed: u64 = std::env::var("FROGDROP_SEED0").ok().and_then(|s| s.parse().ok()).unwrap_or(1000);
    let mut b = B::new();
    let xq = b.alloc_n(256);
    let pl = b.alloc_n(NP);
    let t = trav_forward_pl(&mut b, &xq, &pl, Some(&pl));
    eprintln!("census build: {} T, {} ops, peak {}", b.tof, b.ops.len(), b.peak);
    let marks = MARKS.with(|m| m.borrow().clone());
    let colsx = COLSX.with(|m| m.borrow().clone());
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let width = (b.width() as usize).max(aq as usize);
    let mut qs = vec![0u64; width];
    let mut bits = vec![0u64; (nb as usize).max(1)];
    let mut xs = sample(64, seed);
    let mut rng = Rng::new(seed ^ 0x77);
    let p = pval();
    let fx = std::env::var("FROGDROP_X").ok().map(|v| N::from_str_radix(&v, 16).unwrap());
    let fdy = std::env::var("FROGDROP_DY").ok().map(|v| N::from_str_radix(&v, 16).unwrap());
    if let Some(x) = fx { xs = vec![x; 64]; }
    for s in 0..64 {
        put(&mut qs, &xq, s, &xs[s]);
        let dy = rng.below(256) % p;
        let dy = fdy.unwrap_or(dy);
        put(&mut qs, &pl[..256], s, &dy);
    }
    // FD_WATCH=<qubit id>: print every change of that qubit on shot 0 (op index, column, stage mark)
    let watch: Option<usize> = std::env::var("FD_WATCH").ok().and_then(|v| v.parse().ok());
    let mut h = sha3::Shake256::default();
    h.update(b"frogdrop-census");
    let mut xof = h.finalize_xof();
    let mut cstack: Vec<u64> = vec![];
    let mut base = u64::MAX;
    let mut out = String::new();
    // scratch id -> label
    let mut lab: Vec<i32> = vec![-1; width];
    for (i, q) in t.pool.iter().enumerate() { lab[q.0 as usize] = i as i32; }
    let mapx = super::frogdrop_col::MAPEXTRA.with(|m| m.borrow().clone());
    for (i, q) in mapx.iter().enumerate() { lab[q.0 as usize] = 200 + i as i32; }
    let mut col = 0usize;
    let mut mi = 0usize;
    let nops = b.ops.len();
    let mut i = 0usize;
    while mi < marks.len() {
        let (a, st) = marks[mi];
        let z = if mi + 1 < marks.len() { marks[mi + 1].0 } else { nops };
        if st == 0 {
            if mi > 0 { col += 1; }
            for l in lab.iter_mut() { if *l >= 100 { *l = -1; } }
            for (j, q) in colsx[col].iter().enumerate() { lab[q.0 as usize] = 100 + j as i32; }
        }
        assert!(i <= a);
        // ops before this mark (outside columns) are simulated without census
        let mut step = |op: &Op, qs: &mut Vec<u64>, bits: &mut Vec<u64>| {
            let mut cond = base;
            if op.c_condition != crate::circuit::NO_BIT { cond &= bits[op.c_condition.0 as usize]; }
            let q = |qs: &Vec<u64>, id: QubitId| qs[id.0 as usize];
            match op.kind {
                OT::CCX => { let v = cond & q(qs, op.q_control1) & q(qs, op.q_control2); qs[op.q_target.0 as usize] ^= v; }
                OT::CX => { let v = cond & q(qs, op.q_control1); qs[op.q_target.0 as usize] ^= v; }
                OT::Swap => {
                    let mut c1 = q(qs, op.q_control1); let mut tt = q(qs, op.q_target);
                    c1 ^= tt; tt ^= cond & c1; c1 ^= tt;
                    qs[op.q_control1.0 as usize] = c1; qs[op.q_target.0 as usize] = tt;
                }
                OT::X => { qs[op.q_target.0 as usize] ^= cond; }
                OT::Hmr => {
                    let mut buf = [0u8; 8]; xof.read(&mut buf); let r = u64::from_le_bytes(buf);
                    let ct = op.c_target.0 as usize;
                    bits[ct] &= !cond; bits[ct] ^= r & cond;
                    qs[op.q_target.0 as usize] &= !cond;
                }
                OT::R => {
                    let mut buf = [0u8; 8]; xof.read(&mut buf);
                    qs[op.q_target.0 as usize] &= !cond;
                }
                OT::BitInvert => { bits[op.c_target.0 as usize] ^= cond; }
                OT::BitStore0 => { bits[op.c_target.0 as usize] &= !cond; }
                OT::BitStore1 => { bits[op.c_target.0 as usize] |= cond; }
                OT::PushCondition => { cstack.push(base); base &= bits[op.c_condition.0 as usize]; }
                OT::PopCondition => { if let Some(v) = cstack.pop() { base = v; } }
                _ => {}
            }
        };
        while i < a { step(&b.ops[i], &mut qs, &mut bits); i += 1; }
        // start register range right after the P frame rotation (sz += sy)
        if st == 102 || st == 202 {
            let wide = colsx.len() > col && false;
            let _ = wide;
            let mut lo = u64::MAX; let mut hi = 0u64;
            for sh in 0..64 {
                let mut v = 0u64;
                for (bi, q) in t.pool[..9].iter().enumerate() { v |= ((qs[q.0 as usize] >> sh) & 1) << bi; }
                let w8 = ((v & 255) + 256 - 228) % 256;
                let w9 = (v + 512 - 228) % 512;
                lo = lo.min(w9); hi = hi.max(w8);
            }
            out.push_str(&format!("{{\"c\":{},\"s\":{},\"svlo\":{},\"svhi\":{}}}\n", col, 1000 + st, lo, hi));
        }
        // occupancy over [a, z)
        let occ_now = |qs: &Vec<u64>, lab: &Vec<i32>| -> Vec<i32> {
            let mut v = vec![];
            for q in t.pool.iter().chain(colsx[col].iter()).chain(mapx.iter()) { if qs[q.0 as usize] != 0 { v.push(lab[q.0 as usize]); } }
            v
        };
        let mut cur = occ_now(&qs, &lab).len() as i32;
        let mut best = cur;
        let mut best_at = a;
        let mut best_l = occ_now(&qs, &lab);
        while i < z {
            let op = &b.ops[i];
            if let Some(w) = watch {
                let before = qs[w] & 1;
                let mut q2 = qs.clone(); let mut b2 = bits.clone();
                let _ = (&mut q2, &mut b2);
                if op.q_target.0 as usize == w || (op.kind == OT::Swap && op.q_control1.0 as usize == w) {
                    // evaluated after the step below
                    let _ = before;
                }
            }
            let wb = watch.map(|w| qs[w] & 1);
            let tg = [op.q_target, op.q_control1];
            let before: Vec<bool> = tg.iter().map(|x| (x.0 as usize) < width && lab[x.0 as usize] >= 0 && qs[x.0 as usize] != 0).collect();
            step(op, &mut qs, &mut bits);
            for (k, x) in tg.iter().enumerate() {
                if k == 1 && op.kind != OT::Swap { break; }
                if (x.0 as usize) >= width || lab[x.0 as usize] < 0 { continue; }
                let after = qs[x.0 as usize] != 0;
                if after && !before[k] { cur += 1; }
                if !after && before[k] { cur -= 1; }
            }
            if cur > best { best = cur; best_at = i; best_l = occ_now(&qs, &lab); }
            if let (Some(w), Some(v0)) = (watch, wb) {
                if qs[w] & 1 != v0 {
                    eprintln!("WATCH op {} col {} mark {} kind {:?} c2 {} c1 {} t {} -> {}", i, col, st, op.kind,
                              op.q_control2.0, op.q_control1.0, op.q_target.0, qs[w] & 1);
                }
            }
            i += 1;
        }
        out.push_str(&format!("{{\"c\":{},\"s\":{},\"occ\":{},\"at\":{},\"lanes\":{:?}}}\n", col, st, best, best_at - a, best_l));
        mi += 1;
    }
    std::fs::write(std::env::var("FD_CENSUS_OUT").unwrap_or("/tmp/vcensus.json".into()), out).unwrap();
    let info = super::frogdrop_col::COLINFO.with(|m| m.borrow().join("\n"));
    std::fs::write(std::env::var("FD_CENSUS_OUT").unwrap_or("/tmp/vcensus.json".into()) + ".cols", info).unwrap();
    eprintln!("value census: {} columns", col + 1);
}

/// cmp_csub_carries_vz == cmp_csub_carries with an explicit zero top lane (random values, 1..3 carry lanes)
#[test]
#[ignore = "tool"]
fn sub700b_vz_unit() {
    use crate::circuit::analyze_ops;
    for nand in 1..4usize {
        for n in [3usize, 6, 25] {
            let mut outs = vec![];
            for vz in [false, true] {
                let mut b = B::new();
                let t = b.alloc_n(n);
                let s = b.alloc_n(n);
                let c0 = b.alloc();
                let out = b.alloc();
                let andc = b.alloc_n(nand);
                if vz { cmp_csub_carries_vz(&mut b, &t, &s[..n - 1], c0, out, &andc); }
                else { cmp_csub_carries(&mut b, &t, &s, c0, out, &andc); }
                let (aq, nb, _, _) = analyze_ops(b.ops.iter());
                let mut h = sha3::Shake256::default();
                h.update(b"vz");
                let mut xof = h.finalize_xof();
                let mut sim = Simulator::new((b.width() as usize).max(aq as usize), (nb as usize).max(1), &mut xof);
                let mut rng = Rng::new(7 + n as u64 + 100 * nand as u64);
                let mut ins = vec![];
                for sh in 0..64 {
                    let tv = rng.below(n); let sv = rng.below(n - 1);
                    put(&mut sim.qubits, &t, sh, &tv);
                    put(&mut sim.qubits, &s[..n - 1], sh, &sv);
                    ins.push((tv, sv));
                }
                sim.apply_iter(b.ops.iter());
                let res: Vec<(N, u64, u64)> = (0..64).map(|sh| (get(&sim.qubits, &t, sh), (sim.qubits[out.0 as usize] >> sh) & 1,
                    andc.iter().chain(s.iter()).chain([c0].iter()).map(|q| (sim.qubits[q.0 as usize] >> sh) & 1).sum::<u64>())).collect();
                outs.push((res, sim.phase));
            }
            assert_eq!(outs[0].0, outs[1].0, "n {n} nand {nand}");
            eprintln!("vz ok n {n} nand {nand} phases {:#x} {:#x}", outs[0].1, outs[1].1);
        }
    }
}

// agent_lowq_quot: lowq-size's lowsize_census (predictor at K24 precision)
/// Reconstructed lowsize_census = lowq640_pressure_census
/// + f1_dump / LS_PROFILE_ONLY + predictor-failing shots excluded from the pressure count (LS_KEEP_BAD keeps them).
/// The per-column max and the global max follow the original; the json records keep lowq640's fields.
#[test]
#[ignore = "tool"]
fn quot_lowsize_census() {
    use super::pointadd_frogdrop::*;
    use super::payload::NP;
    use super::frogdrop_col::MARKS;
    use super::frogdrop_sched::sample;
    use crate::circuit::OperationType as OT;
    use sha3::digest::XofReader;
    std::env::set_var("FD_MARK", "1");
    const W: usize = 4;
    let seed: u64 = std::env::var("FROGDROP_SEED0").ok().and_then(|s| s.parse().ok()).unwrap_or(1000);
    let mut b = B::new();
    let xq = b.alloc_n(256);
    let pl = b.alloc_n(NP);
    let t = trav_forward_pl(&mut b, &xq, &pl, Some(&pl));
    eprintln!("census build: {} T, {} ops, peak {}", b.tof, b.ops.len(), b.peak);
    super::f1_dump();
    if std::env::var_os("LS_PROFILE_ONLY").is_some() { return; }
    let marks = MARKS.with(|m| m.borrow().clone());
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let width = (b.width() as usize).max(aq as usize);
    // group labels: 0 ring, 1 q, 2 size A (fd.sy at the end), 3 size B (fd.sx at the end), 4 ph, 5 pool, 6 payload,
    // 7 other
    let mut grp: Vec<(u8, u16)> = vec![(7, 0); width];
    for (i, q) in t.fd.ring.iter().enumerate() { grp[q.0 as usize] = (0, i as u16); }
    for (i, q) in t.fd.q.iter().enumerate() { grp[q.0 as usize] = (1, i as u16); }
    for (i, q) in t.fd.sy.iter().enumerate() { grp[q.0 as usize] = (2, i as u16); }
    for (i, q) in t.fd.sx.iter().enumerate() { grp[q.0 as usize] = (3, i as u16); }
    grp[t.fd.ph.0 as usize] = (4, 0);
    for (i, q) in t.pool.iter().enumerate() { grp[q.0 as usize] = (5, i as u16); }
    for (i, q) in pl.iter().enumerate() { grp[q.0 as usize] = (6, i as u16); }
    let mut qs = vec![[0u64; W]; width];
    let mut bits = vec![[0u64; W]; (nb as usize).max(1)];
    let p = pval();
    for wd in 0..W {
        let xs = sample(64, seed + wd as u64);
        let mut rng = Rng::new((seed + wd as u64) ^ 0x77);
        let mut tmp = vec![0u64; width];
        for s in 0..64 {
            put(&mut tmp, &xq, s, &xs[s]);
            let dy = rng.below(256) % p;
            put(&mut tmp, &pl[..256], s, &dy);
        }
        for i in 0..width { qs[i][wd] = tmp[i]; }
    }
    // shots the classical predictor fails are excluded (LS_KEEP_BAD keeps them): their garbage is a counted failure
    let mut good = [u64::MAX; W];
    if std::env::var_os("LS_KEEP_BAD").is_none() {
        let sc = super::frogdrop_sched::from_text(SCHED_FROGDROP);
        let mut nbad = 0;
        for wd in 0..W {
            let xs = sample(64, seed + wd as u64);
            for s in 0..64 {
                if super::frogdrop_sched::predict_n(xs[s], &sc, 24, KP, QB, TOT, NQ, EMAX, N).is_some() {
                    good[wd] &= !(1u64 << s); nbad += 1;
                }
            }
        }
        eprintln!("census: {} of {} shots predicted to fail, excluded", nbad, 64 * W);
    }
    let mut h = sha3::Shake256::default();
    h.update(b"frogdrop-census");
    let mut xof = h.finalize_xof();
    let mut cstack: Vec<[u64; W]> = vec![];
    let mut base = [u64::MAX; W];
    let nz = |v: &[u64; W]| v.iter().zip(good.iter()).any(|(&x, &g)| x & g != 0);
    let mut cur: i64 = qs.iter().filter(|v| nz(v)).count() as i64;
    let mut out = String::new();
    let nops = b.ops.len();
    let mut col: i64 = -1;
    let mut i = 0usize;
    let mut gmax = 0i64;
    for mi in 0..=marks.len() {
        let (a, st) = if mi < marks.len() { marks[mi] } else { (nops, 9999) };
        let z = if mi + 1 < marks.len() { marks[mi + 1].0 } else { nops };
        if mi < marks.len() && st == 0 { col += 1; }
        let mut best = cur;
        let mut best_at = i;
        let mut snap: Option<Vec<bool>> = None;
        let seg_end = if mi < marks.len() { z } else { nops };
        let start = if mi < marks.len() { a } else { i };
        while i < seg_end {
            let op = &b.ops[i];
            let mut cond = base;
            if op.c_condition != crate::circuit::NO_BIT {
                for w in 0..W { cond[w] &= bits[op.c_condition.0 as usize][w]; }
            }
            let touched = [op.q_target, op.q_control1];
            let before: Vec<bool> = touched.iter().map(|x| (x.0 as usize) < width && nz(&qs[x.0 as usize])).collect();
            match op.kind {
                OT::CCX => { for w in 0..W { let v = cond[w] & qs[op.q_control1.0 as usize][w] & qs[op.q_control2.0 as usize][w]; qs[op.q_target.0 as usize][w] ^= v; } }
                OT::CX => { for w in 0..W { let v = cond[w] & qs[op.q_control1.0 as usize][w]; qs[op.q_target.0 as usize][w] ^= v; } }
                OT::Swap => { for w in 0..W {
                    let mut c1 = qs[op.q_control1.0 as usize][w]; let mut tt = qs[op.q_target.0 as usize][w];
                    c1 ^= tt; tt ^= cond[w] & c1; c1 ^= tt;
                    qs[op.q_control1.0 as usize][w] = c1; qs[op.q_target.0 as usize][w] = tt; } }
                OT::X => { for w in 0..W { qs[op.q_target.0 as usize][w] ^= cond[w]; } }
                OT::Hmr => { for w in 0..W {
                    let mut buf = [0u8; 8]; xof.read(&mut buf); let r = u64::from_le_bytes(buf);
                    let ct = op.c_target.0 as usize;
                    bits[ct][w] &= !cond[w]; bits[ct][w] ^= r & cond[w];
                    qs[op.q_target.0 as usize][w] &= !cond[w]; } }
                OT::R => { for w in 0..W { qs[op.q_target.0 as usize][w] &= !cond[w]; } }
                OT::BitInvert => { for w in 0..W { bits[op.c_target.0 as usize][w] ^= cond[w]; } }
                OT::BitStore0 => { for w in 0..W { bits[op.c_target.0 as usize][w] &= !cond[w]; } }
                OT::BitStore1 => { for w in 0..W { bits[op.c_target.0 as usize][w] |= cond[w]; } }
                OT::PushCondition => { cstack.push(base); for w in 0..W { base[w] &= bits[op.c_condition.0 as usize][w]; } }
                OT::PopCondition => { if let Some(v) = cstack.pop() { base = v; } }
                _ => {}
            }
            for (k, x) in touched.iter().enumerate() {
                if k == 1 && op.kind != OT::Swap { break; }
                if (x.0 as usize) >= width { continue; }
                let after = nz(&qs[x.0 as usize]);
                if after && !before[k] { cur += 1; }
                if !after && before[k] { cur -= 1; }
            }
            if cur > best || snap.is_none() && cur >= best {
                best = cur; best_at = i;
                snap = Some(qs.iter().map(|v| nz(v)).collect());
            }
            i += 1;
        }
        if mi == marks.len() { break; }
        let _ = start;
        gmax = gmax.max(best);
        let s = snap.unwrap_or_else(|| qs.iter().map(|v| nz(v)).collect());
        let mut cnt = [0usize; 8];
        let mut idle: Vec<String> = vec![];
        for (id, &on) in s.iter().enumerate() {
            let (g, ix) = grp[id];
            if on { cnt[g as usize] += 1; }
            else if matches!(g, 2 | 3 | 4 | 5) { idle.push(format!("{}{}", ["r","q","A","B","ph","p","pl","o"][g as usize], ix)); }
        }
        let zr: Vec<u16> = (0..width).filter(|&id| !s[id] && grp[id].0 == 0).map(|id| grp[id].1).collect();
        let zq: Vec<u16> = (0..width).filter(|&id| !s[id] && grp[id].0 == 1).map(|id| grp[id].1).collect();
        let zp: Vec<u16> = (0..width).filter(|&id| !s[id] && grp[id].0 == 6).map(|id| grp[id].1).collect();
        out.push_str(&format!("{{\"c\":{},\"s\":{},\"max\":{},\"at\":{},\"cnt\":{:?},\"idle\":{:?},\"zr\":{:?},\"zq\":{:?},\"zp\":{:?}}}\n",
                              col, st, best, best_at - a.min(best_at), cnt, idle, zr, zq, zp));
    }
    std::fs::write(std::env::var("FD_CENSUS_OUT").unwrap_or("/tmp/scensus.json".into()), out).unwrap();
    eprintln!("pressure census: {} columns, global max {}", col + 1, gmax);
}

// agent_lowq_lane: lane liveness at every V-form play. Per play (marks 33x1 .. 3300 in midg::middle): the act shots
// (act lane = 1 at the start mark, predictor-good) and, over every op of the play, which lanes stay 0 (c0) or 1 (c1)
// on all of them; plus position-relative constants at the start mark: Q + x128 at sy + o, the payload at sz + o / sy + o
// (value and equal-to-next), the ring at sz + o (both directions). LANE_W words of 64 shots (default 8).
#[test]
#[ignore = "tool"]
fn lane_vform_census() {
    use super::pointadd_frogdrop::*;
    use super::payload::NP;
    use super::frogdrop_col::{MARKS, VINFO};
    use super::frogdrop_sched::sample;
    use crate::circuit::OperationType as OT;
    use sha3::digest::XofReader;
    std::env::set_var("FD_MARK", "1");
    const WW: usize = 8;
    let ww = WW;
    let seed: u64 = std::env::var("FROGDROP_SEED0").ok().and_then(|s| s.parse().ok()).unwrap_or(1000);
    let mut b = B::new();
    let xq = b.alloc_n(256);
    let pl = b.alloc_n(NP);
    let _t = trav_forward_pl(&mut b, &xq, &pl, Some(&pl));
    eprintln!("lane census build: {} T, {} ops, peak {}", b.tof, b.ops.len(), b.peak);
    let marks = MARKS.with(|m| m.borrow().clone());
    let vinfo = VINFO.with(|m| m.borrow().clone());
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let width = (b.width() as usize).max(aq as usize);
    let mut qs = vec![[0u64; WW]; width];
    let mut bits = vec![[0u64; WW]; (nb as usize).max(1)];
    let p = pval();
    for wd in 0..ww {
        let xs = sample(64, seed + wd as u64);
        let mut rng = Rng::new((seed + wd as u64) ^ 0x77);
        let mut tmp = vec![0u64; width];
        for s in 0..64 {
            put(&mut tmp, &xq, s, &xs[s]);
            let dy = rng.below(256) % p;
            put(&mut tmp, &pl[..256], s, &dy);
        }
        for i in 0..width { qs[i][wd] = tmp[i]; }
    }
    let mut good = [u64::MAX; WW];
    {
        let sc = super::frogdrop_sched::from_text(SCHED_FROGDROP);
        let mut nbad = 0;
        for wd in 0..ww {
            let xs = sample(64, seed + wd as u64);
            for s in 0..64 {
                if super::frogdrop_sched::predict_n(xs[s], &sc, 24, KP, QB, TOT, NQ, EMAX, N).is_some() {
                    good[wd] &= !(1u64 << s); nbad += 1;
                }
            }
        }
        eprintln!("lane census: {} of {} shots predicted to fail, excluded", nbad, 64 * ww);
    }
    // events: (op index, Some(vinfo index) = play start / None = play end)
    let mut ev: Vec<(usize, Option<usize>)> = vec![];
    let mut vi = 0;
    for &(at, st) in &marks {
        if st == 3300 { ev.push((at, None)); }
        else if (3311..=3381).contains(&st) && st % 10 == 1 { assert_eq!(vinfo[vi].at, at); ev.push((at, Some(vi))); vi += 1; }
    }
    assert_eq!(vi, vinfo.len());
    let bit = |qs: &Vec<[u64; WW]>, l: QubitId, w: usize, s: usize| (qs[l.0 as usize][w] >> s) & 1;
    let val = |qs: &Vec<[u64; WW]>, r: &[QubitId], w: usize, s: usize| -> usize {
        r.iter().enumerate().map(|(i, &l)| (bit(qs, l, w, s) as usize) << i).sum()
    };
    struct Seg { v: usize, actm: [u64; 8], or0: Vec<bool>, and1: Vec<bool>, head: String, touched: Vec<bool> }
    let mut out = String::new();
    let mut cur: Option<Seg> = None;
    let mut h = sha3::Shake256::default();
    h.update(b"frogdrop-census");
    let mut xof = h.finalize_xof();
    let mut cstack: Vec<[u64; WW]> = vec![];
    let mut base = [u64::MAX; WW];
    let nops = b.ops.len();
    let mut ei = 0;
    let label = |v: &super::frogdrop_col::VInfo, l: usize| -> String {
        let id = QubitId(l as u64);
        let star = if v.r.contains(&id) { "*" } else { "" };
        let f = |r: &[QubitId], nm: &str| r.iter().position(|&x| x == id).map(|i| format!("{nm}{i}"));
        let s = f(&v.sy, "sy").or_else(|| f(&v.sz, "sz")).or_else(|| f(&v.sx, "sx")).or_else(|| f(&v.q, "Q"))
            .or_else(|| f(&v.ring, "ring")).or_else(|| f(&pl, "p"))
            .or_else(|| [(v.act, "act"), (v.x128, "x128"), (v.ph, "ph"), (v.sw, "sw"), (v.pzero, "pzero"), (v.c0, "c0")]
                     .iter().find(|x| x.0 == id).map(|x| x.1.to_string()))
            .unwrap_or(format!("o{l}"));
        format!("{s}{star}")
    };
    for i in 0..=nops {
        while ei < ev.len() && ev[ei].0 == i {
            match ev[ei].1 {
                None => {
                    if let Some(s) = cur.take() {
                        let v = &vinfo[s.v];
                        let c0: Vec<String> = (0..width).filter(|&l| !s.or0[l]).map(|l| label(v, l)).collect();
                        let c1: Vec<String> = (0..width).filter(|&l| s.and1[l]).map(|l| label(v, l)).collect();
                        let tq: Vec<usize> = v.q.iter().enumerate().filter(|(_, l)| s.touched[l.0 as usize]).map(|(i, _)| i).collect();
                        let tx = s.touched[v.x128.0 as usize];
                        out.push_str(&format!("{},\"tq\":{:?},\"tx\":{},\"c0\":{:?},\"c1\":{:?}}}\n", s.head, tq, tx, c0, c1));
                    }
                }
                Some(k) => {
                    let v = &vinfo[k];
                    let mut actm = [0u64; WW];
                    for w in 0..ww { actm[w] = qs[v.act.0 as usize][w] & good[w]; }
                    let nact: u32 = actm.iter().map(|x| x.count_ones()).sum();
                    let or0: Vec<bool> = (0..width).map(|l| (0..ww).any(|w| qs[l][w] & actm[w] != 0)).collect();
                    let and1: Vec<bool> = (0..width).map(|l| nact > 0 && (0..ww).all(|w| qs[l][w] & actm[w] == actm[w])).collect();
                    // position-relative constants on the act shots
                    let mut q129 = v.q.clone();
                    q129.push(v.x128);
                    let n = v.ring.len();
                    let (mut symin, mut symax, mut szmin, mut szmax) = (usize::MAX, 0, usize::MAX, 0);
                    // per offset: [ones, zeros, out of range] and payload equal-to-next counts
                    const OQ: isize = 4; const NQO: usize = 32;
                    const OP: isize = 12; const NPO: usize = 25;
                    let mut qrel = vec![[0u32; 3]; NQO];
                    let mut pz = vec![[0u32; 4]; NPO];
                    let mut py = vec![[0u32; 4]; NPO];
                    let mut rz = vec![[0u32; 2]; n];
                    let mut rzn = vec![[0u32; 2]; n];
                    for w in 0..ww {
                        for s in 0..64 {
                            if (actm[w] >> s) & 1 == 0 { continue; }
                            let sy = val(&qs, &v.sy, w, s);
                            let sz = val(&qs, &v.sz, w, s) + if v.zoff { v.zlo } else { 0 };
                            symin = symin.min(sy); symax = symax.max(sy); szmin = szmin.min(sz); szmax = szmax.max(sz);
                            for (j, e) in qrel.iter_mut().enumerate() {
                                let idx = sy as isize + j as isize - OQ;
                                if idx < 0 || idx >= q129.len() as isize { e[2] += 1; continue; }
                                e[bit(&qs, q129[idx as usize], w, s) as usize] += 1;
                            }
                            for (bse, arr) in [(sz, &mut pz), (sy, &mut py)] {
                                for (j, e) in arr.iter_mut().enumerate() {
                                    let idx = bse as isize + j as isize - OP;
                                    if idx < 0 || idx + 1 >= NP as isize { e[2] += 1; continue; }
                                    let a = bit(&qs, pl[idx as usize], w, s);
                                    let c = bit(&qs, pl[idx as usize + 1], w, s);
                                    e[a as usize] += 1;
                                    if a == c { e[3] += 1; }
                                }
                            }
                            for o in 0..n {
                                rz[o][bit(&qs, v.ring[(sz + o) % n], w, s) as usize] += 1;
                                rzn[o][bit(&qs, v.ring[(o + n - sz % n) % n], w, s) as usize] += 1;
                            }
                        }
                    }
                    let na = nact;
                    let qc0: Vec<isize> = (0..NQO).filter(|&j| na > 0 && qrel[j][0] == na).map(|j| j as isize - OQ).collect();
                    let qc1: Vec<isize> = (0..NQO).filter(|&j| na > 0 && qrel[j][1] == na).map(|j| j as isize - OQ).collect();
                    let pc = |arr: &Vec<[u32; 4]>, c: usize| -> Vec<isize> {
                        (0..NPO).filter(|&j| na > 0 && arr[j][2] == 0 && (if c < 2 { arr[j][c] == na } else if c == 2 { arr[j][3] == na } else { arr[j][3] == 0 }))
                            .map(|j| j as isize - OP).collect()
                    };
                    let rc = |arr: &Vec<[u32; 2]>, c: usize| -> Vec<usize> { (0..n).filter(|&o| na > 0 && arr[o][c] == na).collect() };
                    let head = format!("{{\"c\":{},\"k\":{},\"n\":{},\"sgw\":{},\"zoff\":{},\"kmax\":{},\"sy\":[{},{}],\"sz\":[{},{}],\"q0\":{:?},\"q1\":{:?},\"pz0\":{:?},\"pz1\":{:?},\"pze\":{:?},\"py0\":{:?},\"py1\":{:?},\"pye\":{:?},\"pzn\":{:?},\"pyn\":{:?},\"rz0\":{:?},\"rz1\":{:?},\"rzn0\":{:?},\"rzn1\":{:?}",
                        v.col, v.code, na, v.sgw, v.zoff, v.kmax, symin, symax, szmin, szmax, qc0, qc1,
                        pc(&pz, 0), pc(&pz, 1), pc(&pz, 2), pc(&py, 0), pc(&py, 1), pc(&py, 2), pc(&pz, 3), pc(&py, 3),
                        rc(&rz, 0), rc(&rz, 1), rc(&rzn, 0), rc(&rzn, 1));
                    if std::env::var("LANE_DUMP").ok().and_then(|x| x.parse::<usize>().ok()) == Some(v.col) {
                        let mut d = String::new();
                        let bs = |r: &[QubitId], w: usize, s: usize| -> String { r.iter().map(|&l| if bit(&qs, l, w, s) == 1 { '1' } else { '0' }).collect() };
                        let mut nd = 0;
                        for w in 0..ww { for s in 0..64 {
                            if (actm[w] >> s) & 1 == 0 || nd >= 8 { continue; }
                            nd += 1;
                            d.push_str(&format!("{{\"code\":{},\"w\":{},\"s\":{},\"sy\":{},\"sz\":{},\"ph\":{},\"p\":\"{}\",\"q\":\"{}\",\"ring\":\"{}\"}}\n",
                                v.code, w, s, val(&qs, &v.sy, w, s), val(&qs, &v.sz, w, s) + if v.zoff { v.zlo } else { 0 },
                                bit(&qs, v.ph, w, s), bs(&pl, w, s), bs(&q129, w, s), bs(&v.ring, w, s)));
                        } }
                        use std::io::Write;
                        let mut f = std::fs::OpenOptions::new().create(true).append(true)
                            .open("/tmp/lane_dump.json").unwrap();
                        f.write_all(d.as_bytes()).unwrap();
                    }
                    cur = Some(Seg { v: k, actm, or0, and1, head, touched: vec![false; width] });
                }
            }
            ei += 1;
        }
        if i == nops { break; }
        let op = &b.ops[i];
        let mut cond = base;
        if op.c_condition != crate::circuit::NO_BIT {
            for w in 0..ww { cond[w] &= bits[op.c_condition.0 as usize][w]; }
        }
        let (t, c1, c2) = (op.q_target.0 as usize, op.q_control1.0 as usize, op.q_control2.0 as usize);
        match op.kind {
            OT::CCX => { for w in 0..ww { let v = cond[w] & qs[c1][w] & qs[c2][w]; qs[t][w] ^= v; } }
            OT::CX => { for w in 0..ww { let v = cond[w] & qs[c1][w]; qs[t][w] ^= v; } }
            OT::Swap => { for w in 0..ww {
                let mut a = qs[c1][w]; let mut tt = qs[t][w];
                a ^= tt; tt ^= cond[w] & a; a ^= tt;
                qs[c1][w] = a; qs[t][w] = tt; } }
            OT::X => { for w in 0..ww { qs[t][w] ^= cond[w]; } }
            OT::Hmr => { for w in 0..ww {
                let mut buf = [0u8; 8]; xof.read(&mut buf); let r = u64::from_le_bytes(buf);
                let ct = op.c_target.0 as usize;
                bits[ct][w] &= !cond[w]; bits[ct][w] ^= r & cond[w];
                qs[t][w] &= !cond[w]; } }
            OT::R => { for w in 0..ww { qs[t][w] &= !cond[w]; } }
            OT::BitInvert => { for w in 0..ww { bits[op.c_target.0 as usize][w] ^= cond[w]; } }
            OT::BitStore0 => { for w in 0..ww { bits[op.c_target.0 as usize][w] &= !cond[w]; } }
            OT::BitStore1 => { for w in 0..ww { bits[op.c_target.0 as usize][w] |= cond[w]; } }
            OT::PushCondition => { cstack.push(base); for w in 0..ww { base[w] &= bits[op.c_condition.0 as usize][w]; } }
            OT::PopCondition => { if let Some(v) = cstack.pop() { base = v; } }
            _ => {}
        }
        if let Some(s) = cur.as_mut() {
            let touched: &[usize] = if op.kind == OT::Swap { &[t, c1] } else { &[t] };
            for &l in touched {
                if l >= width { continue; }
                s.touched[l] = true;
                for w in 0..ww {
                    let x = qs[l][w] & s.actm[w];
                    if x != 0 { s.or0[l] = true; }
                    if x != s.actm[w] { s.and1[l] = false; }
                }
            }
        }
    }
    let path = std::env::var("LANE_OUT").unwrap_or("/tmp/lane_census.json".into());
    std::fs::write(&path, out).unwrap();
    eprintln!("lane census: {} V-form plays -> {}", vinfo.len(), path);
}

// ---- lowq-size tools (ported from agent_lowq_size/base695) ----
#[test]
#[ignore = "tool"]
fn lowsize_census() {
    use super::pointadd_frogdrop::*;
    use super::payload::NP;
    use super::frogdrop_col::MARKS;
    use super::frogdrop_sched::sample;
    use crate::circuit::OperationType as OT;
    use sha3::digest::XofReader;
    std::env::set_var("FD_MARK", "1");
    const W: usize = 4;
    let seed: u64 = std::env::var("FROGDROP_SEED0").ok().and_then(|s| s.parse().ok()).unwrap_or(1000);
    let mut b = B::new();
    let xq = b.alloc_n(256);
    let pl = b.alloc_n(NP);
    // LS_NO_PL=1: the payload-free forward traversal (T3 of the point add: the payload lanes are only dirty passengers)
    let with_pl = std::env::var_os("LS_NO_PL").is_none();
    let t = trav_forward_pl(&mut b, &xq, &pl, if with_pl { Some(&pl) } else { None });
    eprintln!("census build: {} T, {} ops, peak {}", b.tof, b.ops.len(), b.peak);
    super::f1_dump();
    if std::env::var_os("LS_PROFILE_ONLY").is_some() { return; }
    let marks = MARKS.with(|m| m.borrow().clone());
    // which final register (A = fd.sy, B = fd.sx at the end) is the spare sx at each column start
    let colsx = super::frogdrop_col::COLSX.with(|m| m.borrow().clone());
    let sx_is_b: Vec<bool> = colsx.iter().map(|v| v[0] == t.fd.sx[0]).collect();
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let width = (b.width() as usize).max(aq as usize);
    // group labels: 0 ring, 1 q, 2 size A (fd.sy at the end), 3 size B (fd.sx at the end), 4 ph, 5 pool, 6 payload,
    // 7 other
    let mut grp: Vec<(u8, u16)> = vec![(7, 0); width];
    for (i, q) in t.fd.ring.iter().enumerate() { grp[q.0 as usize] = (0, i as u16); }
    for (i, q) in t.fd.q.iter().enumerate() { grp[q.0 as usize] = (1, i as u16); }
    for (i, q) in t.fd.sy.iter().enumerate() { grp[q.0 as usize] = (2, i as u16); }
    for (i, q) in t.fd.sx.iter().enumerate() { grp[q.0 as usize] = (3, i as u16); }
    grp[t.fd.ph.0 as usize] = (4, 0);
    for (i, q) in t.pool.iter().enumerate() { grp[q.0 as usize] = (5, i as u16); }
    for (i, q) in pl.iter().enumerate() { grp[q.0 as usize] = (6, i as u16); }
    let mut qs = vec![[0u64; W]; width];
    let mut bits = vec![[0u64; W]; (nb as usize).max(1)];
    let p = pval();
    for wd in 0..W {
        let xs = sample(64, seed + wd as u64);
        let mut rng = Rng::new((seed + wd as u64) ^ 0x77);
        let mut tmp = vec![0u64; width];
        for s in 0..64 {
            put(&mut tmp, &xq, s, &xs[s]);
            let dy = rng.below(256) % p;
            put(&mut tmp, &pl[..256], s, &dy);
        }
        for i in 0..width { qs[i][wd] = tmp[i]; }
    }
    // shots the classical predictor fails are excluded (LS_KEEP_BAD keeps them): their garbage is a counted failure
    let mut good = [u64::MAX; W];
    if std::env::var_os("LS_KEEP_BAD").is_none() {
        let sc = super::frogdrop_sched::from_text(SCHED_FROGDROP);
        let mut nbad = 0;
        for wd in 0..W {
            let xs = sample(64, seed + wd as u64);
            for s in 0..64 {
                if super::frogdrop_sched::predict_n(xs[s], &sc, 24, KP, QB, TOT, NQ, EMAX, N).is_some() {
                    good[wd] &= !(1u64 << s); nbad += 1;
                }
            }
        }
        eprintln!("census: {} of {} shots predicted to fail, excluded", nbad, 64 * W);
    }
    let mut h = sha3::Shake256::default();
    h.update(b"frogdrop-census");
    let mut xof = h.finalize_xof();
    let mut cstack: Vec<[u64; W]> = vec![];
    let mut base = [u64::MAX; W];
    let nz = |v: &[u64; W]| v.iter().zip(good.iter()).any(|(&x, &g)| x & g != 0);
    let mut cur: i64 = qs.iter().filter(|v| nz(v)).count() as i64;
    let mut out = String::new();
    let nops = b.ops.len();
    let mut col: i64 = -1;
    let mut i = 0usize;
    let mut gmax = 0i64;
    let gprobe = std::env::var_os("LS_GPROBE").is_some();
    let mut gst: std::collections::BTreeMap<usize, (i64, i64, usize, usize, Vec<(usize, u64, u64, usize)>)> = Default::default();
    for mi in 0..=marks.len() {
        let (a, st) = if mi < marks.len() { marks[mi] } else { (nops, 9999) };
        let z = if mi + 1 < marks.len() { marks[mi + 1].0 } else { nops };
        if mi < marks.len() && st == 0 { col += 1; }
        // LS_GPROBE: g = 257 - sz - sy per good shot at every middle mark (ZOFF off: sz plain)
        if gprobe && mi < marks.len() && col >= 1 {
            // stage marks (sz, sy plain) and the parked V-form windows (sy[7] borrowed: low seven bits, 0 = 128)
            let win = [3101, 3102, 3121, 3122].contains(&st);
            let mid = (2..=7).contains(&st) || win;
            if mid {
                let c = col as usize;
                let syr: &[QubitId] = if sx_is_b[c] { &t.fd.sy } else { &t.fd.sx };
                let szr: &[QubitId] = &t.pool[0..8];
                for wd in 0..W { for sh in 0..64 {
                    if (good[wd] >> sh) & 1 == 0 { continue; }
                    let rd = |l: &[QubitId]| l.iter().enumerate().map(|(i, q)| ((qs[q.0 as usize][wd] >> sh) & 1) << i).sum::<u64>();
                    let (z, mut y) = (rd(szr), rd(syr));
                    if win { y &= 127; if y == 0 { y = 128; } }
                    let g = 257i64 - z as i64 - y as i64;
                    let e = gst.entry(c).or_insert((i64::MAX, i64::MIN, 0usize, 0usize, vec![]));
                    e.0 = e.0.min(g); e.1 = e.1.max(g);
                    if g < 0 { e.2 += 1; }
                    if g >= 32 { e.3 += 1; }
                    if (g < 0 || g >= 32) && e.4.len() < 6 { e.4.push((st, z, y, wd * 64 + sh)); }
                } }
            }
        }
        let mut best = cur;
        let mut best_at = i;
        let mut snap: Option<Vec<u32>> = None;
        let seg_end = if mi < marks.len() { z } else { nops };
        let start = if mi < marks.len() { a } else { i };
        while i < seg_end {
            let op = &b.ops[i];
            let mut cond = base;
            if op.c_condition != crate::circuit::NO_BIT {
                for w in 0..W { cond[w] &= bits[op.c_condition.0 as usize][w]; }
            }
            let touched = [op.q_target, op.q_control1];
            let before: Vec<bool> = touched.iter().map(|x| (x.0 as usize) < width && nz(&qs[x.0 as usize])).collect();
            match op.kind {
                OT::CCX => { for w in 0..W { let v = cond[w] & qs[op.q_control1.0 as usize][w] & qs[op.q_control2.0 as usize][w]; qs[op.q_target.0 as usize][w] ^= v; } }
                OT::CX => { for w in 0..W { let v = cond[w] & qs[op.q_control1.0 as usize][w]; qs[op.q_target.0 as usize][w] ^= v; } }
                OT::Swap => { for w in 0..W {
                    let mut c1 = qs[op.q_control1.0 as usize][w]; let mut tt = qs[op.q_target.0 as usize][w];
                    c1 ^= tt; tt ^= cond[w] & c1; c1 ^= tt;
                    qs[op.q_control1.0 as usize][w] = c1; qs[op.q_target.0 as usize][w] = tt; } }
                OT::X => { for w in 0..W { qs[op.q_target.0 as usize][w] ^= cond[w]; } }
                OT::Hmr => { for w in 0..W {
                    let mut buf = [0u8; 8]; xof.read(&mut buf); let r = u64::from_le_bytes(buf);
                    let ct = op.c_target.0 as usize;
                    bits[ct][w] &= !cond[w]; bits[ct][w] ^= r & cond[w];
                    qs[op.q_target.0 as usize][w] &= !cond[w]; } }
                OT::R => { for w in 0..W { qs[op.q_target.0 as usize][w] &= !cond[w]; } }
                OT::BitInvert => { for w in 0..W { bits[op.c_target.0 as usize][w] ^= cond[w]; } }
                OT::BitStore0 => { for w in 0..W { bits[op.c_target.0 as usize][w] &= !cond[w]; } }
                OT::BitStore1 => { for w in 0..W { bits[op.c_target.0 as usize][w] |= cond[w]; } }
                OT::PushCondition => { cstack.push(base); for w in 0..W { base[w] &= bits[op.c_condition.0 as usize][w]; } }
                OT::PopCondition => { if let Some(v) = cstack.pop() { base = v; } }
                _ => {}
            }
            for (k, x) in touched.iter().enumerate() {
                if k == 1 && op.kind != OT::Swap { break; }
                if (x.0 as usize) >= width { continue; }
                let after = nz(&qs[x.0 as usize]);
                if after && !before[k] { cur += 1; }
                if !after && before[k] { cur -= 1; }
            }
            if cur > best || snap.is_none() && cur >= best {
                best = cur; best_at = i;
                snap = Some(qs.iter().map(|v| v.iter().zip(good.iter()).map(|(x, g)| (x & g).count_ones()).sum::<u32>()).collect());
            }
            i += 1;
        }
        if mi == marks.len() { break; }
        let _ = start;
        gmax = gmax.max(best);
        let s: Vec<u32> = snap.unwrap_or_else(|| qs.iter().map(|v| v.iter().zip(good.iter()).map(|(x, g)| (x & g).count_ones()).sum::<u32>()).collect());
        let mut cnt = [0usize; 8];
        let mut small: Vec<String> = vec![];
        let mut rare = [0usize; 8];
        for (id, &c) in s.iter().enumerate() {
            let (g, ix) = grp[id];
            if c > 0 { cnt[g as usize] += 1; }
            if matches!(g, 2 | 3 | 4 | 5) { small.push(format!("{}{}:{}", ["r","q","A","B","ph","p","pl","o"][g as usize], ix, c)); }
            else if c > 0 && c <= 4 { rare[g as usize] += 1; }
        }
        let sxb = if col >= 0 && (col as usize) < sx_is_b.len() { sx_is_b[col as usize] } else { false };
        out.push_str(&format!("{{\"c\":{},\"s\":{},\"max\":{},\"at\":{},\"cnt\":{:?},\"rare\":{:?},\"sx_is_b\":{},\"small\":{:?}}}\n",
                              col, st, best, best_at - a.min(best_at), cnt, rare, sxb, small));
    }
    std::fs::write(std::env::var("FD_CENSUS_OUT").unwrap_or("/tmp/scensus.json".into()), out).unwrap();
    eprintln!("pressure census: {} columns, global max {}", col + 1, gmax);
    if gprobe {
        let colinfo = super::frogdrop_col::COLINFO.with(|m| m.borrow().clone());
        let (mut lo, mut hi) = (i64::MAX, i64::MIN);
        for (c, e) in &gst {
            lo = lo.min(e.0); hi = hi.max(e.1);
            eprintln!("GPROBE col {} g [{}, {}] neg {} ge32 {} ex {:?} info {}", c, e.0, e.1, e.2, e.3, e.4,
                      colinfo.get(*c).cloned().unwrap_or_default());
        }
        eprintln!("GPROBE global g [{}, {}]", lo, hi);
    }
}

/// A/B the column-boundary states of the forward traversal with an env toggle (LS_AB_VAR=1 vs unset) on 64 census
/// shots: prints the first column whose boundary state differs and the differing lanes.
#[test]
#[ignore = "tool"]
fn lowsize_ab_boundaries() {
    use super::pointadd_frogdrop::*;
    use super::payload::NP;
    use super::frogdrop_col::MARKS;
    use super::frogdrop_sched::sample;
    super::bake_knobs();
    let var = std::env::var("LS_AB_VAR").unwrap_or("FD_NARROW_DELTA".into());
    let seed: u64 = std::env::var("FROGDROP_SEED0").ok().and_then(|s| s.parse().ok()).unwrap_or(1000);
    std::env::set_var("FD_MARK", "1");
    let xs = sample(64, seed);
    let mut rng = Rng::new(seed ^ 0x77);
    let p = pval();
    let dys: Vec<N> = (0..64).map(|_| rng.below(256) % p).collect();
    // predictor-failing shots (and shots already failing in the reference) are dropped from the comparison
    let mut bad = 0u64;
    {
        let sc = super::frogdrop_sched::from_text(SCHED_FROGDROP);
        for s in 0..64 {
            if super::frogdrop_sched::predict_n(xs[s], &sc, 24, KP, QB, TOT, NQ, EMAX, N).is_some() { bad |= 1u64 << s; }
        }
    }
    // one build at a time (memory): each build is simulated column by column and only its boundary states are kept
    let mut snaps: Vec<Vec<(Vec<u64>, u64)>> = vec![];
    let mut names_of: Vec<(String, QubitId)> = vec![];
    for on in [false, true] {
        let val = std::env::var("LS_AB_VAL").unwrap_or("1".into());
        if on { std::env::set_var(&var, &val); } else { std::env::remove_var(&var); }
        // LS_AB_EXTRA="K=V,K=V": more settings for the "on" build only (LS_AB_BASE: for the reference build)
        for (key, on_side) in [("LS_AB_EXTRA", true), ("LS_AB_BASE", false)] {
            if let Ok(ex) = std::env::var(key) {
                for kv in ex.split(',').filter(|x| !x.is_empty()) {
                    let (k, v) = kv.split_once('=').unwrap();
                    if on == on_side { std::env::set_var(k, v); } else { std::env::remove_var(k); }
                }
            }
        }
        MARKS.with(|m| m.borrow_mut().clear());
        let mut b = B::new();
        let xq = b.alloc_n(256);
        let pl = b.alloc_n(NP);
        let with_pl = std::env::var_os("LS_NO_PL").is_none();
        let t = trav_forward_pl(&mut b, &xq, &pl, if with_pl { Some(&pl) } else { None });
        let marks = MARKS.with(|m| m.borrow().clone());
        let starts: Vec<usize> = marks.iter().filter(|(_, s)| *s == 0).map(|(o, _)| *o).collect();
        eprintln!("{} = {}: {} T, {} cols", var, on, b.tof, starts.len());
        if !on {
            for (i, q) in t.fd.ring.iter().enumerate() { names_of.push((format!("ring{}", i), *q)); }
            for (i, q) in t.fd.q.iter().enumerate() { names_of.push((format!("q{}", i), *q)); }
            for (i, q) in t.fd.sy.iter().enumerate() { names_of.push((format!("A{}", i), *q)); }
            for (i, q) in t.fd.sx.iter().enumerate() { names_of.push((format!("B{}", i), *q)); }
            names_of.push(("ph".into(), t.fd.ph));
            for (i, q) in t.pool.iter().enumerate() { names_of.push((format!("p{}", i), *q)); }
            for (i, q) in pl.iter().enumerate() { names_of.push((format!("pl{}", i), *q)); }
        }
        let (aq, nb, _, _) = analyze_ops(b.ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(b"frogdrop-ab");
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new((b.width() as usize).max(aq as usize), (nb as usize).max(1), &mut xof);
        for s in 0..64 { put(&mut sim.qubits, &xq, s, &xs[s]); put(&mut sim.qubits, &pl[..256], s, &dys[s]); }
        let mut at = 0usize;
        let mut v = vec![];
        for c in 1..=starts.len() {
            let end = if c < starts.len() { starts[c] } else { b.ops.len() };
            sim.apply_iter(b.ops[at..end].iter());
            at = end;
            v.push((sim.qubits.clone(), sim.phase));
        }
        snaps.push(v);
    }
    let ncol = snaps[0].len().min(snaps[1].len());
    for c in 0..ncol {
        let (q0, ph0) = &snaps[0][c];
        let (q1, ph1) = &snaps[1][c];
        bad |= *ph0;
        let w = q0.len().min(q1.len());
        let diff: Vec<usize> = (0..w).filter(|&i| (q0[i] ^ q1[i]) & !bad != 0).collect();
        if !diff.is_empty() || (ph0 ^ ph1) & !bad != 0 {
            let name = |i: usize| -> String {
                names_of.iter().find(|(_, q)| q.0 as usize == i).map(|(n, _)| n.clone()).unwrap_or(format!("o{}", i))
            };
            let shots: u64 = diff.iter().fold(0, |a, &i| a | (q0[i] ^ q1[i]));
            eprintln!("first boundary diff after column {}: {} lanes, shots mask {:#x}, phase {:#x}/{:#x}", c,
                      diff.len(), shots, ph0, ph1);
            let names: Vec<String> = diff.iter().take(40).map(|&i| name(i)).collect();
            eprintln!("  lanes {:?}", names);
            panic!("B2 A/B column boundary differs after column {c}");
        }
    }
    assert_eq!(ncol, 203, "B2 A/B must cover all public columns");
    eprintln!("all {} column boundaries identical (reference-failing shots dropped: {:#x})", ncol, bad);

}

/// Cross-check the census's hand simulator against crate::sim on one build (64 shots): first op where they differ.
#[test]
#[ignore = "tool"]
fn lowsize_census_sim_check() {
    use super::pointadd_frogdrop::*;
    use super::payload::NP;
    use super::frogdrop_sched::sample;
    use crate::circuit::OperationType as OT;
    use sha3::digest::XofReader;
    let seed: u64 = std::env::var("FROGDROP_SEED0").ok().and_then(|s| s.parse().ok()).unwrap_or(1000);
    let mut b = B::new();
    let xq = b.alloc_n(256);
    let pl = b.alloc_n(NP);
    std::env::set_var("FD_MARK", "1");
    super::frogdrop_col::MARKS.with(|m| m.borrow_mut().clear());
    let _t = trav_forward_pl(&mut b, &xq, &pl, Some(&pl));
    let starts: Vec<usize> = super::frogdrop_col::MARKS.with(|m| m.borrow().iter().filter(|(_, s)| *s == 0).map(|(o, _)| *o).collect());
    let mut next_b = 0usize;
    let mut done_to = 0usize;
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let width = (b.width() as usize).max(aq as usize);
    let xs = sample(64, seed);
    let mut rng = Rng::new(seed ^ 0x77);
    let p = pval();
    let mut init = vec![0u64; width];
    for s in 0..64 { put(&mut init, &xq, s, &xs[s]); let dy = rng.below(256) % p; put(&mut init, &pl[..256], s, &dy); }
    let mk = || { let mut h = sha3::Shake256::default(); h.update(b"frogdrop-census"); h.finalize_xof() };
    let mut xa = mk();
    let mut xb = mk();
    let mut sim = Simulator::new(width, (nb as usize).max(1), &mut xa);
    sim.qubits.copy_from_slice(&init);
    let mut qs = init.clone();
    let mut bits = vec![0u64; (nb as usize).max(1)];
    let mut cstack: Vec<u64> = vec![];
    let mut base = u64::MAX;
    for (i, op) in b.ops.iter().enumerate() {
        let mut cond = base;
        if op.c_condition != crate::circuit::NO_BIT { cond &= bits[op.c_condition.0 as usize]; }
        match op.kind {
            OT::CCX => { let v = cond & qs[op.q_control1.0 as usize] & qs[op.q_control2.0 as usize]; qs[op.q_target.0 as usize] ^= v; }
            OT::CX => { let v = cond & qs[op.q_control1.0 as usize]; qs[op.q_target.0 as usize] ^= v; }
            OT::Swap => { let mut c1 = qs[op.q_control1.0 as usize]; let mut tt = qs[op.q_target.0 as usize];
                c1 ^= tt; tt ^= cond & c1; c1 ^= tt; qs[op.q_control1.0 as usize] = c1; qs[op.q_target.0 as usize] = tt; }
            OT::X => { qs[op.q_target.0 as usize] ^= cond; }
            OT::Hmr => { let mut buf = [0u8; 8]; xb.read(&mut buf); let r = u64::from_le_bytes(buf);
                let ct = op.c_target.0 as usize; bits[ct] &= !cond; bits[ct] ^= r & cond; qs[op.q_target.0 as usize] &= !cond; }
            OT::R => { let mut buf = [0u8; 8]; xb.read(&mut buf); qs[op.q_target.0 as usize] &= !cond; }
            OT::BitInvert => { bits[op.c_target.0 as usize] ^= cond; }
            OT::BitStore0 => { bits[op.c_target.0 as usize] &= !cond; }
            OT::BitStore1 => { bits[op.c_target.0 as usize] |= cond; }
            OT::PushCondition => { cstack.push(base); base &= bits[op.c_condition.0 as usize]; }
            OT::PopCondition => { if let Some(v) = cstack.pop() { base = v; } }
            _ => {}
        }
        let at_b = if next_b < starts.len() && i + 1 == starts[next_b] { true } else { i + 1 == b.ops.len() };
        if at_b {
            sim.apply_iter(b.ops[done_to..i + 1].iter());
            done_to = i + 1;
            let diff: Vec<usize> = (0..width).filter(|&k| sim.qubits[k] != qs[k]).collect();
            if !diff.is_empty() {
                eprintln!("census sim differs at boundary {} (op {}): {} lanes, e.g. {:?}", next_b, i + 1, diff.len(), &diff[..diff.len().min(10)]);
                return;
            }
            next_b += 1;
        }
    }
    eprintln!("census sim agrees with crate::sim over {} ops", b.ops.len());
}

#[test]
#[ignore = "tool"]
fn lowsize_predict_seed() {
    use super::pointadd_frogdrop::*;
    let seed: u64 = std::env::var("FROGDROP_SEED0").ok().and_then(|s| s.parse().ok()).unwrap_or(1000);
    let sc = super::frogdrop_sched::from_text(SCHED_FROGDROP);
    let xs = super::frogdrop_sched::sample(64, seed);
    for s in 0..64 {
        if let Some(k) = super::frogdrop_sched::predict_n(xs[s], &sc, 24, KP, QB, TOT, NQ, EMAX, N) { eprintln!("seed {seed} shot {s}: {k}"); }
    }
}
