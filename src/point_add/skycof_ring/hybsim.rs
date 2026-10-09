//! Research probe (`SKYCOF_RESEARCH=1 SKYCOF_PROBE=hybsim`): classical model of the hybrid walk -- public
//! layout with the k2 decoder on ticks `< T1`, the masked ring (its own decoder) from `T1` on -- for several
//! switch ticks at once. Reports, per `T1`, the per-tick history quantiles (bases), the tail of the history
//! excess, and the walk failure rate from the public widths (ticks `< T1`) and the ring windows (ticks
//! `>= T1`). Writes `hybsim_bases.tsv` (columns: t, then one base column per `T1`).
//! Knobs: `SKYCOF_HYB_N1` (base walks), `SKYCOF_HYB_N2` (tail walks), `SKYCOF_HYB_T1S` (comma list),
//! `SKYCOF_HYB_THREADS`, `SKYCOF_HYB_SEED`.
use super::dec;
use super::rwalk::WEnv;
use super::wtest::{cof_bits, true_walk};
use crate::point_add::skycof::k2dec;
use crate::point_add::skycof::walk::Envelope;
use ruint::Uint;

type U = Uint<512, 8>;

fn bits(x: U) -> usize {
    512 - x.leading_zeros()
}

fn knob_usize(k: &str, d: usize) -> usize {
    crate::point_add::skycof::pointadd::knob(k).map(|v| v.parse().unwrap()).unwrap_or(d)
}

fn rng_next(s: &mut u64) -> u64 {
    *s = s.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *s;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Per-walk outputs.
struct WalkOut {
    /// cumulative public-decoder pushes after tick t (k0 at t <= 2, k2 after; the public decoder's windows)
    pubc: Vec<u16>,
    /// cumulative ring-decoder pushes after tick t
    ringc: Vec<u16>,
    /// first tick whose public widths fail (rails or cofactor field), usize::MAX if none
    pub_fail: usize,
    /// per tick: ring windows violated at this tick (entry or decoder windows)
    ring_bad: Vec<bool>,
    /// failures that do not depend on T1 within the ring region (park before TP, odometer, fold, unparked)
    tail_bad: bool,
}

fn limbs(x: U) -> Vec<u64> {
    x.as_limbs().to_vec()
}

fn walk(d: U, p: U, penv: &Envelope, renv: &WEnv, w_pub: usize, k2: (usize, usize)) -> WalkOut {
    let n = renv.n;
    let r_ticks = renv.r;
    let (recs, _, _, park, fold_ok) = true_walk(d, p, n, r_ticks, renv.fold_w);
    let mut out = WalkOut {
        pubc: vec![0; r_ticks],
        ringc: vec![0; r_ticks],
        pub_fail: usize::MAX,
        ring_bad: vec![false; r_ticks],
        tail_bad: false,
    };
    match park {
        None => out.tail_bad = true,
        Some(k) => {
            if k < renv.tp || r_ticks - k > (1usize << renv.odo_bits) - 1 {
                out.tail_bad = true;
            }
        }
    }
    if !fold_ok {
        out.tail_bad = true;
    }
    let inr = |x: usize, r: &super::ring::Rng| x >= r.lo && x <= r.hi;
    // ring windows per tick
    for (t, rc) in recs.iter().enumerate() {
        if let Some(e) = rc.entry {
            match &renv.z[t] {
                None => out.ring_bad[t] = true,
                Some(z) => {
                    let zs = [z.ka, z.ua, z.vb, z.kap, z.uap, z.vbp];
                    if (0..6).any(|f| !inr(e[f], &zs[f])) {
                        out.ring_bad[t] = true;
                    }
                }
            }
        }
        if t >= 1 {
            if let Some(q) = rc.post {
                match &renv.dz[t] {
                    None => out.ring_bad[t] = true,
                    Some(z) => {
                        if !inr(q[0], &z.ka) || !inr(q[1], &z.vb) || !inr(q[2], &z.rb) {
                            out.ring_bad[t] = true;
                        }
                    }
                }
            }
        }
    }
    // the walk itself, both decoders, public widths
    let (mut u, mut v, mut s, mut r) = (d, p, U::ZERO, U::from(1u64));
    let (mut hp, mut hr) = (0u16, 0u16);
    let mut ppark_test_fp = false;
    for t in 0..r_ticks {
        if u.is_zero() {
            out.pubc[t] = hp;
            out.ringc[t] = hr;
            continue;
        }
        let letter;
        if !u.bit(0) {
            u >>= 1usize;
            s <<= 1usize;
            letter = 0;
        } else if u >= v {
            u = (u - v) >> 1usize;
            r += s;
            s <<= 1usize;
            letter = 1;
        } else {
            let nu = (v - u) >> 1usize;
            v = u;
            u = nu;
            let ns = r << 1usize;
            r += s;
            s = ns;
            letter = 2;
        }
        let _ = letter;
        if !u.is_zero() {
            // public widths: rails {+-u, u+v} need bits(u+v)+1 <= rail(t) (pre and post), cofactors bits <= cof(t)
            if out.pub_fail == usize::MAX {
                let rw = bits(u + v) + 1;
                if rw > penv.rail[t] || bits(s).max(bits(r)) > penv.cof[t] {
                    out.pub_fail = t;
                }
            }
            if t >= 1 {
                // public decoder
                let e = penv.cof[t];
                let (sl, rl) = (limbs(s), limbs(r));
                let amb = if t >= k2.0 && t <= k2.1 {
                    k2dec::model::letters(&sl, &rl, e, w_pub, true).1
                } else {
                    crate::point_add::skycof::decoder::model::decide(&sl, &rl, e, w_pub, true).1
                };
                if amb {
                    hp += 1;
                }
                // ring decoder
                if let Some(z) = &renv.dz[t] {
                    let ac = cof_bits(s, u, n);
                    let bc = cof_bits(r, v, n);
                    let (_, amb) = dec::model(&ac, &bc, bits(s), bits(v), n, z, true);
                    if amb {
                        hr += 1;
                    }
                }
            }
            if t >= renv.tp && v == U::from(1u64) {
                let all = (n - 1 - renv.park_j..n - 1).all(|j| r.bit(j) == renv.p[j]);
                if all {
                    ppark_test_fp = true;
                }
            }
        }
        out.pubc[t] = hp;
        out.ringc[t] = hr;
    }
    if ppark_test_fp {
        out.tail_bad = true;
    }
    out
}

fn hyb_h(o: &WalkOut, t1: usize, t: usize) -> usize {
    if t < t1 {
        o.pubc[t] as usize
    } else {
        o.pubc[t1 - 1] as usize + o.ringc[t] as usize - o.ringc[t1 - 1] as usize
    }
}

pub fn run() {
    let penv = crate::point_add::skycof::pointadd::envelope();
    let renv = super::pointadd::envelope().clone();
    let w_pub = crate::point_add::skycof::pointadd::params().walk.w_dec;
    let k2 = crate::point_add::skycof::walk::k2_range();
    let p = U::from_limbs_slice(&crate::point_add::SECP256K1_P.into_limbs());
    let n1 = knob_usize("SKYCOF_HYB_N1", 200_000);
    let n2 = knob_usize("SKYCOF_HYB_N2", 1_000_000);
    let nth = knob_usize("SKYCOF_HYB_THREADS", 16);
    let seed0 = knob_usize("SKYCOF_HYB_SEED", 0x4b1d) as u64;
    let t1s: Vec<usize> = crate::point_add::skycof::pointadd::knob("SKYCOF_HYB_T1S")
        .unwrap_or_else(|| "200,220,240,260,280,300".into())
        .split(',')
        .map(|x| x.trim().parse().unwrap())
        .collect();
    let rt = renv.r;
    const NB: usize = 400;
    let nt = t1s.len();
    eprintln!("HYBSIM N1={n1} N2={n2} threads={nth} T1s={t1s:?} R={rt} public w={w_pub} k2={k2:?} ring TP={}", renv.tp);
    let gen = |sd: u64, k: usize| -> Vec<U> {
        let mut st = sd;
        let mut v = Vec::with_capacity(k);
        while v.len() < k {
            let mut x = U::ZERO;
            for i in 0..4 {
                x |= U::from(rng_next(&mut st)) << (64 * i);
            }
            let x = x.reduce_mod(p);
            if !x.is_zero() {
                v.push(x);
            }
        }
        v
    };
    // pass 1: bases
    let per = n1 / nth;
    let hs: Vec<Vec<u32>> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..nth)
            .map(|th| {
                let (renv, t1s) = (&renv, &t1s);
                sc.spawn(move || {
                    let mut h = vec![0u32; nt * rt * NB];
                    for d in gen(seed0.wrapping_mul(1_000_003).wrapping_add(th as u64), per) {
                        let o = walk(d, p, penv, renv, w_pub, k2);
                        for (j, &t1) in t1s.iter().enumerate() {
                            for t in 0..rt {
                                h[(j * rt + t) * NB + hyb_h(&o, t1, t).min(NB - 1)] += 1;
                            }
                        }
                    }
                    h
                })
            })
            .collect();
        hs.into_iter().map(|x| x.join().unwrap()).collect()
    });
    let mut tot = vec![0u64; nt * rt * NB];
    for h in hs {
        for (a, b) in tot.iter_mut().zip(h) {
            *a += b as u64;
        }
    }
    let kq = ((per * nth) as u64 / 1000).max(1);
    let quant = |h: &[u64]| -> usize {
        let mut acc = 0u64;
        for v in (0..NB).rev() {
            acc += h[v];
            if acc >= kq {
                return v;
            }
        }
        0
    };
    let mut base = vec![vec![0usize; rt]; nt];
    for j in 0..nt {
        for t in 0..rt {
            base[j][t] = quant(&tot[(j * rt + t) * NB..(j * rt + t + 1) * NB]);
        }
        for t in 1..rt {
            base[j][t] = base[j][t].max(base[j][t - 1]);
        }
    }
    eprintln!("HYBSIM pass1 done: {} walks", per * nth);
    // pass 2: excess tails and failure rates
    let per2 = n2 / nth;
    struct Agg {
        exc: Vec<[u64; 20]>,
        pubf: Vec<u64>,
        ringf: Vec<u64>,
        any_nonh: Vec<u64>,
        n: u64,
    }
    let aggs: Vec<Agg> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..nth)
            .map(|th| {
                let (renv, t1s, base) = (&renv, &t1s, &base);
                sc.spawn(move || {
                    let mut g = Agg { exc: vec![[0; 20]; nt], pubf: vec![0; nt], ringf: vec![0; nt], any_nonh: vec![0; nt], n: 0 };
                    for d in gen((seed0 + 77).wrapping_mul(1_000_003).wrapping_add(th as u64), per2) {
                        let o = walk(d, p, penv, renv, w_pub, k2);
                        g.n += 1;
                        for (j, &t1) in t1s.iter().enumerate() {
                            let mut mx = -1000i64;
                            for t in 0..rt {
                                mx = mx.max(hyb_h(&o, t1, t) as i64 - base[j][t] as i64);
                            }
                            for m in 0..20 {
                                if mx > m as i64 {
                                    g.exc[j][m] += 1;
                                }
                            }
                            let pf = o.pub_fail < t1;
                            let rf = o.ring_bad[t1..].iter().any(|&b| b) || o.tail_bad;
                            if pf {
                                g.pubf[j] += 1;
                            }
                            if rf {
                                g.ringf[j] += 1;
                            }
                            if pf || rf {
                                g.any_nonh[j] += 1;
                            }
                        }
                    }
                    g
                })
            })
            .collect();
        hs.into_iter().map(|x| x.join().unwrap()).collect()
    });
    let mut exc = vec![[0u64; 20]; nt];
    let (mut pubf, mut ringf, mut anyf) = (vec![0u64; nt], vec![0u64; nt], vec![0u64; nt]);
    let mut nn = 0u64;
    for g in aggs {
        nn += g.n;
        for j in 0..nt {
            for m in 0..20 {
                exc[j][m] += g.exc[j][m];
            }
            pubf[j] += g.pubf[j];
            ringf[j] += g.ringf[j];
            anyf[j] += g.any_nonh[j];
        }
    }
    for (j, &t1) in t1s.iter().enumerate() {
        let mut l = String::new();
        for m in 6..20 {
            l += &format!(" +{m}:{:.1e}", exc[j][m] as f64 / nn as f64);
        }
        eprintln!("HYBSIM T1={t1}: base end {} (t=320: {}); public-width fail {:.2e}, ring-window/park fail {:.2e}, any non-H {:.2e}; P(H excess > m):{l}",
            base[j][rt - 1], base[j][320], pubf[j] as f64 / nn as f64, ringf[j] as f64 / nn as f64, anyf[j] as f64 / nn as f64);
    }
    let mut f = std::fs::File::create("hybsim_bases.tsv").unwrap();
    use std::io::Write;
    writeln!(f, "t\t{}", t1s.iter().map(|x| format!("T1_{x}")).collect::<Vec<_>>().join("\t")).unwrap();
    for t in 0..rt {
        writeln!(f, "{t}\t{}", (0..nt).map(|j| base[j][t].to_string()).collect::<Vec<_>>().join("\t")).unwrap();
    }
    eprintln!("HYBSIM wrote hybsim_bases.tsv ({nn} tail walks)");
}
