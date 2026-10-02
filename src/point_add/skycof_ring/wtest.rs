//! Whole-walk checks of the SKY-COF ring walk ([`super::rwalk`]).
//!
//! `SKYCOF_RING_WALKTEST=small`: every odd modulus `p` of `K` bits (`K = 4..KMAX`, register width `K+1`),
//! every `d` in `[1, p)` coprime to `p`: exact per-tick windows from the classical walk (margin 0), the forward walk and
//! the walk back simulated at gate level. Checks: after the forward walk `s = (sign ? +1 : -1) 2^R / d
//! (mod p)`, nothing but `s`, `KA`, `H`, `odo`, `sign` is non-zero, zero phase, no dirty release; after the walk
//! back `d` restored, every other wire zero, zero phase, no dirty release.
//! `SKYCOF_RING_WALKTEST=full`: the full-width walk with the source envelope on random `d` (64 per batch),
//! checked the same way against the classical prediction of failures ([`classify`]).
use super::dec::{self, DecZ};
use super::ring::{Rng, TickZ};
use super::rwalk::{self, WEnv};
use super::selftest::Sim;
use crate::circuit::QubitId as Q;
use crate::point_add::builder::Builder;
use ruint::Uint;

type U = Uint<512, 8>;

fn bits(x: U) -> usize {
    512 - x.leading_zeros()
}

/// Classical state of the true walk.
#[derive(Clone, Copy, Debug)]
pub struct KSt {
    pub u: U,
    pub v: U,
    pub s: U,
    pub r: U,
}

fn rev(x: U, n: usize) -> U {
    let mut y = U::ZERO;
    for i in 0..n {
        if x.bit(i) {
            y.set_bit(n - 1 - i, true);
        }
    }
    y
}

fn cof_bits(field: U, other: U, n: usize) -> Vec<bool> {
    let x = field | rev(other, n);
    (0..n).map(|j| x.bit(j)).collect()
}

/// Per-tick record of one walk.
#[derive(Clone, Debug, Default)]
pub struct Rec {
    /// entry fields (ka, ua, vb, kap, uap, vbp) when unparked at entry
    pub entry: Option<[usize; 6]>,
    /// post fields (ka', vb', rb') when unparked after the tick
    pub post: Option<[usize; 3]>,
    /// letter 0 A, 1 B, 2 C, 3 parked
    pub letter: u8,
}

/// The true walk of `d` for `r` ticks with the circuit's fold; returns per-tick records, the final s, sign and
/// the park tick.
pub fn true_walk(d: U, p: U, n: usize, r: usize, fold_w: usize) -> (Vec<Rec>, U, bool, Option<usize>, bool) {
    let mut st = KSt { u: d, v: p, s: U::ZERO, r: U::from(1u64) };
    let mut recs = Vec::with_capacity(r);
    let mut sign = false;
    let mut park = None;
    let mut fold_ok = true;
    let top = U::from(1u64) << (n - 1);
    for t in 0..r {
        let mut rec = Rec::default();
        if park.is_none() {
            let KSt { u, v, s, r: rr } = st;
            let swap = u.bit(0) && u < v;
            let (kap, uap, vbp) = if swap { (bits(rr), bits(v), bits(u)) } else { (bits(s), bits(u), bits(v)) };
            rec.entry = Some([bits(s), bits(u), bits(v), kap, uap, vbp]);
            if !u.bit(0) {
                st = KSt { u: u >> 1usize, v, s: s << 1usize, r: rr };
                rec.letter = 0;
            } else if !swap {
                st = KSt { u: (u - v) >> 1usize, v, s: s << 1usize, r: rr + s };
                rec.letter = 1;
            } else {
                st = KSt { u: (v - u) >> 1usize, v: u, s: rr << 1usize, r: rr + s };
                rec.letter = 2;
                sign = !sign;
            }
            if st.u.is_zero() {
                park = Some(t);
            }
        } else {
            st.s <<= 1usize;
            rec.letter = 3;
        }
        if park.is_some() && st.s >= top {
            let m = (U::from(1u64) << fold_w) - U::from(1u64);
            let c = top - p;
            if ((st.s & m) + c) >> fold_w != U::ZERO {
                fold_ok = false;
            }
            st.s -= p;
            // the lazy fold keeps s below 2^(n-1) only while 2s - p < 2^(n-1) (secp256k1: s >= p never seen)
            if st.s >= top {
                fold_ok = false;
            }
        }
        if park.is_none() {
            rec.post = Some([bits(st.s), bits(st.v), bits(st.r)]);
        }
        recs.push(rec);
        let _ = sign;
    }
    // store the post states for the decoder model separately (recomputed by callers when needed)
    (recs, st.s, sign, park, fold_ok)
}

/// Push decisions of the circuit decoder along the walk of `d` (needs the post-states, so it re-walks).
pub fn pushes(d: U, p: U, n: usize, env: &WEnv) -> (Vec<u32>, bool) {
    let mut st = KSt { u: d, v: p, s: U::ZERO, r: U::from(1u64) };
    let mut h = 0u32;
    let mut out = Vec::with_capacity(env.r);
    let mut sound = true;
    for t in 0..env.r {
        if st.u.is_zero() {
            out.push(h);
            continue;
        }
        let KSt { u, v, s, r: rr } = st;
        let swap = u.bit(0) && u < v;
        let letter;
        if !u.bit(0) {
            st = KSt { u: u >> 1usize, v, s: s << 1usize, r: rr };
            letter = 0;
        } else if !swap {
            st = KSt { u: (u - v) >> 1usize, v, s: s << 1usize, r: rr + s };
            letter = 1;
        } else {
            st = KSt { u: (v - u) >> 1usize, v: u, s: rr << 1usize, r: rr + s };
            letter = 2;
        }
        if t >= 1 && !st.u.is_zero() {
            if let Some(z) = &env.dz[t] {
                let ac = cof_bits(st.s, st.u, n);
                let bc = cof_bits(st.r, st.v, n);
                let (dd, amb) = dec::model(&ac, &bc, bits(st.s), bits(st.v), n, z, true);
                if letter == 1 && !amb {
                    sound = false;
                }
                if letter == 2 && dd {
                    sound = false;
                }
                if amb {
                    h += 1;
                }
            } else {
                sound = false;
            }
        }
        out.push(h);
    }
    (out, sound)
}

#[derive(Clone, Copy)]
struct Acc {
    lo: [usize; 9],
    hi: [usize; 9],
    seen: [bool; 9],
}

impl Acc {
    fn new() -> Self {
        Acc { lo: [usize::MAX; 9], hi: [0; 9], seen: [false; 9] }
    }
    fn put(&mut self, f: usize, x: usize) {
        self.lo[f] = self.lo[f].min(x);
        self.hi[f] = self.hi[f].max(x);
        self.seen[f] = true;
    }
    fn rng(&self, f: usize) -> Rng {
        Rng::new(self.lo[f], self.hi[f])
    }
}

/// Exact envelope for every `d` in `[1, p)` (margin 0).
fn small_env(p: u64, k: usize) -> (WEnv, Vec<U>) {
    let n = k + 1;
    let pu = U::from(p);
    fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
    let r0 = 6 * n + 8;
    // inputs the walk serves exactly: coprime to p, and the lazy post-park fold valid along the walk
    let ds: Vec<U> = (1..p)
        .filter(|&d| gcd(d, p) == 1)
        .map(U::from)
        .filter(|&d| true_walk(d, pu, n, r0, n - 1).4)
        .collect();
    let mut acc = vec![Acc::new(); r0];
    let (mut pmin, mut pmax) = (usize::MAX, 0);
    for &d in &ds {
        let (recs, _, _, park, _) = true_walk(d, pu, n, r0, n - 1);
        let pk = park.expect("small walk did not park");
        pmin = pmin.min(pk);
        pmax = pmax.max(pk);
        for (t, rc) in recs.iter().enumerate() {
            if let Some(e) = rc.entry {
                for f in 0..6 {
                    acc[t].put(f, e[f]);
                }
            }
            if let Some(q) = rc.post {
                for f in 0..3 {
                    acc[t].put(6 + f, q[f]);
                }
            }
        }
    }
    let r = pmax + 3;
    let tp = pmin.max(1);
    let z: Vec<Option<TickZ>> = (0..r)
        .map(|t| {
            let a = &acc[t];
            a.seen[0].then(|| TickZ { ka: a.rng(0), ua: a.rng(1), vb: a.rng(2), kap: a.rng(3), uap: a.rng(4), vbp: a.rng(5) })
        })
        .collect();
    let dz: Vec<Option<DecZ>> = (0..r)
        .map(|t| {
            let a = &acc[t];
            (t >= 1 && a.seen[6]).then(|| DecZ { ka: a.rng(6), vb: a.rng(7), rb: a.rng(8), w: 64 })
        })
        .collect();
    let odo_bits = (usize::BITS - (r - tp + 1).leading_zeros()) as usize;
    let pbits: Vec<bool> = (0..n - 1).map(|j| (p >> j) & 1 == 1).collect();
    let mut env = WEnv { n, p: pbits, r, tp, park_j: n - 1, fold_w: n - 1, odo_bits, cap: None, z, dz, h: vec![0; r] };
    let mut h = vec![0u32; r];
    for &d in &ds {
        let (hs, sound) = pushes(d, pu, n, &env);
        assert!(sound, "small walk p={p} d={d}: decoder unsound");
        for t in 0..r {
            h[t] = h[t].max(hs[t]);
        }
    }
    for t in 1..r {
        h[t] = h[t].max(h[t - 1]);
    }
    env.h = h.iter().map(|&x| x as usize).collect();
    (env, ds)
}

fn modpow2(e: usize, p: U) -> U {
    let mut x = U::from(1u64);
    for _ in 0..e {
        x = (x << 1usize).reduce_mod(p);
    }
    x
}

pub(crate) struct Built {
    pub(crate) ops_f: Vec<crate::circuit::Op>,
    pub(crate) ops_b: Vec<crate::circuit::Op>,
    nq: usize,
    nb: usize,
    d: Vec<Q>,
    pass: Vec<Q>,
    s: Vec<Q>,
    keep_f: Vec<Q>,
    sign: Q,
    d2: Vec<Q>,
    pub(crate) peak: usize,
    /// forward accounting ranges (when enabled before the build)
    pub(crate) acct_f: Option<Vec<(&'static str, usize, usize)>>,
}

pub(crate) fn build(env: &WEnv, npass: usize) -> Built {
    let mut c = Builder::new();
    let d = c.alloc_qubits(env.n - 1);
    let pass = c.alloc_qubits(npass);
    let pk = rwalk::forward(&mut c, env, &d);
    let ops_f = c.take_ops();
    let acct_f = rwalk::ACCT.with(|x| x.borrow_mut().take());
    let mut keep_f: Vec<Q> = pk.s.iter().chain(&pk.ka).chain(&pk.h.wires).chain(&pk.odo).copied().collect();
    keep_f.push(pk.sign);
    keep_f.extend(&pass);
    let (s, sign) = (pk.s.clone(), pk.sign);
    let d2 = rwalk::backward(&mut c, env, pk);
    let ops_b = c.take_ops();
    let (nq, nb) = c.i13_dims();
    Built { ops_f, ops_b, nq, nb, d, pass, s, keep_f, sign, d2, peak: c.peak_total() as usize, acct_f }
}

/// Simulate `ds` through the built walk; returns the indices of lanes that failed (with a reason).
pub(crate) fn simulate(bt: &Built, env: &WEnv, p: U, ds: &[U], seed: u64) -> Vec<(usize, String)> {
    let mut bad = Vec::new();
    let r2 = modpow2(env.r, p);
    let mut keep_b = bt.d2.clone();
    keep_b.extend(&bt.pass);
    for (bi, chunk) in ds.chunks(64).enumerate() {
        let mut sim = Sim::new(bt.nq, bt.nb + 1, seed ^ (bi as u64) * 0x9E37);
        for (l, &d) in chunk.iter().enumerate() {
            sim.set(&bt.d, d, l);
        }
        sim.run(&bt.ops_f);
        let gf = sim.residue(&bt.keep_f);
        let (phf, dirf) = (sim.phase, sim.dirty);
        let mut fwd_bad = vec![None; chunk.len()];
        for (l, &d) in chunk.iter().enumerate() {
            let sv = sim.get(&bt.s, l);
            let sg = sim.getu(&[bt.sign], l) == 1;
            let want = r2.mul_mod(d.inv_mod(p).unwrap(), p);
            let want = if sg { want } else { (p - want).reduce_mod(p) };
            let mut why = Vec::new();
            if sv != want {
                why.push(format!("s {sv:#x} want {want:#x} sign {sg}"));
            }
            if (gf >> l) & 1 == 1 {
                why.push("fwd garbage".into());
            }
            if (phf >> l) & 1 == 1 {
                why.push("fwd phase".into());
            }
            if (dirf >> l) & 1 == 1 {
                why.push("fwd dirty".into());
            }
            if !why.is_empty() {
                fwd_bad[l] = Some(why.join(", "));
            }
        }
        sim.run(&bt.ops_b);
        let gb = sim.residue(&keep_b);
        for (l, &d) in chunk.iter().enumerate() {
            let mut why: Vec<String> = fwd_bad[l].iter().cloned().collect();
            if sim.get(&bt.d2, l) != d {
                why.push("d not restored".into());
            }
            if (gb >> l) & 1 == 1 {
                why.push("back garbage".into());
            }
            if (sim.phase >> l) & 1 == 1 {
                why.push("back phase".into());
            }
            if (sim.dirty >> l) & 1 == 1 {
                why.push("back dirty".into());
            }
            if !why.is_empty() {
                bad.push((bi * 64 + l, why.join(", ")));
            }
        }
    }
    bad
}

fn small(kmax: usize) {
    for k in 4..=kmax {
        let (mut moduli, mut walks, mut maxr, mut maxh) = (0usize, 0usize, 0usize, 0usize);
        for p in ((1u64 << (k - 1)) + 1..(1u64 << k)).step_by(2) {
            let (env, ds) = small_env(p, k);
            if ds.is_empty() {
                continue;
            }
            let bt = build(&env, 2);
            let bad = simulate(&bt, &env, U::from(p), &ds, p);
            if let Some((i, why)) = bad.first() {
                panic!("ring walk K={k} p={p} d={}: {why} ({} bad lanes)", ds[*i], bad.len());
            }
            moduli += 1;
            walks += ds.len();
            maxr = maxr.max(env.r);
            maxh = maxh.max(*env.h.last().unwrap());
        }
        println!("{{\"kind\":\"skycof-ring-walk-small\",\"K\":{k},\"N\":{},\"moduli\":{moduli},\"walks\":{walks},\"max_R\":{maxr},\"max_H\":{maxh}}}", k + 1);
    }
}

/// Trace one small walk tick by tick against the true walk (`SKYCOF_RING_WALKTEST=trace P D`).
fn trace_one(p: u64, k: usize, d: u64) {
    let (env, _) = small_env(p, k);
    let n = env.n;
    let pu = U::from(p);
    let mut c = Builder::new();
    let dq = c.alloc_qubits(n - 1);
    let mut snaps: Vec<(usize, Vec<crate::circuit::Op>, Vec<Vec<Q>>)> = Vec::new();
    let _pk = rwalk::forward_hooked(&mut c, &env, &dq, &mut |c, t, r, h, odo, sign| {
        let ops = c.take_ops();
        snaps.push((t, ops, vec![r.a.clone(), r.b.clone(), r.ka.clone(), r.vb.clone(), h.wires.clone(), odo.to_vec(), vec![sign]]));
    });
    let (nq, nb) = c.i13_dims();
    let mut sim = Sim::new(nq, nb + 1, 1);
    sim.set(&dq, U::from(d), 0);
    let mut st = KSt { u: U::from(d), v: pu, s: U::ZERO, r: U::from(1u64) };
    let top = U::from(1u64) << (n - 1);
    eprintln!("env: R={} tp={} h={:?}", env.r, env.tp, env.h);
    for (t, ops, regs) in &snaps {
        sim.run(ops);
        // true step
        if !st.u.is_zero() {
            let KSt { u, v, s, r: rr } = st;
            if !u.bit(0) { st = KSt { u: u >> 1usize, v, s: s << 1usize, r: rr }; }
            else if u >= v { st = KSt { u: (u - v) >> 1usize, v, s: s << 1usize, r: rr + s }; }
            else { st = KSt { u: (v - u) >> 1usize, v: u, s: rr << 1usize, r: rr + s }; }
            if st.u.is_zero() && st.s >= top { st.s -= pu; }
        } else {
            st.s <<= 1usize;
            if st.s >= top { st.s -= pu; }
        }
        let wa = st.u | rev(st.s, n);
        let wb = st.v | rev(st.r, n);
        let g = |i: usize| sim.get(&regs[i], 0);
        eprintln!("t={t} A={:#x} (want {wa:#x}) B={:#x} (want {wb:#x}) KA={} (bits s {}) VB={} (bits v {}) H={:#b} odo={} sign={} phase={} dirty={} z={:?} dz={:?}",
                  g(0), g(1), g(2), bits(st.s), g(3), bits(st.v), g(4), g(5), g(6), sim.phase & 1, sim.dirty & 1, env.z[*t].is_some(), env.dz[*t]);
    }
}

pub fn run() {
    crate::point_add::skycof::pointadd::snapshot_knobs();
    let mode = std::env::var("SKYCOF_RING_WALKTEST").unwrap_or_default();
    let t0 = std::time::Instant::now();
    let kmax = std::env::var("SKYCOF_RING_KMAX").ok().and_then(|v| v.parse().ok()).unwrap_or(8);
    match mode.trim() {
        "small" | "1" => small(kmax),
        "full" => super::wfull::run(),
        "trace" => {
            let a: Vec<u64> = std::env::var("SKYCOF_RING_TRACE_PD").unwrap().split(',').map(|x| x.trim().parse().unwrap()).collect();
            let k = (64 - a[0].leading_zeros()) as usize;
            trace_one(a[0], k, a[1]);
        }
        o => panic!("SKYCOF_RING_WALKTEST={o}"),
    }
    println!("{{\"kind\":\"skycof-ring-walktest\",\"result\":\"PASS\",\"mode\":\"{}\",\"secs\":{:.1}}}", mode.trim(), t0.elapsed().as_secs_f64());
}

