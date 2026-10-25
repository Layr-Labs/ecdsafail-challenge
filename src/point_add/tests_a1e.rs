//! Lane A1e tests (lean 9, POOL_1 = 6): the S2 window-envelope screen of the moved pop, and the kernels of the
//! lean-9 rewrites.

use super::froghop_one::{LayOne, W1};
use super::refmodel_one::{self as rm, bl, Ph, St, N};
use super::tests_one::expect_lanes_one;
use std::sync::Mutex;

fn hex(x: &N) -> String {
    format!("{:x}", x)
}

/// S2 ladder lanes that take part in the compare for an OUT shot with k == 0 at slot `sigma` (the circuit's mask
/// semantics, mask.rs): lanes outside every source window are ordinary (always active); a masked lane is active iff
/// the running mask f is 1 there, f toggled on at lane pi (pi source, window [0, min(jw, lv))) and off at lane
/// bq + 2 + base (bq source, window [p1lo, lv)), each toggle taking effect before its lane's cell.
pub(crate) fn s2_active(lay: &LayOne, sigma: usize, pi: u32, b: u32) -> impl Fn(usize) -> bool {
    let r = lay.rows[sigma];
    let (lv, jw, p1lo) = (r[0].min(W1), r[1], r[2]);
    let base = lay.base[sigma] as i64;
    let bq = (b as i64 - 1 - base).rem_euclid(64);
    let lpi = pi as usize;
    let pi_tog = lpi < jw.min(lv);
    let lbq = (bq + 2 + base) as usize;
    let bq_tog = p1lo < lv && lbq >= p1lo && lbq < lv;
    move |l: usize| {
        if l >= lv { return false; }
        let masked = l < jw.min(lv) || (p1lo < lv && l >= p1lo);
        if !masked { return true; }
        (pi_tog && lpi <= l) ^ (bq_tog && lbq <= l)
    }
}

/// [S > R] over the active lanes (the masked compare's top carry with carry-in 0).
fn masked_ct(dl: &[u8], vl: &[u8], act: &dyn Fn(usize) -> bool, lv: usize) -> bool {
    for l in (0..lv.min(W1)).rev() {
        if act(l) && dl[l] != vl[l] {
            return vl[l] == 1;
        }
    }
    false
}

#[derive(Default, Clone, Copy)]
struct Tally {
    /// OUT, k == 0, b != 1, d >= 2 slot events
    pop_slots: u64,
    /// ... whose stack-top lane takes part in the S2 compare (the mask covers it)
    top_cov: u64,
    /// ... where the compare result with the top bit present differs from the one with it cleared
    diff: u64,
    /// ... of which the parent (top cleared) gets the model's alignment decision right and the moved pop does not
    diff_parent_ok: u64,
    /// ... of which the parent is already wrong there (and the moved pop right)
    diff_parent_bad: u64,
    /// top lane covered, both compares equal, parent compare off the model (the parent's own miss)
    cov_parent_bad: u64,
}

/// One division (x' already reflected): the S2 envelope events of the moved pop (lane A1e). Returns the tally and
/// the first event slot of each class.
pub(crate) fn s2_envelope_events(x: N, lay: &LayOne) -> (Tally, Vec<(usize, &'static str)>) {
    let mut st = St::new(x);
    let mut t = Tally::default();
    let mut ev = vec![];
    for s in 0..lay.s {
        if st.ph == Ph::Dn { break; }
        let s0 = st.clone();
        let d0 = s0.stk.len();
        if s0.ph == Ph::Out && s0.k == 0 && s0.b != 1 && d0 >= 2 && s >= 1 && s < lay.trail_start {
            t.pop_slots += 1;
            let br = bl(&s0.r);
            let top = br as usize + d0 - 1;
            let act = s2_active(lay, s, s0.pi, s0.b);
            if top < W1 && act(top) {
                t.top_cov += 1;
                let lv = lay.rows[s][0];
                let (dn, vl) = expect_lanes_one(&s0);
                let mut dp = dn.clone();
                dp[top] = 0;
                let ctn = masked_ct(&dn, &vl, &act, lv);
                let ctp = masked_ct(&dp, &vl, &act, lv);
                let ctm = (s0.rv << s0.pi as usize) > s0.r;
                if ctn != ctp {
                    t.diff += 1;
                    if ctp == ctm { t.diff_parent_ok += 1; ev.push((s, "diff_parent_ok")); }
                    else { t.diff_parent_bad += 1; ev.push((s, "diff_parent_bad")); }
                } else {
                    if ctp != ctm { t.cov_parent_bad += 1; }
                    ev.push((s, "cov"));
                }
            }
        }
        st.fwd_at(s);
    }
    (t, ev)
}

/// A1E_SCREEN=<n> A1E_SEED=<s> A1E_THREADS=<t> [A1E_OUT=<file>]: n random reflected x' through the integer model;
/// per OUT k == 0 d >= 2 slot, whether the S2 mask covers the stack-top lane (it must not on a window hit) and, if
/// so, whether the compare with the top bit still in D (the moved pop) differs from the parent's (top bit already
/// popped) and which of the two matches the model. Prints the tally; the x' of every covering event go to A1E_OUT.
/// A1E_SCREEN_FILE=<file> screens the hex x' listed there instead.
#[test]
fn a1e_s2_envelope_screen() {
    let lay = super::layout_one();
    if let Ok(path) = std::env::var("A1E_SCREEN_FILE") {
        let mut tot = Tally::default();
        for l in std::fs::read_to_string(&path).unwrap().lines() {
            let l = l.split('#').next().unwrap().trim();
            let l = l.split_whitespace().last().unwrap_or("");
            if l.is_empty() || l.starts_with('[') { continue; }
            let Ok(x) = N::from_str_radix(l.trim_start_matches("0x"), 16) else { continue };
            if x == N::ZERO || x >= rm::p() { continue; }
            let x = St::new(x).rv;
            let (t, ev) = s2_envelope_events(x, &lay);
            add(&mut tot, &t);
            if !ev.is_empty() { println!("A1EV {} {:?}", hex(&x), ev); }
        }
        println!("A1ESCREENFILE {}", fmt(&tot));
        return;
    }
    let Ok(n) = std::env::var("A1E_SCREEN") else { return };
    let n: usize = n.parse().unwrap();
    let seed: u64 = std::env::var("A1E_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
    let threads: usize = std::env::var("A1E_THREADS").ok().and_then(|v| v.parse().ok()).unwrap_or(6);
    let t0 = std::time::Instant::now();
    let found: Mutex<Vec<(u64, N, Vec<(usize, &'static str)>)>> = Mutex::new(vec![]);
    let tot: Mutex<Tally> = Mutex::new(Tally::default());
    let per = n.div_ceil(threads);
    std::thread::scope(|sc| {
        for th in 0..threads {
            let (lay, found, tot) = (&lay, &found, &tot);
            sc.spawn(move || {
                let mut rng = super::tests_double::Rng::new(seed * 104729 + th as u64);
                let mut loc = Tally::default();
                for i in 0..per {
                    let mut v = N::ZERO;
                    for w in 0..4 { v |= N::from(rng.next()) << (64 * w); }
                    if v == N::ZERO || v >= rm::p() { continue; }
                    let x = St::new(v).rv;
                    let (t, ev) = s2_envelope_events(x, lay);
                    add(&mut loc, &t);
                    if !ev.is_empty() { found.lock().unwrap().push(((th * per + i) as u64, x, ev)); }
                }
                add(&mut tot.lock().unwrap(), &loc);
            });
        }
    });
    let mut f = found.into_inner().unwrap();
    f.sort_by_key(|v| v.0);
    let mut out = String::new();
    for (_, x, ev) in &f {
        println!("A1EV {} {:?}", hex(x), ev);
        out += &format!("{}\n", hex(x));
    }
    if let Ok(p) = std::env::var("A1E_OUT") { std::fs::write(p, out).unwrap(); }
    println!("A1ESCREEN {} divisions seed {seed} threads {threads}: {} ({:.1}s)", per * threads,
             fmt(&tot.into_inner().unwrap()), t0.elapsed().as_secs_f64());
}

fn add(a: &mut Tally, b: &Tally) {
    a.pop_slots += b.pop_slots;
    a.top_cov += b.top_cov;
    a.diff += b.diff;
    a.diff_parent_ok += b.diff_parent_ok;
    a.diff_parent_bad += b.diff_parent_bad;
    a.cov_parent_bad += b.cov_parent_bad;
}

fn fmt(t: &Tally) -> String {
    format!("pop slots (OUT k=0 d>=2) {} | stack top covered by the S2 mask {} (parent compare already off the model \
             there with the compares equal {}) | compares differ {} (parent right, moved pop wrong {}; parent wrong {})",
            t.pop_slots, t.top_cov, t.cov_parent_bad, t.diff, t.diff_parent_ok, t.diff_parent_bad)
}

/// The mask model above against the gate-level S2 ladder is checked indirectly: on every window hit the top lane
/// must be inactive (B1 + 1 = b + 1 <= top); this asserts it on random model trajectories.
#[test]
fn a1e_s2_mask_model_window_hit() {
    let lay = super::layout_one();
    let mut rng = super::tests_double::Rng::new(0xa1e);
    let mut checked = 0u64;
    for _ in 0..2000 {
        let mut v = N::ZERO;
        for w in 0..4 { v |= N::from(rng.next()) << (64 * w); }
        if v == N::ZERO || v >= rm::p() { continue; }
        let mut st = St::new(St::new(v).rv);
        for s in 0..lay.s {
            if st.ph == Ph::Dn { break; }
            let d0 = st.stk.len();
            if st.ph == Ph::Out && st.k == 0 && st.b != 1 && d0 >= 2 && s >= 1 && s < lay.trail_start {
                let r = lay.rows[s];
                let br = bl(&st.r) as usize;
                let hit = br + 1 >= r[2] && br + 2 <= r[0];
                if hit {
                    let act = s2_active(&lay, s, st.pi, st.b);
                    assert!(!act(br + d0 - 1), "slot {s}: window hit but the top lane is active");
                    assert!(act(br) || br < st.pi as usize, "slot {s}: lane b inactive on a window hit");
                    checked += 1;
                }
            }
            st.fwd_at(s);
        }
    }
    eprintln!("A1e S2 mask model: {checked} window-hit pop slots, top lane inactive on every one");
}

/// Lane A1e: `onehot_scan_short` (short skip-k decoder, lane pairs plus unpaired lanes) against `onehot_scan` with a
/// plain retained decoder, both moving x into V[j] at the matching lane by Fredkins (the pair form as
/// cswap(v0, V[j], V[j+1]) cswap(p, x, V[j]) cswap(v0, V[j], V[j+1]), the unpaired form as a Barenco-controlled
/// Fredkin on a dirty lane): every value v (n = 6..8, k = 2..3 where the short form has its dirty lanes), several
/// windows and offsets of both parities, x / V / dirty random; identical results, decoder lanes back to 0, v and the
/// dirty lane restored, zero phase.
#[test]
fn a1e_short_scan_exhaustive() {
    use super::builder::B;
    use super::mask::{fredkin_pair, fredkin_single, onehot_scan, onehot_scan_short, short_pre, skip_pre_k};
    use super::tests_double::{run, Rng};
    use crate::circuit::QubitId;
    let mut rng = Rng::new(0xa1e5);
    let mut checked = 0usize;
    for (n, k) in [(6usize, 2usize), (7, 2), (7, 3), (8, 2), (8, 3)] {
        for (lo, hi) in [(0usize, 12usize), (3, 14), (1, 2), (2, 3), (5, 40), (0, 1), (9, 75)] {
            for off in [-3isize, 0, 1, 6, 7, (1isize << n) - 20, (1isize << n) - 61] {
                let build = |short: bool| -> (B, Vec<QubitId>, Vec<QubitId>, QubitId, Vec<QubitId>, QubitId) {
                    let mut b = B::new();
                    let v = b.alloc_n(n);
                    let pre = b.alloc_n(if short { n - 2 - k } else { n - 1 });
                    let x = b.alloc();
                    let vl = b.alloc_n(hi + 1);
                    let dq = b.alloc();
                    if short {
                        let pm = short_pre(&skip_pre_k(&pre, k));
                        onehot_scan_short(&mut b, &v, &pm, lo, hi, off,
                            |b, j, p, q0| fredkin_pair(b, q0, p, x, vl[j], vl[j + 1]),
                            |b, j, p, lit| fredkin_single(b, p, lit, x, vl[j], dq));
                    } else {
                        onehot_scan(&mut b, &v, &pre, lo, hi, off, |b, j, o| { b.cswap(o, x, vl[j]); });
                    }
                    (b, v, pre, x, vl, dq)
                };
                let (bs, vs, ps, xs, vls, dqs) = build(true);
                let (br, vr, pr, xr, vlr, dqr) = build(false);
                for base in (0..1usize << n).step_by(64) {
                    let vals: Vec<usize> = (0..64).map(|sh| (base + sh) % (1 << n)).collect();
                    let xw = rng.next();
                    let vw: Vec<u64> = (0..=hi).map(|_| rng.next()).collect();
                    let dw = rng.next();
                    let mk = |v: &[QubitId], x: QubitId, vl: &[QubitId], dq: QubitId| {
                        let (v, vl) = (v.to_vec(), vl.to_vec());
                        let vals = vals.clone();
                        let vw = vw.clone();
                        move |w: &mut Vec<u64>| {
                            for i in 0..n {
                                let mut wd = 0u64;
                                for (sh, &val) in vals.iter().enumerate() { if (val >> i) & 1 == 1 { wd |= 1 << sh; } }
                                w[v[i].0 as usize] = wd;
                            }
                            w[x.0 as usize] = xw;
                            for (i, &q) in vl.iter().enumerate() { w[q.0 as usize] = vw[i]; }
                            w[dq.0 as usize] = dw;
                        }
                    };
                    let rs = run(&bs.ops, bs.width() as usize, &mk(&vs, xs, &vls, dqs));
                    let rr = run(&br.ops, br.width() as usize, &mk(&vr, xr, &vlr, dqr));
                    assert_eq!(rs.phase, 0, "phase n {n} k {k} [{lo},{hi}) off {off}");
                    assert_eq!(rr.phase, 0);
                    for i in 0..n { assert_eq!(rs.q[vs[i].0 as usize], rr.q[vr[i].0 as usize], "v restored"); }
                    for &q in &ps { assert_eq!(rs.q[q.0 as usize], 0, "short decoder lane n {n} k {k} [{lo},{hi}) off {off}"); }
                    for &q in &pr { assert_eq!(rr.q[q.0 as usize], 0); }
                    assert_eq!(rs.q[dqs.0 as usize], dw, "dirty lane restored");
                    assert_eq!(rs.q[xs.0 as usize], rr.q[xr.0 as usize], "x n {n} k {k} [{lo},{hi}) off {off}");
                    for i in 0..=hi { assert_eq!(rs.q[vls[i].0 as usize], rr.q[vlr[i].0 as usize], "V[{i}] n {n} k {k} [{lo},{hi}) off {off}"); }
                    checked += 64;
                }
            }
        }
    }
    eprintln!("A1e short scan: {checked} (value, window, offset) cases identical to the retained scan");
}

/// Lane A1e, gate (a)/(d) inputs: Lagrange constructions x' = B t^-1 mod p (Legendre: (B, t) is then a (remainder,
/// cofactor) pair of the division, so the quotient before remainder B is about p / (t B)), with t chosen so that this
/// quotient is Q = 2^(k-1) + 2^s + (random below 2^s), s = 1..3 (the moved pop's hazard pattern: zero stack bits
/// above a one at the alignment height s), or a random Q of bit length k; k = 8..72. Each x' is screened like
/// `a1e_s2_envelope_screen`; prints every x' with a covering event (A1EV) and the tally. A1E_CONSTRUCT=<n>
/// [A1E_SEED, A1E_THREADS, A1E_OUT].
#[test]
fn a1e_hazard_construct() {
    let Ok(n) = std::env::var("A1E_CONSTRUCT") else { return };
    let n: usize = n.parse().unwrap();
    let seed: u64 = std::env::var("A1E_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(7);
    let threads: usize = std::env::var("A1E_THREADS").ok().and_then(|v| v.parse().ok()).unwrap_or(6);
    let lay = super::layout_one();
    let pp = rm::p();
    let t0 = std::time::Instant::now();
    let found: Mutex<Vec<(N, Vec<(usize, &'static str)>, String)>> = Mutex::new(vec![]);
    let tot: Mutex<Tally> = Mutex::new(Tally::default());
    let per = n.div_ceil(threads);
    std::thread::scope(|sc| {
        for th in 0..threads {
            let (lay, found, tot) = (&lay, &found, &tot);
            sc.spawn(move || {
                let mut rng = super::tests_double::Rng::new(seed * 7907 + th as u64);
                let mut loc = Tally::default();
                for _ in 0..per {
                    let lb = 1 + (rng.next() % 200) as usize;
                    let k = 8 + (rng.next() % 65) as usize;
                    let s = 1 + (rng.next() % 3) as usize;
                    let pattern = rng.next() % 4 != 0;
                    let bb: N = (N::from(1u64) << (lb - 1)) | (rng.below(lb - 1));
                    let q: N = if pattern {
                        (N::from(1u64) << (k - 1)) | (N::from(1u64) << s) | rng.below(s)
                    } else {
                        (N::from(1u64) << (k - 1)) | rng.below(k - 1)
                    };
                    let den: N = bb * q + (bb >> 1usize);
                    if den.is_zero() || den >= pp { continue; }
                    let t = pp / den;
                    if t.is_zero() || bb * t * N::from(2u64) >= pp { continue; }
                    let Some(ti) = t.inv_mod(pp) else { continue };
                    let x = bb.mul_mod(ti, pp);
                    if x.is_zero() { continue; }
                    let x = St::new(x).rv;
                    let (tl, ev) = s2_envelope_events(x, lay);
                    add(&mut loc, &tl);
                    if !ev.is_empty() {
                        found.lock().unwrap().push((x, ev, format!("B~2^{lb} k {k} s {s} pat {pattern}")));
                    }
                }
                add(&mut tot.lock().unwrap(), &loc);
            });
        }
    });
    let f = found.into_inner().unwrap();
    let mut out = String::new();
    for (x, ev, tag) in &f {
        println!("A1EV {} {:?} # {tag}", hex(x), ev);
        out += &format!("{}  # {tag} {:?}\n", hex(x), ev);
    }
    if let Ok(p) = std::env::var("A1E_OUT") { std::fs::write(p, out).unwrap(); }
    println!("A1ECONSTRUCT {} constructions seed {seed}: {} ({:.1}s)", per * threads, fmt(&tot.into_inner().unwrap()),
             t0.elapsed().as_secs_f64());
}

/// Lane A1e: the paired ghost traversal (forward ghost + repaired inverse, the build's pair) of pools 7 and 6 on the
/// inputs of A1E_XFILE, simulated with A1E_SEEDS (default 30) different measurement streams; per input and pool, how
/// often the pair leaves a classical / ancilla error (V != x', any other wire dirty, foreign words changed) and how
/// often only the phase. A measurement-dependent (phase-coin) failure shows as a fraction strictly between 0 and the
/// seed count. Prints every input whose classical / ancilla failure count differs between the pools (A1EPH) unless
/// A1E_PH_ALL=1 (every input), then the totals.
#[test]
fn a1e_paired_phase_seeds() {
    use super::builder::B;
    use super::froghop_one::FhOne;
    use super::tests_one::putv;
    use sha3::digest::{ExtendableOutput, Update};
    let Ok(path) = std::env::var("A1E_XFILE") else { return };
    let nseeds: usize = std::env::var("A1E_SEEDS").ok().and_then(|v| v.parse().ok()).unwrap_or(30);
    let all = std::env::var("A1E_PH_ALL").is_ok();
    let lay = super::layout_one();
    let mut xs: Vec<N> = std::fs::read_to_string(&path).unwrap().lines().filter_map(|l| {
        let t = l.split('#').next().unwrap().trim();
        let t = t.split_whitespace().next()?;
        let x = N::from_str_radix(t.trim_start_matches("0x"), 16).ok()?;
        (x > N::ZERO && x < rm::p()).then(|| St::new(x).rv)
    }).collect();
    assert!(!xs.is_empty());
    let nx = xs.len();
    while xs.len() % 64 != 0 { xs.push(xs[0]); }
    let mut tallies = vec![[[0usize; 2]; 2]; xs.len()]; // [pool][data, phase-only]
    for (ti, npool) in [7usize, 6].into_iter().enumerate() {
        let mut b = B::new();
        let d = b.alloc_n(W1);
        let v = b.alloc_n(W1);
        let par = b.alloc();
        let foreign = b.alloc_n(256);
        let mut f = FhOne::alloc_with_pool(&mut b, d, v, &lay, par, foreign.clone(), 0, npool);
        let vl = f.v[1..257].to_vec();
        f.init(&mut b, &lay);
        let trace = f.forward_ghost(&mut b, &lay);
        f.inverse_ghost(&mut b, &lay, trace);
        f.init(&mut b, &lay);
        let (aq, nbits, _, _) = crate::circuit::analyze_ops(b.ops.iter());
        let nq = (b.width() as usize).max(aq as usize);
        for batch in 0..xs.len() / 64 {
            for seed in 0..nseeds {
                let mut rng = super::tests_double::Rng::new(77 + seed as u64);
                let fw: Vec<u64> = foreign.iter().map(|_| rng.next()).collect();
                let mut h = sha3::Shake256::default();
                h.update(format!("a1e-phase-seed-{seed}").as_bytes());
                let mut xof = h.finalize_xof();
                let mut sim = crate::sim::Simulator::new(nq, (nbits as usize).max(1), &mut xof);
                for k in 0..64 { putv(&mut sim.qubits, &vl, k, &xs[64 * batch + k]); }
                for (i, &q) in foreign.iter().enumerate() { sim.qubits[q.0 as usize] = fw[i]; }
                sim.apply_iter(b.ops.iter());
                let q = &sim.qubits;
                let mut bad = 0u64;
                for w in 0..nq {
                    if vl.iter().chain(foreign.iter()).any(|x| x.0 as usize == w) { continue; }
                    bad |= q[w];
                }
                for (i, &x) in foreign.iter().enumerate() { bad |= q[x.0 as usize] ^ fw[i]; }
                for k in 0..64 {
                    let mut got = N::ZERO;
                    for (i, &x) in vl.iter().enumerate() { if (q[x.0 as usize] >> k) & 1 == 1 { got.set_bit(i, true); } }
                    if got != xs[64 * batch + k] { bad |= 1 << k; }
                }
                for k in 0..64 {
                    let t = &mut tallies[64 * batch + k][ti];
                    if (bad >> k) & 1 == 1 { t[0] += 1; } else if (sim.phase >> k) & 1 == 1 { t[1] += 1; }
                }
            }
        }
    }
    let (mut data_diff, mut ph7, mut ph6, mut d7, mut d6) = (0usize, 0usize, 0usize, 0usize, 0usize);
    for k in 0..nx {
        let t = &tallies[k];
        d7 += t[0][0]; d6 += t[1][0]; ph7 += t[0][1]; ph6 += t[1][1];
        if t[0][0] != t[1][0] { data_diff += 1; }
        if all || t[0][0] != t[1][0] {
            println!("A1EPH x' {} | pool 7: data/ancilla {} phase-only {} of {nseeds} | pool 6: data/ancilla {} phase-only {} of {nseeds}",
                     hex(&xs[k]), t[0][0], t[0][1], t[1][0], t[1][1]);
        }
    }
    println!("A1EPHSUM {nx} inputs x {nseeds} seeds: classical/ancilla failures pool 7 {d7}, pool 6 {d6}; inputs whose \
              classical/ancilla failure count differs {data_diff}; phase-only failures pool 7 {ph7}, pool 6 {ph6}");
}
