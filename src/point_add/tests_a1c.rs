//! Lane A1c tests (lean 5, POOL_1 = 10): component identities of the po-free S1..S5 and a two-pool differential of
//! the traversal (the 811 parent at pool 11 and this tree's lean form at pool 10, both from this source) on directed
//! adversarial inputs plus random ones, slot by slot in Plain mode and end to end in the paired ghost mode.

use super::builder::B;
use super::froghop_one::{FhOne, LayOne, W1};
use super::refmodel_one::{self as rm, bl, Ph, St, N};
use super::tests_double::run;
use super::tests_one::{expect_lanes_one, gb, getv, putv};
use crate::circuit::QubitId;

/// S5's be erase without po (lean >= 5) against the parent's be and po erasures, as Boolean functions of every
/// assignment of (fo, dep5, f1, se, cmp, be, po), with and without the first-step f1 term:
/// (a) the regenerated be (inverse playback from be = po = 0) is the same function in both;
/// (b) every input the parent leaves clean (be = po = 0) the new erase leaves clean (be = 0);
/// (c) counted, not asserted: inputs the new erase leaves clean and the parent does not (po off its S5 value).
#[test]
fn a1c_s5_be_formula_exhaustive() {
    let mut only_new = 0;
    for f1slot in [false, true] {
        for x in 0u32..128 {
            let bit = |i: u32| (x >> i) & 1 == 1;
            let (fo, dep5, f1, se, cmp, be, po) = (bit(0), bit(1), bit(2) && f1slot, bit(3), bit(4), bit(5), bit(6));
            // parent (froghop_one.rs S5, lean 4): be ^= (po ^ se) & cmp, then po ^= fo & (dep5 | cmp & !f1)
            let pbe = be ^ ((po ^ se) & cmp);
            let ppo = po ^ (fo & (dep5 | (cmp & !f1)));
            // new: be ^= (fo & (dep5 | !f1) ^ se) & cmp
            let nbe = be ^ (((fo & (dep5 | !f1)) ^ se) & cmp);
            if !pbe && !ppo {
                assert!(!nbe, "parent clean, new dirty: {x:07b} f1slot {f1slot}");
            }
            if !nbe && (pbe || ppo) {
                only_new += 1;
            }
            // regeneration from 0
            if !be && !po {
                let rpo = fo & (dep5 | (cmp & !f1));
                let rbe = (rpo ^ se) & cmp;
                let rn = ((fo & (dep5 | !f1)) ^ se) & cmp;
                assert_eq!(rbe, rn, "regenerated be differs: {x:07b} f1slot {f1slot}");
            }
        }
    }
    eprintln!("A1c S5 be erase: parent-clean => new-clean on all 256 assignments; regenerated be identical; \
               {only_new} assignments clean only in the new form (parent po off its regenerated value)");
}

/// S1's po erase (lean >= 5) as a Boolean identity over every pre-S1 depth code d6 (all 64, including the unused
/// codes 0..30), fo, the D lane the old scan would read for d = 1 (lane b) and the stack-top lane for d >= 2:
/// after dec, the implicit-top-1 fix and the d >= 2 scan, po == fo & (dep5_new | be) on every input.
#[test]
fn a1c_s1_po_identity_exhaustive() {
    for d6 in 0u32..64 {
        for fo in [false, true] {
            for top in [false, true] {
                let po = fo && (d6 >> 5) & 1 == 1;
                let d6n = if po { d6 - 1 } else { d6 };
                let dep5n = (d6n >> 5) & 1 == 1;
                let mut be = false;
                be ^= po && !dep5n; // the fix
                if po && dep5n { be ^= top; } // the scan (d_old >= 2 only): be <-> stack top
                assert_eq!(po, fo && (dep5n || be), "d6 {d6} fo {fo} top {top}");
            }
        }
    }
    eprintln!("A1c S1 po identity: exact on 256 inputs (all depth codes)");
}

fn state_ok(words: &[u64], f: &FhOne, lay: &LayOne, sigma: usize, k: usize, m: &St) -> bool {
    let parity = ((sigma + 1) & 1) as u64;
    if m.pi as u64 & 1 != parity || 2 * getv(words, &f.pi, k) + parity != m.pi as u64 { return false; }
    let (ed, ev) = expect_lanes_one(m);
    for j in 0..W1 {
        if gb(words, f.d[j], k) as u8 != ed[j] || gb(words, f.v[j], k) as u8 != ev[j] { return false; }
    }
    if gb(words, f.al_s, k) != (m.k != 0) as u64 { return false; }
    if m.ph != Ph::Dn {
        if getv(words, &f.k, k) != m.k as u64 || getv(words, &f.dep, k) != m.stk.len() as u64 + 31 { return false; }
    } else {
        let kb = super::froghop_one::KB;
        let stamp = sigma - lay.first_termon - 1 - m.cnt as usize;
        if getv(words, &f.cnt(), k) != (stamp ^ (0b111 << kb)) as u64 { return false; }
        if getv(words, &f.dep[3..], k) != 0b011 { return false; }
    }
    let bb = super::froghop_one::BB;
    let bs = lay.base[sigma.saturating_sub(1)];
    let first_fin = lay.rows.iter().position(|r| r[9] != 0).unwrap_or(lay.s);
    let brep = if m.ph == Ph::Out && m.k > 0 { bl(&m.r) } else { m.b };
    let b1 = if sigma <= first_fin && m.k != 0 { brep + m.pi } else { brep };
    let u = (b1 as i64 - 1 - bs as i64).rem_euclid(1 << bb) as u64;
    if getv(words, &f.bq, k) != u { return false; }
    let f1on = sigma < lay.f1w;
    let (fo, fd, fnn) = (gb(words, f.fo, k), gb(words, f.fd, k), gb(words, f.fnn, k));
    let done = if f1on { 0 } else { fnn };
    let want = match m.ph { Ph::Out => (1, 0, 0), Ph::Ret => (0, 0, 0), Ph::Div => (0, 1, 0), Ph::Dn => (0, 0, 1) };
    if (fo, fd, done) != want { return false; }
    if f1on && fnn as u8 != m.f1 { return false; }
    gb(words, f.par, k) as u8 == m.par
}

/// Directed traversal inputs (already reflected, x' = min(x, p - x)): small values, powers of two and their
/// neighbours, p >> k (first quotient about 2^k) and neighbours, (p - 1) / 2, Fibonacci-ratio divisors (all
/// quotients 1), and p - 2^k (reflected to 2^k - c).
pub(crate) fn a1c_directed() -> Vec<N> {
    let pp = rm::p();
    let one = N::from(1u64);
    let mut xs: Vec<N> = vec![];
    for v in 1u64..=32 { xs.push(N::from(v)); }
    for k in 1..256 {
        let t = one << k;
        for x in [t - one, t, t + one] { xs.push(x); }
        if k < 256 { xs.push(pp - t); }
    }
    for k in 1..128 {
        let t = pp >> k;
        for x in [t - one, t, t + one] { xs.push(x); }
    }
    let half = (pp - one) >> 1;
    for x in [half, half - one, half - N::from(2u64)] { xs.push(x); }
    // Fibonacci ratio: x / p ~ 1 / phi^2 (after reflection), quotients 2, 1, 1, ...
    let (mut a, mut b) = (N::from(1u64), N::from(1u64));
    for i in 0..200 {
        let c = a + b;
        a = b;
        b = c;
        if i > 150 && b.bit_len() < 120 {
            let x = pp * a / b;
            xs.push(x);
            xs.push(x + one);
        }
    }
    let mut out: Vec<N> = xs.into_iter().filter(|x| *x > N::ZERO && *x < pp).map(|x| St::new(x).rv).collect();
    out.sort();
    out.dedup();
    out
}

fn tree(lay: &LayOne, npool: usize) -> (B, FhOne, Vec<QubitId>) {
    let mut b = B::new();
    let d = b.alloc_n(W1);
    let v = b.alloc_n(W1);
    let par = b.alloc();
    let mut f = FhOne::alloc_with_pool(&mut b, d, v, lay, par, vec![], 0, npool);
    let vl: Vec<QubitId> = f.v[1..257].to_vec();
    f.init(&mut b, lay);
    (b, f, vl)
}

/// (parent pool, new pool): A1C_POOLS=<parent>,<new>, default (POOL_1 + 1, POOL_1).
fn pools() -> (usize, usize) {
    let p = super::froghop_one::POOL_1;
    std::env::var("A1C_POOLS").ok().map(|v| {
        let w: Vec<usize> = v.split(',').map(|t| t.trim().parse().unwrap()).collect();
        (w[0], w[1])
    }).unwrap_or((p + 1, p))
}

fn inputs(nrand: usize, seed: u64) -> (Vec<N>, usize) {
    // lane A1e: A1E_XFILE=<file> (hex x' per line, '#' comments) replaces the directed list
    let mut xs = match std::env::var("A1E_XFILE") {
        Ok(path) => std::fs::read_to_string(&path).unwrap().lines().filter_map(|l| {
            let t = l.split('#').next().unwrap().trim();
            let t = t.split_whitespace().next()?;
            let x = N::from_str_radix(t.trim_start_matches("0x"), 16).ok()?;
            (x > N::ZERO && x < rm::p()).then(|| St::new(x).rv)
        }).collect(),
        Err(_) => a1c_directed(),
    };
    let ndir = xs.len();
    let mut rng = super::tests_double::Rng::new(seed);
    while xs.len() < ndir + nrand || xs.len() % 64 != 0 {
        let mut v = N::ZERO;
        for i in 0..4 { v |= N::from(rng.next()) << (64 * i); }
        if v > N::ZERO && v < rm::p() { xs.push(St::new(v).rv); }
    }
    (xs, ndir)
}

/// Simulate one Plain-mode slot op by op from `w` (64 shots). Returns (words, phase, bad): `bad` marks the shots on
/// which some measurement-based AND uncompute (Hmr then a CZ conditioned on its outcome) met a target that is not
/// the AND of its controls; such a shot is off its specification whatever the measurement outcome.
fn step(ops: &[crate::circuit::Op], nq: usize, w: &[u64]) -> (Vec<u64>, u64, u64) {
    use crate::circuit::OperationType as OT;
    use sha3::digest::{ExtendableOutput, Update};
    let mut h = sha3::Shake256::default();
    h.update(b"a1c-step");
    let mut xof = h.finalize_xof();
    let (aq, nbits, _, _) = crate::circuit::analyze_ops(ops.iter());
    let mut sim = crate::sim::Simulator::new(nq.max(aq as usize), (nbits as usize).max(1), &mut xof);
    sim.qubits[..w.len()].copy_from_slice(w);
    let mut bad = 0u64;
    for (i, op) in ops.iter().enumerate() {
        assert!(!matches!(op.kind, OT::PushCondition | OT::PopCondition), "condition blocks in a Plain slot");
        if op.kind == OT::Hmr {
            let nx = &ops[i + 1];
            assert!(nx.kind == OT::CZ && nx.c_condition == op.c_target, "Hmr outside an AND uncompute");
            let q = &sim.qubits;
            bad |= q[op.q_target.0 as usize] ^ (q[nx.q_control1.0 as usize] & q[nx.q_target.0 as usize]);
        }
        sim.apply_iter(std::iter::once(op));
    }
    (sim.qubits[..w.len()].to_vec(), sim.phase, bad)
}

/// Plain-mode differential, pool 11 (parent, lean 4) vs pool 10 (lean 5), slot by slot from identical inputs. A
/// parent slot is good on a shot when it maps an on-model state to the next on-model state with zero phase, a clean
/// pool and every measured AND uncompute exact. On every good parent slot the new tree must agree on D, V, par,
/// flags, pi, k, depth, b offset and al_s, and itself have zero phase, a clean pool and exact uncomputes.
/// Divergences in or after the slot where the parent left its specification are counted.
/// Inputs: `a1c_directed()` then A1C_DIFF_RANDOM=<n> (default 64) random reflected x'; A1C_DIFF_X=<hex> runs one input.
#[test]
fn a1c_traversal_differential() {
    let lay = super::layout_one();
    let nrand: usize = std::env::var("A1C_DIFF_RANDOM").ok().and_then(|v| v.parse().ok()).unwrap_or(64);
    let (mut xs, ndir) = inputs(nrand, 4711);
    if let Ok(h) = std::env::var("A1C_DIFF_X") { xs = vec![St::new(N::from_str_radix(h.trim(), 16).unwrap()).rv; 64]; }
    let (mut good_end, mut parent_off, mut off_div) = (0usize, 0usize, 0usize);
    let mut off_hist = std::collections::BTreeMap::<usize, usize>::new();
    let nb = xs.len() / 64;
    for batch in 0..nb {
        let chunk: Vec<N> = xs[64 * batch..64 * batch + 64].to_vec();
        let (pp, pn) = pools();
        let (mut bp, mut fp, vlp) = tree(&lay, pp);
        let (mut bn, mut fnw, vln) = tree(&lay, pn);
        assert_eq!(vlp, vln);
        let ncmp = fp.pool[0].0 as usize; // every qubit below the pool: D, V, par and the traversal state
        assert_eq!(ncmp, fnw.pool[0].0 as usize);
        let (nqp, nqn) = (bp.width() as usize, bn.width() as usize);
        let init = |wd: &mut Vec<u64>| { for k in 0..64 { putv(wd, &vlp, k, &chunk[k]); } };
        let mut wp = run(&bp.ops, nqp, &init).q;
        let mut wn = run(&bn.ops, nqn, &init).q;
        let mut models: Vec<St> = chunk.iter().map(|&x| St::new(x)).collect();
        let mut off = [usize::MAX; 64]; // the slot in which the parent left its specification
        let mut div = [usize::MAX; 64]; // the first slot in which the trees disagree
        for sigma in 0..=lay.s {
            for k in 0..64 {
                if off[k] == usize::MAX && !state_ok(&wp, &fp, &lay, sigma, k, &models[k]) {
                    off[k] = sigma.saturating_sub(1);
                }
            }
            if sigma == lay.s { break; }
            let sp = bp.ops.len();
            fp.slot(&mut bp, &lay, sigma);
            let (wp1, php, badp) = step(&bp.ops[sp..], nqp, &wp);
            let sn = bn.ops.len();
            fnw.slot(&mut bn, &lay, sigma);
            let (wn1, phn, badn) = step(&bn.ops[sn..], nqn, &wn);
            wp = wp1;
            wn = wn1;
            let mut pd = 0u64;
            for &q in fp.pool.iter() { pd |= wp[q.0 as usize]; }
            let mut nd = 0u64;
            for &q in fnw.pool.iter() { nd |= wn[q.0 as usize]; }
            let mut diff = php | phn | pd | nd | badp | badn;
            for q in 0..ncmp { diff |= wp[q] ^ wn[q]; }
            for k in 0..64 {
                if ((pd | php | badp) >> k) & 1 == 1 && off[k] == usize::MAX { off[k] = sigma; }
                if (diff >> k) & 1 == 1 && div[k] == usize::MAX { div[k] = sigma; }
            }
            for m in models.iter_mut() { m.fwd_at(sigma); }
        }
        for k in 0..64 {
            if off[k] == usize::MAX { good_end += 1; } else { parent_off += 1; *off_hist.entry(off[k]).or_insert(0) += 1; }
            if div[k] != usize::MAX {
                assert!(off[k] != usize::MAX && off[k] <= div[k],
                        "x' {:#x}: trees diverge in slot {} on a good parent slot (parent off in {})",
                        chunk[k], div[k], off[k]);
                off_div += 1;
            }
        }
        eprintln!("  batch {}/{nb}: on spec to the end {good_end}, parent left its spec {parent_off}, \
                   divergences (all in or after that slot) {off_div}", batch + 1);
    }
    eprintln!("A1c differential (Plain, pools {:?}): {} inputs ({ndir} directed), parent on spec to the end \
               {good_end}, parent left its spec {parent_off} (slot histogram {:?}), trees diverged (only in or after \
               that slot) {off_div}", pools(), xs.len(), off_hist);
}

/// Paired ghost differential (forward ghost + repaired inverse, the build's traversal pair), pool 11 vs 10, on the
/// directed and random inputs: per shot, the pair must restore V = x', zero every other wire (pool, state, D) and
/// leave zero phase. The failing sets of the two trees must be equal (A1C_PAIR_RANDOM=<n>, default 64).
#[test]
fn a1c_paired_differential() {
    let lay = super::layout_one();
    let nrand: usize = std::env::var("A1C_PAIR_RANDOM").ok().and_then(|v| v.parse().ok()).unwrap_or(64);
    let (xs, ndir) = inputs(nrand, 815);
    let nb = xs.len() / 64;
    let (mut both, mut only_p, mut only_n) = (0u32, 0u32, 0u32);
    for batch in 0..nb {
        let chunk: Vec<N> = xs[64 * batch..64 * batch + 64].to_vec();
        let mut fails = [0u64; 2];
        for (ti, npool) in [pools().0, pools().1].into_iter().enumerate() {
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
            let mut rng = super::tests_double::Rng::new(77 + batch as u64);
            let fw: Vec<u64> = foreign.iter().map(|_| rng.next()).collect();
            let r = run(&b.ops, b.width() as usize, &|wd| {
                for k in 0..64 { putv(wd, &vl, k, &chunk[k]); }
                for (i, &q) in foreign.iter().enumerate() { wd[q.0 as usize] = fw[i]; }
            });
            let mut bad = r.phase;
            for q in 0..b.width() as usize {
                if vl.iter().chain(foreign.iter()).any(|x| x.0 as usize == q) { continue; }
                bad |= r.q[q];
            }
            for (i, &q) in foreign.iter().enumerate() { bad |= r.q[q.0 as usize] ^ fw[i]; }
            for k in 0..64 {
                let mut got = N::ZERO;
                for (i, &q) in vl.iter().enumerate() { if (r.q[q.0 as usize] >> k) & 1 == 1 { got.set_bit(i, true); } }
                if got != chunk[k] { bad |= 1 << k; }
            }
            fails[ti] = bad;
        }
        both += (fails[0] & fails[1]).count_ones();
        only_p += (fails[0] & !fails[1]).count_ones();
        only_n += (fails[1] & !fails[0]).count_ones();
        for k in 0..64 {
            if ((fails[0] ^ fails[1]) >> k) & 1 == 1 {
                eprintln!("  paired differs x' {:#x}: parent fails {}, new fails {}", chunk[k], (fails[0] >> k) & 1, (fails[1] >> k) & 1);
            }
        }
        eprintln!("  batch {}/{nb}: both fail {both}, only parent {only_p}, only new {only_n}", batch + 1);
    }
    eprintln!("A1c paired differential (pools {:?}): {} inputs ({ndir} directed): both fail {both}, only parent \
               {only_p}, only new {only_n}", pools(), xs.len());
    assert_eq!(only_n, 0, "a shot fails only in the new tree");
    assert_eq!(only_p, 0, "a shot fails only in the parent tree");
}

/// Emitted Toffoli per stage of a Plain traversal for several pool sizes side by side (A1C_PROF_POOLS=11,10,9).
#[test]
fn a1c_profile_pools() {
    use crate::circuit::OperationType as OT;
    use std::collections::BTreeMap;
    let Ok(ps) = std::env::var("A1C_PROF_POOLS") else { return };
    let lay = super::layout_one();
    let pools: Vec<usize> = ps.split(',').map(|t| t.trim().parse().unwrap()).collect();
    let mut cols: Vec<BTreeMap<&'static str, u64>> = vec![];
    for &np in &pools {
        let mut b = B::new();
        let d = b.alloc_n(W1);
        let v = b.alloc_n(W1);
        let par = b.alloc();
        let mut f = FhOne::alloc_with_pool(&mut b, d, v, &lay, par, vec![], 0, np);
        f.init(&mut b, &lay);
        let mut tot: BTreeMap<&'static str, u64> = BTreeMap::new();
        for sigma in 0..lay.s {
            f.marks.clear();
            let start = b.ops.len();
            f.slot(&mut b, &lay, sigma);
            let mut mk = vec![("pre", start)];
            mk.extend(f.marks.iter().cloned());
            mk.push(("end", b.ops.len()));
            for i in 0..mk.len() - 1 {
                let c = b.ops[mk[i].1..mk[i + 1].1].iter().filter(|o| matches!(o.kind, OT::CCX | OT::CCZ)).count() as u64;
                *tot.entry(mk[i].0).or_default() += c;
            }
            b.ops.clear();
        }
        cols.push(tot);
    }
    let keys: Vec<&str> = cols[0].keys().copied().collect();
    eprintln!("stage  {}", pools.iter().map(|p| format!("{:>10}", format!("pool {p}"))).collect::<String>());
    for k in keys {
        eprintln!("{:6} {}", k, cols.iter().map(|c| format!("{:>10}", c.get(k).copied().unwrap_or(0))).collect::<String>());
    }
    eprintln!("total  {}", cols.iter().map(|c| format!("{:>10}", c.values().sum::<u64>())).collect::<String>());
}
