//! Gate-level selftests of the D2 integration: `D2_INT_SELFTEST=1 build_circuit` (runs after the recipe is
//! installed, then exits; the default build never calls it).
//!
//! The legs are built standalone, so the coordinate / square / back-seam fusions that hand state across phase
//! boundaries are switched off for the selftest process (`R4_YSUB_FUSE`, `R4_YFIN_FUSE`, `R5_YFIN2`,
//! `FD_COORD_FUSE`, `NATIVE_SFUSE_B`, `BACK_SEAM_FUSE`); the walk, the stacks, the cells and the FD seed /
//! payload are the production ones at the production cap.
//!   L  letters: the rails-only D2 walk (FD seed -> layout -> 394 ticks with the cell-traversal plans -> walk back
//!      with the rails-only plans -> unseed) on random denominators. At every cell slot the (typ wire, s wire) pair
//!      is copied out and compared with the production carry walk's letter (typ_t, s_t) of the same input (FD seed,
//!      production tick recursion); the walk back must restore every wire, leave zero phase and no garbage.
//!   D  division leg `y <- y / x (mod p)` on random (x, y): x restored, zero phase, no garbage.
//!   M  multiplication leg `y <- y * x (mod p)`, same checks.
//! Every lane runs the real circuit; lanes that fail are listed with their park tick (the walk's own failure
//! modes: unparked at R, overflow, window tails, cell approximations) and the test fails only above
//! `D2_INT_SELFTEST_MAXFAIL` (default 2) per test.
//! Knobs: `D2_INT_SELFTEST_ONLY=LDM`, `D2_INT_SELFTEST_LANES` (default 128), `D2_INT_SELFTEST_SEED`.
use super::super::super::super::builder::Builder;
use super::super::super::super::N;
use super::*;
use crate::circuit::QubitId;
use crate::sim::Simulator;
use alloy_primitives::U256;
use sha3::{digest::{ExtendableOutput, Update}, Shake256};

fn xof(tag: &[u8]) -> sha3::Shake256Reader {
    let mut h = Shake256::default();
    h.update(b"d2-int-selftest-v1");
    h.update(tag);
    h.finalize_xof()
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn scalar(&mut self) -> U256 {
        let p = super::super::super::super::SECP256K1_P;
        loop {
            let v = U256::from_limbs([self.next(), self.next(), self.next(), self.next()]);
            if v != U256::ZERO && v < p {
                return v;
            }
        }
    }
}

fn envu(k: &str, d: usize) -> usize {
    std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d)
}

fn p() -> U256 {
    super::super::super::super::SECP256K1_P
}

/// Signed rails for the classical production walk: (negative, magnitude), |v| < 2^257.
#[derive(Clone, Copy, Debug)]
struct S {
    neg: bool,
    mag: U256,
}
impl S {
    fn from_i(neg: bool, mag: U256) -> S {
        S { neg: neg && mag != U256::ZERO, mag }
    }
    fn odd(&self) -> bool {
        // two's complement LSB equals the magnitude's LSB
        self.mag.bit(0)
    }
    /// Arithmetic shift right by one (floor division by 2).
    fn sar1(&self) -> S {
        if !self.neg {
            S::from_i(false, self.mag >> 1)
        } else {
            // floor(-m / 2) = -ceil(m / 2)
            S::from_i(true, (self.mag + U256::from(1u64)) >> 1)
        }
    }
    fn add(&self, o: &S) -> S {
        if self.neg == o.neg {
            S::from_i(self.neg, self.mag + o.mag)
        } else if self.mag >= o.mag {
            S::from_i(self.neg, self.mag - o.mag)
        } else {
            S::from_i(o.neg, o.mag - self.mag)
        }
    }
    fn negate(&self) -> S {
        S::from_i(!self.neg, self.mag)
    }
    /// Sign bit of the two's complement value (negative).
    fn sign(&self) -> bool {
        self.neg
    }
}

/// Production letters (typ_t, s_t) for t = 1..rounds-1 (index t - 1), from the FD seed of `d`.
fn production_letters(d: U256, rounds: usize) -> Vec<(bool, bool)> {
    let b = d.bit(0);
    // X = (d - b p) / 2, Y = d - (1 - b) p + X
    let dd = S::from_i(false, d);
    let pp = S::from_i(false, p());
    let x = if b { dd.add(&pp.negate()) } else { dd };
    let x = S::from_i(x.neg, x.mag >> 1); // exact halving (even value)
    let y = if b { dd.add(&x) } else { dd.add(&pp.negate()).add(&x) };
    let o0 = x.mag < y.mag;
    let (mut r1, mut r2) = (x, y);
    let mut typ = o0;
    let mut out = Vec::with_capacity(rounds - 1);
    for _ in 1..rounds {
        let c = r1.odd();
        if c {
            std::mem::swap(&mut r1, &mut r2);
        }
        let h = r1.sar1();
        let agree = h.sign() == r2.sign();
        let new = if agree { r2.add(&h.negate()) } else { r2.add(&h) };
        let s = agree ^ (h.sign() == new.sign());
        typ ^= c;
        out.push((typ, s));
        r1 = h;
        r2 = new;
    }
    out
}

fn set_val(sim: &mut Simulator<'_, sha3::Shake256Reader>, reg: &[QubitId], vals: &[U256]) {
    for (i, &q) in reg.iter().enumerate() {
        let mut w = 0u64;
        for (l, v) in vals.iter().enumerate() {
            if v.bit(i) {
                w |= 1 << l;
            }
        }
        *sim.qubit_mut(q) = w;
    }
}

fn get_val(sim: &Simulator<'_, sha3::Shake256Reader>, reg: &[QubitId], lane: usize) -> U256 {
    let mut v = U256::ZERO;
    for (i, &q) in reg.iter().enumerate() {
        if (sim.qubit(q) >> lane) & 1 == 1 {
            v.set_bit(i, true);
        }
    }
    v
}

/// Run `ops` on lanes of (x, y) inputs; return per-lane (x_out, y_out, phase ok, other wires clean).
fn run_lanes(ops: &[crate::circuit::Op], nq: usize, nb: usize, x: &[QubitId], y: &[QubitId], xs: &[U256], ys: &[U256],
             tag: &[u8]) -> Vec<(U256, U256, bool, bool)> {
    let mut out = Vec::new();
    let mut r = xof(tag);
    let mut sim = Simulator::new(nq, nb + 64, &mut r);
    let io: std::collections::BTreeSet<u64> = x.iter().chain(y.iter()).map(|q| q.0).collect();
    for chunk in 0..xs.len().div_ceil(64) {
        let lo = chunk * 64;
        let hi = (lo + 64).min(xs.len());
        sim.clear_for_shot();
        set_val(&mut sim, x, &xs[lo..hi]);
        set_val(&mut sim, y, &ys[lo..hi]);
        sim.apply_iter(ops.iter());
        let mut dirty = 0u64;
        for q in 0..nq as u64 {
            if !io.contains(&q) {
                dirty |= sim.qubit(QubitId(q));
            }
        }
        for l in 0..hi - lo {
            out.push((get_val(&sim, x, l), get_val(&sim, y, l), (sim.phase >> l) & 1 == 0, (dirty >> l) & 1 == 0));
        }
    }
    out
}

fn standalone_env() {
    for k in ["R4_YSUB_FUSE", "R4_YFIN_FUSE", "R5_YFIN2", "FD_COORD_FUSE", "NATIVE_SFUSE_B", "BACK_SEAM_FUSE"] {
        std::env::remove_var(k);
    }
}

fn test_leg(kind: char, lanes: usize, seed: u64, maxfail: usize) {
    let mut b = Builder::new();
    let x = b.alloc_qubits(N);
    let y = b.alloc_qubits(N);
    match kind {
        'D' => super::super::divide(&mut b, &y, &x),
        'M' => super::super::multiply(&mut b, &y, &x),
        _ => unreachable!(),
    }
    b.finalize_records();
    let (nq, nb) = b.i13_dims();
    let peak = b.peak_total();
    let ops = b.take_ops();
    let tof = ops.iter().filter(|o| o.kind == crate::circuit::OperationType::CCX).count();
    let mut rng = Rng(seed ^ kind as u64);
    let xs: Vec<U256> = (0..lanes).map(|_| rng.scalar()).collect();
    let ys: Vec<U256> = (0..lanes).map(|_| rng.scalar()).collect();
    let res = run_lanes(&ops, nq, nb, &x, &y, &xs, &ys, &[kind as u8]);
    let pm = p();
    let mut fails = Vec::new();
    for (i, (xo, yo, ph, cl)) in res.iter().enumerate() {
        let want = match kind {
            'D' => ys[i].mul_mod(xs[i].pow_mod(pm - U256::from(2u64), pm), pm),
            _ => ys[i].mul_mod(xs[i], pm),
        };
        let ok_x = *xo == xs[i];
        let ok_y = *yo == want;
        if !(ok_x && ok_y && *ph && *cl) {
            fails.push(format!("lane {i}: x {} y {} phase {} clean {}", ok_x, ok_y, ph, cl));
        }
    }
    for f in &fails {
        eprintln!("  {kind} {f}");
    }
    let name = if kind == 'D' { "division y/x" } else { "multiplication y*x" };
    eprintln!("D2_INT_SELFTEST {kind} {name}: {}/{lanes} lanes exact (x restored, zero phase, no garbage); {} ops, {tof} CCX static, peak {peak}, {nq} qubits",
        lanes - fails.len(), ops.len());
    assert!(fails.len() <= maxfail, "D2_INT_SELFTEST {kind}: {} failing lanes > {maxfail}", fails.len());
}

/// L: letters at every cell slot vs the production walk, then the exact walk back.
fn test_letters(lanes: usize, seed: u64, maxfail: usize) {
    let cfg = config();
    let r = cfg.rounds();
    let d = d2cfg(r);
    let plans = rail_plans(d);
    let mut b = Builder::new();
    let x = b.alloc_qubits(N);
    let y = b.alloc_qubits(N); // idle partner register (checked untouched)
    let rec: Vec<(QubitId, QubitId)> = (0..d.ticks).map(|_| (b.alloc_qubit(), b.alloc_qubit())).collect();
    let (rails, o0, _) = fd_seed(&mut b, &x, wpost(cfg, 0), false);
    let mut w = to_layout(&mut b, rails, o0, d.a, d.sched.pbits());
    let mut marks = Vec::new();
    for t in 0..d.ticks {
        let blocks = d2_stack::tick_blocks(&w.lay, &d.sched, t);
        rail(&mut b, &mut w, &plans.low, t, Dir::Forward);
        d2_stack::after_tick_fwd(&mut b, &blocks);
        b.cx(w.lay.typ_wire(t), rec[t].0);
        b.cx(w.lay.s, rec[t].1);
        d2_stack::after_cell_fwd(&mut b, &blocks);
    }
    marks.push(b.op_count());
    for t in (0..d.ticks).rev() {
        let blocks = d2_stack::tick_blocks(&w.lay, &d.sched, t);
        d2_stack::before_cell_rev(&mut b, &blocks);
        b.cx(w.lay.typ_wire(t), rec[t].0);
        b.cx(w.lay.s, rec[t].1);
        d2_stack::after_cell_rev(&mut b, &blocks);
        rail(&mut b, &mut w, &plans.high, t, Dir::Reverse);
    }
    let (rails, o0) = from_layout(&mut b, w);
    let xo = fd_unseed(&mut b, rails, o0, None, super::super::super::super::back_seam::Leg::Div);
    super::super::super::restore_layout(&mut b, &xo, &x);
    b.finalize_records();
    let (nq, nb) = b.i13_dims();
    let ops = b.take_ops();
    let half = marks[0];
    let mut rng = Rng(seed ^ 0x4c);
    let xs: Vec<U256> = (0..lanes).map(|_| rng.scalar()).collect();
    let ys: Vec<U256> = (0..lanes).map(|_| rng.scalar()).collect();
    let mut xr = xof(b"L");
    let mut sim = Simulator::new(nq, nb + 64, &mut xr);
    let io: std::collections::BTreeSet<u64> = x.iter().chain(y.iter()).map(|q| q.0).collect();
    let mut fails = Vec::new();
    let mut letters_checked = 0usize;
    for chunk in 0..lanes.div_ceil(64) {
        let lo = chunk * 64;
        let hi = (lo + 64).min(lanes);
        sim.clear_for_shot();
        set_val(&mut sim, &x, &xs[lo..hi]);
        set_val(&mut sim, &y, &ys[lo..hi]);
        sim.apply_iter(ops[..half].iter());
        let mut bad_letter = vec![None; hi - lo];
        for l in 0..hi - lo {
            let want = production_letters(xs[lo + l], r);
            for t in 0..d.ticks {
                let typ = (sim.qubit(rec[t].0) >> l) & 1 == 1;
                let s = (sim.qubit(rec[t].1) >> l) & 1 == 1;
                if (typ, s) != want[t] && bad_letter[l].is_none() {
                    bad_letter[l] = Some(t);
                }
                letters_checked += 1;
            }
        }
        sim.apply_iter(ops[half..].iter());
        let mut dirty = 0u64;
        for q in 0..nq as u64 {
            if !io.contains(&q) {
                dirty |= sim.qubit(QubitId(q));
            }
        }
        for l in 0..hi - lo {
            let ok_x = get_val(&sim, &x, l) == xs[lo + l] && get_val(&sim, &y, l) == ys[lo + l];
            let ph = (sim.phase >> l) & 1 == 0;
            let cl = (dirty >> l) & 1 == 0;
            if bad_letter[l].is_some() || !(ok_x && ph && cl) {
                fails.push(format!("lane {}: first letter mismatch {:?}, restored {ok_x}, phase {ph}, clean {cl}", lo + l, bad_letter[l]));
            }
        }
    }
    for f in &fails {
        eprintln!("  L {f}");
    }
    eprintln!("D2_INT_SELFTEST L letters: {}/{lanes} lanes with every (typ, s) at the {} cell slots equal to the production walk and an exact walk back ({letters_checked} letters checked; {} ops, {nq} qubits)",
        lanes - fails.len(), d.ticks, ops.len());
    assert!(fails.len() <= maxfail, "D2_INT_SELFTEST L: {} failing lanes > {maxfail}", fails.len());
}

pub fn run() {
    standalone_env();
    let only = std::env::var("D2_INT_SELFTEST_ONLY").unwrap_or_else(|_| "LDM".into());
    let lanes = envu("D2_INT_SELFTEST_LANES", 128);
    let seed = envu("D2_INT_SELFTEST_SEED", 20261001) as u64;
    let maxfail = envu("D2_INT_SELFTEST_MAXFAIL", 2);
    eprintln!("D2_INT_SELFTEST tests={only} lanes={lanes} seed={seed} cap={}", h7::cap());
    if only.contains('L') {
        test_letters(lanes, seed, maxfail);
    }
    if only.contains('D') {
        test_leg('D', lanes, seed, maxfail);
    }
    if only.contains('M') {
        test_leg('M', lanes, seed, maxfail);
    }
    eprintln!("D2_INT_SELFTEST PASS");
}
