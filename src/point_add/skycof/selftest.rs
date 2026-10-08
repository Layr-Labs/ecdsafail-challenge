//! Gate-level selftests of the SKY-COF tick: `SKYCOF_TICK_SELFTEST=1 build_circuit`
//! (`SKYCOF_TICK_SELFTEST=cost` runs only the cost report). Knobs: `SKYCOF_ST_KMAX` (largest small field,
//! default 8), `SKYCOF_ST_FULL_BATCHES` (64-walk batches at full width, default 16), `SKYCOF_ST_TRAIN`
//! (full-width envelope training walks, default 4000), `SKYCOF_ST_XCHECK` (classical cross-check walks,
//! default 20000), `SKYCOF_DESIGN_WIDTHS` (design width table for the cost report).
//!
//! 1. adders: every plan (ladder, chunks, recursive, vented) x control x carry-in x operand length x room,
//!    exhaustive over all inputs for n <= 6, random at n in {52, 66, 256, 257}; add then subtract.
//! 2. tick, every reachable state: all odd P in (2^(K-1), 2^K), all d in [1, P), every tick of the walk
//!    (pre-park, park, 4 post-park ticks with the park fold), four width layouts (clamped, growing,
//!    steady with operand trim, growing into the clamp), caps from the minimum to unbounded, with and
//!    without typ_{t-1}: one forward tick checked against the classical spec, then the reverse tick.
//! 3. walks, small fields: whole walks at per-tick public widths, forward (checked every tick) and back.
//! 4. walks, full width (secp256k1 p): random d, R = 400, envelope from training walks.
//! 5. classical cross-check of the rail letters against the Kaliski walk (scd.rs semantics).
//! 6. cost per call at the design's widths and model rooms vs the design's cost model.
//! Every gate-level check: values exact, zero phase, no dirty release, every non-register wire zero.
use super::adder::{self, Force, Plan};
use super::tick::*;
use super::walk::with_rail_parity_loan;
use crate::circuit::{Op, OperationType as K, QubitId as Q, NO_BIT};
use crate::point_add::builder::Builder;
use crate::point_add::heo::Rails;
use ruint::Uint;
use std::collections::BTreeMap;

type U = Uint<512, 8>;

fn env_usize(k: &str, d: usize) -> usize {
    std::env::var(k)
        .ok()
        .and_then(|v| v.trim().parse().ok())
        .unwrap_or(d)
}

// ─── simulator (bitsliced, 64 shots; dirty-release detection) ─────────────────

struct Sim {
    q: Vec<u64>,
    b: Vec<u64>,
    phase: u64,
    dirty: u64,
    rng: u64,
    ccx_exec: u64,
}

impl Sim {
    fn new(nq: usize, nb: usize, seed: u64) -> Self {
        Sim {
            q: vec![0; nq],
            b: vec![0; nb.max(1)],
            phase: 0,
            dirty: 0,
            rng: seed ^ 0x5EED_5C0F,
            ccx_exec: 0,
        }
    }
    fn next(&mut self) -> u64 {
        self.rng = self.rng.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.rng;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn clear(&mut self) {
        self.q.iter_mut().for_each(|x| *x = 0);
        self.b.iter_mut().for_each(|x| *x = 0);
        self.phase = 0;
        self.dirty = 0;
        self.ccx_exec = 0;
    }
    fn run(&mut self, ops: &[Op]) {
        let mut stack: Vec<u64> = Vec::new();
        let mut base = u64::MAX;
        for o in ops {
            let mut co = base;
            if o.c_condition != NO_BIT && o.kind != K::PushCondition {
                co &= self.b[o.c_condition.0 as usize];
            }
            let t = o.q_target.0 as usize;
            match o.kind {
                K::X => self.q[t] ^= co,
                K::CX => self.q[t] ^= co & self.q[o.q_control1.0 as usize],
                K::CCX => {
                    let v = co & self.q[o.q_control1.0 as usize] & self.q[o.q_control2.0 as usize];
                    self.q[t] ^= v;
                    self.ccx_exec += co.count_ones() as u64;
                }
                K::Z => self.phase ^= co & self.q[t],
                K::CZ => self.phase ^= co & self.q[t] & self.q[o.q_control1.0 as usize],
                K::CCZ => {
                    self.phase ^= co
                        & self.q[t]
                        & self.q[o.q_control1.0 as usize]
                        & self.q[o.q_control2.0 as usize];
                    self.ccx_exec += co.count_ones() as u64;
                }
                K::Swap => {
                    let a = o.q_control1.0 as usize;
                    let d = (self.q[a] ^ self.q[t]) & co;
                    self.q[a] ^= d;
                    self.q[t] ^= d;
                }
                K::Neg => self.phase ^= co,
                K::Hmr => {
                    let r = self.next();
                    let ct = o.c_target.0 as usize;
                    self.b[ct] = (self.b[ct] & !co) | (r & co);
                    self.phase ^= self.q[t] & r & co;
                    self.q[t] &= !co;
                }
                K::R => {
                    self.dirty |= co & self.q[t];
                    self.q[t] &= !co;
                }
                K::BitInvert => self.b[o.c_target.0 as usize] ^= co,
                K::BitStore0 => self.b[o.c_target.0 as usize] &= !co,
                K::BitStore1 => self.b[o.c_target.0 as usize] |= co,
                K::PushCondition => {
                    stack.push(base);
                    base &= self.b[o.c_condition.0 as usize];
                }
                K::PopCondition => base = stack.pop().expect("condition stack underflow"),
                K::Register | K::AppendToRegister | K::DebugPrint => {}
            }
        }
        assert!(stack.is_empty(), "unbalanced conditions");
    }
    fn set(&mut self, reg: &[Q], v: U, shot: usize) {
        for (i, w) in reg.iter().enumerate() {
            let q = &mut self.q[w.0 as usize];
            if v.bit(i) {
                *q |= 1 << shot
            } else {
                *q &= !(1 << shot)
            }
        }
    }
    fn get(&self, reg: &[Q], shot: usize) -> U {
        let mut v = U::ZERO;
        for (i, w) in reg.iter().enumerate() {
            if (self.q[w.0 as usize] >> shot) & 1 == 1 {
                v.set_bit(i, true);
            }
        }
        v
    }
    fn get_signed(&self, reg: &[Q], shot: usize) -> U {
        let mut v = self.get(reg, shot);
        if !reg.is_empty() && v.bit(reg.len() - 1) {
            for i in reg.len()..512 {
                v.set_bit(i, true);
            }
        }
        v
    }
    fn wire(&self, q: Q, shot: usize) -> bool {
        (self.q[q.0 as usize] >> shot) & 1 == 1
    }
    /// OR over all qubits outside `keep`.
    fn residue(&self, keep: &[Q]) -> u64 {
        let mut m = vec![false; self.q.len()];
        for k in keep {
            m[k.0 as usize] = true;
        }
        self.q
            .iter()
            .enumerate()
            .filter(|(i, _)| !m[*i])
            .fold(0, |a, (_, &x)| a | x)
    }
}

fn mask(n: usize) -> u64 {
    if n >= 64 {
        u64::MAX
    } else {
        (1u64 << n) - 1
    }
}

// ─── classical model ─────────────────────────────────────────────────────────

fn neg(x: U) -> bool {
    x.bit(511)
}
fn sar1(x: U) -> U {
    let y = x >> 1usize;
    if neg(x) {
        y | (U::from(1u64) << 511usize)
    } else {
        y
    }
}
fn bits(x: U) -> usize {
    512 - x.leading_zeros()
}
/// Signed two's-complement width (incl. sign).
fn sw(x: U) -> usize {
    if neg(x) {
        bits(!x) + 1
    } else {
        bits(x) + 1
    }
}
fn pow2(k: usize) -> U {
    U::from(1u64) << k
}
fn secp_p() -> U {
    pow2(256) - pow2(32) - U::from(977u64)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct St {
    r1: U,
    r2: U,
    s: U,
    r: U,
    typ: bool,
}

#[derive(Clone, Copy, Debug)]
struct Step {
    post: St,
    isc: bool,
    c: bool,
    agree: bool,
    /// rail-add operand and both R2 values (widths)
    h: U,
    r2_old: U,
    /// cofactor add operand `s'` before the relabel
    s_op: U,
}

/// The tick's classical spec (rails drive the letters).
fn spec(st: &St) -> Step {
    let (mut r1, mut r2) = (st.r1, st.r2);
    let c = r1.bit(0);
    if c {
        std::mem::swap(&mut r1, &mut r2);
    }
    let h = sar1(r1);
    let agree = neg(h) == neg(r2);
    let r2n = if agree {
        r2.wrapping_sub(h)
    } else {
        r2.wrapping_add(h)
    };
    let isc = neg(r2n) != neg(r2);
    let typ = st.typ ^ c;
    let (mut s, mut r) = (st.s, st.r);
    if isc {
        std::mem::swap(&mut s, &mut r);
    }
    if !typ {
        r += s;
    }
    let s_op = s;
    s <<= 1usize;
    Step {
        post: St {
            r1: h,
            r2: r2n,
            s,
            r,
            typ,
        },
        isc,
        c,
        agree,
        h,
        r2_old: r2,
        s_op,
    }
}

/// Park fold at clamp `w`: `x >= 2^w -> x - p`. None when the result leaves the field.
fn fold(x: U, p: U, w: usize) -> Option<U> {
    if x >= pow2(w) {
        let y = x - p;
        if y >= pow2(w) {
            None
        } else {
            Some(y)
        }
    } else {
        Some(x)
    }
}

fn seed(d: U, p: U) -> St {
    St {
        r1: d + p,
        r2: d,
        s: U::ZERO,
        r: U::from(1u64),
        typ: false,
    }
}

/// Kaliski reference letter for (u, v) (scd.rs): 0 = A, 1 = B, 2 = C, 3 = parked.
fn kal_step(u: &mut U, v: &mut U, s: &mut U, r: &mut U, p: U, w: usize) -> u8 {
    if u.is_zero() {
        *s <<= 1usize;
        *s = fold(*s, p, w).unwrap_or(*s);
        return 3;
    }
    let l;
    if !u.bit(0) {
        *u >>= 1usize;
        *s <<= 1usize;
        l = 0;
    } else if *u >= *v {
        *u = (*u - *v) >> 1usize;
        *r += *s;
        *s <<= 1usize;
        l = 1;
    } else {
        let nu = (*v - *u) >> 1usize;
        *v = *u;
        *u = nu;
        let ns = *r << 1usize;
        *r += *s;
        *s = ns;
        l = 2;
    }
    if u.is_zero() {
        *s = fold(*s, p, w).unwrap_or(*s);
    }
    l
}

fn rail_letter(sp: &Step) -> u8 {
    if sp.post.typ {
        0
    } else if sp.isc {
        2
    } else {
        1
    }
}

// ─── 1. adders ───────────────────────────────────────────────────────────────

struct AddRun {
    det_ccx: usize,
    exp_ccx: f64,
    model: f64,
    peak: usize,
}

#[allow(clippy::too_many_arguments)]
fn adder_case(
    n: usize,
    m: usize,
    gc: bool,
    cinc: bool,
    room: usize,
    force: Force,
    cases: Option<usize>,
    seed: u64,
) -> Option<AddRun> {
    let cand = adder::plans(n, gc, cinc, m == n, room);
    let want = |p: &Plan| match force {
        Force::Auto => true,
        Force::Ladder => *p == Plan::Ladder,
        Force::Chunks => matches!(p, Plan::Chunks(_)),
        Force::Recursive => *p == Plan::Recursive,
        Force::Vented => matches!(p, Plan::Vented(_)),
    };
    let model = cand.iter().find(|(p, _)| want(p))?.1;
    let mut c = Builder::new();
    let t = c.alloc_qubits(n);
    let o = c.alloc_qubits(m);
    let g = gc.then(|| c.alloc_qubit());
    let cin = cinc.then(|| c.alloc_qubit());
    let base = c.active_qubits() as usize;
    let cap = Some(base + room);
    let (_, pk) = c.r3_peak(|c| adder::add_forced(c, g, &o, &t, cin, cap, force));
    assert_eq!(c.active_qubits() as usize, base, "add leaks wires");
    let mid = c.op_count();
    let (_, pk2) = c.r3_peak(|c| {
        c.x_all(&t);
        adder::add_forced(c, g, &o, &t, cin, cap, force);
        c.x_all(&t);
    });
    let peak = (pk.max(pk2) as usize) - base;
    assert!(
        peak <= room,
        "add n={n} room={room} {force:?}: scratch {peak}"
    );
    let (nq, nb) = c.i13_dims();
    let ops = c.take_ops();
    let det = ops[..mid].iter().filter(|x| x.kind == K::CCX).count();
    let mut keep: Vec<Q> = t.iter().chain(o.iter()).copied().collect();
    keep.extend(g);
    keep.extend(cin);
    let total = 1usize << (n + m + usize::from(gc) + usize::from(cinc));
    let ncase = cases.map_or(total, |k| k);
    let mut sim = Sim::new(nq, nb, seed);
    let mut rng = Sim::new(1, 1, seed.wrapping_mul(31));
    let (mut exe, mut shots) = (0u64, 0u64);
    let mut idx = 0usize;
    while idx < ncase {
        let lanes = 64.min(ncase - idx);
        sim.clear();
        let mut want_add = Vec::new();
        let mut input = Vec::new();
        for l in 0..lanes {
            let (tv, ov, gv, cv) = if cases.is_none() {
                let k = idx + l;
                let tv = U::from((k & ((1 << n) - 1)) as u64);
                let k = k >> n;
                let ov = U::from((k & ((1usize << m) - 1)) as u64);
                let k = k >> m;
                let gv = gc && (k & 1 == 1);
                let k = if gc { k >> 1 } else { k };
                (tv, ov, gv, cinc && (k & 1 == 1))
            } else {
                let mut tv = U::ZERO;
                let mut ov = U::ZERO;
                for i in 0..n {
                    if rng.next() & 1 == 1 {
                        tv.set_bit(i, true);
                    }
                }
                for i in 0..m {
                    if rng.next() & 1 == 1 {
                        ov.set_bit(i, true);
                    }
                }
                (
                    tv,
                    ov,
                    gc && rng.next() & 1 == 1,
                    cinc && rng.next() & 1 == 1,
                )
            };
            sim.set(&t, tv, l);
            sim.set(&o, ov, l);
            if let Some(g) = g {
                sim.set(&[g], U::from(gv as u64), l);
            }
            if let Some(ci) = cin {
                sim.set(&[ci], U::from(cv as u64), l);
            }
            let add = if gv || !gc {
                ov + U::from(cv as u64)
            } else {
                U::ZERO
            };
            let w = (tv + add) & (pow2(n) - U::from(1u64));
            want_add.push(w);
            input.push((tv, ov, gv, cv));
        }
        sim.run(&ops[..mid]);
        exe += sim.ccx_exec;
        shots += lanes as u64;
        let lm = mask(lanes);
        assert_eq!(
            sim.phase & lm,
            0,
            "add phase n={n} m={m} g={gc} cin={cinc} room={room} {force:?}"
        );
        assert_eq!(sim.dirty & lm, 0, "add dirty n={n} room={room} {force:?}");
        assert_eq!(
            sim.residue(&keep) & lm,
            0,
            "add garbage n={n} room={room} {force:?}"
        );
        for l in 0..lanes {
            let (_, ov, gv, cv) = input[l];
            assert_eq!(
                sim.get(&t, l),
                want_add[l],
                "add value n={n} m={m} g={gc} cin={cinc} room={room} {force:?} in={:?}",
                input[l]
            );
            assert_eq!(sim.get(&o, l), ov);
            if let Some(g) = g {
                assert_eq!(sim.wire(g, l), gv);
            }
            if let Some(ci) = cin {
                assert_eq!(sim.wire(ci, l), cv);
            }
        }
        sim.run(&ops[mid..]);
        assert_eq!(sim.phase & lm, 0, "sub phase n={n} room={room} {force:?}");
        assert_eq!(sim.dirty & lm, 0, "sub dirty n={n} room={room} {force:?}");
        assert_eq!(sim.residue(&keep) & lm, 0, "sub garbage");
        for l in 0..lanes {
            assert_eq!(
                sim.get(&t, l),
                input[l].0,
                "sub value n={n} room={room} {force:?}"
            );
        }
        idx += lanes;
    }
    Some(AddRun {
        det_ccx: det,
        exp_ccx: exe as f64 / shots as f64,
        model,
        peak,
    })
}

fn test_adders() {
    let forces = [
        Force::Ladder,
        Force::Chunks,
        Force::Recursive,
        Force::Vented,
    ];
    let mut runs = 0usize;
    let mut cases = 0usize;
    let mut per: BTreeMap<String, usize> = BTreeMap::new();
    for n in 1..=6usize {
        for m in [n - 1, n] {
            for gc in [false, true] {
                for cinc in [false, true] {
                    for room in 0..=n {
                        for f in forces {
                            if let Some(r) = adder_case(
                                n,
                                m,
                                gc,
                                cinc,
                                room,
                                f,
                                None,
                                17 + n as u64 * 1000 + room as u64,
                            ) {
                                runs += 1;
                                cases += 1 << (n + m + usize::from(gc) + usize::from(cinc));
                                *per.entry(format!("{f:?}")).or_default() += 1;
                                let _ = r;
                            }
                        }
                    }
                }
            }
        }
    }
    println!("{{\"kind\":\"skycof-adder-exhaustive\",\"n_max\":6,\"circuits\":{runs},\"inputs\":{cases},\"per_plan\":{per:?},\"value\":\"pass\",\"phase\":\"pass\",\"cleanup\":\"pass\"}}");
    for (n, m) in [
        (52usize, 52usize),
        (66, 66),
        (256, 255),
        (256, 256),
        (257, 256),
    ] {
        for gc in [false, true] {
            let cinc = !gc;
            for room in [0usize, 1, 2, 3, 5, 8, 9, 12, 16, 23, 40, 100, n] {
                for f in forces {
                    if let Some(r) =
                        adder_case(n, m, gc, cinc, room, f, Some(256), 99 + room as u64)
                    {
                        println!("{{\"kind\":\"skycof-adder-random\",\"n\":{n},\"operand\":{m},\"controlled\":{gc},\"cin\":{cinc},\"room\":{room},\"plan\":\"{f:?}\",\"inputs\":256,\"ccx_ops\":{},\"ccx_expected\":{:.1},\"ccx_model\":{:.1},\"scratch\":{},\"value\":\"pass\",\"phase\":\"pass\",\"cleanup\":\"pass\"}}",
                                 r.det_ccx, r.exp_ccx, r.model, r.peak);
                    }
                }
            }
        }
    }
}

// ─── 2./3./4. ticks ──────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug)]
struct Layout {
    e_in: usize,
    wsw: usize,
    wad: usize,
    e_prev: usize,
    ecof: usize,
    clamp: usize,
}

fn op_len(l: &Layout) -> usize {
    if l.ecof == l.clamp && l.e_prev >= l.clamp {
        l.ecof
    } else {
        l.ecof - 1
    }
}

fn fits(pre: &St, sp: &Step, l: &Layout) -> bool {
    let k = op_len(l);
    sw(pre.r1) <= l.e_in.min(l.wsw)
        && sw(pre.r2) <= l.e_in.min(l.wsw)
        && sw(sp.h) <= l.wad
        && sw(sp.r2_old) <= l.wad
        && sw(sp.post.r2) <= l.wad
        && bits(pre.s) <= l.e_prev
        && bits(pre.r) <= l.e_prev
        && bits(sp.post.r) <= l.ecof
        && bits(sp.s_op) <= k
}

struct TickCircuit {
    ops: Vec<Op>,
    mid: usize,
    nq: usize,
    nb: usize,
    r1: Vec<Q>,
    r2: Vec<Q>,
    s: Vec<Q>,
    r: Vec<Q>,
    i_r1: Vec<Q>,
    i_r2: Vec<Q>,
    i_s: Vec<Q>,
    i_r: Vec<Q>,
    tp: Option<Q>,
    m_r1: Vec<Q>,
    m_r2: Vec<Q>,
    m_s: Vec<Q>,
    m_r: Vec<Q>,
    m_typ: Q,
    plans: (TickPlans, TickPlans),
    peak_extra: usize,
    ccx_fwd: usize,
    ccx_rev: usize,
}

fn build_tick(l: &Layout, with_tp: bool, extra: Option<usize>) -> Option<TickCircuit> {
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut c = Builder::new();
        let r1 = c.alloc_qubits(l.e_in);
        let r2 = c.alloc_qubits(l.e_in);
        let s = c.alloc_qubits(l.e_prev);
        let r = c.alloc_qubits(l.e_prev);
        let tp = with_tp.then(|| c.alloc_qubit());
        let base = c.active_qubits() as usize;
        let cap = extra.map(|x| base + x);
        let mut rails = Rails {
            r1: r1.clone(),
            r2: r2.clone(),
        };
        let mut cof = Cof {
            s: s.clone(),
            r: r.clone(),
        };
        let w = TickWidths {
            wsw: l.wsw,
            wad: l.wad,
            post_r1: l.wad,
            post_r2: l.wad,
            ecof: l.ecof,
            clamp: l.clamp,
        };
        let ((typ, prev, pf), pk1) = c.r3_peak(|c| fwd_tick(c, &mut rails, &mut cof, tp, &w, cap));
        let mid = c.op_count();
        let (m_r1, m_r2, m_s, m_r) = (
            rails.r1.clone(),
            rails.r2.clone(),
            cof.s.clone(),
            cof.r.clone(),
        );
        let (pr, pk2) = c.r3_peak(|c| rev_tick(c, &mut rails, &mut cof, typ, tp, &w, &prev, cap));
        assert_eq!(c.active_qubits() as usize, base, "tick leaks wires");
        let (nq, nb) = c.i13_dims();
        let ops = c.take_ops();
        let ccx_fwd = ops[..mid].iter().filter(|x| x.kind == K::CCX).count();
        let ccx_rev = ops[mid..].iter().filter(|x| x.kind == K::CCX).count();
        TickCircuit {
            ops,
            mid,
            nq,
            nb,
            r1: rails.r1,
            r2: rails.r2,
            s: cof.s,
            r: cof.r,
            i_r1: r1,
            i_r2: r2,
            i_s: s,
            i_r: r,
            tp,
            m_r1,
            m_r2,
            m_s,
            m_r,
            m_typ: typ,
            plans: (pf, pr),
            peak_extra: (pk1.max(pk2) as usize).saturating_sub(base),
            ccx_fwd,
            ccx_rev,
        }
    }));
    std::panic::set_hook(hook);
    let tc = res.ok()?;
    // the tick's own wires (isC, the relabel LSB, field growth) are not scratch: a cap below them is infeasible
    if extra.is_some_and(|x| tc.peak_extra > x) {
        return None;
    }
    Some(tc)
}

fn run_tick_cases(tc: &TickCircuit, cases: &[(St, Step)], seed: u64, label: &str) {
    let mut sim = Sim::new(tc.nq, tc.nb, seed);
    let mut keep_mid: Vec<Q> = tc
        .m_r1
        .iter()
        .chain(&tc.m_r2)
        .chain(&tc.m_s)
        .chain(&tc.m_r)
        .copied()
        .collect();
    keep_mid.push(tc.m_typ);
    keep_mid.extend(tc.tp);
    let mut keep_end: Vec<Q> = tc
        .r1
        .iter()
        .chain(&tc.r2)
        .chain(&tc.s)
        .chain(&tc.r)
        .copied()
        .collect();
    keep_end.extend(tc.tp);
    for chunk in cases.chunks(64) {
        sim.clear();
        let lm = mask(chunk.len());
        for (l, (pre, _)) in chunk.iter().enumerate() {
            sim.set(&tc.i_r1, pre.r1, l);
            sim.set(&tc.i_r2, pre.r2, l);
            sim.set(&tc.i_s, pre.s, l);
            sim.set(&tc.i_r, pre.r, l);
            if let Some(tp) = tc.tp {
                sim.set(&[tp], U::from(pre.typ as u64), l);
            }
        }
        sim.run(&tc.ops[..tc.mid]);
        let bad = (sim.phase | sim.dirty) & lm;
        if bad != 0 {
            let l = bad.trailing_zeros() as usize;
            // locate the first dirty release
            let mut s2 = Sim::new(tc.nq, tc.nb, 1);
            let pre = &chunk[l].0;
            s2.set(&tc.i_r1, pre.r1, 0);
            s2.set(&tc.i_r2, pre.r2, 0);
            s2.set(&tc.i_s, pre.s, 0);
            s2.set(&tc.i_r, pre.r, 0);
            if let Some(tp) = tc.tp {
                s2.set(&[tp], U::from(pre.typ as u64), 0);
            }
            for (i, o) in tc.ops[..tc.mid].iter().enumerate() {
                s2.run(std::slice::from_ref(o));
                if s2.dirty & 1 != 0 {
                    eprintln!("first dirty release at op {i}: {o:?}");
                    for (j, o2) in tc.ops[i.saturating_sub(30)..i + 1].iter().enumerate() {
                        eprintln!(
                            "  {} {:?} t{} c{} c{} ",
                            i.saturating_sub(30) + j,
                            o2.kind,
                            o2.q_target.0,
                            o2.q_control1.0,
                            o2.q_control2.0
                        );
                    }
                    eprintln!("regs r1 {:?} r2 {:?} s {:?} r {:?} tp {:?}; mid s {:?} r {:?} r1 {:?} r2 {:?} typ {:?}", tc.r1, tc.r2, tc.s, tc.r, tc.tp, tc.m_s, tc.m_r, tc.m_r1, tc.m_r2, tc.m_typ);
                    break;
                }
            }
            panic!(
                "tick fwd {label}: phase {:x} dirty {:x}; first bad lane pre {:?} step {:?}",
                sim.phase & lm,
                sim.dirty & lm,
                chunk[l].0,
                chunk[l].1
            );
        }
        assert_eq!(sim.residue(&keep_mid) & lm, 0, "tick fwd garbage");
        for (l, (pre, sp)) in chunk.iter().enumerate() {
            let p = &sp.post;
            let ok = sim.get_signed(&tc.m_r1, l) == p.r1
                && sim.get_signed(&tc.m_r2, l) == p.r2
                && sim.get(&tc.m_s, l) == p.s
                && sim.get(&tc.m_r, l) == p.r
                && sim.wire(tc.m_typ, l) == p.typ
                && tc.tp.is_none_or(|tp| sim.wire(tp, l) == pre.typ);
            assert!(
                ok,
                "tick fwd value: pre {pre:?} want {p:?} got r1 {} r2 {} s {} r {} typ {}",
                sim.get_signed(&tc.m_r1, l),
                sim.get_signed(&tc.m_r2, l),
                sim.get(&tc.m_s, l),
                sim.get(&tc.m_r, l),
                sim.wire(tc.m_typ, l)
            );
        }
        sim.run(&tc.ops[tc.mid..]);
        assert_eq!(sim.phase & lm, 0, "tick rev phase");
        assert_eq!(sim.dirty & lm, 0, "tick rev dirty release");
        assert_eq!(sim.residue(&keep_end) & lm, 0, "tick rev garbage");
        for (l, (pre, _)) in chunk.iter().enumerate() {
            let ok = sim.get_signed(&tc.r1, l) == pre.r1
                && sim.get_signed(&tc.r2, l) == pre.r2
                && sim.get(&tc.s, l) == pre.s
                && sim.get(&tc.r, l) == pre.r
                && tc.tp.is_none_or(|tp| sim.wire(tp, l) == pre.typ);
            assert!(ok, "tick rev value: pre {pre:?}");
        }
    }
}

/// Every reachable tick state for fields of K bits: (pre, step, t == 0, letter key).
fn small_states(kb: usize) -> (Vec<(St, Step, bool, String)>, BTreeMap<String, usize>) {
    let mut out = Vec::new();
    let mut xc: BTreeMap<String, usize> = BTreeMap::new();
    let lo = (1usize << (kb - 1)) + 1;
    for pp in (lo..(1usize << kb)).step_by(2) {
        let p = U::from(pp as u64);
        for d in 1..pp {
            let mut st = seed(U::from(d as u64), p);
            let (mut u, mut v, mut ks, mut kr) = (U::from(d as u64), p, U::ZERO, U::from(1u64));
            let mut post_park = 0;
            for t in 0..(6 * kb + 12) {
                let sp = spec(&st);
                let kl = kal_step(&mut u, &mut v, &mut ks, &mut kr, p, kb);
                let rl = rail_letter(&sp);
                let park_tick = kl != 3 && u.is_zero();
                // cross-check against Kaliski: letters, cofactors (park tick: B or C)
                match kl {
                    3 => {
                        assert!(
                            sp.post.typ && !sp.isc,
                            "post-park tick not typ=1/isC=0 P={pp} d={d} t={t}"
                        );
                    }
                    _ if park_tick => {
                        assert!(rl == 1 || rl == 2, "park tick letter {rl}");
                        *xc.entry(format!("park_as_{}", if rl == 2 { "C" } else { "B" }))
                            .or_default() += 1;
                    }
                    _ => {
                        assert_eq!(rl, kl, "rail letter != Kaliski letter P={pp} d={d} t={t}");
                        assert!(
                            sp.post.s == ks && sp.post.r == kr,
                            "cofactors != Kaliski P={pp} d={d} t={t}"
                        );
                    }
                }
                let sign = [
                    sp.c as u8,
                    sp.agree as u8,
                    neg(st.r1) as u8,
                    neg(st.r2) as u8,
                ];
                let key = format!(
                    "{}{}c{}a{}s{}{}tp{}",
                    ["A", "B", "C", "P"][if kl == 3 { 3 } else { rl as usize }],
                    if park_tick { "*" } else { "" },
                    sign[0],
                    sign[1],
                    sign[2],
                    sign[3],
                    st.typ as u8
                );
                out.push((st, sp, t == 0, key));
                let mut nx = sp.post;
                match fold(nx.s, p, kb) {
                    Some(f) => nx.s = f,
                    None => break,
                }
                if kl == 3 {
                    // post-park relation: s_rail = +-s_kaliski (mod p)
                    let a = nx.s % p;
                    let b = ks % p;
                    let coprime = {
                        let (mut x, mut y) = (pp, d);
                        while y != 0 {
                            (x, y) = (y, x % y);
                        }
                        x == 1
                    };
                    assert!(
                        !coprime || a == b || (a + b) % p == U::ZERO,
                        "post-park s relation P={pp} d={d}"
                    );
                    post_park += 1;
                    if post_park >= 4 {
                        break;
                    }
                }
                st = nx;
            }
        }
    }
    (out, xc)
}

fn test_ticks_exhaustive(kmax: usize) {
    for kb in 4..=kmax {
        let (states, xc) = small_states(kb);
        let mut cover: BTreeMap<String, usize> = BTreeMap::new();
        for (_, _, _, key) in &states {
            *cover.entry(key.clone()).or_default() += 1;
        }
        let layouts = [
            Layout {
                e_in: kb + 2,
                wsw: kb + 2,
                wad: kb + 2,
                e_prev: kb,
                ecof: kb,
                clamp: kb,
            },
            Layout {
                e_in: kb + 2,
                wsw: kb + 3,
                wad: kb + 2,
                e_prev: kb,
                ecof: kb + 1,
                clamp: kb + 2,
            },
            Layout {
                e_in: kb + 3,
                wsw: kb + 2,
                wad: kb + 3,
                e_prev: kb + 1,
                ecof: kb + 1,
                clamp: kb + 3,
            },
            Layout {
                e_in: kb + 2,
                wsw: kb + 2,
                wad: kb + 2,
                e_prev: kb,
                ecof: kb + 1,
                clamp: kb + 1,
            },
        ];
        let mut circuits = 0usize;
        let mut checked = 0usize;
        let mut plan_seen: BTreeMap<String, usize> = BTreeMap::new();
        for (li, l) in layouts.iter().enumerate() {
            for with_tp in [false, true] {
                let cases: Vec<(St, Step)> = states
                    .iter()
                    .filter(|(pre, sp, t0, _)| *t0 != with_tp && fits(pre, sp, l))
                    .map(|(a, b, _, _)| (*a, *b))
                    .collect();
                let skipped =
                    states.iter().filter(|(_, _, t0, _)| *t0 != with_tp).count() - cases.len();
                let mut extras: Vec<Option<usize>> = (0..=12).map(Some).collect();
                extras.push(None);
                for ex in extras {
                    let Some(tc) = build_tick(l, with_tp, ex) else {
                        continue;
                    };
                    let key = format!(
                        "rail:{:?}/cof:{:?}",
                        plan_name(&tc.plans.0.rail),
                        plan_name(&tc.plans.0.cof)
                    );
                    *plan_seen.entry(key).or_default() += 1;
                    run_tick_cases(
                        &tc,
                        &cases,
                        1000 * kb as u64 + li as u64,
                        &format!(
                            "K={kb} layout {l:?} tp={with_tp} extra={ex:?} plans {:?}",
                            tc.plans.0
                        ),
                    );
                    circuits += 1;
                    checked += cases.len();
                }
                let _ = skipped;
            }
        }
        println!("{{\"kind\":\"skycof-tick-exhaustive\",\"K\":{kb},\"reachable_states\":{},\"layouts\":4,\"circuits\":{circuits},\"tick_checks\":{checked},\"selector_cases\":{},\"park\":{xc:?},\"plans\":{plan_seen:?},\"kaliski_crosscheck\":\"pass\",\"value\":\"pass\",\"phase\":\"pass\",\"cleanup\":\"pass\",\"reverse\":\"exact\"}}",
                 states.len(), cover.len());
        if kb == kmax {
            println!("{{\"kind\":\"skycof-tick-selector-cover\",\"K\":{kb},\"cases\":{cover:?}}}");
        }
    }
}

fn plan_name(p: &Plan) -> String {
    match p {
        Plan::Ladder => "ladder".into(),
        Plan::Chunks(c) => format!("chunks{}", c.len()),
        Plan::Recursive => "recursive".into(),
        Plan::Vented(f) => format!("vented{f}"),
    }
}

/// Fold gadget for the tests (the park step is not part of the tick): `s` has `w + 1` wires;
/// `s_low += top * (2^w - p)`, then `top ^= s_low[0]` (the result is odd iff it folded).
fn test_fold(c: &mut Builder, s: &mut Vec<Q>, p: U, w: usize) {
    assert_eq!(s.len(), w + 1);
    let top = s.pop().unwrap();
    let kc = pow2(w) - p;
    let kreg = c.alloc_qubits(w);
    for i in 0..w {
        if kc.bit(i) {
            c.x(kreg[i]);
        }
    }
    adder::add(c, Some(top), &kreg, s, None, None);
    for i in 0..w {
        if kc.bit(i) {
            c.x(kreg[i]);
        }
    }
    c.free_vec(&kreg);
    c.cx(s[0], top);
    c.free(top);
}

fn test_unfold(c: &mut Builder, s: &mut Vec<Q>, p: U, w: usize) {
    assert_eq!(s.len(), w);
    let top = c.alloc_qubit();
    c.cx(s[0], top);
    let kc = pow2(w) - p;
    let kreg = c.alloc_qubits(w);
    for i in 0..w {
        if kc.bit(i) {
            c.x(kreg[i]);
        }
    }
    adder::sub(c, Some(top), &kreg, s, None, None);
    for i in 0..w {
        if kc.bit(i) {
            c.x(kreg[i]);
        }
    }
    c.free_vec(&kreg);
    s.push(top);
}

/// Per-tick public widths of a walk family.
struct Envelope {
    e_in: usize,
    w: Vec<TickWidths>,
}

/// Whole walks at per-tick widths: forward (checked every tick), then back. Returns (walks, ticks, ccx fwd, ccx rev).
#[allow(clippy::too_many_arguments)]
#[derive(Clone)]
enum CapMode {
    None,
    /// cap = live count at each tick's entry + extra
    Extra(usize),
    /// absolute cap with zero filler wires standing in for the rest of the design's live set
    Design {
        cap: usize,
        fill: Vec<usize>,
    },
}

fn run_walks(
    p: U,
    kb: usize,
    env: &Envelope,
    walks: &[(U, Vec<St>)],
    capm: CapMode,
    seed_v: u64,
) -> (usize, usize, usize) {
    let rt = env.w.len();
    let mut c = Builder::new();
    let r1 = c.alloc_qubits(env.e_in);
    let r2 = c.alloc_qubits(env.e_in);
    let e0 = 2usize;
    let s = c.alloc_qubits(e0);
    let r = c.alloc_qubits(e0);
    let base = c.active_qubits() as usize;
    let mut rails = Rails {
        r1: r1.clone(),
        r2: r2.clone(),
    };
    let mut cof = Cof {
        s: s.clone(),
        r: r.clone(),
    };
    let mut typs: Vec<Q> = Vec::new();
    let mut filler: Vec<Q> = Vec::new();
    // Design mode: the kept typ wires (the test's tape) stand in for part of the filler (the design
    // erases typ or pushes it into the history, which the filler counts).
    let tick_cap =
        |c: &mut Builder, filler: &mut Vec<Q>, t: usize, live_typ: usize| -> Option<usize> {
            match &capm {
                CapMode::None => None,
                CapMode::Extra(x) => Some(c.active_qubits() as usize + x),
                CapMode::Design { cap, fill } => {
                    resize_unsigned(c, filler, fill[t].saturating_sub(live_typ));
                    Some(*cap)
                }
            }
        };
    let mut prevs = Vec::new();
    let mut folded = Vec::new();
    let mut marks = Vec::new(); // (op index, r1, r2, s, r, typ)
    for t in 0..rt {
        let cap = tick_cap(&mut c, &mut filler, t, typs.len());
        let _ = c.take_win_peak();
        let (typ, prev, _) = fwd_tick(
            &mut c,
            &mut rails,
            &mut cof,
            typs.last().copied(),
            &env.w[t],
            cap,
        );
        if let (CapMode::Design { cap, .. }, pk) = (&capm, c.take_win_peak() as usize) {
            assert!(pk <= *cap, "forward tick {t} peak {pk} over cap {cap}");
        }
        typs.push(typ);
        prevs.push(prev);
        let f = cof.s.len() > cof.r.len();
        if f {
            test_fold(&mut c, &mut cof.s, p, env.w[t].clamp);
        }
        folded.push(f);
        marks.push((
            c.op_count(),
            rails.r1.clone(),
            rails.r2.clone(),
            cof.s.clone(),
            cof.r.clone(),
            typ,
        ));
    }
    let mid = c.op_count();
    for t in (0..rt).rev() {
        if folded[t] {
            test_unfold(&mut c, &mut cof.s, p, env.w[t].clamp);
        }
        let cap = tick_cap(&mut c, &mut filler, t, t);
        let tp = if t > 0 { Some(typs[t - 1]) } else { None };
        let _ = c.take_win_peak();
        rev_tick(
            &mut c, &mut rails, &mut cof, typs[t], tp, &env.w[t], &prevs[t], cap,
        );
        if let (CapMode::Design { cap, .. }, pk) = (&capm, c.take_win_peak() as usize) {
            assert!(pk <= *cap, "reverse tick {t} peak {pk} over cap {cap}");
        }
    }
    resize_unsigned(&mut c, &mut filler, 0);
    assert_eq!(c.active_qubits() as usize, base, "walk leaks wires");
    let (f1, f2, fs, fr) = (
        rails.r1.clone(),
        rails.r2.clone(),
        cof.s.clone(),
        cof.r.clone(),
    );
    let (nq, nb) = c.i13_dims();
    let ops = c.take_ops();
    let ccx_f = ops[..mid].iter().filter(|x| x.kind == K::CCX).count();
    let ccx_r = ops[mid..].iter().filter(|x| x.kind == K::CCX).count();
    let mut sim = Sim::new(nq, nb, seed_v);
    let keep0: Vec<Q> = f1
        .iter()
        .chain(&f2)
        .chain(&fs)
        .chain(&fr)
        .copied()
        .collect();
    for chunk in walks.chunks(64) {
        sim.clear();
        let lm = mask(chunk.len());
        for (l, (d, _)) in chunk.iter().enumerate() {
            let st = seed(*d, p);
            sim.set(&r1, st.r1, l);
            sim.set(&r2, st.r2, l);
            sim.set(&s, st.s, l);
            sim.set(&r, st.r, l);
        }
        let mut at = 0usize;
        for (t, (end, m1, m2, ms, mr, mt)) in marks.iter().enumerate() {
            sim.run(&ops[at..*end]);
            at = *end;
            assert_eq!(sim.dirty & lm, 0, "walk dirty release at tick {t}");
            assert_eq!(sim.phase & lm, 0, "walk phase at tick {t}");
            for (l, (d, traj)) in chunk.iter().enumerate() {
                let w = &traj[t];
                let ok = sim.get_signed(m1, l) == w.r1
                    && sim.get_signed(m2, l) == w.r2
                    && sim.get(ms, l) == w.s
                    && sim.get(mr, l) == w.r
                    && sim.wire(*mt, l) == w.typ;
                assert!(
                    ok,
                    "walk value d={d} tick {t}: want {w:?} got s {} r {}",
                    sim.get(ms, l),
                    sim.get(mr, l)
                );
            }
        }
        let mut keep_mid: Vec<Q> = marks
            .last()
            .map(|m| {
                m.1.iter()
                    .chain(&m.2)
                    .chain(&m.3)
                    .chain(&m.4)
                    .copied()
                    .collect()
            })
            .unwrap();
        keep_mid.extend(typs.iter().copied());
        assert_eq!(sim.residue(&keep_mid) & lm, 0, "walk garbage at park");
        sim.run(&ops[mid..]);
        assert_eq!(sim.dirty & lm, 0, "walk-back dirty release");
        assert_eq!(sim.phase & lm, 0, "walk-back phase");
        assert_eq!(sim.residue(&keep0) & lm, 0, "walk-back garbage");
        for (l, (d, _)) in chunk.iter().enumerate() {
            let st = seed(*d, p);
            assert!(
                sim.get_signed(&f1, l) == st.r1
                    && sim.get_signed(&f2, l) == st.r2
                    && sim.get(&fs, l) == st.s
                    && sim.get(&fr, l) == st.r,
                "walk-back value d={d}"
            );
        }
    }
    let _ = kb;
    (walks.len(), ccx_f, ccx_r)
}

/// Classical trajectory with the park fold: post-tick states (after the fold) for `rt` ticks, plus the
/// per-tick width needs (pre rails, add rails, post cofactors). None if the fold leaves the field.
fn trajectory(
    d: U,
    p: U,
    clamp: usize,
    rt: usize,
) -> Option<(Vec<St>, Vec<(usize, usize, usize)>)> {
    let mut st = seed(d, p);
    let mut traj = Vec::with_capacity(rt);
    let mut need = Vec::with_capacity(rt);
    for _ in 0..rt {
        let sp = spec(&st);
        let pre_sw = sw(st.r1).max(sw(st.r2));
        let ad = sw(sp.h).max(sw(sp.r2_old)).max(sw(sp.post.r2));
        let cofn = bits(sp.post.r).max(bits(sp.s_op) + 1);
        let mut nx = sp.post;
        nx.s = fold(nx.s, p, clamp)?;
        need.push((pre_sw, ad, cofn));
        traj.push(nx);
        st = nx;
    }
    Some((traj, need))
}

fn envelope(
    needs: &[Vec<(usize, usize, usize)>],
    e_in: usize,
    clamp: usize,
    m_rail: usize,
    m_cof: usize,
) -> Envelope {
    let rt = needs[0].len();
    let mut w: Vec<TickWidths> = (0..rt)
        .map(|t| {
            let sw_need = needs.iter().map(|n| n[t].0).max().unwrap();
            let ad_need = needs.iter().map(|n| n[t].1).max().unwrap();
            let cof_need = needs.iter().map(|n| n[t].2).max().unwrap();
            TickWidths {
                wsw: (sw_need + m_rail).max(3),
                wad: (ad_need + m_rail).max(2),
                post_r1: (ad_need + m_rail).max(2),
                post_r2: (ad_need + m_rail).max(2),
                ecof: (cof_need + m_cof).clamp(2, clamp),
                clamp,
            }
        })
        .collect();
    // a tick whose doubled cofactor may exceed the clamp (park / post-park) runs clamped on both sides
    for t in 0..rt {
        if needs.iter().any(|n| n[t].2 > clamp) {
            w[t].ecof = clamp;
            if t > 0 {
                w[t - 1].ecof = clamp;
            }
        }
    }
    for t in 1..rt {
        if w[t].ecof < w[t - 1].ecof {
            w[t].ecof = w[t - 1].ecof;
        }
    }
    Envelope { e_in, w }
}

fn test_walks_small(kmax: usize) {
    for kb in [5usize, 6, kmax] {
        let lo = (1usize << (kb - 1)) + 1;
        let ps: Vec<usize> = (lo..(1usize << kb))
            .step_by(2)
            .filter(|x| x % 3 != 0)
            .take(6)
            .collect();
        let mut tot = (0usize, 0usize);
        for &pp in &ps {
            let p = U::from(pp as u64);
            // walk length: the latest park + 3 post-park ticks
            let mut rt = 0;
            for d in 1..pp {
                let (mut u, mut v, mut s, mut r) = (U::from(d as u64), p, U::ZERO, U::from(1u64));
                let mut t = 0;
                while !u.is_zero() {
                    kal_step(&mut u, &mut v, &mut s, &mut r, p, kb);
                    t += 1;
                }
                rt = rt.max(t + 3);
            }
            let mut walks = Vec::new();
            let mut needs = Vec::new();
            let mut out_of_field = 0;
            for d in 1..pp {
                match trajectory(U::from(d as u64), p, kb, rt) {
                    Some((traj, need)) => {
                        walks.push((U::from(d as u64), traj));
                        needs.push(need);
                    }
                    None => out_of_field += 1,
                }
            }
            for (mr, mc, capx) in [
                (0usize, 0usize, CapMode::None),
                (1, 1, CapMode::None),
                (0, 0, CapMode::Extra(4)),
                (1, 1, CapMode::Extra(6)),
            ] {
                let env = envelope(&needs, kb + 2, kb, mr, mc);
                let (n, cf, cr) = run_walks(p, kb, &env, &walks, capx, pp as u64 * 7 + mr as u64);
                tot.0 += n;
                tot.1 += env.w.len() * n;
                let _ = (cf, cr);
            }
            let _ = out_of_field;
        }
        println!("{{\"kind\":\"skycof-walk-small\",\"K\":{kb},\"moduli\":{ps:?},\"walks\":{},\"ticks\":{},\"margins_caps\":\"0/0,1/1,0/0+4,1/1+6\",\"per_tick_check\":\"pass\",\"walk_back\":\"exact\",\"phase\":\"pass\",\"cleanup\":\"pass\"}}",
                 tot.0, tot.1);
    }
}

fn rand_scalar(rng: &mut Sim, p: U) -> U {
    loop {
        let x = U::from_limbs([rng.next(), rng.next(), rng.next(), rng.next(), 0, 0, 0, 0]);
        if !x.is_zero() && x < p {
            return x;
        }
    }
}

/// Random full-width walks inside `env` (classically checked); misses are counted, not run.
fn sample_walks(env: &Envelope, n: usize, rng: &mut Sim) -> (Vec<(U, Vec<St>)>, usize) {
    let p = secp_p();
    let rt = env.w.len();
    let mut walks = Vec::new();
    let mut miss = 0usize;
    while walks.len() < n {
        let d = rand_scalar(rng, p);
        let Some((traj, need)) = trajectory(d, p, 256, rt) else {
            miss += 1;
            continue;
        };
        let inside = need.iter().zip(&env.w).enumerate().all(|(t, (x, w))| {
            let e_prev = if t == 0 { 2 } else { env.w[t - 1].ecof };
            let k = if w.ecof == w.clamp && e_prev >= w.clamp {
                w.ecof
            } else {
                w.ecof - 1
            };
            x.0 <= w.wsw && x.1 <= w.wad && x.2 <= k + 1
        });
        if !inside {
            miss += 1;
            continue;
        }
        walks.push((d, traj));
    }
    (walks, miss)
}

fn test_walks_full() {
    let p = secp_p();
    let rt = 400;
    let ntrain = env_usize("SKYCOF_ST_TRAIN", 4000);
    let nb = env_usize("SKYCOF_ST_FULL_BATCHES", 64);
    let mut rng = Sim::new(1, 1, 0xC0F_7E57);
    let mut needs = Vec::new();
    for _ in 0..ntrain {
        let d = rand_scalar(&mut rng, p);
        if let Some((_, n)) = trajectory(d, p, 256, rt) {
            needs.push(n);
        }
    }
    let env = envelope(&needs, 258, 256, 2, 2);
    let sum_sw: usize = env.w.iter().map(|w| w.wsw).sum();
    let sum_ad: usize = env.w.iter().map(|w| w.wad).sum();
    let sum_cof: usize = env.w.iter().map(|w| w.ecof).sum();
    let (walks, miss) = sample_walks(&env, 64 * nb, &mut rng);
    let t0 = std::time::Instant::now();
    let (n, cf, cr) = run_walks(p, 256, &env, &walks, CapMode::None, 0xF011);
    println!("{{\"kind\":\"skycof-walk-full\",\"p\":\"secp256k1\",\"R\":{rt},\"widths\":\"trained {ntrain} walks, margins rail/cof 2/2\",\"sum_wsw\":{sum_sw},\"sum_wad\":{sum_ad},\"sum_ecof\":{sum_cof},\"walks\":{n},\"envelope_misses_skipped\":{miss},\"ccx_fwd_ops\":{cf},\"ccx_rev_ops\":{cr},\"per_tick_check\":\"pass\",\"walk_back\":\"exact\",\"phase\":\"pass\",\"cleanup\":\"pass\",\"secs\":{:.1}}}",
             t0.elapsed().as_secs_f64());
    // the design's own widths (rails srail+8 both at swap and add, cofactors min(kcof+8, 256)), unbounded
    // and at the design CAP with the model's live set as filler
    let (_, rows) = design_rows();
    let w: Vec<TickWidths> = (0..rows.len())
        .map(|t| TickWidths {
            wsw: if t == 0 { 258 } else { rows[t - 1][1] as usize },
            wad: rows[t][1] as usize,
            post_r1: rows[t][1] as usize,
            post_r2: rows[t][1] as usize,
            ecof: rows[t][2] as usize,
            clamp: 256,
        })
        .collect();
    let denv = Envelope { e_in: 258, w };
    let fill: Vec<usize> = rows.iter().map(|r| r[3] as usize + 256 + 10 + 2).collect();
    let cap = rows[0][5] as usize;
    let nd = env_usize("SKYCOF_ST_DESIGN_BATCHES", 16);
    let (walks, miss) = sample_walks(&denv, 64 * nd, &mut rng);
    for (label, mode) in [
        ("unbounded", CapMode::None),
        (
            "design-cap",
            CapMode::Design {
                cap,
                fill: fill.clone(),
            },
        ),
    ] {
        let t0 = std::time::Instant::now();
        let (n, cf, cr) = run_walks(p, 256, &denv, &walks, mode, 0xD051);
        println!("{{\"kind\":\"skycof-walk-design-widths\",\"mode\":\"{label}\",\"cap\":{cap},\"walks\":{n},\"envelope_misses_skipped\":{miss},\"ccx_fwd_ops\":{cf},\"ccx_rev_ops\":{cr},\"per_tick_check\":\"pass\",\"walk_back\":\"exact\",\"phase\":\"pass\",\"cleanup\":\"pass\",\"secs\":{:.1}}}",
                 t0.elapsed().as_secs_f64());
    }
}

/// 5. classical: rail letters vs Kaliski letters at full width.
fn test_crosscheck_full() {
    let p = secp_p();
    let n = env_usize("SKYCOF_ST_XCHECK", 20000);
    let mut rng = Sim::new(1, 1, 0xA11_CE);
    let (mut ticks, mut park_c, mut park_b, mut post) = (0u64, 0u64, 0u64, 0u64);
    for _ in 0..n {
        let d = rand_scalar(&mut rng, p);
        let mut st = seed(d, p);
        let (mut u, mut v, mut ks, mut kr) = (d, p, U::ZERO, U::from(1u64));
        for t in 0..400 {
            let sp = spec(&st);
            let kl = kal_step(&mut u, &mut v, &mut ks, &mut kr, p, 256);
            let rl = rail_letter(&sp);
            let park_tick = kl != 3 && u.is_zero();
            if kl == 3 {
                assert!(sp.post.typ && !sp.isc, "full: post-park letter t={t}");
                post += 1;
            } else if park_tick {
                if rl == 2 {
                    park_c += 1
                } else {
                    assert_eq!(rl, 1);
                    park_b += 1
                }
            } else {
                assert_eq!(rl, kl, "full: rail letter != Kaliski t={t}");
                assert!(
                    sp.post.s == ks && sp.post.r == kr,
                    "full: cofactors != Kaliski t={t}"
                );
                // isC = s_new[1] and not typ; s even and r odd
                assert_eq!(sp.post.s.bit(1) && !sp.post.typ, sp.isc);
                assert!(!sp.post.s.bit(0) && sp.post.r.bit(0));
            }
            let mut nx = sp.post;
            nx.s = fold(nx.s, p, 256).expect("full: fold left the field");
            if kl == 3 || park_tick {
                let a = nx.s % p;
                let b = ks % p;
                assert!(a == b || (a + b) % p == U::ZERO);
            }
            st = nx;
            ticks += 1;
        }
    }
    println!("{{\"kind\":\"skycof-kaliski-crosscheck\",\"walks\":{n},\"ticks\":{ticks},\"letters_equal_prepark\":\"pass\",\"cofactors_equal_prepark\":\"pass\",\"park_labelled_B\":{park_b},\"park_labelled_C\":{park_c},\"postpark_ticks_typ1_isC0\":{post},\"s_rail_eq_pm_s_kaliski\":\"pass\"}}");
}

// ─── 6. cost at the design's widths ──────────────────────────────────────────

fn expected_ccx(ops: &[Op]) -> f64 {
    let mut depth = 0i32;
    let mut e = 0.0;
    for o in ops {
        match o.kind {
            K::PushCondition => depth += 1,
            K::PopCondition => depth -= 1,
            K::CCX | K::CCZ => {
                let d = depth + i32::from(o.c_condition != NO_BIT);
                e += 0.5f64.powi(d);
            }
            _ => {}
        }
    }
    e
}

fn design_rows() -> (String, Vec<Vec<f64>>) {
    let path = std::env::var("SKYCOF_DESIGN_WIDTHS").unwrap_or_else(|_| {
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/src/point_add/skycof/design_widths_k0w64_1e-4.tsv"
        )
        .to_string()
    });
    let text = std::fs::read_to_string(&path).expect("design widths table");
    let hdr = text
        .lines()
        .find(|l| l.starts_with('#'))
        .unwrap_or("")
        .replace('"', "'");
    // t rail cof H live cap A model_rails model_cof
    let rows = text
        .lines()
        .filter(|l| !l.starts_with('#') && !l.starts_with('t'))
        .map(|l| l.split('\t').map(|x| x.parse::<f64>().unwrap()).collect())
        .collect();
    (hdr, rows)
}

/// Forward traversal at the design's widths: rails and cofactor stages measured separately, the room
/// each add actually saw, plans, and the tick's peak against the design CAP.
pub fn cost_report() {
    let (hdr, rows) = design_rows();
    let (pass, small, flags) = (256usize, 10usize, 4usize);
    for mode in ["unbounded", "model-room"] {
        let mut c = Builder::new();
        let mut rails = Rails {
            r1: c.alloc_qubits(258),
            r2: c.alloc_qubits(258),
        };
        let e0 = rows[0][2] as usize - 1;
        let mut cof = Cof {
            s: c.alloc_qubits(e0),
            r: c.alloc_qubits(e0),
        };
        let mut filler: Vec<Q> = Vec::new();
        let mut typ_prev: Option<Q> = None;
        let (mut t_rail, mut t_cof, mut m_rail, mut m_cof) = (0.0, 0.0, 0.0, 0.0);
        let mut m_cof_myroom = 0.0;
        let mut peak_over = 0i64;
        let mut cof_plans: BTreeMap<String, usize> = BTreeMap::new();
        let mut rail_plans: BTreeMap<String, usize> = BTreeMap::new();
        let mut room_min = (usize::MAX, usize::MAX, usize::MAX);
        let mut per_tick = Vec::new();
        for (t, row) in rows.iter().enumerate() {
            let (rail, ecof, hh, cap, a_model) = (
                row[1] as usize,
                row[2] as usize,
                row[3] as usize,
                row[5] as usize,
                row[6] as usize,
            );
            m_rail += row[7];
            m_cof += row[8];
            // filler = H + PASS + SMALL (typ_{t-1} is a real wire) + the model's 2 flags this tick does not use
            let want_fill = hh + pass + small + (flags - 2) - usize::from(typ_prev.is_some());
            resize_unsigned(&mut c, &mut filler, want_fill);
            let wsw = if t == 0 { 258 } else { rows[t - 1][1] as usize };
            let w = TickWidths {
                wsw,
                wad: rail,
                post_r1: rail,
                post_r2: rail,
                ecof,
                clamp: 256,
            };
            let capo = (mode == "model-room").then_some(cap);
            let _ = c.take_win_peak();
            let o0 = c.op_count();
            // room the rail add will see: rails at wad (r2 and e2), typ (old LSB) and the sign wire
            let (typ, isc, rp) = rail_fwd(&mut c, &mut rails, typ_prev, w.wsw, w.wad, capo, None);
            let o1 = c.op_count();
            let room_rail = adder::LAST_AVAIL.load(std::sync::atomic::Ordering::Relaxed);
            let cp = cof_fwd(&mut c, &mut cof, typ, isc, &w, capo);
            let room_cof = adder::LAST_AVAIL
                .load(std::sync::atomic::Ordering::Relaxed)
                .min(100000) as i64;
            let o2 = c.op_count();
            let m = c.alloc_bit();
            c.hmr(isc, m);
            c.x(typ);
            c.cz_if(cof.s[1], typ, m);
            c.x(typ);
            c.free_bit(m);
            c.release_clean(isc);
            let pk = c.take_win_peak() as i64;
            if cof.s.len() > cof.r.len() {
                let top = cof.s.pop().unwrap();
                c.free(top); // cost harness only: the park fold is a separate component
            }
            peak_over = peak_over.max(pk - cap as i64);
            *rail_plans.entry(plan_name(&rp)).or_default() += 1;
            *cof_plans.entry(plan_name(&cp)).or_default() += 1;
            let ops = c.take_ops();
            let (er, ec) = (expected_ccx(&ops[o0..o1]), expected_ccx(&ops[o1..o2]));
            t_rail += er;
            t_cof += ec;
            let rc = room_cof.max(0) as usize;
            m_cof_myroom += ecof as f64 + adder::plans(ecof, true, false, false, rc.min(1000))[0].1;
            room_min.0 = room_min.0.min(rc);
            room_min.1 = room_min.1.min(a_model);
            room_min.2 = room_min.2.min(room_rail);
            per_tick.push(format!(
                "{t}:{er:.0}/{ec:.0}/{}/{rc}/{a_model}",
                room_rail.min(100000)
            ));
            if let Some(tp) = typ_prev {
                c.free(tp);
            }
            typ_prev = Some(typ);
        }
        println!("{{\"kind\":\"skycof-tick-cost\",\"widths\":\"{hdr}\",\"mode\":\"{mode}\",\"ticks\":{},\"fwd_rails_ccx\":{t_rail:.0},\"fwd_cof_ccx\":{t_cof:.0},\"model_rails\":{m_rail:.0},\"model_cof\":{m_cof:.0},\"model_cof_at_measured_room\":{m_cof_myroom:.0},\"min_room_rail_add\":{},\"min_room_cof_add\":{},\"min_room_model_cof\":{},\"cof_plans\":{cof_plans:?},\"rail_plans\":{rail_plans:?},\"tick_peak_over_cap\":{peak_over}}}",
                 rows.len(), room_min.2.min(100000), room_min.0.min(100000), room_min.1);
        if std::env::var_os("SKYCOF_COST_TICKS").is_some() {
            println!("{{\"kind\":\"skycof-tick-cost-ticks\",\"mode\":\"{mode}\",\"t:rails/cof/room_rail/room_cof/model_room\":\"{}\"}}", per_tick.join(" "));
        }
    }
}

/// Exact per-tick reverse cost at the design widths (built, not modelled): forward then reverse of each
/// tick in isolation at the design's widths and model room.
fn rev_cost_exact() {
    let (_, rows) = design_rows();
    let (mut f_tot, mut r_tot) = (0.0, 0.0);
    let mut scr = (0usize, 0usize);
    let mut over = i64::MIN;
    let mut samples: Vec<String> = Vec::new();
    let (mut f_tot_u, mut r_tot_u) = (0.0, 0.0);
    for t in 0..rows.len() {
        let rail = rows[t][1] as usize;
        let ecof = rows[t][2] as usize;
        let e_prev = if t == 0 {
            ecof - 1
        } else {
            rows[t - 1][2] as usize
        };
        let wsw = if t == 0 { 258 } else { rows[t - 1][1] as usize };
        let (hh, cap) = (rows[t][3] as usize, rows[t][5] as usize);
        for bounded in [true, false] {
            let mut c = Builder::new();
            let fill = c.alloc_qubits(hh + 256 + 10 + 2 - 1);
            let tp = c.alloc_qubit();
            let mut rails = Rails {
                r1: c.alloc_qubits(wsw),
                r2: c.alloc_qubits(wsw),
            };
            let mut cof = Cof {
                s: c.alloc_qubits(e_prev),
                r: c.alloc_qubits(e_prev),
            };
            let w = TickWidths {
                wsw,
                wad: rail,
                post_r1: rail,
                post_r2: rail,
                ecof,
                clamp: 256,
            };
            let capo = bounded.then_some(cap);
            let entry = c.active_qubits() as usize;
            let _ = c.take_win_peak();
            let (typ, prev, _) = fwd_tick(&mut c, &mut rails, &mut cof, Some(tp), &w, capo);
            let pf = c.take_win_peak() as usize;
            let mid = c.op_count();
            rev_tick(&mut c, &mut rails, &mut cof, typ, Some(tp), &w, &prev, capo);
            let pr = c.take_win_peak() as usize;
            let sc = pf.max(pr) - entry;
            if bounded {
                scr.0 = scr.0.max(sc);
                over = over.max(pf.max(pr) as i64 - cap as i64);
            } else {
                scr.1 = scr.1.max(sc);
            }
            let ops = c.take_ops();
            let (f, r) = (expected_ccx(&ops[..mid]), expected_ccx(&ops[mid..]));
            if [0usize, 100, 200, 300, 317, 340, 399].contains(&t) {
                samples.push(format!("{{\"t\":{t},\"mode\":\"{}\",\"wsw\":{wsw},\"wad\":{rail},\"cof\":\"{e_prev}->{ecof}\",\"room_model\":{},\"fwd\":{f:.1},\"rev\":{r:.1},\"peak_above_entry\":{sc}}}",
                                     if bounded { "cap" } else { "unbounded" }, rows[t][6]));
            }
            if bounded {
                f_tot += f;
                r_tot += r;
            } else {
                f_tot_u += f;
                r_tot_u += r;
            }
            let _ = fill;
        }
    }
    println!("{{\"kind\":\"skycof-tick-cost-exact\",\"ticks\":{},\"fwd_ccx_model_room\":{f_tot:.0},\"rev_ccx_model_room\":{r_tot:.0},\"fwd_ccx_unbounded\":{f_tot_u:.0},\"rev_ccx_unbounded\":{r_tot_u:.0},\"max_peak_above_entry_cap\":{},\"max_peak_above_entry_unbounded\":{},\"max_peak_minus_cap\":{over},\"samples\":[{}]}}",
             rows.len(), scr.0, scr.1, samples.join(","));
}

/// Heo identity: with unbounded room the rail part is op-for-op `heo::fwd_tick` / `heo::rev_tick`.
fn test_heo_identity() {
    for (wsw, wad) in [(10usize, 10usize), (12, 10), (9, 11), (266, 265)] {
        let mk = |mine: bool| {
            let mut c = Builder::new();
            let r1 = c.alloc_qubits(wsw);
            let r2 = c.alloc_qubits(wsw);
            let tp = c.alloc_qubit();
            let mut rails = Rails {
                r1: r1.clone(),
                r2: r2.clone(),
            };
            if mine {
                let (typ, isc, _) = rail_fwd(&mut c, &mut rails, Some(tp), wsw, wad, None, None);
                rail_rev(
                    &mut c,
                    &mut rails,
                    typ,
                    isc,
                    Some(tp),
                    wsw,
                    (wsw, wsw),
                    None,
                    None,
                );
            } else {
                let (typ, s) =
                    crate::point_add::heo::fwd_tick(&mut c, &mut rails, Some(tp), wsw, wad);
                crate::point_add::heo::rev_tick(
                    &mut c,
                    &mut rails,
                    typ,
                    s,
                    Some(tp),
                    wsw,
                    (wsw, wsw),
                );
            }
            c.take_ops()
        };
        let (a, b) = (mk(true), mk(false));
        assert_eq!(
            a.len(),
            b.len(),
            "rail tick op count differs from heo at {wsw}/{wad}"
        );
        let ident = a == b;
        println!("{{\"kind\":\"skycof-heo-identity\",\"wsw\":{wsw},\"wad\":{wad},\"ops\":{},\"identical\":{ident}}}", a.len());
        assert!(ident, "rail tick differs from heo::fwd_tick/rev_tick");
    }
}

/// Exhaustive reduced-width differential for the source-sign-extension
/// tau/isC host.  Compare the complete post-rail logical state, residual
/// phase/garbage, then the explicit reverse and physical input restoration.
fn test_signext_isc_host() {
    struct Built {
        ops: Vec<Op>,
        contract_start: usize,
        fwd_end: usize,
        nq: usize,
        nb: usize,
        input_r1: Vec<Q>,
        input_r2: Vec<Q>,
        typ_prev: Q,
        r0: Q,
        pre_r1: Vec<Q>,
        pre_r2: Vec<Q>,
        mid_r1: Vec<Q>,
        mid_r2: Vec<Q>,
        typ: Q,
        isc: Q,
        final_r1: Vec<Q>,
        final_r2: Vec<Q>,
        peak: u32,
    }

    fn build(n: usize, hosted: bool, drop_r1: usize, drop_r2: usize) -> Built {
        assert!(drop_r1 >= 1 && drop_r1 < n && drop_r2 < n);
        let mut c = Builder::new();
        let input_r1 = c.alloc_qubits(n);
        let input_r2 = c.alloc_qubits(n);
        let typ_prev = c.alloc_qubit();
        let r0 = c.alloc_qubit();
        c.x(r0);
        let mut rails = Rails {
            r1: input_r1.clone(),
            r2: input_r2.clone(),
        };
        let (typ, isc, _) = if hosted {
            rail_fwd_signext_host(
                &mut c,
                &mut rails,
                Some(typ_prev),
                n,
                n,
                None,
                Some(r0),
            )
        } else {
            rail_fwd(
                &mut c,
                &mut rails,
                Some(typ_prev),
                n,
                n,
                None,
                Some(r0),
            )
        };
        let pre_r1 = rails.r1.clone();
        let pre_r2 = rails.r2.clone();
        let contract_start = c.op_count();
        resize_signed(&mut c, &mut rails.r1, n - drop_r1);
        resize_signed(&mut c, &mut rails.r2, n - drop_r2);
        let mid_r1 = rails.r1.clone();
        let mid_r2 = rails.r2.clone();
        let fwd_end = c.op_count();
        if hosted {
            resize_signed(&mut c, &mut rails.r1, n - 1);
            resize_signed(&mut c, &mut rails.r2, n);
            rail_rev_signext_host(
                &mut c,
                &mut rails,
                typ,
                isc,
                Some(typ_prev),
                n,
                (n, n),
                None,
                Some(r0),
            );
        } else {
            resize_signed(&mut c, &mut rails.r1, n);
            resize_signed(&mut c, &mut rails.r2, n);
            rail_rev(
                &mut c,
                &mut rails,
                typ,
                isc,
                Some(typ_prev),
                n,
                (n, n),
                None,
                Some(r0),
            );
        }
        assert_eq!(rails.r1.len(), n, "rail1 restored width at n={n}");
        assert_eq!(rails.r2.len(), n, "rail2 restored width at n={n}");
        let final_r1 = rails.r1;
        let final_r2 = rails.r2;
        let peak = c.peak_total();
        let (nq, nb) = c.i13_dims();
        Built {
            ops: c.take_ops(),
            contract_start,
            fwd_end,
            nq,
            nb,
            input_r1,
            input_r2,
            typ_prev,
            r0,
            pre_r1,
            pre_r2,
            mid_r1,
            mid_r2,
            typ,
            isc,
            final_r1,
            final_r2,
            peak,
        }
    }

    // The invariant-one r0 loan checks condition depth through the phase
    // reporter, so enable that observer before constructing either circuit.
    std::env::set_var("HEO_RESEARCH", "1");
    std::env::set_var("HEO_PHASE_REPORT", "1");
    fn sign_extended(sim: &Sim, reg: &[Q], keep: usize, lane: usize) -> bool {
        let sign = sim.wire(reg[keep - 1], lane);
        reg[keep..].iter().all(|&q| sim.wire(q, lane) == sign)
    }

    // Every distinct (source contraction, target contraction) geometry used by
    // the newly hosted production rows.  The kernel proof is exhaustive over
    // arbitrary pre-rail inputs; contraction/re-growth is checked on exactly
    // the lanes satisfying its public sign-extension support promise.
    let geometries = [
        (1usize, 0usize), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0),
    ];
    let mut total_cases = 0usize;
    let mut total_supported = 0usize;
    for (drop_r1, drop_r2) in geometries {
      let n_min = if (drop_r1, drop_r2) == (1, 0) { 3 } else { 4 };
      for n in n_min..=8 {
        let baseline = build(n, false, drop_r1, drop_r2);
        let hosted = build(n, true, drop_r1, drop_r2);
        assert_eq!(hosted.peak + 1, baseline.peak, "hosted peak delta n={n}");
        let cases = 1usize << (2 * n + 1);
        total_cases += cases;
        let mut supported_cases = 0usize;
        for lo in (0..cases).step_by(64) {
            let hi = (lo + 64).min(cases);
            let mut sb = Sim::new(baseline.nq, baseline.nb, 0xB451_0000 + lo as u64);
            let mut sh = Sim::new(hosted.nq, hosted.nb, 0xB451_0000 + lo as u64);
            for case in lo..hi {
                let lane = case - lo;
                let bits = 1usize << n;
                let r1 = U::from((case % bits) as u64);
                let r2 = U::from(((case / bits) % bits) as u64);
                let tp = ((case >> (2 * n)) & 1) != 0;
                sb.set(&baseline.input_r1, r1, lane);
                sb.set(&baseline.input_r2, r2, lane);
                sh.set(&hosted.input_r1, r1, lane);
                sh.set(&hosted.input_r2, r2, lane);
                *sb.q.get_mut(baseline.r0.0 as usize).unwrap() |= 1u64 << lane;
                *sh.q.get_mut(hosted.r0.0 as usize).unwrap() |= 1u64 << lane;
                if tp {
                    *sb.q.get_mut(baseline.typ_prev.0 as usize).unwrap() |= 1u64 << lane;
                    *sh.q.get_mut(hosted.typ_prev.0 as usize).unwrap() |= 1u64 << lane;
                }
            }
            sb.run(&baseline.ops[..baseline.contract_start]);
            sh.run(&hosted.ops[..hosted.contract_start]);
            let live_mask = mask(hi - lo);
            assert_eq!(
                sb.phase & live_mask,
                sh.phase & live_mask,
                "pre-contract phase differential n={n} lo={lo}"
            );
            let mut support_mask = 0u64;
            for lane in 0..hi - lo {
                if sign_extended(&sb, &baseline.pre_r1, n - drop_r1, lane)
                    && sign_extended(&sb, &baseline.pre_r2, n - drop_r2, lane)
                {
                    support_mask |= 1u64 << lane;
                    supported_cases += 1;
                }
            }
            sb.run(&baseline.ops[baseline.contract_start..baseline.fwd_end]);
            sh.run(&hosted.ops[hosted.contract_start..hosted.fwd_end]);
            let checked = live_mask & support_mask;
            assert_eq!(
                sb.phase & checked,
                sh.phase & checked,
                "forward phase differential n={n} lo={lo}"
            );
            assert_eq!(sb.dirty & checked, 0, "baseline forward dirty n={n} lo={lo}");
            assert_eq!(sh.dirty & checked, 0, "hosted forward dirty n={n} lo={lo}");
            for lane in 0..hi - lo {
                if (checked >> lane) & 1 == 0 {
                    continue;
                }
                assert_eq!(
                    sb.get(&baseline.mid_r1, lane),
                    sh.get(&hosted.mid_r1, lane),
                    "forward r1 n={n} case={}",
                    lo + lane
                );
                assert_eq!(
                    sb.get(&baseline.mid_r2, lane),
                    sh.get(&hosted.mid_r2, lane),
                    "forward r2 n={n} case={}",
                    lo + lane
                );
                assert_eq!(
                    sb.wire(baseline.typ, lane),
                    sh.wire(hosted.typ, lane),
                    "forward typ n={n} case={}",
                    lo + lane
                );
                assert_eq!(
                    sb.wire(baseline.isc, lane),
                    sh.wire(hosted.isc, lane),
                    "forward isc n={n} case={}",
                    lo + lane
                );
            }
            let keep_b: Vec<Q> = baseline
                .mid_r1
                .iter()
                .chain(&baseline.mid_r2)
                .copied()
                .chain([baseline.typ, baseline.isc, baseline.typ_prev, baseline.r0])
                .collect();
            let keep_h: Vec<Q> = hosted
                .mid_r1
                .iter()
                .chain(&hosted.mid_r2)
                .copied()
                .chain([hosted.typ, hosted.isc, hosted.typ_prev, hosted.r0])
                .collect();
            assert_eq!(sb.residue(&keep_b) & checked, 0, "baseline fwd residue n={n}");
            assert_eq!(sh.residue(&keep_h) & checked, 0, "hosted fwd residue n={n}");

            sb.run(&baseline.ops[baseline.fwd_end..]);
            sh.run(&hosted.ops[hosted.fwd_end..]);
            for lane in 0..hi - lo {
                if (checked >> lane) & 1 == 0 {
                    continue;
                }
                assert_eq!(
                    sb.get(&baseline.final_r1, lane),
                    sh.get(&hosted.final_r1, lane),
                    "reverse r1 differential n={n} case={}",
                    lo + lane
                );
                assert_eq!(
                    sb.get(&baseline.final_r2, lane),
                    sh.get(&hosted.final_r2, lane),
                    "reverse r2 differential n={n} case={}",
                    lo + lane
                );
            }
            assert_eq!(
                sb.phase & checked,
                sh.phase & checked,
                "reverse phase differential n={n} lo={lo}"
            );
            assert_eq!(
                sb.dirty & checked,
                sh.dirty & checked,
                "reverse dirty differential n={n} lo={lo}"
            );
            let keep_b: Vec<Q> = baseline
                .final_r1
                .iter()
                .chain(&baseline.final_r2)
                .copied()
                .chain([baseline.typ_prev, baseline.r0])
                .collect();
            let keep_h: Vec<Q> = hosted
                .final_r1
                .iter()
                .chain(&hosted.final_r2)
                .copied()
                .chain([hosted.typ_prev, hosted.r0])
                .collect();
            assert_eq!(sb.residue(&keep_b) & checked, 0, "baseline reverse residue n={n}");
            assert_eq!(sh.residue(&keep_h) & checked, 0, "hosted reverse residue n={n}");
        }
        assert!(supported_cases > 0, "empty contraction support geometry");
        total_supported += supported_cases;
        println!(
            "{{\"kind\":\"skycof-signext-isc-host\",\"n\":{n},\"drop_r1\":{drop_r1},\"drop_r2\":{drop_r2},\"cases\":{cases},\"supported\":{supported_cases},\"baseline_peak\":{},\"hosted_peak\":{},\"forward\":\"equal\",\"reverse\":\"exact\",\"phase\":\"clean\",\"garbage\":\"clean\"}}",
            baseline.peak, hosted.peak
        );
      }
    }
    println!(
        "{{\"kind\":\"skycof-signext-isc-host-summary\",\"n_min\":3,\"n_max\":8,\"geometries\":7,\"cases\":{total_cases},\"supported\":{total_supported},\"result\":\"PASS\"}}"
    );
}

/// Exact reduced-width falsifier for the reverse-tick324 late-return r0 lease.
/// Legal poststates are generated by the ordinary hosted forward kernel, then
/// contracted to `(n-1,n-1)` before comparing the incumbent reverse with the
/// late-return owner rotation.
fn test_late_r0_target_lease() {
    struct Built {
        ops: Vec<Op>,
        contract_start: usize,
        fwd_end: usize,
        nq: usize,
        nb: usize,
        in_r1: Vec<Q>,
        in_r2: Vec<Q>,
        pre_r2: Vec<Q>,
        out_r1: Vec<Q>,
        out_r2: Vec<Q>,
        typ_prev: Q,
        typ: Q,
        isc: Q,
        spectator: Q,
        r0: Q,
        donor: Q,
        rev_peak: u32,
        plan: Plan,
    }

    fn build(n: usize, late: bool) -> Built {
        let mut c = Builder::new();
        let in_r1 = c.alloc_qubits(n - 1);
        let in_r2 = c.alloc_qubits(n);
        let typ_prev = c.alloc_qubit();
        let spectator = c.alloc_qubit();
        let r0 = c.alloc_qubit();
        c.x(r0);
        let mut rails = Rails { r1: in_r1.clone(), r2: in_r2.clone() };
        let (typ, isc, _) = rail_fwd_signext_host(
            &mut c, &mut rails, Some(typ_prev), n, n, None, Some(r0));
        assert_eq!(rails.r1.len(), n - 1);
        assert_eq!(rails.r2.len(), n);
        let pre_r2 = rails.r2.clone();
        let contract_start = c.op_count();
        resize_signed(&mut c, &mut rails.r2, n - 1);
        let fwd_end = c.op_count();
        let cap = c.active_qubits() as usize;
        let ((plan, donor), rev_peak) = c.r3_peak(|c| {
            if late {
                let p = rail_rev_signext_late_r0(
                    c, &mut rails, typ, isc, Some(typ_prev), n,
                    (n - 1, n), cap, r0);
                (p, *rails.r2.last().unwrap())
            } else {
                resize_signed(c, &mut rails.r2, n);
                let p = rail_rev_signext_host(
                    c, &mut rails, typ, isc, Some(typ_prev), n,
                    (n - 1, n), Some(cap), Some(r0));
                (p, *rails.r2.last().unwrap())
            }
        });
        assert_eq!(plan, Plan::Vented(0));
        assert_eq!(rails.r1.len(), n - 1);
        assert_eq!(rails.r2.len(), n);
        if late {
            assert_eq!(*rails.r2.last().unwrap(), isc, "late donor ID is not hosted isC");
            assert_eq!(donor, isc);
            assert!(!rails.r1.contains(&r0) && !rails.r2.contains(&r0));
        }
        let out_r1 = rails.r1;
        let out_r2 = rails.r2;
        let (nq, nb) = c.i13_dims();
        Built {
            ops: c.take_ops(), contract_start, fwd_end, nq, nb, in_r1, in_r2, pre_r2, out_r1, out_r2,
            typ_prev, typ, isc, spectator, r0, donor, rev_peak, plan,
        }
    }

    // Symplectic conjugation for CX(a,q);CX(q,a), ordered as
    // [Xa,Xq | Za,Zq]. This proves the coherent move on q=0 also transports
    // entanglement with an arbitrary spectator and introduces no phase gate.
    fn cx(p: &mut [bool; 4], control: usize, target: usize) {
        p[target] ^= p[control];
        p[2 + control] ^= p[2 + target];
    }
    fn moved(mut p: [bool; 4]) -> [bool; 4] {
        cx(&mut p, 0, 1);
        cx(&mut p, 1, 0);
        p
    }
    assert_eq!(moved([true,false,false,false]), [false,true,false,false]); // Xa -> Xq
    assert_eq!(moved([false,true,false,false]), [true,true,false,false]); // Xq -> XaXq
    assert_eq!(moved([false,false,true,false]), [false,false,true,true]); // Za -> ZaZq
    assert_eq!(moved([false,false,false,true]), [false,false,true,false]); // Zq -> Za
    for a in [false, true] {
        for spectator in [false, true] {
            let (mut aa, mut q) = (a, false);
            q ^= aa;
            aa ^= q;
            assert_eq!((aa, q, spectator), (false, a, spectator));
        }
    }

    std::env::set_var("HEO_RESEARCH", "1");
    std::env::set_var("HEO_PHASE_REPORT", "1");
    fn sign_extended(sim: &Sim, reg: &[Q], keep: usize, lane: usize) -> bool {
        let sign = sim.wire(reg[keep - 1], lane);
        reg[keep..].iter().all(|&q| sim.wire(q, lane) == sign)
    }
    let mut generated = 0u64;
    let mut supported = 0u64;
    let mut saw_isc = [false; 2];
    let mut saw_typ = [false; 2];
    for n in 4usize..=8 {
        let ordinary = build(n, false);
        let late = build(n, true);
        assert_eq!(late.rev_peak + 1, ordinary.rev_peak,
            "late-r0 peak delta n={n}");
        assert_eq!(ordinary.plan, Plan::Vented(0));
        assert_eq!(late.plan, Plan::Vented(0));
        assert_eq!(late.donor, late.isc);
        let bits = 2 * n + 1; // r1(n-1), r2(n), typ_prev, spectator
        let cases = 1u64 << bits;
        generated += cases;
        for lo in (0..cases).step_by(64) {
            let hi = (lo + 64).min(cases);
            let live = if hi - lo == 64 { u64::MAX } else { (1u64 << (hi - lo)) - 1 };
            let mut so = Sim::new(ordinary.nq, ordinary.nb + 1, 0x1A7E_0000 ^ lo);
            let mut sl = Sim::new(late.nq, late.nb + 1, 0x1A7E_0000 ^ lo);
            let mut r1v = Vec::new();
            let mut r2v = Vec::new();
            for case in lo..hi {
                let lane = (case - lo) as usize;
                let rv1 = U::from(case & ((1u64 << (n - 1)) - 1));
                let rv2 = U::from((case >> (n - 1)) & ((1u64 << n) - 1));
                let tp = (case >> (2 * n - 1)) & 1 != 0;
                let sp = (case >> (2 * n)) & 1 != 0;
                so.set(&ordinary.in_r1, rv1, lane);
                so.set(&ordinary.in_r2, rv2, lane);
                sl.set(&late.in_r1, rv1, lane);
                sl.set(&late.in_r2, rv2, lane);
                if tp { so.q[ordinary.typ_prev.0 as usize] |= 1u64 << lane; sl.q[late.typ_prev.0 as usize] |= 1u64 << lane; }
                if sp { so.q[ordinary.spectator.0 as usize] |= 1u64 << lane; sl.q[late.spectator.0 as usize] |= 1u64 << lane; }
                r1v.push(rv1);
                r2v.push(rv2);
            }
            so.run(&ordinary.ops[..ordinary.contract_start]);
            sl.run(&late.ops[..late.contract_start]);
            let mut support = 0u64;
            for lane in 0..(hi - lo) as usize {
                if sign_extended(&so, &ordinary.pre_r2, n - 1, lane) {
                    support |= 1u64 << lane;
                    supported += 1;
                    saw_isc[so.wire(ordinary.isc, lane) as usize] = true;
                    saw_typ[so.wire(ordinary.typ, lane) as usize] = true;
                    assert_eq!(so.wire(ordinary.isc, lane), sl.wire(late.isc, lane));
                    assert_eq!(so.wire(ordinary.typ, lane), sl.wire(late.typ, lane));
                }
            }
            let checked = live & support;
            so.run(&ordinary.ops[ordinary.contract_start..ordinary.fwd_end]);
            sl.run(&late.ops[late.contract_start..late.fwd_end]);
            assert_eq!(so.dirty & checked, 0, "ordinary forward dirty n={n} lo={lo}");
            assert_eq!(sl.dirty & checked, 0, "late forward dirty n={n} lo={lo}");
            so.run(&ordinary.ops[ordinary.fwd_end..]);
            sl.run(&late.ops[late.fwd_end..]);
            assert_eq!(so.phase & checked, sl.phase & checked, "late-r0 phase n={n} lo={lo}");
            assert_eq!(so.dirty & checked, sl.dirty & checked, "late-r0 dirty n={n} lo={lo}");
            for lane in 0..(hi - lo) as usize {
                if (checked >> lane) & 1 == 0 { continue; }
                assert_eq!(so.get(&ordinary.out_r1, lane), r1v[lane]);
                assert_eq!(so.get(&ordinary.out_r2, lane), r2v[lane]);
                assert_eq!(sl.get(&late.out_r1, lane), r1v[lane]);
                assert_eq!(sl.get(&late.out_r2, lane), r2v[lane]);
                assert_eq!(so.wire(ordinary.typ_prev, lane), sl.wire(late.typ_prev, lane));
                assert_eq!(so.wire(ordinary.spectator, lane), sl.wire(late.spectator, lane));
                assert!(so.wire(ordinary.r0, lane));
                assert!(sl.wire(late.r0, lane));
            }
            let keep_o: Vec<Q> = ordinary.out_r1.iter().chain(&ordinary.out_r2)
                .copied().chain([ordinary.typ_prev, ordinary.spectator, ordinary.r0]).collect();
            let keep_l: Vec<Q> = late.out_r1.iter().chain(&late.out_r2)
                .copied().chain([late.typ_prev, late.spectator, late.r0]).collect();
            assert_eq!(so.residue(&keep_o) & checked, 0, "ordinary garbage n={n} lo={lo}");
            assert_eq!(sl.residue(&keep_l) & checked, 0, "late garbage n={n} lo={lo}");
        }
        println!(
            "{{\"kind\":\"skycof-late-r0-target-lease\",\"n\":{n},\"cases\":{cases},\"ordinary_peak\":{},\"late_peak\":{},\"plan\":\"Vented0\",\"r0\":\"restored1\",\"donor_id\":{},\"result\":\"PASS\"}}",
            ordinary.rev_peak, late.rev_peak, late.donor.0
        );
    }
    assert_eq!(saw_isc, [true, true]);
    assert_eq!(saw_typ, [true, true]);
    println!(
        "{{\"kind\":\"skycof-late-r0-target-lease-summary\",\"n_min\":4,\"n_max\":8,\"generated\":{generated},\"supported\":{supported},\"isc_values\":2,\"typ_values\":2,\"two_cx_stabilizer\":\"PASS\",\"result\":\"PASS\"}}"
    );
}

/// Exhaustive differential for rotating the forward-inserted zero cofactor
/// head into the reverse `isC` owner.  The low odd R invariant is fixed to 1;
/// every other cofactor bit, typ, and high-tail shape is exhaustive.
fn test_cofzero_isc_recycle() {
    struct Built {
        ops: Vec<Op>,
        nq: usize,
        nb: usize,
        input_s: Vec<Q>,
        input_r: Vec<Q>,
        typ: Q,
        output_s: Vec<Q>,
        output_r: Vec<Q>,
        isc: Q,
        peak: u32,
    }

    fn build(n: usize, recycled: bool) -> Built {
        let mut c = Builder::new();
        let zero_head = c.alloc_qubit();
        let input_s = c.alloc_qubits(n);
        let input_r = c.alloc_qubits(n);
        let typ = c.alloc_qubit();
        let mut cof = Cof {
            s: std::iter::once(zero_head)
                .chain(input_s.iter().copied())
                .collect(),
            r: input_r.clone(),
        };
        let base = c.active_qubits();
        let (isc, peak) = if recycled {
            let (isc, peak) = c.r3_peak(|c| {
                let isc = isc_recompute_from_zero_head(c, &mut cof, typ);
                cof_rev_at_zero_head(c, &mut cof, typ, isc, n, None, 100);
                isc
            });
            (isc, peak)
        } else {
            let (isc, peak) = c.r3_peak(|c| {
                let isc = isc_recompute(c, &cof, typ);
                cof_rev_at(c, &mut cof, typ, isc, n, None, 100);
                isc
            });
            (isc, peak)
        };
        assert_eq!(c.active_qubits(), base, "cofzero rotation changed live count");
        assert_eq!(cof.s.len(), n);
        assert_eq!(cof.r.len(), n);
        let (nq, nb) = c.i13_dims();
        Built {
            ops: c.take_ops(),
            nq,
            nb: nb + 1,
            input_s,
            input_r,
            typ,
            output_s: cof.s,
            output_r: cof.r,
            isc,
            peak,
        }
    }

    std::env::set_var("HEO_RESEARCH", "1");
    std::env::set_var("HEO_PHASE_REPORT", "1");
    let mut total_cases = 0usize;
    for n in 2usize..=8 {
        let ordinary = build(n, false);
        let recycled = build(n, true);
        assert!(
            recycled.peak <= ordinary.peak,
            "cofzero rotation raised peak at n={n}"
        );
        let cases = 1usize << (2 * n);
        total_cases += cases;
        for lo in (0..cases).step_by(64) {
            let hi = (lo + 64).min(cases);
            let mut so = Sim::new(ordinary.nq, ordinary.nb, 0xC0F0_0000 + lo as u64);
            let mut sr = Sim::new(recycled.nq, recycled.nb, 0xC0F0_0000 + lo as u64);
            for case in lo..hi {
                let lane = case - lo;
                let sm = (1usize << n) - 1;
                let s = U::from((case & sm) as u64);
                let rhi = (case >> n) & ((1usize << (n - 1)) - 1);
                let r = U::from(((rhi << 1) | 1) as u64);
                let typ = (case >> (2 * n - 1)) & 1 != 0;
                so.set(&ordinary.input_s, s, lane);
                so.set(&ordinary.input_r, r, lane);
                sr.set(&recycled.input_s, s, lane);
                sr.set(&recycled.input_r, r, lane);
                if typ {
                    *so.q.get_mut(ordinary.typ.0 as usize).unwrap() |= 1u64 << lane;
                    *sr.q.get_mut(recycled.typ.0 as usize).unwrap() |= 1u64 << lane;
                }
            }
            so.run(&ordinary.ops);
            sr.run(&recycled.ops);
            let live = mask(hi - lo);
            assert_eq!(so.phase & live, sr.phase & live, "cofzero phase n={n} lo={lo}");
            assert_eq!(so.dirty & live, sr.dirty & live, "cofzero dirty n={n} lo={lo}");
            for lane in 0..hi - lo {
                assert_eq!(
                    so.get(&ordinary.output_s, lane),
                    sr.get(&recycled.output_s, lane),
                    "cofzero s n={n} case={}",
                    lo + lane
                );
                assert_eq!(
                    so.get(&ordinary.output_r, lane),
                    sr.get(&recycled.output_r, lane),
                    "cofzero r n={n} case={}",
                    lo + lane
                );
                assert_eq!(so.wire(ordinary.typ, lane), sr.wire(recycled.typ, lane));
                assert_eq!(so.wire(ordinary.isc, lane), sr.wire(recycled.isc, lane));
            }
            let keep_o: Vec<Q> = ordinary
                .output_s
                .iter()
                .chain(&ordinary.output_r)
                .copied()
                .chain([ordinary.typ, ordinary.isc])
                .collect();
            let keep_r: Vec<Q> = recycled
                .output_s
                .iter()
                .chain(&recycled.output_r)
                .copied()
                .chain([recycled.typ, recycled.isc])
                .collect();
            assert_eq!(so.residue(&keep_o) & live, 0, "ordinary cofzero residue n={n}");
            assert_eq!(sr.residue(&keep_r) & live, 0, "recycled cofzero residue n={n}");
        }
        println!(
            "{{\"kind\":\"skycof-cofzero-isc-recycle\",\"n\":{n},\"cases\":{cases},\"ordinary_peak\":{},\"recycled_peak\":{},\"state\":\"equal\",\"phase\":\"equal\",\"garbage\":\"clean\"}}",
            ordinary.peak, recycled.peak
        );
    }
    println!(
        "{{\"kind\":\"skycof-cofzero-isc-recycle-summary\",\"n_min\":2,\"n_max\":8,\"cases\":{total_cases},\"result\":\"PASS\"}}"
    );
}

/// Isolated R4 recurrence: ordinary `cof_fwd + erase_isc` versus clearing the
/// last-use isC owner and immediately rotating that exact clean ID into the
/// fresh zero head. Reverse uses the matching zero-head-to-isC rotation.
fn test_cof_isc_zero_rotation() {
    struct Built {
        ops: Vec<Op>,
        fwd_end: usize,
        nq: usize,
        nb: usize,
        input_s: Vec<Q>,
        input_r: Vec<Q>,
        typ: Q,
        isc_in: Q,
        spectator: Q,
        mid_s: Vec<Q>,
        mid_r: Vec<Q>,
        out_s: Vec<Q>,
        out_r: Vec<Q>,
        isc_out: Q,
        peak: u32,
    }
    fn build(n: usize, rotated: bool) -> Built {
        let mut c = Builder::new();
        let input_s = c.alloc_qubits(n);
        let input_r = c.alloc_qubits(n);
        let typ = c.alloc_qubit();
        let isc_in = c.alloc_qubit();
        let spectator = c.alloc_qubit();
        let mut cof = Cof { s: input_s.clone(), r: input_r.clone() };
        let w = TickWidths {
            wsw: n,
            wad: n,
            post_r1: n,
            post_r2: n,
            ecof: n,
            clamp: 256,
        };
        if rotated {
            cof_fwd_rotate_isc_fixture(&mut c, &mut cof, typ, isc_in, &w, None);
        } else {
            cof_fwd(&mut c, &mut cof, typ, isc_in, &w, None);
            erase_isc(&mut c, &cof, typ, isc_in);
        }
        let mid_s = cof.s.clone();
        let mid_r = cof.r.clone();
        let fwd_end = c.op_count();
        let isc_out = if rotated {
            let q = isc_recompute_from_zero_head(&mut c, &mut cof, typ);
            cof_rev_at_zero_head(&mut c, &mut cof, typ, q, n, None, 100);
            q
        } else {
            let q = isc_recompute(&mut c, &cof, typ);
            cof_rev_at(&mut c, &mut cof, typ, q, n, None, 100);
            q
        };
        let out_s = cof.s;
        let out_r = cof.r;
        let peak = c.peak_total();
        let (nq, nb) = c.i13_dims();
        Built {
            ops: c.take_ops(), fwd_end, nq, nb, input_s, input_r, typ, isc_in,
            spectator, mid_s, mid_r, out_s, out_r, isc_out, peak,
        }
    }
    std::env::set_var("HEO_RESEARCH", "1");
    std::env::set_var("HEO_PHASE_REPORT", "1");
    let mut valid_total = 0usize;
    let mut clean_total = 0usize;
    for n in 2usize..=8 {
        let ordinary = build(n, false);
        let rotated = build(n, true);
        assert!(rotated.peak <= ordinary.peak, "R4 raised peak n={n}");
        let raw_cases = 1usize << (2 * (n - 1) + 3);
        let mut valid_n = 0usize;
        for lo in (0..raw_cases).step_by(64) {
            let hi = (lo + 64).min(raw_cases);
            let mut so = Sim::new(ordinary.nq, ordinary.nb, 0xC04F_0000 + lo as u64);
            let mut sr = Sim::new(rotated.nq, rotated.nb, 0xC04F_0000 + lo as u64);
            let mut valid = 0u64;
            for case in lo..hi {
                let lane = case - lo;
                let high_mask = (1usize << (n - 1)) - 1;
                let sh = case & high_mask;
                let rh = (case >> (n - 1)) & high_mask;
                let typ = (case >> (2 * (n - 1))) & 1 != 0;
                let isc = (case >> (2 * (n - 1) + 1)) & 1 != 0;
                let spectator = (case >> (2 * (n - 1) + 2)) & 1 != 0;
                if typ && isc { continue; }
                valid |= 1u64 << lane;
                valid_n += 1;
                for (sim, built) in [(&mut so, &ordinary), (&mut sr, &rotated)] {
                    sim.set(&built.input_s, U::from((sh << 1) as u64), lane);
                    sim.set(&built.input_r, U::from(((rh << 1) | 1) as u64), lane);
                    if typ { sim.q[built.typ.0 as usize] |= 1u64 << lane; }
                    if isc { sim.q[built.isc_in.0 as usize] |= 1u64 << lane; }
                    if spectator { sim.q[built.spectator.0 as usize] |= 1u64 << lane; }
                }
            }
            so.run(&ordinary.ops[..ordinary.fwd_end]);
            sr.run(&rotated.ops[..rotated.fwd_end]);
            let checked = valid & !so.dirty;
            clean_total += checked.count_ones() as usize;
            assert_eq!(so.phase & checked, sr.phase & checked, "R4 fwd phase n={n} lo={lo}");
            assert_eq!(sr.dirty & checked, 0);
            for lane in 0..hi - lo {
                if (checked >> lane) & 1 == 0 { continue; }
                assert_eq!(so.get(&ordinary.mid_s, lane), sr.get(&rotated.mid_s, lane));
                assert_eq!(so.get(&ordinary.mid_r, lane), sr.get(&rotated.mid_r, lane));
                assert_eq!(so.wire(ordinary.typ, lane), sr.wire(rotated.typ, lane));
                assert_eq!(so.wire(ordinary.spectator, lane), sr.wire(rotated.spectator, lane));
            }
            so.run(&ordinary.ops[ordinary.fwd_end..]);
            sr.run(&rotated.ops[rotated.fwd_end..]);
            assert_eq!(so.phase & checked, sr.phase & checked, "R4 rev phase n={n} lo={lo}");
            assert_eq!(so.dirty & checked, sr.dirty & checked);
            for lane in 0..hi - lo {
                if (checked >> lane) & 1 == 0 { continue; }
                assert_eq!(so.get(&ordinary.out_s, lane), sr.get(&rotated.out_s, lane));
                assert_eq!(so.get(&ordinary.out_r, lane), sr.get(&rotated.out_r, lane));
                for (qo, qr) in [(ordinary.typ, rotated.typ),
                    (ordinary.spectator, rotated.spectator),
                    (ordinary.isc_out, rotated.isc_out)] {
                    assert_eq!(so.wire(qo, lane), sr.wire(qr, lane));
                }
            }
        }
        valid_total += valid_n;
        println!(
            "{{\"kind\":\"skycof-cof-isc-zero-rotation\",\"n\":{n},\"valid_cases\":{valid_n},\"ordinary_peak\":{},\"rotated_peak\":{},\"forward\":\"equal\",\"reverse\":\"equal\",\"phase\":\"equal\",\"spectator\":\"restored\"}}",
            ordinary.peak, rotated.peak
        );
    }
    println!(
        "{{\"kind\":\"skycof-cof-isc-zero-rotation-summary\",\"valid_cases\":{valid_total},\"clean_supported\":{clean_total},\"result\":\"PASS\"}}"
    );
}

/// Exhaustive physical-ID test for beginning the rail-parity loan before the
/// clamp predicate. The body models ParkTest's fresh AND owner followed by its
/// exact measurement/phase repair; under r1[0] XOR r2[0] = 1 the released rail
/// ID may be reused and must return with arbitrary rail/control state intact.
fn test_park_parity_loan() {
    std::env::set_var("HEO_RESEARCH", "1");
    std::env::set_var("HEO_PHASE_REPORT", "1");
    struct Built {
        ops: Vec<Op>,
        nq: usize,
        nb: usize,
        a: Q,
        q: Q,
        u: Q,
        v: Q,
        peak: u32,
    }
    fn build(loan: bool) -> Built {
        let mut c = Builder::new();
        let a = c.alloc_qubit();
        let q = c.alloc_qubit();
        let u = c.alloc_qubit();
        let v = c.alloc_qubit();
        let rails = Rails { r1: vec![a], r2: vec![q] };
        let body = |c: &mut Builder| {
            let z = c.alloc_qubit();
            c.ccx(u, v, z);
            let m = c.alloc_bit();
            c.hmr(z, m);
            c.cz_if(u, v, m);
            c.free_bit(m);
            c.release_clean(z);
        };
        if loan {
            with_rail_parity_loan(&mut c, &rails, body);
        } else {
            body(&mut c);
        }
        let peak = c.peak_total();
        let (nq, nb) = c.i13_dims();
        Built { ops: c.take_ops(), nq, nb, a, q, u, v, peak }
    }
    let ordinary = build(false);
    let loaned = build(true);
    assert_eq!(loaned.peak + 1, ordinary.peak);
    let mut so = Sim::new(ordinary.nq, ordinary.nb, 0xB1A0_0001);
    let mut sl = Sim::new(loaned.nq, loaned.nb, 0xB1A0_0001);
    for case in 0..8usize {
        let a = case & 1 != 0;
        let q = !a;
        let u = case & 2 != 0;
        let v = case & 4 != 0;
        for (sim, built) in [(&mut so, &ordinary), (&mut sl, &loaned)] {
            if a { sim.q[built.a.0 as usize] |= 1u64 << case; }
            if q { sim.q[built.q.0 as usize] |= 1u64 << case; }
            if u { sim.q[built.u.0 as usize] |= 1u64 << case; }
            if v { sim.q[built.v.0 as usize] |= 1u64 << case; }
        }
    }
    so.run(&ordinary.ops);
    sl.run(&loaned.ops);
    let live = mask(8);
    assert_eq!(so.phase & live, sl.phase & live);
    assert_eq!(so.dirty & live, 0);
    assert_eq!(sl.dirty & live, 0);
    for case in 0..8usize {
        for (qo, ql) in [(ordinary.a, loaned.a), (ordinary.q, loaned.q), (ordinary.u, loaned.u), (ordinary.v, loaned.v)] {
            assert_eq!(so.wire(qo, case), sl.wire(ql, case));
        }
    }
    let keep_o = [ordinary.a, ordinary.q, ordinary.u, ordinary.v];
    let keep_l = [loaned.a, loaned.q, loaned.u, loaned.v];
    assert_eq!(so.residue(&keep_o) & live, 0);
    assert_eq!(sl.residue(&keep_l) & live, 0);
    println!(
        "{{\"kind\":\"skycof-park-parity-loan\",\"cases\":8,\"ordinary_peak\":{},\"loaned_peak\":{},\"state\":\"equal\",\"phase\":\"equal\",\"garbage\":\"clean\"}}",
        ordinary.peak, loaned.peak
    );
}

/// Isolated R6-A fixture: replace ghost_odo's fresh `g=z&!typ` with the
/// invariant physical r0=|1>. The host is zeroed, used for the same predicate,
/// HMR/phase-cleared with the incumbent Z/CZ correction, then reacquired and
/// restored to |1>; unrelated target/spectator data must be identical.
fn test_ghost_r0_host() {
    struct Built {
        ops: Vec<Op>,
        nq: usize,
        nb: usize,
        r0: Q,
        z: Q,
        typ: Q,
        targets: Vec<Q>,
        spectator: Q,
        peak: u32,
    }
    fn build(hosted: bool) -> Built {
        let mut c = Builder::new();
        let r0 = c.alloc_qubit();
        c.x(r0);
        let z = c.alloc_qubit();
        let typ = c.alloc_qubit();
        let targets = c.alloc_qubits(3);
        let spectator = c.alloc_qubit();
        let g = if hosted {
            c.x(r0);
            r0
        } else {
            c.alloc_qubit()
        };
        c.x(typ);
        c.ccx(z, typ, g);
        c.x(typ);
        for &q in &targets {
            c.cx(g, q);
        }
        let m = c.alloc_bit();
        c.hmr(g, m);
        c.z_if(z, m);
        c.cz_if(z, typ, m);
        c.free_bit(m);
        c.release_clean(g);
        if hosted {
            c.reacquire(r0);
            c.x(r0);
        }
        let peak = c.peak_total();
        let (nq, nb) = c.i13_dims();
        Built { ops: c.take_ops(), nq, nb, r0, z, typ, targets, spectator, peak }
    }
    let ordinary = build(false);
    let hosted = build(true);
    assert_eq!(hosted.peak + 1, ordinary.peak);
    let mut so = Sim::new(ordinary.nq, ordinary.nb, 0x6605_7001);
    let mut sh = Sim::new(hosted.nq, hosted.nb, 0x6605_7001);
    for case in 0..64usize {
        for (sim, built) in [(&mut so, &ordinary), (&mut sh, &hosted)] {
            if case & 1 != 0 { sim.q[built.z.0 as usize] |= 1u64 << case; }
            if case & 2 != 0 { sim.q[built.typ.0 as usize] |= 1u64 << case; }
            for (i, &q) in built.targets.iter().enumerate() {
                if (case >> (2 + i)) & 1 != 0 { sim.q[q.0 as usize] |= 1u64 << case; }
            }
            if case & 32 != 0 { sim.q[built.spectator.0 as usize] |= 1u64 << case; }
        }
    }
    so.run(&ordinary.ops);
    sh.run(&hosted.ops);
    assert_eq!(so.phase, sh.phase);
    assert_eq!(so.dirty, 0);
    assert_eq!(sh.dirty, 0);
    for case in 0..64usize {
        for (qo, qh) in [(ordinary.r0, hosted.r0), (ordinary.z, hosted.z),
            (ordinary.typ, hosted.typ), (ordinary.spectator, hosted.spectator)] {
            assert_eq!(so.wire(qo, case), sh.wire(qh, case));
        }
        for (&qo, &qh) in ordinary.targets.iter().zip(&hosted.targets) {
            assert_eq!(so.wire(qo, case), sh.wire(qh, case));
        }
    }
    let keep_o: Vec<Q> = [ordinary.r0, ordinary.z, ordinary.typ, ordinary.spectator]
        .into_iter().chain(ordinary.targets.iter().copied()).collect();
    let keep_h: Vec<Q> = [hosted.r0, hosted.z, hosted.typ, hosted.spectator]
        .into_iter().chain(hosted.targets.iter().copied()).collect();
    assert_eq!(so.residue(&keep_o), 0);
    assert_eq!(sh.residue(&keep_h), 0);
    println!(
        "{{\"kind\":\"skycof-ghost-r0-host\",\"cases\":64,\"ordinary_peak\":{},\"hosted_peak\":{},\"state\":\"equal\",\"phase\":\"equal\",\"r0\":\"restored\",\"spectator\":\"restored\"}}",
        ordinary.peak, hosted.peak
    );
}

/// Reduced-width differential for the narrow tick318 dual-known-constant
/// loan.  Production geometry is `(prev_r1,prev_r2)=(n-1,n+1)`,
/// `(wsw,wadd,post1,post2)=(n+1,n,n,n)`.  The target contraction is checked on
/// exactly its sign-extension support; typ_prev and an unrelated spectator are
/// arbitrary, and the ordinary reverse must restore every physical input.
fn test_t318_dual_loan() {
    struct Built {
        ops: Vec<Op>,
        fwd_end: usize,
        nq: usize,
        nb: usize,
        in_r1: Vec<Q>,
        in_r2: Vec<Q>,
        typ_prev: Q,
        spectator: Q,
        qs: Q,
        qr: Q,
        mid_r1: Vec<Q>,
        mid_r2: Vec<Q>,
        typ: Q,
        isc: Q,
        out_r1: Vec<Q>,
        out_r2: Vec<Q>,
        peak: u32,
    }
    fn build(n: usize, dual: bool) -> Built {
        let mut c = Builder::new();
        let qs = c.alloc_qubit();
        let qr = c.alloc_qubit();
        c.x(qr);
        let spectator = c.alloc_qubit();
        let typ_prev = c.alloc_qubit();
        let in_r1 = c.alloc_qubits(n - 1);
        let in_r2 = c.alloc_qubits(n + 1);
        let mut rails = Rails { r1: in_r1.clone(), r2: in_r2.clone() };
        let w = TickWidths {
            wsw: n + 1,
            wad: n,
            post_r1: n,
            post_r2: n,
            ecof: n,
            clamp: 256,
        };
        let (typ, isc, _) = if dual {
            c.release_clean(qs);
            c.x(qr);
            c.release_clean(qr);
            c.set_avoid(&[qs, qr]);
            c.reacquire(qs);
            c.reacquire(qr);
            c.x(qr);
            c.set_avoid(&[]);
            let out = rail_fwd_micro(
                &mut c,
                &mut rails,
                Some(typ_prev),
                &w,
                None,
                Some(qr),
                None,
            );
            assert!(out.0 != qs && out.0 != qr && out.1 != qs && out.1 != qr);
            assert!(!rails.r1.contains(&qs) && !rails.r2.contains(&qs));
            assert!(!rails.r1.contains(&qr) && !rails.r2.contains(&qr));
            out
        } else {
            rail_fwd_micro(
                &mut c,
                &mut rails,
                Some(typ_prev),
                &w,
                None,
                Some(qr),
                None,
            )
        };
        let mid_r1 = rails.r1.clone();
        let mid_r2 = rails.r2.clone();
        let fwd_end = c.op_count();
        rail_rev_micro(
            &mut c,
            &mut rails,
            typ,
            isc,
            Some(typ_prev),
            &w,
            (n - 1, n + 1),
            None,
            Some(qr),
            None,
        );
        let out_r1 = rails.r1;
        let out_r2 = rails.r2;
        let peak = c.peak_total();
        let (nq, nb) = c.i13_dims();
        Built {
            ops: c.take_ops(), fwd_end, nq, nb, in_r1, in_r2, typ_prev,
            spectator, qs, qr, mid_r1, mid_r2, typ, isc, out_r1, out_r2, peak,
        }
    }
    std::env::set_var("HEO_RESEARCH", "1");
    std::env::set_var("HEO_PHASE_REPORT", "1");
    let mut total = 0usize;
    let mut supported = 0usize;
    for n in 3usize..=7 {
        let ordinary = build(n, false);
        let dual = build(n, true);
        assert!(dual.peak <= ordinary.peak);
        let cases = 1usize << (2 * n + 2);
        total += cases;
        for lo in (0..cases).step_by(64) {
            let hi = (lo + 64).min(cases);
            let mut so = Sim::new(ordinary.nq, ordinary.nb, 0xD0A1_0000 + lo as u64);
            let mut sd = Sim::new(dual.nq, dual.nb, 0xD0A1_0000 + lo as u64);
            let mut checked = 0u64;
            for case in lo..hi {
                let lane = case - lo;
                let r1m = (1usize << (n - 1)) - 1;
                let r2m = (1usize << (n + 1)) - 1;
                let r1 = U::from((case & r1m) as u64);
                let r2 = U::from(((case >> (n - 1)) & r2m) as u64);
                let tp = (case >> (2 * n)) & 1 != 0;
                let sp = (case >> (2 * n + 1)) & 1 != 0;
                for (sim, built) in [(&mut so, &ordinary), (&mut sd, &dual)] {
                    sim.set(&built.in_r1, r1, lane);
                    sim.set(&built.in_r2, r2, lane);
                    sim.q[built.qr.0 as usize] |= 1u64 << lane;
                    if tp { sim.q[built.typ_prev.0 as usize] |= 1u64 << lane; }
                    if sp { sim.q[built.spectator.0 as usize] |= 1u64 << lane; }
                }
                if r2.bit(n) == r2.bit(n - 1) {
                    checked |= 1u64 << lane;
                    supported += 1;
                }
            }
            so.run(&ordinary.ops[..ordinary.fwd_end]);
            sd.run(&dual.ops[..dual.fwd_end]);
            assert_eq!(so.phase & checked, sd.phase & checked);
            assert_eq!(so.dirty & checked, 0);
            assert_eq!(sd.dirty & checked, 0);
            for lane in 0..hi - lo {
                if (checked >> lane) & 1 == 0 { continue; }
                for (ro, rd) in [(&ordinary.mid_r1, &dual.mid_r1), (&ordinary.mid_r2, &dual.mid_r2)] {
                    assert_eq!(so.get(ro, lane), sd.get(rd, lane));
                }
                for (qo, qd) in [(ordinary.typ, dual.typ), (ordinary.isc, dual.isc),
                    (ordinary.typ_prev, dual.typ_prev), (ordinary.spectator, dual.spectator),
                    (ordinary.qs, dual.qs), (ordinary.qr, dual.qr)] {
                    assert_eq!(so.wire(qo, lane), sd.wire(qd, lane));
                }
            }
            so.run(&ordinary.ops[ordinary.fwd_end..]);
            sd.run(&dual.ops[dual.fwd_end..]);
            assert_eq!(so.phase & checked, sd.phase & checked);
            assert_eq!(so.dirty & checked, sd.dirty & checked);
            for lane in 0..hi - lo {
                if (checked >> lane) & 1 == 0 { continue; }
                assert_eq!(so.get(&ordinary.out_r1, lane), sd.get(&dual.out_r1, lane));
                assert_eq!(so.get(&ordinary.out_r2, lane), sd.get(&dual.out_r2, lane));
                for (qo, qd) in [(ordinary.typ_prev, dual.typ_prev),
                    (ordinary.spectator, dual.spectator), (ordinary.qs, dual.qs),
                    (ordinary.qr, dual.qr)] {
                    assert_eq!(so.wire(qo, lane), sd.wire(qd, lane));
                }
            }
        }
        println!(
            "{{\"kind\":\"skycof-t318-dual-loan\",\"n\":{n},\"cases\":{cases},\"ordinary_peak\":{},\"dual_peak\":{},\"state\":\"equal\",\"phase\":\"equal\",\"spectator\":\"restored\"}}",
            ordinary.peak, dual.peak
        );
    }
    println!(
        "{{\"kind\":\"skycof-t318-dual-loan-summary\",\"cases\":{total},\"supported\":{supported},\"result\":\"PASS\"}}"
    );
}

pub fn run() {
    let mode = std::env::var("SKYCOF_TICK_SELFTEST").unwrap_or_default();
    let t0 = std::time::Instant::now();
    if mode.trim() == "signext-host" {
        test_signext_isc_host();
        return;
    }
    if mode.trim() == "late-r0" {
        test_late_r0_target_lease();
        return;
    }
    if mode.trim() == "cofzero" {
        test_cofzero_isc_recycle();
        return;
    }
    if mode.trim() == "cofrotate" {
        test_cof_isc_zero_rotation();
        return;
    }
    if mode.trim() == "park-parity" {
        test_park_parity_loan();
        return;
    }
    if mode.trim() == "ghost-r0" {
        test_ghost_r0_host();
        return;
    }
    if mode.trim() == "cost" {
        cost_report();
        rev_cost_exact();
        return;
    }
    let kmax = env_usize("SKYCOF_ST_KMAX", 8);
    test_heo_identity();
    test_adders();
    test_ticks_exhaustive(kmax);
    test_walks_small(kmax);
    test_crosscheck_full();
    test_walks_full();
    cost_report();
    rev_cost_exact();
    println!(
        "{{\"kind\":\"skycof-selftest\",\"result\":\"PASS\",\"secs\":{:.1}}}",
        t0.elapsed().as_secs_f64()
    );
}
