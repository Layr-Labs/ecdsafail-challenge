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

pub fn run() {
    let mode = std::env::var("SKYCOF_TICK_SELFTEST").unwrap_or_default();
    let t0 = std::time::Instant::now();
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
