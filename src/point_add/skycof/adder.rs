//! Room-aware exact ripple adds for the SKY-COF tick (research code, inert in the default build).
//!
//! [`add`]: `target += g * (operand + cin)  (mod 2^n)`, `n = target.len()`, `operand.len()` in `{n-1, n}`
//! (a missing top operand bit is zero). `operand`, `g` and `cin` are restored; `g = None` means
//! unconditional. Scratch is bounded by `cap - active` at entry (`cap = None`: unbounded).
//!
//! Plans (all exact; the expected Toffoli below counts measurement-conditioned replays at 1/2):
//! * `Ladder`    `avail >= n-1`: one carry wire per bit, HMR-cleared.  `n-1` (+ `n` controlled sums).
//!   Unconditional ladders call `heo::gidney_add` itself (op-for-op the Skywalk rail add).
//! * `Chunks`    clean-prefix chunk schedule (retained chunk carries, replayed under the HMR outcome):
//!   `n-1 + (n-1-avail)/2` (+ `n`).
//! * `Recursive` binary split on a held boundary carry: `P(n, avail)` (+ `n`),
//!   `P(n,A) = min_k P(k,A-1) + 1 + P(n-k,A-1) + P(k,A)/2`.
//! * `Vented(f)` `f` carries on fresh wires, the rest in place (Cuccaro MAJ / un-MAJ):
//!   `2(n-1) - f` (+ `n`). Needs `f >= 1` when there is no carry-in wire.
//! The controlled sum is one CCX per bit in every plan; the carry chain is computed for the
//! UNcontrolled sum `target + operand + cin` and cleared with the post-sum identity
//! `MAJ(t, o, c) = MAJ(t' xor g, o, c)`, `t' = t xor g (o xor c)`.
use crate::circuit::QubitId as Q;
use crate::point_add::builder::Builder;
use std::sync::OnceLock;

#[derive(Clone, Debug, PartialEq)]
pub enum Plan {
    Ladder,
    Chunks(Vec<usize>),
    Recursive,
    Vented(usize),
    /// Unconditional adds only: [`Plan::Recursive`] whose adding leaves may also be `Vented` (fresh carries for
    /// the first `f` positions, the rest in place); the boundary phase passes are the `Recursive` ones.
    Rec2,
}

/// Forced plan (tests): `None` = cheapest feasible.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Force {
    Auto,
    Ladder,
    Chunks,
    Recursive,
    Vented,
    Rec2,
}

/// `Plan::Rec2` offered to the planner (`SKYCOF_REC2=0/1` research override; source default
/// [`super::pointadd::REC2`]).
pub fn rec2_on() -> bool {
    super::pointadd::knob("SKYCOF_REC2").map(|v| v != "0").unwrap_or(super::pointadd::REC2)
}

/// `Rec2` table entry: leaf ladder (0), vented leaf with `arg` fresh carries (1), split at `arg` (2), none (255).
#[derive(Clone, Copy)]
struct R2 {
    cost: f64,
    kind: u8,
    arg: usize,
}

fn rec2_table() -> &'static Vec<Vec<R2>> {
    static T: OnceLock<Vec<Vec<R2>>> = OnceLock::new();
    T.get_or_init(|| {
        let old = rec_table();
        let miss = R2 { cost: f64::INFINITY, kind: 255, arg: 0 };
        let mut t = vec![vec![miss; REC_MAX + 1]; REC_MAX];
        for a in 0..REC_MAX {
            for n in 1..=REC_MAX {
                let mut best = miss;
                if n - 1 <= a {
                    best = R2 { cost: (n - 1) as f64, kind: 0, arg: 0 };
                }
                let f = a.min(n - 1);
                let v = (2 * (n - 1) - f) as f64;
                if v < best.cost {
                    best = R2 { cost: v, kind: 1, arg: f };
                }
                if a > 0 && n - 1 > a {
                    for k in 1..n {
                        let q = old[a][k].cost;
                        if !q.is_finite() {
                            continue;
                        }
                        let c = t[a - 1][k].cost + 1.0 + t[a - 1][n - k].cost + 0.5 * q;
                        if c < best.cost {
                            best = R2 { cost: c, kind: 2, arg: k };
                        }
                    }
                }
                t[a][n] = best;
            }
        }
        t
    })
}

/// The `Rec2` plan at (`n`, `a`) can be emitted (a vented leaf without carry-in needs a fresh wire).
fn rec2_ok(n: usize, a: usize, has_in: bool) -> bool {
    let p = rec2_table()[a.min(REC_MAX - 1)][n];
    match p.kind {
        0 => true,
        1 => has_in || p.arg >= 1 || n == 1,
        2 => a >= 1 && rec2_ok(p.arg, a - 1, has_in) && rec2_ok(n - p.arg, a - 1, true),
        _ => false,
    }
}

const REC_MAX: usize = 300;

#[derive(Clone, Copy)]
struct RecPlan {
    cost: f64,
    split: usize,
}

fn rec_table() -> &'static Vec<Vec<RecPlan>> {
    static T: OnceLock<Vec<Vec<RecPlan>>> = OnceLock::new();
    T.get_or_init(|| {
        let miss = RecPlan { cost: f64::INFINITY, split: 0 };
        let mut t = vec![vec![miss; REC_MAX + 1]; REC_MAX];
        for a in 0..REC_MAX {
            for n in 1..=REC_MAX {
                if n - 1 <= a {
                    t[a][n] = RecPlan { cost: (n - 1) as f64, split: 0 };
                } else if a > 0 {
                    for k in 1..n {
                        let c = t[a - 1][k].cost + 1.0 + t[a - 1][n - k].cost + 0.5 * t[a][k].cost;
                        if c < t[a][n].cost {
                            t[a][n] = RecPlan { cost: c, split: k };
                        }
                    }
                }
            }
        }
        t
    })
}

/// Clean-prefix chunk schedule over `count` carries with `avail` wires (each non-final chunk keeps one).
pub fn chunk_plan(count: usize, avail: usize) -> Option<Vec<usize>> {
    if count == 0 {
        return Some(Vec::new());
    }
    if avail == 0 {
        return None;
    }
    let (mut rem, mut held, mut ch) = (count, 0usize, Vec::new());
    while rem > avail.saturating_sub(held) {
        let room = avail.saturating_sub(held);
        if room < 2 {
            return None;
        }
        let k = room.min(rem - room + 1);
        ch.push(k);
        rem -= k;
        held += 1;
    }
    if rem != 0 {
        ch.push(rem);
    }
    Some(ch)
}

/// Expected Toffoli of each feasible plan: `(plan, cost)` sorted cheapest first.
pub fn plans(n: usize, controlled: bool, has_cin: bool, op_full: bool, avail: usize) -> Vec<(Plan, f64)> {
    assert!(n >= 1);
    let count = n - 1;
    // controlled sums: one CCX per bit, except a top bit with neither operand nor carry
    let sums = if controlled { (n - usize::from(n == 1 && !op_full && !has_cin)) as f64 } else { 0.0 };
    let mut v = Vec::new();
    if avail >= count {
        v.push((Plan::Ladder, count as f64 + sums));
    }
    if count > avail {
        if let Some(ch) = chunk_plan(count, avail) {
            v.push((Plan::Chunks(ch), count as f64 + 0.5 * (count - avail) as f64 + sums));
        }
        if n <= REC_MAX {
            let p = rec_table()[avail.min(REC_MAX - 1)][n];
            if p.cost.is_finite() {
                v.push((Plan::Recursive, p.cost + sums));
            }
        }
    }
    let f = avail.min(count);
    if count == 0 || f >= 1 || has_cin {
        v.push((Plan::Vented(f), (count + count - f) as f64 + sums));
    }
    // last, so that a tie keeps the plans above (stable sort)
    if count > avail && !controlled && n <= REC_MAX && rec2_on() {
        let a = avail.min(REC_MAX - 1);
        let p = rec2_table()[a][n];
        if p.cost.is_finite() && rec2_ok(n, a, has_cin) {
            v.push((Plan::Rec2, p.cost));
        }
    }
    v.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap());
    v
}

/// Scratch available to the most recent add (reports only).
pub static LAST_AVAIL: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

pub fn avail_of(c: &Builder, cap: Option<usize>) -> usize {
    match cap {
        None => usize::MAX / 4,
        Some(k) => k.saturating_sub(c.active_qubits() as usize),
    }
}

/// `target += g * (operand + cin) (mod 2^n)`. Returns the plan used.
pub fn add(c: &mut Builder, g: Option<Q>, operand: &[Q], target: &[Q], cin: Option<Q>, cap: Option<usize>) -> Plan {
    add_forced(c, g, operand, target, cin, cap, Force::Auto)
}

/// `target -= g * (operand + cin) (mod 2^n)`, as NOT(NOT target + g (operand + cin)).
pub fn sub(c: &mut Builder, g: Option<Q>, operand: &[Q], target: &[Q], cin: Option<Q>, cap: Option<usize>) -> Plan {
    c.x_all(target);
    let p = add(c, g, operand, target, cin, cap);
    c.x_all(target);
    p
}

pub fn add_forced(c: &mut Builder, g: Option<Q>, operand: &[Q], target: &[Q], cin: Option<Q>, cap: Option<usize>,
                  force: Force) -> Plan {
    let n = target.len();
    assert!(n >= 1, "add: empty target");
    assert!(operand.len() == n || operand.len() + 1 == n, "add: operand {} vs target {n}", operand.len());
    let op_full = operand.len() == n;
    let avail = avail_of(c, cap);
    LAST_AVAIL.store(avail, std::sync::atomic::Ordering::Relaxed);
    let cands = plans(n, g.is_some(), cin.is_some(), op_full, avail);
    let pick = cands.into_iter().find(|(p, _)| match force {
        Force::Auto => true,
        Force::Ladder => *p == Plan::Ladder,
        Force::Chunks => matches!(p, Plan::Chunks(_)),
        Force::Recursive => *p == Plan::Recursive,
        Force::Vented => matches!(p, Plan::Vented(_)),
        Force::Rec2 => *p == Plan::Rec2,
    });
    let Some((plan, _)) = pick else {
        panic!("skycof add: no {force:?} plan for n={n} avail={avail} cin={} g={}", cin.is_some(), g.is_some());
    };
    let o: Vec<Option<Q>> = (0..n).map(|i| operand.get(i).copied()).collect();
    match &plan {
        Plan::Ladder if g.is_none() && op_full => super::super::heo::gidney_add(c, operand, target, cin),
        Plan::Ladder => vented(c, g, &o, target, cin, n - 1),
        Plan::Vented(f) => vented(c, g, &o, target, cin, *f),
        Plan::Chunks(ch) => chunks(c, g, &o, target, cin, ch),
        Plan::Recursive => recursive(c, g, &o, target, cin, Action::Add(None), avail),
        Plan::Rec2 => {
            assert!(g.is_none(), "Rec2: unconditional adds only");
            rec2(c, &o, target, cin, None, avail, 0, &[])
        }
    }
    plan
}

// ─── gate helpers (target t, operand o, carry p) ─────────────────────────────

/// `t ^= g` (controlled) or `t ^= 1`.
fn comp(c: &mut Builder, g: Option<Q>, t: Q) {
    match g {
        Some(g) => c.cx(g, t),
        None => c.x(t),
    }
}

/// `out ^= MAJ(t, o, p)`; with `complement`, `t` is post-sum and is read as `t xor g`.
fn majority(c: &mut Builder, g: Option<Q>, t: Q, o: Option<Q>, p: Option<Q>, out: Q, complement: bool) {
    let o = o.expect("majority needs an operand bit");
    if complement {
        comp(c, g, t);
    }
    if let Some(p) = p {
        c.cx(p, t);
        c.cx(p, o);
        c.ccx(t, o, out);
        c.cx(p, out);
        c.cx(p, o);
        c.cx(p, t);
    } else {
        c.ccx(t, o, out);
    }
    if complement {
        comp(c, g, t);
    }
}

/// Phase `(-1)^MAJ(t xor g, o, p)` (Clifford).
fn phase(c: &mut Builder, g: Option<Q>, t: Q, o: Option<Q>, p: Option<Q>) {
    let o = o.expect("phase needs an operand bit");
    comp(c, g, t);
    c.cz(t, o);
    if let Some(p) = p {
        c.cz(t, p);
        c.cz(o, p);
    }
    comp(c, g, t);
}

/// `t ^= g (o xor p)`.
fn sum(c: &mut Builder, g: Option<Q>, t: Q, o: Option<Q>, p: Option<Q>) {
    match (o, p) {
        (Some(o), p) => {
            if let Some(p) = p {
                c.cx(p, o);
            }
            match g {
                Some(g) => c.ccx(g, o, t),
                None => c.cx(o, t),
            }
            if let Some(p) = p {
                c.cx(p, o);
            }
        }
        (None, Some(p)) => match g {
            Some(g) => c.ccx(g, p, t),
            None => c.cx(p, t),
        },
        (None, None) => {}
    }
}

/// HMR-clear `out = MAJ(t xor g, o, p)` with the Clifford phase repair.
fn clear(c: &mut Builder, g: Option<Q>, out: Q, t: Q, o: Option<Q>, p: Option<Q>) {
    let m = c.alloc_bit();
    c.hmr(out, m);
    c.push_condition(m);
    phase(c, g, t, o, p);
    c.pop_condition();
    c.free_bit(m);
    c.release_clean(out);
}

// ─── plans ────────────────────────────────────────────────────────────────────

/// Mixed Gidney / Cuccaro ripple: the first `fresh` carries on fresh wires, the rest held in the
/// operand wire (in-place MAJ). Sums in the backward pass.
fn vented(c: &mut Builder, g: Option<Q>, a: &[Option<Q>], b: &[Q], cin: Option<Q>, fresh: usize) {
    let n = b.len();
    let mut carry: Vec<Option<Q>> = vec![None; n];
    carry[0] = cin;
    let mut kind_fresh = vec![false; n.saturating_sub(1)];
    for i in 0..n.saturating_sub(1) {
        let ai = a[i].expect("vented: operand bit below the top");
        let ci = carry[i];
        if i < fresh || ci.is_none() {
            assert!(i < fresh, "vented: no carry-in and no fresh wire");
            if let Some(ci) = ci {
                c.cx(ci, ai);
                c.cx(ci, b[i]);
            }
            let t = c.alloc_qubit();
            c.ccx(ai, b[i], t);
            if let Some(ci) = ci {
                c.cx(ci, t);
            }
            carry[i + 1] = Some(t);
            kind_fresh[i] = true;
        } else {
            let ci = ci.unwrap();
            c.cx(ai, b[i]);
            c.cx(ai, ci);
            c.ccx(ci, b[i], ai);
            carry[i + 1] = Some(ai);
        }
    }
    // top bit: b ^= g (a xor c)
    let top = n - 1;
    match (a[top], carry[top]) {
        (Some(at), Some(ct)) => {
            c.cx(ct, at);
            match g {
                Some(g) => c.ccx(g, at, b[top]),
                None => c.cx(at, b[top]),
            }
            c.cx(ct, at);
        }
        (Some(at), None) => match g {
            Some(g) => c.ccx(g, at, b[top]),
            None => c.cx(at, b[top]),
        },
        (None, Some(ct)) => match g {
            Some(g) => c.ccx(g, ct, b[top]),
            None => c.cx(ct, b[top]),
        },
        (None, None) => {}
    }
    for i in (0..n.saturating_sub(1)).rev() {
        let ai = a[i].unwrap();
        let ci = carry[i];
        if kind_fresh[i] {
            let t = carry[i + 1].unwrap();
            if let Some(ci) = ci {
                c.cx(ci, t);
            }
            let m = c.alloc_bit();
            c.hmr(t, m);
            c.cz_if(ai, b[i], m);
            c.free_bit(m);
            c.release_clean(t);
            match g {
                Some(g) => c.ccx(g, ai, b[i]),
                None => c.cx(ai, b[i]),
            }
            if let Some(ci) = ci {
                c.cx(ci, ai);
                c.cx(ci, b[i]);
            }
        } else {
            let ci = ci.unwrap();
            c.ccx(ci, b[i], ai);
            c.cx(ai, ci);
            c.cx(ai, b[i]);
            c.cx(ci, ai);
            match g {
                Some(g) => c.ccx(g, ai, b[i]),
                None => c.cx(ai, b[i]),
            }
            c.cx(ci, ai);
        }
    }
}

/// Clean-prefix chunks: inline sums, retained chunk carries replayed under their HMR outcome.
fn chunks(c: &mut Builder, g: Option<Q>, o: &[Option<Q>], t: &[Q], cin: Option<Q>, ch: &[usize]) {
    let n = t.len();
    let count = n - 1;
    let mut bounds: Vec<Q> = Vec::new();
    let mut ranges = Vec::new();
    let mut start = 0;
    for &size in ch {
        let end = start + size;
        let initial = bounds.last().copied().or(cin);
        let mut chain: Vec<Q> = Vec::new();
        for i in start..end {
            let next = c.alloc_qubit();
            let prev = chain.last().copied().or(initial);
            majority(c, g, t[i], o[i], prev, next, false);
            sum(c, g, t[i], o[i], prev);
            chain.push(next);
        }
        let keep = end < count;
        if !keep {
            sum(c, g, t[count], o[count], chain.last().copied().or(initial));
        }
        for j in (0..chain.len() - usize::from(keep)).rev() {
            let prev = if j == 0 { initial } else { Some(chain[j - 1]) };
            clear(c, g, chain[j], t[start + j], o[start + j], prev);
        }
        if keep {
            bounds.push(chain.pop().unwrap());
            ranges.push((start, end));
        }
        start = end;
    }
    assert_eq!(start, count);
    if ch.is_empty() {
        sum(c, g, t[0], o[0], cin);
    }
    while let Some(bd) = bounds.pop() {
        let (start, end) = ranges.pop().unwrap();
        let initial = bounds.last().copied().or(cin);
        let m = c.alloc_bit();
        c.hmr(bd, m);
        c.release_clean(bd);
        c.push_condition(m);
        let mut chain: Vec<Q> = Vec::new();
        for i in start..end - 1 {
            let next = c.alloc_qubit();
            majority(c, g, t[i], o[i], chain.last().copied().or(initial), next, true);
            chain.push(next);
        }
        phase(c, g, t[end - 1], o[end - 1], chain.last().copied().or(initial));
        for j in (0..chain.len()).rev() {
            let prev = if j == 0 { initial } else { Some(chain[j - 1]) };
            clear(c, g, chain[j], t[start + j], o[start + j], prev);
        }
        c.pop_condition();
        c.free_bit(m);
    }
}

#[derive(Clone, Copy)]
enum Action {
    Add(Option<Q>),
    Carry(Q),
    Phase,
}

fn recursive(c: &mut Builder, g: Option<Q>, o: &[Option<Q>], t: &[Q], incoming: Option<Q>, action: Action, avail: usize) {
    let n = t.len();
    let plan = rec_table()[avail.min(REC_MAX - 1)][n];
    assert!(plan.cost.is_finite(), "recursive add: no plan n={n} avail={avail}");
    if plan.split != 0 {
        let k = plan.split;
        let bd = c.alloc_qubit();
        let low = match action {
            Action::Add(_) => Action::Add(Some(bd)),
            _ => Action::Carry(bd),
        };
        recursive(c, g, &o[..k], &t[..k], incoming, low, avail - 1);
        recursive(c, g, &o[k..], &t[k..], Some(bd), action, avail - 1);
        let m = c.alloc_bit();
        c.hmr(bd, m);
        c.release_clean(bd);
        c.push_condition(m);
        recursive(c, g, &o[..k], &t[..k], incoming, Action::Phase, avail);
        c.pop_condition();
        c.free_bit(m);
        return;
    }
    let adding = matches!(action, Action::Add(_));
    let mut chain: Vec<Q> = Vec::new();
    for i in 0..n - 1 {
        let next = c.alloc_qubit();
        let prev = chain.last().copied().or(incoming);
        majority(c, g, t[i], o[i], prev, next, !adding);
        if adding {
            sum(c, g, t[i], o[i], prev);
        }
        chain.push(next);
    }
    let prev = chain.last().copied().or(incoming);
    match action {
        Action::Add(out) => {
            if let Some(out) = out {
                majority(c, g, t[n - 1], o[n - 1], prev, out, false);
            }
            sum(c, g, t[n - 1], o[n - 1], prev);
        }
        Action::Carry(out) => majority(c, g, t[n - 1], o[n - 1], prev, out, true),
        Action::Phase => phase(c, g, t[n - 1], o[n - 1], prev),
    }
    while let Some(q) = chain.pop() {
        let i = chain.len();
        clear(c, g, q, t[i], o[i], chain.last().copied().or(incoming));
    }
}

// ─── deferred boundary debts (research; FRAME walk only) ─────────────────────
//
// A forward walk add `t += o + cin` that must chunk (room < carries) keeps one boundary carry per
// chunk. The base clears each boundary by HMR plus a replay of its chunk under the outcome
// (expected half a chunk). Here the boundary is HMR-cleared with NO replay: the phase debt
// `(-1)^(m c_e)` is a function of the walk state right after the add (c_e = carry into position
// e of the uncontrolled sum = [o_L + cin > t'_L] on the post-add low bits), and that exact state
// reappears in the walk back, whose inverse add `t -= o + cin` (computed as NOT(NOT t + o + cin))
// materialises the same carry into position e on a wire in its first pass: `Z^m` there pays the
// debt at zero Toffoli. Debts are kept on a LIFO stack (forward pushes, backward pops).

use crate::circuit::BitId;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Mutex;

type DeferRec = (usize, usize, Vec<(usize, BitId)>);
static DEFER_STACK: Mutex<Vec<DeferRec>> = Mutex::new(Vec::new());
static DEFER_ACTIVE: AtomicBool = AtomicBool::new(false);

/// Turn deferral on/off for the adds between (set by the frame walk around each traversal).
pub fn defer_active(on: bool) {
    DEFER_ACTIVE.store(on, Ordering::Relaxed);
}

pub fn defer_stack_len() -> usize {
    DEFER_STACK.lock().unwrap().len()
}

/// Deferred-debt record of another walk op (the frame decoder's compare): push / pop by tag.
pub fn defer_push(tag: usize, n: usize, debts: Vec<(usize, BitId)>) {
    DEFER_STACK.lock().unwrap().push((tag, n, debts));
}

pub fn defer_pop(tag: usize, n: usize) -> Vec<(usize, BitId)> {
    let (t2, n2, d) = DEFER_STACK.lock().unwrap().pop().expect("defer_pop: empty defer stack");
    assert_eq!((t2, n2), (tag, n), "defer_pop: mismatched record");
    d
}

pub fn defer_enabled_pub() -> bool {
    defer_enabled()
}

fn defer_enabled() -> bool {
    DEFER_ACTIVE.load(Ordering::Relaxed) && super::pointadd::defer_on()
}

/// Smallest scratch for a deferred chunked add: two wires suffice (one held boundary + one carry; chunks of one
/// carry after the first). `SKYCOF_DEFER_MIN` research override; source default [`super::pointadd::DEFER_MIN`].
fn defer_min() -> usize {
    super::pointadd::knob("SKYCOF_DEFER_MIN").map(|v| v.parse().expect("SKYCOF_DEFER_MIN")).unwrap_or(super::pointadd::DEFER_MIN)
}

/// `target += operand + cin (mod 2^n)` (unconditional) with deferred chunk-boundary debts. `tag`
/// must match the paired [`sub_pay`].
pub fn add_defer(c: &mut Builder, operand: &[Q], target: &[Q], cin: Option<Q>, cap: Option<usize>, tag: usize) -> Plan {
    if !defer_enabled() {
        return add(c, None, operand, target, cin, cap);
    }
    let n = target.len();
    let count = n.saturating_sub(1);
    let avail = avail_of(c, cap);
    if count <= avail || count == 0 || avail < defer_min() {
        let p = add(c, None, operand, target, cin, cap);
        DEFER_STACK.lock().unwrap().push((tag, n, Vec::new()));
        return p;
    }
    assert!(operand.len() == n || operand.len() + 1 == n);
    let o: Vec<Option<Q>> = (0..n).map(|i| operand.get(i).copied()).collect();
    let debts = chunks_deferred(c, &o, target, cin, avail);
    DEFER_STACK.lock().unwrap().push((tag, n, debts));
    Plan::Chunks(Vec::new())
}

/// Exact inverse of [`add_defer`] (`target -= operand + cin`), paying its deferred debts.
pub fn sub_pay(c: &mut Builder, operand: &[Q], target: &[Q], cin: Option<Q>, cap: Option<usize>, tag: usize) -> Plan {
    if !defer_enabled() {
        return sub(c, None, operand, target, cin, cap);
    }
    let n = target.len();
    let (t2, n2, debts) = DEFER_STACK.lock().unwrap().pop().expect("sub_pay: empty defer stack");
    assert_eq!((t2, n2), (tag, n), "sub_pay: mismatched deferred add");
    if debts.is_empty() {
        return sub(c, None, operand, target, cin, cap);
    }
    let mut hk: Vec<Option<BitId>> = vec![None; n + 1];
    for &(e, m) in &debts {
        assert!(e >= 1 && e < n);
        hk[e] = Some(m);
    }
    c.x_all(target);
    let p = add_hooked(c, operand, target, cin, cap, &hk);
    c.x_all(target);
    for (_, m) in debts {
        c.free_bit(m);
    }
    p
}

fn hook(c: &mut Builder, hk: &[Option<BitId>], e: usize, w: Q) {
    if let Some(Some(m)) = hk.get(e) {
        c.z_if(w, *m);
    }
}

/// Chunked unconditional add, each boundary HMR-cleared as soon as the next chunk is done; returns
/// the (position, outcome) debts. Exactly `n - 1` Toffoli.
fn chunks_deferred(c: &mut Builder, o: &[Option<Q>], t: &[Q], cin: Option<Q>, avail: usize) -> Vec<(usize, BitId)> {
    let n = t.len();
    let count = n - 1;
    let mut debts = Vec::new();
    let mut prev_bd: Option<Q> = None;
    let mut start = 0;
    while start < count {
        let held = usize::from(prev_bd.is_some());
        let size = (avail - held).min(count - start);
        assert!(size >= 1);
        let end = start + size;
        let initial = prev_bd.or(cin);
        let mut chain: Vec<Q> = Vec::with_capacity(size);
        for i in start..end {
            let next = c.alloc_qubit();
            let prev = chain.last().copied().or(initial);
            majority(c, None, t[i], o[i], prev, next, false);
            sum(c, None, t[i], o[i], prev);
            chain.push(next);
        }
        let keep = end < count;
        if !keep {
            sum(c, None, t[count], o[count], chain.last().copied().or(initial));
        }
        for j in (0..chain.len() - usize::from(keep)).rev() {
            let prev = if j == 0 { initial } else { Some(chain[j - 1]) };
            clear(c, None, chain[j], t[start + j], o[start + j], prev);
        }
        if let Some(bd) = prev_bd {
            let m = c.alloc_bit();
            c.hmr(bd, m);
            c.release_clean(bd);
            debts.push((start, m));
        }
        prev_bd = if keep { Some(*chain.last().unwrap()) } else { None };
        start = end;
    }
    assert!(prev_bd.is_none());
    debts
}

/// `target += operand + cin` (unconditional) with `Z^m` applied to the carry into position `e`
/// for every `hk[e] = Some(m)`, at the moment that carry first exists on a wire.
fn add_hooked(c: &mut Builder, operand: &[Q], target: &[Q], cin: Option<Q>, cap: Option<usize>, hk: &[Option<BitId>]) -> Plan {
    let n = target.len();
    let op_full = operand.len() == n;
    let avail = avail_of(c, cap);
    let (plan, _) = plans(n, false, cin.is_some(), op_full, avail).into_iter().next().expect("add_hooked: no plan");
    let o: Vec<Option<Q>> = (0..n).map(|i| operand.get(i).copied()).collect();
    match &plan {
        Plan::Ladder => vented_h(c, &o, target, cin, n - 1, hk),
        Plan::Vented(f) => vented_h(c, &o, target, cin, *f, hk),
        Plan::Chunks(ch) => chunks_h(c, &o, target, cin, ch, hk),
        Plan::Recursive => recursive_h(c, &o, target, cin, Action::Add(None), avail, 0, hk),
        Plan::Rec2 => rec2(c, &o, target, cin, None, avail, 0, hk),
    }
    plan
}

/// [`Plan::Rec2`] (g = None): `t += o + incoming`, carry out of the top position into `out` when given, hooks at
/// `off + position` (`hk` empty: none).
#[allow(clippy::too_many_arguments)]
fn rec2(c: &mut Builder, o: &[Option<Q>], t: &[Q], incoming: Option<Q>, out: Option<Q>, avail: usize, off: usize,
        hk: &[Option<BitId>]) {
    let n = t.len();
    let p = rec2_table()[avail.min(REC_MAX - 1)][n];
    match p.kind {
        // n - 1 <= avail: the Recursive table's leaf (fresh carry ladder)
        0 => recursive_h(c, o, t, incoming, Action::Add(out), avail, off, hk),
        1 => vented_leaf(c, o, t, incoming, out, p.arg, off, hk),
        2 => {
            let k = p.arg;
            let bd = c.alloc_qubit();
            rec2(c, &o[..k], &t[..k], incoming, Some(bd), avail - 1, off, hk);
            rec2(c, &o[k..], &t[k..], Some(bd), out, avail - 1, off + k, hk);
            let m = c.alloc_bit();
            c.hmr(bd, m);
            c.release_clean(bd);
            c.push_condition(m);
            recursive(c, None, &o[..k], &t[..k], incoming, Action::Phase, avail);
            c.pop_condition();
            c.free_bit(m);
        }
        _ => panic!("rec2: no plan n={n} avail={avail}"),
    }
}

/// [`vented_h`] with an optional carry out of the top position into `out` and hooks at `off + position`.
#[allow(clippy::too_many_arguments)]
fn vented_leaf(c: &mut Builder, a: &[Option<Q>], b: &[Q], cin: Option<Q>, out: Option<Q>, fresh: usize, off: usize,
               hk: &[Option<BitId>]) {
    let n = b.len();
    let mut carry: Vec<Option<Q>> = vec![None; n];
    carry[0] = cin;
    let mut kind_fresh = vec![false; n.saturating_sub(1)];
    for i in 0..n.saturating_sub(1) {
        let ai = a[i].expect("vented_leaf: operand bit below the top");
        let ci = carry[i];
        if i < fresh || ci.is_none() {
            assert!(i < fresh, "vented_leaf: no carry-in and no fresh wire");
            if let Some(ci) = ci {
                c.cx(ci, ai);
                c.cx(ci, b[i]);
            }
            let t = c.alloc_qubit();
            c.ccx(ai, b[i], t);
            if let Some(ci) = ci {
                c.cx(ci, t);
            }
            hook(c, hk, off + i + 1, t);
            carry[i + 1] = Some(t);
            kind_fresh[i] = true;
        } else {
            let ci = ci.unwrap();
            c.cx(ai, b[i]);
            c.cx(ai, ci);
            c.ccx(ci, b[i], ai);
            hook(c, hk, off + i + 1, ai);
            carry[i + 1] = Some(ai);
        }
    }
    let top = n - 1;
    if let Some(out) = out {
        // out ^= MAJ(b_top, a_top, c_top); b_top, a_top and the carry wire are restored
        match (a[top], carry[top]) {
            (Some(_), p) => majority(c, None, b[top], a[top], p, out, false),
            (None, Some(ct)) => c.ccx(b[top], ct, out),
            (None, None) => {}
        }
        hook(c, hk, off + n, out);
    }
    match (a[top], carry[top]) {
        (Some(at), Some(ct)) => {
            c.cx(ct, at);
            c.cx(at, b[top]);
            c.cx(ct, at);
        }
        (Some(at), None) => c.cx(at, b[top]),
        (None, Some(ct)) => c.cx(ct, b[top]),
        (None, None) => {}
    }
    for i in (0..n.saturating_sub(1)).rev() {
        let ai = a[i].unwrap();
        let ci = carry[i];
        if kind_fresh[i] {
            let t = carry[i + 1].unwrap();
            if let Some(ci) = ci {
                c.cx(ci, t);
            }
            let m = c.alloc_bit();
            c.hmr(t, m);
            c.cz_if(ai, b[i], m);
            c.free_bit(m);
            c.release_clean(t);
            c.cx(ai, b[i]);
            if let Some(ci) = ci {
                c.cx(ci, ai);
                c.cx(ci, b[i]);
            }
        } else {
            let ci = ci.unwrap();
            c.ccx(ci, b[i], ai);
            c.cx(ai, ci);
            c.cx(ai, b[i]);
            c.cx(ci, ai);
            c.cx(ai, b[i]);
            c.cx(ci, ai);
        }
    }
}

/// [`vented`] (g = None) with hooks.
fn vented_h(c: &mut Builder, a: &[Option<Q>], b: &[Q], cin: Option<Q>, fresh: usize, hk: &[Option<BitId>]) {
    let n = b.len();
    let mut carry: Vec<Option<Q>> = vec![None; n];
    carry[0] = cin;
    let mut kind_fresh = vec![false; n.saturating_sub(1)];
    for i in 0..n.saturating_sub(1) {
        let ai = a[i].expect("vented: operand bit below the top");
        let ci = carry[i];
        if i < fresh || ci.is_none() {
            assert!(i < fresh, "vented: no carry-in and no fresh wire");
            if let Some(ci) = ci {
                c.cx(ci, ai);
                c.cx(ci, b[i]);
            }
            let t = c.alloc_qubit();
            c.ccx(ai, b[i], t);
            if let Some(ci) = ci {
                c.cx(ci, t);
            }
            hook(c, hk, i + 1, t);
            carry[i + 1] = Some(t);
            kind_fresh[i] = true;
        } else {
            let ci = ci.unwrap();
            c.cx(ai, b[i]);
            c.cx(ai, ci);
            c.ccx(ci, b[i], ai);
            hook(c, hk, i + 1, ai);
            carry[i + 1] = Some(ai);
        }
    }
    let top = n - 1;
    match (a[top], carry[top]) {
        (Some(at), Some(ct)) => {
            c.cx(ct, at);
            c.cx(at, b[top]);
            c.cx(ct, at);
        }
        (Some(at), None) => c.cx(at, b[top]),
        (None, Some(ct)) => c.cx(ct, b[top]),
        (None, None) => {}
    }
    for i in (0..n.saturating_sub(1)).rev() {
        let ai = a[i].unwrap();
        let ci = carry[i];
        if kind_fresh[i] {
            let t = carry[i + 1].unwrap();
            if let Some(ci) = ci {
                c.cx(ci, t);
            }
            let m = c.alloc_bit();
            c.hmr(t, m);
            c.cz_if(ai, b[i], m);
            c.free_bit(m);
            c.release_clean(t);
            c.cx(ai, b[i]);
            if let Some(ci) = ci {
                c.cx(ci, ai);
                c.cx(ci, b[i]);
            }
        } else {
            let ci = ci.unwrap();
            c.ccx(ci, b[i], ai);
            c.cx(ai, ci);
            c.cx(ai, b[i]);
            c.cx(ci, ai);
            c.cx(ai, b[i]);
            c.cx(ci, ai);
        }
    }
}

/// [`chunks`] (g = None) with hooks in the first pass.
fn chunks_h(c: &mut Builder, o: &[Option<Q>], t: &[Q], cin: Option<Q>, ch: &[usize], hk: &[Option<BitId>]) {
    let n = t.len();
    let count = n - 1;
    let g = None;
    let mut bounds: Vec<Q> = Vec::new();
    let mut ranges = Vec::new();
    let mut start = 0;
    for &size in ch {
        let end = start + size;
        let initial = bounds.last().copied().or(cin);
        let mut chain: Vec<Q> = Vec::new();
        for i in start..end {
            let next = c.alloc_qubit();
            let prev = chain.last().copied().or(initial);
            majority(c, g, t[i], o[i], prev, next, false);
            hook(c, hk, i + 1, next);
            sum(c, g, t[i], o[i], prev);
            chain.push(next);
        }
        let keep = end < count;
        if !keep {
            sum(c, g, t[count], o[count], chain.last().copied().or(initial));
        }
        for j in (0..chain.len() - usize::from(keep)).rev() {
            let prev = if j == 0 { initial } else { Some(chain[j - 1]) };
            clear(c, g, chain[j], t[start + j], o[start + j], prev);
        }
        if keep {
            bounds.push(chain.pop().unwrap());
            ranges.push((start, end));
        }
        start = end;
    }
    assert_eq!(start, count);
    if ch.is_empty() {
        sum(c, g, t[0], o[0], cin);
    }
    while let Some(bd) = bounds.pop() {
        let (start, end) = ranges.pop().unwrap();
        let initial = bounds.last().copied().or(cin);
        let m = c.alloc_bit();
        c.hmr(bd, m);
        c.release_clean(bd);
        c.push_condition(m);
        let mut chain: Vec<Q> = Vec::new();
        for i in start..end - 1 {
            let next = c.alloc_qubit();
            majority(c, g, t[i], o[i], chain.last().copied().or(initial), next, true);
            chain.push(next);
        }
        phase(c, g, t[end - 1], o[end - 1], chain.last().copied().or(initial));
        for j in (0..chain.len()).rev() {
            let prev = if j == 0 { initial } else { Some(chain[j - 1]) };
            clear(c, g, chain[j], t[start + j], o[start + j], prev);
        }
        c.pop_condition();
        c.free_bit(m);
    }
}

/// [`recursive`] (g = None) with hooks on the adding pass; `off` = position of `t[0]`.
#[allow(clippy::too_many_arguments)]
fn recursive_h(c: &mut Builder, o: &[Option<Q>], t: &[Q], incoming: Option<Q>, action: Action, avail: usize, off: usize,
               hk: &[Option<BitId>]) {
    let g = None;
    let n = t.len();
    if !matches!(action, Action::Add(_)) {
        return recursive(c, g, o, t, incoming, action, avail);
    }
    let plan = rec_table()[avail.min(REC_MAX - 1)][n];
    assert!(plan.cost.is_finite(), "recursive add: no plan n={n} avail={avail}");
    if plan.split != 0 {
        let k = plan.split;
        let bd = c.alloc_qubit();
        recursive_h(c, &o[..k], &t[..k], incoming, Action::Add(Some(bd)), avail - 1, off, hk);
        recursive_h(c, &o[k..], &t[k..], Some(bd), action, avail - 1, off + k, hk);
        let m = c.alloc_bit();
        c.hmr(bd, m);
        c.release_clean(bd);
        c.push_condition(m);
        recursive(c, g, &o[..k], &t[..k], incoming, Action::Phase, avail);
        c.pop_condition();
        c.free_bit(m);
        return;
    }
    let mut chain: Vec<Q> = Vec::new();
    for i in 0..n - 1 {
        let next = c.alloc_qubit();
        let prev = chain.last().copied().or(incoming);
        majority(c, g, t[i], o[i], prev, next, false);
        hook(c, hk, off + i + 1, next);
        sum(c, g, t[i], o[i], prev);
        chain.push(next);
    }
    let prev = chain.last().copied().or(incoming);
    if let Action::Add(out) = action {
        if let Some(out) = out {
            majority(c, g, t[n - 1], o[n - 1], prev, out, false);
            hook(c, hk, off + n, out);
        }
        sum(c, g, t[n - 1], o[n - 1], prev);
    }
    while let Some(q) = chain.pop() {
        let i = chain.len();
        clear(c, g, q, t[i], o[i], chain.last().copied().or(incoming));
    }
}
