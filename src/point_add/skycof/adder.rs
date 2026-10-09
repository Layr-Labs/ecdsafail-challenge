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
}

/// Forced plan (tests): `None` = cheapest feasible.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Force {
    Auto,
    Ladder,
    Chunks,
    Recursive,
    Vented,
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
