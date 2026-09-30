//! Opt-in recursive carry schedules and exact constant-aware cost selection.
//! No arithmetic truncation: only the schedule of exact carry recomputation changes.
//! MIDQ_CELL_COST_SELECT=1 additionally compares against the validated route.
//! For C=2^z D and x=l+2^z h, x +/- g*C keeps l and updates the ENTIRE
//! n-z bit suffix h +/- g*D modulo 2^(n-z). No high word bits are dropped.
//! Both schedulers use A=cap-live scratch: the two-level plan's explicit
//! live-set bound, or the recursive children's A-1 plus one boundary.
//! Freeing that measured boundary before replay restores its full A budget.
use super::{clear, env_usize, majority, phase_majority, Addend, Circuit, QReg};
use std::sync::OnceLock;

const MAX_WIDTH: usize = 257;

#[derive(Clone, Copy)]
struct Plan {
    phase_cost: f64,
    split: usize,
}

// P(n,a) is the expected CCX count for a phase on the last carry of n
// columns with a clean workspace wires. XORing that carry costs P(n,a)+1.
// At a split k, the boundary stays live during both children, then is HMR'd
// and freed BEFORE its phase replay. Thus the children get a-1 wires, but
// replay gets a. Its independent measurement condition contributes a factor 1/2.
fn plans() -> &'static Vec<Vec<Plan>> {
    static PLANS: OnceLock<Vec<Vec<Plan>>> = OnceLock::new();
    PLANS.get_or_init(|| {
        let missing = Plan { phase_cost: f64::INFINITY, split: 0 };
        let mut table = vec![vec![missing; MAX_WIDTH + 1]; MAX_WIDTH];
        for a in 0..MAX_WIDTH {
            for n in 1..=MAX_WIDTH {
                if n - 1 <= a {
                    table[a][n] = Plan { phase_cost: (n - 1) as f64, split: 0 };
                } else if a != 0 {
                    for k in 1..n {
                        let cost = table[a - 1][k].phase_cost + 1.0
                            + table[a - 1][n - k].phase_cost
                            + 0.5 * table[a][k].phase_cost;
                        if cost < table[a][n].phase_cost {
                            table[a][n] = Plan { phase_cost: cost, split: k };
                        }
                    }
                }
            }
        }
        table
    })
}

pub(super) fn cost(n: usize, available: usize, overflow: bool) -> f64 {
    assert!((1..=MAX_WIDTH).contains(&n));
    plans()[available.min(MAX_WIDTH - 1)][n].phase_cost + usize::from(overflow) as f64
}

// Only the first column can omit a majority CCX: it has no incoming wire
// and a zero addend bit. All later columns have a wire, even if its value
// happens to be zero. Count every replay of that first column exactly.
fn zero_first_discount(n: usize, available: usize, overflow: bool) -> f64 {
    let p = plans()[available.min(MAX_WIDTH - 1)][n];
    assert!(p.phase_cost.is_finite());
    if p.split == 0 {
        usize::from(n > 1 || overflow) as f64
    } else {
        zero_first_discount(p.split, available - 1, true)
            + 0.5 * zero_first_discount(p.split, available, false)
    }
}

pub(super) fn exact_cost(n: usize, available: usize, overflow: bool, first: bool) -> f64 {
    let bound = cost(n, available, overflow);
    if first || !bound.is_finite() { bound }
    else { bound - zero_first_discount(n, available, overflow) }
}

pub(super) fn chunk_cost(chunks: &[usize], first: bool) -> f64 {
    let columns: usize = chunks.iter().sum();
    if columns == 0 { return 0.0; }
    let replay: usize = chunks.iter().take(chunks.len() - 1).map(|k| k - 1).sum();
    columns as f64 + 0.5 * replay as f64 - if first { 0.0 } else {
        1.0 + if chunks.len() > 1 && chunks[0] > 1 { 0.5 } else { 0.0 }
    }
}

pub(super) fn trailing_zeros(n: usize, constant: &[u8]) -> usize {
    (0..n).find(|&i| super::cbit(constant, i)).unwrap_or(n)
}

pub(super) fn shifted_constant(n: usize, constant: &[u8], shift: usize) -> Vec<u8> {
    assert!(shift <= n);
    let mut shifted = vec![0u8; (n - shift).div_ceil(8)];
    for i in 0..n - shift {
        if super::cbit(constant, shift + i) { shifted[i / 8] |= 1 << (i % 8); }
    }
    shifted
}

pub(super) fn dirty_cost(width: usize) -> f64 {
    // Forward: m-1 CCX. XOR-carries restoration: (m-2)+1+(m-2).
    // The zero/one-bit suffixes are respectively identity/CX, never 3m-4.
    if width < 2 { 0.0 } else { (3 * width - 4) as f64 }
}

/// Return true only after emitting a cheaper exact route (zero-Toffoli
/// identities may tie). With the selector disabled the 7a1784b path is intact.
pub(super) fn try_prefer(c: &mut Circuit, target: &[QReg], addend: Addend<'_>,
    out: Option<&QReg>, subtract: bool, original_chunks: Option<&[usize]>) -> bool {
    if std::env::var("MIDQ_CELL_COST_SELECT").ok().as_deref() != Some("1")
        || std::env::var("MIDQ_CELL_RECURSIVE_CARRY").ok().as_deref() != Some("1")
        || target.is_empty() || target.len() > MAX_WIDTH
    { return false; }
    let n = target.len();
    let (skip, shifted) = match &addend {
        Addend::Constant(_, constant) => {
            assert!(out.is_none(), "constant suffix trimming does not implement overflow");
            let skip = trailing_zeros(n, constant);
            (skip, shifted_constant(n, constant, skip))
        }
        Addend::Word(_) => (0, Vec::new()),
    };
    let a = &target[skip..];
    let trimmed = match &addend {
        Addend::Constant(ctrl, _) => Addend::Constant(ctrl, &shifted),
        Addend::Word(source) => Addend::Word(source),
    };
    // A multiple of 2^n is the identity. A lone top bit toggles by CX in
    // either direction; these cases need neither a cost table nor scratch.
    if a.is_empty() { return true; }
    if a.len() == 1 && out.is_none() {
        let (ctrl, bit) = trimmed.bit(0);
        if bit { c.cx(ctrl, &a[0]); }
        return true;
    }
    c.flush_pending_frees();
    let cap = env_usize("MIDQ_CELL_QCAP", 1009).min(1019);
    let available = cap.saturating_sub(c.b.active_qubits as usize);
    let old_cost = if let Some(chunks) = original_chunks {
        chunk_cost(chunks, addend.bit(0).1)
    } else if n >= 2 && cost(n, available, out.is_some()) < (2 * n - 2) as f64 {
        // This is the exact admission test in the validated recursive route.
        exact_cost(n, available, out.is_some(), addend.bit(0).1)
    } else {
        match &addend {
            // This public helper also serves the outer fold. Require both
            // known caller backends before pricing their fallback as 3m-4.
            Addend::Constant(_, _)
                if std::env::var("MIDQ_DIRTY_CONST").ok().as_deref() == Some("1")
                    && std::env::var("MIDQ_OUTER_DIRTY_CONST").ok().as_deref() == Some("1") => dirty_cost(a.len()),
            Addend::Word(_) => (2 * n - 2) as f64,
            _ => return false,
        }
    };
    let new_chunks = super::clean_chunk_plan::plan(a.len() - usize::from(out.is_none()), available);
    let chunk_t = new_chunks.as_deref().map_or(f64::INFINITY, |p| chunk_cost(p, trimmed.bit(0).1));
    let recursive_t = exact_cost(a.len(), available, out.is_some(), trimmed.bit(0).1);
    if chunk_t.min(recursive_t) >= old_cost { return false; }
    if subtract { for q in a { c.x(q); } }
    if recursive_t < chunk_t {
        add(c, a, trimmed, out, available);
    } else {
        super::emit_plan(c, a, trimmed, out, new_chunks.as_deref().unwrap());
    }
    if subtract { for q in a { c.x(q); } }
    true
}

pub(super) fn selftest_plan() {
    let table = plans();
    for a in 0..MAX_WIDTH {
        for n in 1..=MAX_WIDTH {
            let p = table[a][n];
            if a != 0 { assert!(p.phase_cost <= table[a - 1][n].phase_cost); }
            if !p.phase_cost.is_finite() { continue; }
            if p.split == 0 {
                assert!(n - 1 <= a);
                assert_eq!(p.phase_cost, (n - 1) as f64);
            } else {
                let k = p.split;
                assert!(a > 0 && k > 0 && k < n);
                assert_eq!(p.phase_cost, table[a - 1][k].phase_cost + 1.0
                    + table[a - 1][n - k].phase_cost + 0.5 * table[a][k].phase_cost);
            }
        }
    }
    // A constructive eight-block, 32-bit schedule gives this upper bound;
    // the dynamic program may improve it. The old 256-bit constant fallback
    // emits 3n-4 = 764 CCX, so at A=14 the expected saving is at least 277.
    assert!(cost(256, 14, false) <= 487.0);
}

#[derive(Clone, Copy)]
enum Action<'a> {
    Add(Option<&'a QReg>),
    Carry(&'a QReg),
    Phase,
}

// For Add, the inputs are original target bits. For Carry/Phase, they are
// the updated sum bits and the recurrence is MAJ(~sum, addend, incoming).
// Both recurrences produce the SAME outgoing carry on every bit assignment.
fn emit(c: &mut Circuit, a: &[QReg], addend: &Addend<'_>, start: usize,
    incoming: Option<&QReg>, action: Action<'_>, available: usize) {
    let n = a.len();
    let plan = plans()[available.min(MAX_WIDTH - 1)][n];
    assert!(plan.phase_cost.is_finite());
    if plan.split != 0 {
        let k = plan.split;
        let boundary = c.alloc_qreg("cell.recursive.boundary");
        let low = match action {
            Action::Add(_) => Action::Add(Some(&boundary)),
            _ => Action::Carry(&boundary),
        };
        emit(c, &a[..k], addend, start, incoming, low, available - 1);
        emit(c, &a[k..], addend, start + k, Some(&boundary), action, available - 1);
        let m = c.alloc_bit();
        c.hmr(&boundary, m);
        c.zero_and_free(boundary);
        c.with_condition(m, |c| {
            emit(c, &a[..k], addend, start, incoming, Action::Phase, available);
        });
        c.free_bit(m);
        return;
    }

    let adding = matches!(action, Action::Add(_));
    let mut chain: Vec<QReg> = Vec::new();
    for i in 0..n - 1 {
        let (ctrl, bit) = addend.bit(start + i);
        let previous = chain.last().or(incoming);
        let next = c.alloc_qreg("cell.recursive.carry");
        majority(c, &a[i], ctrl, bit, previous, &next, !adding);
        if adding {
            if let Some(previous) = previous { c.cx(previous, &a[i]); }
            if bit { c.cx(ctrl, &a[i]); }
        }
        chain.push(next);
    }
    let previous = chain.last().or(incoming);
    let (ctrl, bit) = addend.bit(start + n - 1);
    match action {
        Action::Add(out) => {
            if let Some(out) = out { majority(c, &a[n - 1], ctrl, bit, previous, out, false); }
            if let Some(previous) = previous { c.cx(previous, &a[n - 1]); }
            if bit { c.cx(ctrl, &a[n - 1]); }
        }
        Action::Carry(out) => majority(c, &a[n - 1], ctrl, bit, previous, out, true),
        Action::Phase => phase_majority(c, &a[n - 1], ctrl, bit, previous),
    }
    while let Some(q) = chain.pop() {
        let i = chain.len();
        let (ctrl, bit) = addend.bit(start + i);
        clear(c, &q, &a[i], ctrl, bit, chain.last().or(incoming));
        c.zero_and_free(q);
    }
}

pub(super) fn add(c: &mut Circuit, a: &[QReg], addend: Addend<'_>,
    out: Option<&QReg>, available: usize) {
    assert!(!a.is_empty() && a.len() <= MAX_WIDTH);
    let section = c.push_section("midq.cell.recursive");
    emit(c, a, &addend, 0, None, Action::Add(out), available);
    c.pop_section(&section);
}

pub(super) fn try_add(c: &mut Circuit, a: &[QReg], addend: Addend<'_>,
    out: Option<&QReg>, subtract: bool) -> bool {
    if std::env::var("MIDQ_CELL_RECURSIVE_CARRY").ok().as_deref() != Some("1")
        || a.len() < 2 || a.len() > MAX_WIDTH
    { return false; }
    c.flush_pending_frees();
    let cap = env_usize("MIDQ_CELL_QCAP", 1009).min(1019);
    let available = cap.saturating_sub(c.b.active_qubits as usize);
    // Conservative gate: even the 2n Cuccaro sum must be beaten. Constant
    // fallback in the intended MIDQ_DIRTY_CONST route costs about 3n instead.
    if cost(a.len(), available, out.is_some()) >= (2 * a.len() - 2) as f64 {
        return false;
    }
    if subtract { for q in a { c.x(q); } }
    add(c, a, addend, out, available);
    if subtract { for q in a { c.x(q); } }
    true
}
