//! Controlled addition with bounded carries and exact post-sum cleanup.
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};

fn majority(c: &mut Circuit, a: &QReg, b: &QReg, previous: Option<&QReg>,
    out: &QReg, complement: Option<&QReg>) {
    if let Some(g) = complement { c.cx(g, a); }
    if let Some(p) = previous {
        c.cx(p, a); c.cx(p, b);
        c.ccx(a, b, out);
        c.cx(p, out);
        c.cx(p, b); c.cx(p, a);
    } else { c.ccx(a, b, out); }
    if let Some(g) = complement { c.cx(g, a); }
}

fn phase(c: &mut Circuit, a: &QReg, b: &QReg, previous: Option<&QReg>, g: &QReg) {
    // If s=a XOR g*(b XOR carry), MAJ(a,b,carry)=MAJ(s XOR g,b,carry).
    c.cx(g, a);
    c.cz(a, b);
    if let Some(p) = previous { c.cz(a, p); c.cz(b, p); }
    c.cx(g, a);
}

fn clear(c: &mut Circuit, out: &QReg, a: &QReg, b: &QReg, previous: Option<&QReg>, g: &QReg) {
    let m = c.alloc_bit();
    c.hmr(out, m);
    c.with_condition(m, |c| phase(c, a, b, previous, g));
    c.free_bit(m);
}

fn sum(c: &mut Circuit, a: &QReg, b: &QReg, previous: Option<&QReg>, g: &QReg) {
    if let Some(p) = previous { c.cx(p, b); }
    c.ccx(g, b, a);
    if let Some(p) = previous { c.cx(p, b); }
}

pub(crate) fn try_apply(c: &mut Circuit, g: &QReg, a: &[&QReg], b: &[&QReg], budget: usize) -> bool {
    if std::env::var("MIDQ_CHUNKED_CONTROLLED_ADD").ok().as_deref() != Some("1")
        || a.len() < 2 { return false; }
    assert_eq!(a.len(), b.len());
    let mut ids = std::collections::HashSet::new();
    if a.iter().chain(b).any(|q| q.id() == g.id() || !ids.insert(q.id())) { return false; }
    c.flush_pending_frees();
    let cap = std::env::var("MIDQ_CONTROLLED_ADD_QCAP").ok()
        .and_then(|v| v.parse::<usize>().ok()).unwrap_or(1009);
    let available = budget.min(cap.saturating_sub(c.b.active_qubits as usize));
    let count = a.len() - 1;
    // The old fully vented network already attains the same Toffoli count.
    if available >= count { return false; }
    if let Some(chunks) = super::clean_chunk_plan::plan(count, available) {
        emit(c, g, a, b, &chunks);
        return true;
    }
    if std::env::var("MIDQ_CONTROLLED_ADD_RECURSIVE").ok().as_deref() != Some("1")
        || !prefer_recursive(a.len(), available, budget) { return false; }
    let section = c.push_section("chunked.controlled_add.recursive");
    recursive_emit(c, g, a, b, None, RecursiveAction::Add(None), available);
    c.pop_section(&section);
    true
}

const RECURSIVE_MAX_WIDTH: usize = 257;

#[derive(Clone, Copy)]
struct RecursivePlan {
    phase_cost: f64,
    split: usize,
}

// P(n,A) prices a phase on the outgoing carry, reconstructed from post-sum
// words with A clean wires. Carry XOR costs P+1; controlled addition costs
// P+n (one extra CCX per sum bit). At split k, the boundary takes one wire
// during both children, but is measured/freed BEFORE its conditional replay.
// P(n,A) = min_k P(k,A-1)+1+P(n-k,A-1)+P(k,A)/2.
// A leaf uses n-1 wires and costs n-1. All weights are exact dyadic values;
// the halves refer to independent HMR outcomes, never quantum control values.
fn recursive_plans() -> &'static Vec<Vec<RecursivePlan>> {
    static PLANS: std::sync::OnceLock<Vec<Vec<RecursivePlan>>> = std::sync::OnceLock::new();
    PLANS.get_or_init(|| {
        let missing = RecursivePlan { phase_cost: f64::INFINITY, split: 0 };
        let mut table = vec![vec![missing; RECURSIVE_MAX_WIDTH + 1]; RECURSIVE_MAX_WIDTH];
        for available in 0..RECURSIVE_MAX_WIDTH {
            for n in 1..=RECURSIVE_MAX_WIDTH {
                if n - 1 <= available {
                    table[available][n] = RecursivePlan { phase_cost: (n - 1) as f64, split: 0 };
                } else if available > 0 {
                    for k in 1..n {
                        let cost = table[available - 1][k].phase_cost + 1.0
                            + table[available - 1][n - k].phase_cost
                            + 0.5 * table[available][k].phase_cost;
                        if cost < table[available][n].phase_cost {
                            table[available][n] = RecursivePlan { phase_cost: cost, split: k };
                        }
                    }
                }
            }
        }
        table
    })
}

fn recursive_cost(n: usize, available: usize) -> f64 {
    if !(1..=RECURSIVE_MAX_WIDTH).contains(&n) { return f64::INFINITY; }
    n as f64 + recursive_plans()[available.min(RECURSIVE_MAX_WIDTH - 1)][n].phase_cost
}

fn fallback_cost(n: usize, budget: usize) -> f64 {
    match n {
        0 => 0.0,
        1 => 1.0,
        _ => (3 * n - 2 - budget.min(n - 1)) as f64,
    }
}

fn prefer_recursive(n: usize, available: usize, budget: usize) -> bool {
    // Price the actual caller fallback, not a hypothetical cap-clamped vent
    // budget: the caller retains its original budget when try_apply declines.
    (2..=RECURSIVE_MAX_WIDTH).contains(&n)
        && recursive_cost(n, available) < fallback_cost(n, budget)
}

#[derive(Clone, Copy)]
enum RecursiveAction<'a> {
    Add(Option<&'a QReg>),
    Carry(&'a QReg),
    Phase,
}

fn recursive_emit(c: &mut Circuit, g: &QReg, a: &[&QReg], b: &[&QReg],
    incoming: Option<&QReg>, action: RecursiveAction<'_>, available: usize) {
    let n = a.len();
    assert!((1..=RECURSIVE_MAX_WIDTH).contains(&n));
    assert_eq!(n, b.len());
    let plan = recursive_plans()[available.min(RECURSIVE_MAX_WIDTH - 1)][n];
    assert!(plan.phase_cost.is_finite());
    if plan.split != 0 {
        let k = plan.split;
        let boundary = c.alloc_qreg("cadd.recursive.boundary");
        let low = match action {
            RecursiveAction::Add(_) => RecursiveAction::Add(Some(&boundary)),
            _ => RecursiveAction::Carry(&boundary),
        };
        recursive_emit(c, g, &a[..k], &b[..k], incoming, low, available - 1);
        recursive_emit(c, g, &a[k..], &b[k..], Some(&boundary), action, available - 1);
        let m = c.alloc_bit();
        c.hmr(&boundary, m);
        c.zero_and_free(boundary);
        c.with_condition(m, |c| {
            recursive_emit(c, g, &a[..k], &b[..k], incoming, RecursiveAction::Phase, available);
        });
        c.free_bit(m);
        return;
    }

    // For g=0, s=a; for g=1, s=a XOR b XOR incoming. In either case
    // MAJ(a,b,incoming) = MAJ(s XOR g,b,incoming). Carry/Phase never write
    // sum bits. Their own HMR cleanup uses the same post-sum identity.
    let adding = matches!(action, RecursiveAction::Add(_));
    let mut chain: Vec<QReg> = Vec::new();
    for i in 0..n - 1 {
        let next = c.alloc_qreg("cadd.recursive.carry");
        let previous = chain.last().or(incoming);
        majority(c, a[i], b[i], previous, &next, (!adding).then_some(g));
        if adding { sum(c, a[i], b[i], previous, g); }
        chain.push(next);
    }
    let previous = chain.last().or(incoming);
    match action {
        RecursiveAction::Add(out) => {
            if let Some(out) = out { majority(c, a[n - 1], b[n - 1], previous, out, None); }
            sum(c, a[n - 1], b[n - 1], previous, g);
        }
        RecursiveAction::Carry(out) => majority(c, a[n - 1], b[n - 1], previous, out, Some(g)),
        RecursiveAction::Phase => phase(c, a[n - 1], b[n - 1], previous, g),
    }
    while let Some(q) = chain.pop() {
        let i = chain.len();
        clear(c, &q, a[i], b[i], chain.last().or(incoming), g);
        c.zero_and_free(q);
    }
}

fn emit(c: &mut Circuit, g: &QReg, a: &[&QReg], b: &[&QReg], chunks: &[usize]) {
    let section = c.push_section("chunked.controlled_add");
    let count = a.len() - 1;
    let mut boundaries: Vec<QReg> = Vec::new();
    let mut ranges = Vec::new();
    let mut start = 0;
    for &size in chunks {
        let end = start + size;
        let initial = boundaries.last();
        let mut chain: Vec<QReg> = Vec::new();
        for i in start..end {
            let next = c.alloc_qreg("cadd.carry");
            let previous = chain.last().or(initial);
            majority(c, a[i], b[i], previous, &next, None);
            sum(c, a[i], b[i], previous, g);
            chain.push(next);
        }
        let keep = end < count;
        if !keep { sum(c, a[count], b[count], chain.last(), g); }
        for j in (0..chain.len() - usize::from(keep)).rev() {
            let previous = if j == 0 { initial } else { Some(&chain[j - 1]) };
            clear(c, &chain[j], a[start + j], b[start + j], previous, g);
        }
        let retained = keep.then(|| chain.pop().unwrap());
        for bit in chain { c.zero_and_free(bit); }
        if let Some(bit) = retained { boundaries.push(bit); ranges.push((start, end)); }
        start = end;
    }
    assert_eq!(start, count);
    while let Some(boundary) = boundaries.pop() {
        let (start, end) = ranges.pop().unwrap();
        let initial = boundaries.last();
        let m = c.alloc_bit();
        c.hmr(&boundary, m);
        c.zero_and_free(boundary);
        c.with_condition(m, |c| {
            let mut chain: Vec<QReg> = Vec::new();
            for i in start..end - 1 {
                let next = c.alloc_qreg("cadd.phase.carry");
                majority(c, a[i], b[i], chain.last().or(initial), &next, Some(g));
                chain.push(next);
            }
            phase(c, a[end - 1], b[end - 1], chain.last().or(initial), g);
            for j in (0..chain.len()).rev() {
                let previous = if j == 0 { initial } else { Some(&chain[j - 1]) };
                clear(c, &chain[j], a[start + j], b[start + j], previous, g);
            }
            for bit in chain { c.zero_and_free(bit); }
        });
        c.free_bit(m);
    }
    c.pop_section(&section);
}

#[path = "chunked_controlled_add_selftest.rs"]
mod tests;
#[path = "chunked_controlled_add_recursive_selftest.rs"]
mod recursive_tests;

pub(crate) fn selftest() {
    tests::run();
    recursive_tests::run();
}
