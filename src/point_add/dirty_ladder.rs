//! Recognize two complete trips around a Barenco dirty MCX chain. Reuse exact
//! proven-zero existing wires and erase the intermediate conjunctions in X.
use crate::circuit::{analyze_ops, BitId, Op, OperationType as K, QubitId, QubitOrBit, NO_BIT};
#[path = "ladder_loans.rs"]
mod ladder_loans;
#[path = "plane_cache/names.rs"]
mod names;
use ladder_loans::{Forest, Loan};
const MAX_D: usize = 64;
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
struct Edge {
    a: u16,
    b: u16,
    t: u16,
}
fn edge(o: &Op) -> Option<Edge> {
    if o.kind != K::CCX || o.c_condition != NO_BIT {
        return None;
    }
    let (a, b) = (o.q_control1.0 as u16, o.q_control2.0 as u16);
    Some(Edge {
        a: a.min(b),
        b: a.max(b),
        t: o.q_target.0 as u16,
    })
}
#[derive(Debug)]
struct Ladder {
    control: Vec<u16>,
    dirty: Vec<u16>,
    target: u16,
}
fn recognize(ops: &[Op]) -> Option<Ladder> {
    let first = edge(ops.first()?)?;
    let next = edge(ops.get(1)?)?;
    if !(first.t == next.a || first.t == next.b || next.t == first.a || next.t == first.b) {
        return None;
    }
    for d in 1..=MAX_D.min(ops.len() / 4) {
        // A spectator or measurement between the copies is a hard barrier.
        let mid = 2 * d;
        let at = edge(&ops[mid])?;
        if edge(&ops[mid - 1]).is_none() {
            return None;
        }
        if at != first {
            continue;
        }
        let mut half = Vec::with_capacity(mid);
        let mut ok = true;
        for j in 0..mid {
            let Some(x) = edge(&ops[j]) else {
                ok = false;
                break;
            };
            if edge(&ops[mid + j]) != Some(x) {
                ok = false;
                break;
            }
            half.push(x);
        }
        if !ok {
            continue;
        }
        let mut wires = Vec::with_capacity(d + 1);
        for e in &half {
            if !wires.contains(e) {
                wires.push(*e);
            }
        }
        if wires.len() != d + 1 {
            continue;
        }
        // Edges form a directed path. Every edge target, external control and
        // the ultimate target must be a different quantum wire.
        let base = wires
            .iter()
            .find(|base| !wires.iter().any(|e| e.t == base.a || e.t == base.b))
            .copied();
        let Some(base) = base else { continue };
        let mut chain = vec![base];
        let mut control = vec![base.a, base.b];
        let mut used = vec![base.a, base.b, base.t];
        if base.a == base.b || base.a == base.t || base.b == base.t {
            continue;
        }
        for _ in 0..d {
            let prev = chain.last().unwrap().t;
            let Some(e) = wires.iter().find(|e| e.a == prev || e.b == prev).copied() else {
                break;
            };
            let c = if e.a == prev { e.b } else { e.a };
            if used.contains(&c) || used.contains(&e.t) || c == e.t {
                break;
            }
            used.extend([c, e.t]);
            control.push(c);
            chain.push(e);
        }
        if chain.len() != d + 1 {
            continue;
        }
        let last = *chain.last().unwrap();
        let phase = half.iter().position(|e| *e == last).unwrap();
        if !(0..mid).all(|j| half[(phase + j) % mid] == chain[d.abs_diff(j)]) {
            continue;
        }
        return Some(Ladder {
            control,
            dirty: chain[..d].iter().map(|e| e.t).collect(),
            target: last.t,
        });
    }
    None
}
fn ccx(a: u16, b: u16, t: u16) -> Op {
    Op {
        kind: K::CCX,
        q_control1: QubitId(a as u64),
        q_control2: QubitId(b as u64),
        q_target: QubitId(t as u64),
        ..Op::empty()
    }
}
fn emit_dirty(controls: &[u16], target: u16, dirty: &[u16], mut emit: impl FnMut(Op)) {
    let n = controls.len();
    if n == 2 {
        emit(ccx(controls[0], controls[1], target));
        return;
    }
    let d = n - 2;
    for _ in 0..2 {
        emit(ccx(controls[n - 1], dirty[d - 1], target));
        for j in (1..d).rev() {
            emit(ccx(controls[j + 1], dirty[j - 1], dirty[j]));
        }
        emit(ccx(controls[0], controls[1], dirty[0]));
        for j in 1..d {
            emit(ccx(controls[j + 1], dirty[j - 1], dirty[j]));
        }
    }
}
fn simple(controls: &[u16], t: u16) -> Op {
    match controls {
        [] => Op {
            kind: K::X,
            q_target: QubitId(t as u64),
            ..Op::empty()
        },
        &[a] => Op {
            kind: K::CX,
            q_control1: QubitId(a as u64),
            q_target: QubitId(t as u64),
            ..Op::empty()
        },
        &[a, b] => ccx(a, b, t),
        _ => unreachable!(),
    }
}
fn simplify(l: &Ladder, n: &names::Names) -> Option<Vec<u16>> {
    let mut keep = Vec::new();
    for &q in &l.control {
        let f = n.wires[q as usize];
        if f.zero() {
            return None;
        }
        if f.form.1 == 0 {
            continue;
        }
        if let Some(&p) = keep.iter().find(|&&p| n.wires[p as usize].form == f.form) {
            if n.wires[p as usize].sign != f.sign {
                return None;
            }
        } else {
            keep.push(q);
        }
    }
    Some(keep)
}
fn park(w: &Loan, put: &mut impl FnMut(Op)) {
    let target = QubitId(w.wire as u64);
    if w.sign {
        put(Op {
            kind: K::X,
            q_target: target,
            ..Op::empty()
        });
    }
    for &q in &w.terms {
        put(Op {
            kind: K::CX,
            q_control1: QubitId(q as u64),
            q_target: target,
            ..Op::empty()
        });
    }
}
fn emit(l: &Ladder, ctrl: &[u16], clean: &[Loan], mask: BitId, mut put: impl FnMut(Op)) {
    if ctrl.len() <= 2 {
        put(simple(ctrl, l.target));
        return;
    }
    for w in clean {
        park(w, &mut put);
    }
    let mut prev = ctrl[0];
    for (j, w) in clean.iter().enumerate() {
        put(ccx(prev, ctrl[j + 1], w.wire));
        prev = w.wire;
    }
    let mut rest = vec![prev];
    rest.extend_from_slice(&ctrl[clean.len() + 1..]);
    let donors = l
        .dirty
        .iter()
        .copied()
        .filter(|q| !clean.iter().any(|w| w.wire == *q))
        .collect::<Vec<_>>();
    emit_dirty(&rest, l.target, &donors, &mut put);
    for j in (0..clean.len()).rev() {
        let q = |v: u16| QubitId(v as u64);
        let a = if j == 0 { ctrl[0] } else { clean[j - 1].wire };
        put(Op {
            kind: K::Hmr,
            q_target: q(clean[j].wire),
            c_target: mask,
            ..Op::empty()
        });
        put(Op {
            kind: K::CZ,
            q_control1: q(a),
            q_target: q(ctrl[j + 1]),
            c_condition: mask,
            ..Op::empty()
        });
    }
    if !clean.is_empty() {
        put(Op {
            kind: K::BitStore0,
            c_target: mask,
            ..Op::empty()
        });
    }
    for w in clean.iter().rev() {
        park(w, &mut put);
    }
}
#[derive(Debug, Default)]
pub(super) struct Stats {
    pub hits: u64,
    pub eligible: u64,
    pub saved: u64,
    pub added_ops: i64,
    pub measurements: u64,
    pub gap_slots: usize,
    pub max_prefix_growth: usize,
    pub limited: u64,
    pub zero_or_complement: u64,
    pub short_controls: u64,
    pub affine_loans: u64,
    pub parking_cliffords: u64,
    pub by_d: std::collections::BTreeMap<usize, (u64, u64, u64)>,
    pub examples: Vec<(usize, Vec<u16>, u16, Vec<u16>, Vec<(u16, Vec<u16>, bool)>)>,
}
pub(super) fn apply(ops: &mut Vec<Op>, reserve: usize) -> Stats {
    let (nq, nb, _, regs) = analyze_ops(ops.iter());
    assert!(nq < 65535);
    let n = ops.len();
    let mut input = vec![false; nq as usize];
    for r in regs.iter().flatten() {
        if let QubitOrBit::Qubit(q) = r {
            input[q.0 as usize] = true;
        }
    }
    let mut facts = names::Names::new(&input);
    let mut forest = Forest::new(nq as usize);
    let mut result = Stats::default();
    // Reuse available storage and refuse any edit whose replacement cannot fit
    // before the current source cursor. Keep space for the original trailer.
    let gap = (ops.capacity() - n)
        .saturating_sub(reserve)
        .min(n / 16 + 128)
        .min(1 << 23);
    result.gap_slots = gap;
    if gap > 0 {
        ops.resize(n + gap, Op::empty());
        ops.copy_within(..n, gap);
    }
    let (mut read, mut wrote, mut depth) = (0usize, 0usize, 0usize);
    while read < n {
        let x = ops[gap + read];
        let mut used = 1;
        let mut replacement = None;
        if depth == 0 && x.kind == K::CCX && x.c_condition == NO_BIT {
            if let Some(l) = recognize(&ops[gap + read..gap + n]) {
                let d = l.dirty.len();
                used = 4 * d;
                result.hits += 1;
                result.by_d.entry(d).or_default().0 += 1;
                let effective = simplify(&l, &facts);
                let mut clean = Vec::new();
                if let Some(c) = &effective {
                    if c.len() > 2 {
                        clean = forest.choices(&facts, &l, c.len() - 2);
                    }
                }
                if effective
                    .as_ref()
                    .map_or(true, |x| x.len() != l.control.len())
                    || !clean.is_empty()
                {
                    let mut v = Vec::with_capacity(
                        used + clean.iter().map(Loan::cost).sum::<usize>() * 2 + 1,
                    );
                    if let Some(c) = &effective {
                        emit(&l, c, &clean, BitId(nb), |o| v.push(o));
                    }
                    let t = v.iter().filter(|o| o.kind == K::CCX).count();
                    assert!(t < used);
                    if v.len() <= read + used + gap - wrote {
                        result.eligible += 1;
                        result.saved += (used - t) as u64;
                        result.added_ops += v.len() as i64 - used as i64;
                        result.measurements += clean.len() as u64;
                        result.affine_loans += clean.iter().filter(|z| z.cost() > 0).count() as u64;
                        result.parking_cliffords +=
                            2 * clean.iter().map(Loan::cost).sum::<usize>() as u64;
                        if effective.is_none() {
                            result.zero_or_complement += 1;
                        } else if effective.as_ref().unwrap().len() != l.control.len() {
                            result.short_controls += 1;
                        }
                        let e = result.by_d.get_mut(&d).unwrap();
                        e.1 += 1;
                        e.2 += (used - t) as u64;
                        if !result.examples.iter().any(|e| e.3.len() == d) {
                            result.examples.push((
                                read,
                                l.control.clone(),
                                l.target,
                                l.dirty.clone(),
                                clean
                                    .iter()
                                    .map(|q| (q.wire, q.terms.clone(), q.sign))
                                    .collect(),
                            ));
                        }
                        replacement = Some(v);
                    } else {
                        result.limited += 1;
                    }
                }
                // A complete macro restores every wire other than its target.
                // Apply its logical summary, including for untouched source macros.
                if let Some(c) = effective {
                    if c.len() <= 2 {
                        facts.observe(&simple(&c, l.target), true)
                    } else {
                        facts.observe(&simple(&[], l.target), false)
                    } // conservative fresh opaque target
                }
            }
        }
        if used == 1 {
            let un = depth == 0 && x.c_condition == NO_BIT;
            facts.observe(&x, un);
            match x.kind {
                K::PushCondition => depth += 1,
                K::PopCondition => depth = depth.checked_sub(1).unwrap(),
                _ => {}
            }
        }
        if let Some(v) = replacement {
            ops[wrote..wrote + v.len()].copy_from_slice(&v);
            wrote += v.len();
        } else {
            if gap + read != wrote {
                ops.copy_within(gap + read..gap + read + used, wrote);
            }
            wrote += used;
        }
        read += used;
        result.max_prefix_growth = result.max_prefix_growth.max(wrote.saturating_sub(read));
    }
    ops.truncate(wrote);
    result
}
