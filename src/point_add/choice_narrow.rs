//! choice_narrow (w-lambda): a final stream pass that narrows the walks' choice-compare windows from below.
//!
//! The a2 walk's choice compare `Y = [a > 2b]` over a window of the two rails is a carry chain of Gidney MAJ units
//! (`leapfrog::w1_chain_s`): unit j computes `t_j = AND(x_j ^ c, !y_j ^ c) ^ c` with `c = t_{j-1}` (`c = x_0` for the
//! first unit), and the chain is later erased by measurement in reverse order. Starting the window `d` positions
//! higher (the builder's own window with `L - d`, i.e. `LF_YP8_LATE` lowered by d) is exactly: drop units 1..=d
//! (compute and measurement erase) and give unit d+1 the carry literal `x_d` instead of `t_d`. The compare then
//! differs from the full window only when the dropped low bits would have carried: the walk takes the other choice,
//! which costs nothing unless that path later exceeds the rail width table. Forward and reverse instances of a tick's
//! compare are narrowed alike, so the reverse walk recomputes the same letter.
//!
//! `choice_narrow.txt` rows `<t> <x> <y> <c> <occ> <d>`: the chain whose first unit is `CCX(x, y -> t)` with carry
//! wire `c`, at its `occ`-th occurrence in stream order, is narrowed by `d`. Every touched op is matched exactly
//! (fail-closed: a row whose chain does not match is an assertion failure).
use crate::circuit::{Op, OperationType, QubitId, NO_BIT};
use std::collections::HashMap;

#[derive(Clone, Copy)]
struct Unit {
    i: usize,
    x: QubitId,
    y: QubitId,
    t: QubitId,
    c: QubitId,
}

fn is_cx(o: &Op, c: QubitId, t: QubitId) -> bool {
    o.kind == OperationType::CX && o.c_condition == NO_BIT && o.q_control1 == c && o.q_target == t
}
fn is_x(o: &Op, t: QubitId) -> bool {
    o.kind == OperationType::X && o.c_condition == NO_BIT && o.q_target == t
}

/// `CX c,x; CX c,y; X y; CCX(x, y -> t); X y; CX c,t; CX c,y; CX c,x` with the CCX at i.
fn unit_at(ops: &[Op], i: usize) -> Option<Unit> {
    let o = &ops[i];
    if o.kind != OperationType::CCX || o.c_condition != NO_BIT || i < 3 || i + 4 >= ops.len() { return None; }
    let (y, x) = if is_x(&ops[i - 1], o.q_control1) { (o.q_control1, o.q_control2) } else { (o.q_control2, o.q_control1) };
    if !is_x(&ops[i - 1], y) || !is_x(&ops[i + 1], y) { return None; }
    let c = ops[i - 3].q_control1;
    let t = o.q_target;
    (is_cx(&ops[i - 3], c, x) && is_cx(&ops[i - 2], c, y) && is_cx(&ops[i + 2], c, t) && is_cx(&ops[i + 3], c, y)
        && is_cx(&ops[i + 4], c, x)).then_some(Unit { i, x, y, t, c })
}

/// The unit's measurement erase: `CX c,x; CX c,y; CX c,t; X y; Hmr(t, m); CZ(x, y) if m; X y; CX c,y; CX c,x`;
/// returns the Hmr index.
fn erase_of(ops: &[Op], u: &Unit) -> usize {
    let h = (u.i + 5..ops.len()).find(|&h| ops[h].kind == OperationType::Hmr && ops[h].q_target == u.t).unwrap();
    let m = ops[h].c_target;
    let cz = &ops[h + 1];
    assert!(is_cx(&ops[h - 4], u.c, u.x) && is_cx(&ops[h - 3], u.c, u.y) && is_cx(&ops[h - 2], u.c, u.t)
        && is_x(&ops[h - 1], u.y) && ops[h].c_condition == NO_BIT
        && cz.kind == OperationType::CZ && cz.c_condition == m && cz.q_control1 == u.x && cz.q_target == u.y
        && is_x(&ops[h + 2], u.y) && is_cx(&ops[h + 3], u.c, u.y) && is_cx(&ops[h + 4], u.c, u.x),
        "choice_narrow: erase pattern of t={} at {h}", u.t.0);
    // the measured bit is read by the CZ only
    for o in &ops[h + 2..] {
        if o.kind == OperationType::Hmr && o.c_target == m { break; }
        assert!(o.c_condition != m && !(o.kind == OperationType::PushCondition && o.c_target == m), "choice_narrow: bit reuse");
    }
    h
}

pub(crate) fn run(ops: Vec<Op>) -> Vec<Op> {
    let rows: HashMap<(u64, u64, u64, u64, usize), (usize, usize)> = include_str!("choice_narrow.txt")
        .lines()
        .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
        .map(|l| {
            let f: Vec<u64> = l.split_whitespace().map(|v| v.parse().unwrap()).collect();
            ((f[0], f[1], f[2], f[3], f[4] as usize), (f[5] as usize, (f.get(6).copied().unwrap_or(0) + 16 * f.get(7).copied().unwrap_or(0)) as usize))
        })
        .collect();
    if rows.values().all(|&(d, u)| d == 0 && u == 0) { return ops; }
    let units: Vec<Unit> = (0..ops.len()).filter_map(|i| unit_at(&ops, i)).collect();
    let mut occ: HashMap<(u64, u64, u64, u64), usize> = HashMap::new();
    let mut del = vec![false; ops.len()];
    let mut recarry: Vec<(usize, QubitId, QubitId)> = Vec::new(); // (op, old control, new control)
    let (mut hit, mut cut, mut topcut) = (0usize, 0usize, 0usize);
    let mut retop: Vec<(usize, usize, QubitId)> = Vec::new(); // (top CCX, its erase CZ, carry)
    for k in 0..units.len() {
        let u = units[k];
        let key = (u.t.0, u.x.0, u.y.0, u.c.0);
        let o = occ.entry(key).or_insert(0);
        let (d, ucut) = rows.get(&(key.0, key.1, key.2, key.3, *o)).copied().unwrap_or((0, 0));
        *o += 1;
        if d == 0 && ucut == 0 { continue; }
        if ucut > 0 {
            // the whole chain up to its last MAJ unit
            let mut full = vec![u];
            let mut j = k + 1;
            while j < units.len() && units[j].i < full.last().unwrap().i + 64 {
                if units[j].c == full.last().unwrap().t { full.push(units[j]); }
                j += 1;
            }
            let last = *full.last().unwrap();
            // ucut = top AND (bit 0, if the chain has one) + 16 * MAJ units
            let mut rem = ucut >> 4;
            // the top AND unit `X y; CCX(t_last, y -> T); X y` (the window's top b bit against a zero a bit)
            let (a, b, cc) = (&ops[last.i + 5], &ops[last.i + 6], &ops[last.i + 7]);
            if a.kind == OperationType::X && cc.kind == OperationType::X && a.q_target == cc.q_target && b.kind == OperationType::CCX
                && b.c_condition == NO_BIT && a.c_condition == NO_BIT && cc.c_condition == NO_BIT
                && ((b.q_control1 == last.t && b.q_control2 == a.q_target) || (b.q_control2 == last.t && b.q_control1 == a.q_target)) {
                let (y, tt) = (a.q_target, b.q_target);
                let h = (last.i + 8..ops.len()).find(|&h| ops[h].kind == OperationType::Hmr && ops[h].q_target == tt).unwrap();
                let m = ops[h].c_target;
                let cz = &ops[h + 1];
                assert!(is_x(&ops[h - 1], y) && is_x(&ops[h + 2], y) && cz.kind == OperationType::CZ && cz.c_condition == m
                    && ((cz.q_control1 == y && cz.q_target == last.t) || (cz.q_control1 == last.t && cz.q_target == y)),
                    "choice_narrow: top erase pattern of T={} at {h}", tt.0);
                for o in &ops[h + 2..] {
                    if o.kind == OperationType::Hmr && o.c_target == m { break; }
                    assert!(o.c_condition != m && !(o.kind == OperationType::PushCondition && o.c_target == m), "choice_narrow: top bit reuse");
                }
                if ucut & 1 == 1 {
                    retop.push((last.i + 6, h + 1, last.t));
                    topcut += 1;
                }
            }
            let mut q = full.len();
            while rem > 0 {
                q -= 1;
                assert!(q > d, "choice_narrow: top cut reaches the low cut");
                let v = full[q];
                let h = erase_of(&ops, &v);
                // t_q = t_{q-1}: no CCX, no phase repair (the erase measures |0>, keeps the draw)
                del[v.i] = true;
                del[h + 1] = true;
                rem -= 1;
                topcut += 1;
            }
        }
        if d == 0 { hit += 1; continue; }
        // the chain: unit j+1 is the next unit whose carry wire is t_j
        let mut ch = vec![u];
        let mut j = k + 1;
        while ch.len() < d + 1 {
            let last = *ch.last().unwrap();
            assert!(j < units.len() && units[j].i < last.i + 64, "choice_narrow: chain of t={} too short", u.t.0);
            if units[j].c == last.t { ch.push(units[j]); }
            j += 1;
        }
        let er: Vec<usize> = ch.iter().map(|v| erase_of(&ops, v)).collect();
        for q in 0..d {
            let (v, h) = (ch[q], er[q]);
            // t_q is read only by its own unit and, as the carry wire, by unit q+1's compute and erase
            let nx = ch[q + 1];
            let allowed: Vec<usize> = [nx.i - 3, nx.i - 2, nx.i + 2, nx.i + 3, nx.i + 4, er[q + 1] - 4, er[q + 1] - 3,
                er[q + 1] - 2, er[q + 1] + 3, er[q + 1] + 4].to_vec();
            for p in v.i + 1..h - 4 {
                let o = &ops[p];
                if p >= v.i + 2 && p <= v.i + 4 { continue; }
                if o.q_target == v.t || o.q_control1 == v.t || o.q_control2 == v.t {
                    assert!(allowed.contains(&p), "choice_narrow: t={} used at {p}", v.t.0);
                }
            }
            for p in v.i - 3..=v.i + 4 { del[p] = true; }
            // the erase's Hmr stays (on the now idle |0> wire: no phase, the same random draw as before)
            for p in (h - 4..=h + 4).filter(|&p| p != h) { del[p] = true; }
            cut += 1;
        }
        // unit d+1 takes x_d as its carry wire
        let (nx, h, nc) = (ch[d], er[d], ch[d - 1].x);
        for p in [nx.i - 3, nx.i - 2, nx.i + 2, nx.i + 3, nx.i + 4, h - 4, h - 3, h - 2, h + 3, h + 4] {
            recarry.push((p, nx.c, nc));
        }
        hit += 1;
    }
    let mut ops = ops;
    for (p, ph, c) in retop {
        // T = AND(c, !y) -> T = c; its erase's CZ(y, c) -> Z(c)
        assert!(ops[p].kind == OperationType::CCX && !del[p] && !del[ph]);
        ops[p].kind = OperationType::CX;
        ops[p].q_control1 = c;
        ops[p].q_control2 = crate::circuit::NO_QUBIT;
        ops[ph].kind = OperationType::Z;
        ops[ph].q_target = c;
        ops[ph].q_control1 = crate::circuit::NO_QUBIT;
        ops[ph].q_control2 = crate::circuit::NO_QUBIT;
    }
    for (p, old, new) in recarry {
        assert!(ops[p].q_control1 == old && !del[p]);
        ops[p].q_control1 = new;
    }
    let n = rows.values().filter(|&&(d, u)| d > 0 || u > 0).count();
    eprintln!("choice_narrow: {hit}/{n} chains narrowed, {cut} low units cut, {topcut} top units cut");
    assert_eq!(hit, n, "choice_narrow: every row must match");
    ops.into_iter().zip(del).filter(|(_, d)| !d).map(|(o, _)| o).collect()
}
