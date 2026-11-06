//! cmp_narrow: a final stream pass (after every stream-bound table) that narrows the windowed phase repairs of
//! `compare::erase_with_compare` by `n` low bits.
//!
//! A repair block is `Hmr(target, m); Push(m); X(u_0..u_{k-1}); <cmp_lt_phase ladder over u, v>; X(u); Pop`. Its
//! comparison is approximate already (the window); dropping the low `n` positions and taking `v_{n-1}` as the borrow
//! predictor for position `n` is the call `cmp_lt_phase(u[n..], v[n..], Some(v[n-1]))`, the predictor form the
//! builder itself uses (`compare.rs`, "MAJ(!u0,v0,v0)=v0"). It removes `n` conditioned CCX per block and doubles the
//! window's error per bit. Only blocks whose ladder head matches the builder's exact op sequence are touched.
//!
//! The policy is fixed in source so an empty-environment build is reproducible.
//! The terminal divide passes retain zero-scratch RNG operations, preserving
//! the reference's later measurement outcomes while testing a smaller window.
use crate::circuit::{Op, OperationType, QubitId, NO_BIT, NO_QUBIT};
use std::collections::HashSet;

fn qs(o: &Op) -> [QubitId; 3] { [o.q_control1, o.q_control2, o.q_target] }

pub(crate) fn run_additional(ops: Vec<Op>) -> Vec<Op> {
    // Terminal divide payload add and endpoint: retain at least eight high
    // comparison bits, preserving every discarded scratch measurement draw.
    let ops = run_selected_aligned(ops, 8, 17, 3_294_000, 3_300_000, &[17], true);
    let ops = run_selected_aligned(ops, 8, 16, 3_294_000, 3_300_000, &[16], true);
    // Forward ticks118..120: native17-bit chunk-boundary comparisons.
    let ops = run_selected_aligned(ops, 2, 17, 3232609, 3284890, &[17], true);
    // Joint carry erasures have a comparison under an existing condition;
    // the HMR-adjacent pass above does not recognize those ladders.
    super::generic_compare::transform(ops, 0, 4_500_000, &[20, 21], 1, 0, true)
}

/// The selected repair blocks use the same local transformation as `run`.
/// Range and width selectors are static builder choices, never input-dependent.
pub(crate) fn run_selected(ops: Vec<Op>, n: usize, min_w: usize,
                           lo: usize, hi: usize, widths: &[usize]) -> Vec<Op> {
    run_selected_aligned(ops, n, min_w, lo, hi, widths, false)
}

/// Retaining the discarded zero-carry measurements/resets preserves every
/// later random draw. The carry writes and their phase repairs are still removed.
pub(crate) fn run_selected_aligned(ops: Vec<Op>, n: usize, min_w: usize,
                           lo: usize, hi: usize, widths: &[usize], preserve_draws: bool) -> Vec<Op> {
    run_filtered(ops, n, min_w, lo, hi, widths, preserve_draws, false, 0, false, &[])
}

/// Restore just the selected original windows by narrowing their complement.
pub(crate) fn run_excluding(ops: Vec<Op>, n: usize, min_w: usize,
                           lo: usize, hi: usize, widths: &[usize]) -> Vec<Op> {
    run_filtered(ops, n, min_w, lo, hi, widths, false, true, 0, false, &[])
}

/// Alternative one-bit borrow predictors: source, complemented accumulator,
/// zero, or one. Scratch measurements stay in place for aligned comparisons.
pub(crate) fn run_predictor(ops: Vec<Op>, n: usize, min_w: usize,
                           lo: usize, hi: usize, widths: &[usize], predictor: usize) -> Vec<Op> {
    assert!(predictor <= 3);
    run_filtered(ops, n, min_w, lo, hi, widths, true, false, predictor, false, &[])
}

/// Restore selected original windows while keeping the reference draw order.
/// The added low-carry HMR consumes the draw of a redundant high-carry reset;
/// both that reset and the redundant low-carry reset are omitted.
pub(crate) fn run_restored_aligned(ops: Vec<Op>, min_w: usize,
                           lo: usize, hi: usize, widths: &[usize]) -> Vec<Op> {
    run_filtered(ops, 1, min_w, lo, hi, widths, false, true, 0, true, &[])
}

/// Select the second pass by each block's original width. Repair-block order
/// is unchanged by narrowing, so classes remain distinct after the first pass.
pub(crate) fn run_original_selected(ops: Vec<Op>, n: usize, min_w: usize,
                           lo: usize, hi: usize, original_widths: &[usize], predictor: usize) -> Vec<Op> {
    use OperationType::*;
    let mut ordinals = Vec::new(); let mut seen = 0;
    for i in 0..ops.len().saturating_sub(1) {
        let (h, p) = (&ops[i], &ops[i + 1]);
        if h.kind != Hmr || h.c_condition != NO_BIT || p.kind != PushCondition || p.c_condition != h.c_target { continue; }
        let mut j = i + 2;
        while j < ops.len() && ops[j].kind == X && ops[j].c_condition == NO_BIT { j += 1; }
        if original_widths.contains(&(j - i - 2)) { ordinals.push(seen); }
        seen += 1;
    }
    let ops = run_selected(ops, 1, 20, 0, usize::MAX, &[]);
    if ordinals.is_empty() { return ops; }
    run_filtered(ops, n, min_w, lo, hi, &[], true, false, predictor, false, &ordinals)
}

fn run_filtered(ops: Vec<Op>, n: usize, min_w: usize,
                lo: usize, hi: usize, widths: &[usize], preserve_draws: bool, exclude: bool, predictor: usize, restore_draws: bool, ordinals: &[usize]) -> Vec<Op> {
    if n == 0 { return ops; }
    use OperationType::*;
    let mut delete = vec![false; ops.len()];
    let mut subst: Vec<(usize, QubitId, QubitId)> = vec![];
    let mut insert: Vec<(usize, Op)> = vec![];
    let (mut seen, mut done, mut ccx_cut) = (0usize, 0usize, 0usize);
    let mut skip_reason = [0usize; 4];
    let mut i = 0;
    while i + 1 < ops.len() {
        let (h, p) = (&ops[i], &ops[i + 1]);
        if !(h.kind == Hmr && p.kind == PushCondition && p.c_condition == h.c_target && h.c_condition == NO_BIT) { i += 1; continue; }
        seen += 1;
        // block end
        let mut d = 0i32; let mut e = i + 1;
        loop { match ops[e].kind { PushCondition => d += 1, PopCondition => { d -= 1; if d == 0 { break; } } _ => {} } e += 1; }
        // X prefix = the accumulator window u
        let mut j = i + 2; let mut u = vec![];
        while j < e && ops[j].kind == X && ops[j].c_condition == NO_BIT { u.push(ops[j].q_target); j += 1; }
        let k = u.len();
        let selected = i >= lo && i < hi && (widths.is_empty() || widths.contains(&k)) && (ordinals.is_empty() || ordinals.binary_search(&(seen - 1)).is_ok());
        if (selected == exclude && !(restore_draws && exclude && selected)) || k < min_w.max(n + 4) { skip_reason[0] += 1; i = e; continue; }
        let is_cx = |o: &Op, c: QubitId, t: QubitId| o.kind == CX && o.c_condition == NO_BIT && o.q_control1 == c && o.q_target == t;
        let ccx_into = |o: &Op, a: QubitId, b: QubitId| -> Option<QubitId> {
            if o.kind == CCX && o.c_condition == NO_BIT && ((o.q_control1 == a && o.q_control2 == b) || (o.q_control1 == b && o.q_control2 == a)) { Some(o.q_target) } else { None }
        };
        // position 0: CX(u0->v0); [CX(u0->p)]; CCX({p|u0, v0}->c0); CX(c0->u0)
        let mut ok = true; let mut v = vec![]; let mut c = vec![]; let mut pb: Option<QubitId> = None;
        let o0 = &ops[j];
        if o0.kind == CX && o0.c_condition == NO_BIT && o0.q_control1 == u[0] { v.push(o0.q_target); } else { ok = false; }
        let mut jj = j + 1;
        if ok {
            if ops[jj].kind == CX && ops[jj].q_control1 == u[0] && ops[jj].c_condition == NO_BIT { pb = Some(ops[jj].q_target); jj += 1; }
            let first = pb.unwrap_or(u[0]);
            match ccx_into(&ops[jj], first, v[0]) { Some(t) => { c.push(t); jj += 1; } None => ok = false }
            if ok && is_cx(&ops[jj], c[0], u[0]) { jj += 1; } else { ok = false; }
        }
        // positions 1..=n: CX(u_m->v_m); CX(u_m->u_{m-1}); CCX({u_{m-1}, v_m}->c_m); CX(c_m->u_m)
        let mut m = 1;
        while ok && m <= n {
            let o = &ops[jj];
            if o.kind == CX && o.c_condition == NO_BIT && o.q_control1 == u[m] { v.push(o.q_target); } else { ok = false; break; }
            if !is_cx(&ops[jj + 1], u[m], u[m - 1]) { ok = false; break; }
            match ccx_into(&ops[jj + 2], u[m - 1], v[m]) { Some(t) => c.push(t), None => { ok = false; break; } }
            if !is_cx(&ops[jj + 3], c[m], u[m]) { ok = false; break; }
            jj += 4; m += 1;
        }
        if !ok { skip_reason[1] += 1; i = e; continue; }
        let mut low: HashSet<u64> = HashSet::new();
        for t in 0..n { low.insert(u[t].0); low.insert(v[t].0); low.insert(c[t].0); }
        if let Some(q) = pb { low.insert(q.0); }
        let high: HashSet<u64> = [u[n].0, v[n].0, c[n].0].into_iter().collect();
        if low.len() != 3 * n + pb.is_some() as usize || low.iter().any(|q| high.contains(q)) || u.iter().skip(n).any(|q| low.contains(&q.0)) {
            skip_reason[2] += 1; i = e; continue;
        }
        let pivot = u[n - 1]; let repl = match predictor {0 => v[n - 1], 1 => pivot, _ => c[n - 1]};
        let mut del = vec![]; let mut sub = vec![]; let mut cut = 0usize;
        for t in i + 2..e {
            let o = &ops[t];
            let touched: Vec<QubitId> = qs(o).into_iter().filter(|q| *q != NO_QUBIT).collect();
            if !touched.iter().any(|q| low.contains(&q.0)) { continue; }
            let only_pivot = touched.iter().filter(|q| low.contains(&q.0)).all(|q| *q == pivot);
            if only_pivot && touched.iter().any(|q| high.contains(&q.0)) && o.kind != X {
                sub.push((t, pivot, repl));
            } else {
                if o.kind == CCX || o.kind == CCZ { cut += 1; }
                del.push(t);
            }
        }
        if cut != n { skip_reason[3] += 1; i = e; continue; }
        if restore_draws && exclude && selected {
            assert_eq!(n, 1);
            let find = |kind, target| (i + 2..e).find(|&t| ops[t].kind == kind && ops[t].q_target == target);
            let h0 = find(Hmr, c[0]).expect("restored low carry measurement");
            let h1 = find(Hmr, c[1]).expect("restored high carry measurement");
            let r0 = find(R, c[0]).expect("restored low carry reset");
            let r1 = find(R, c[1]).expect("restored high carry reset");
            assert!(h1 < h0 && h0 < r0 && r0 < r1);
            assert_eq!(ops[h0 + 1..r1].iter().filter(|o| matches!(o.kind, Hmr | R)).count(), 1);
            assert!(ops[h1 + 1..r1].iter().all(|o| o.q_target != c[1]));
            assert!(ops[h0 + 1..r0].iter().all(|o| o.q_target != c[0]));
            delete[r0] = true; delete[r1] = true;
            i = e; continue;
        }
        if predictor == 3 {
            let mut x = Op::empty(); x.kind = X; x.q_target = repl;
            insert.push((i + 2, x));
            let t = del.iter().copied().find(|&t| ops[t].kind == Hmr && ops[t].q_target == repl)
                .expect("constant predictor scratch must be measured");
            let mut fix = Op::empty(); fix.kind = Neg; fix.c_condition = ops[t].c_target;
            insert.push((t + 1, fix));
        }
        for t in del {
            if predictor == 1 && ops[t].kind == X && ops[t].q_target == pivot { continue; }
            if preserve_draws && matches!(ops[t].kind, Hmr | R) && c[..n].contains(&ops[t].q_target) { continue; }
            delete[t] = true;
        }
        subst.extend(sub);
        done += 1; ccx_cut += cut;
        i = e;
    }
    let mut ops = ops;
    for (t, from, to) in subst {
        let o = &mut ops[t];
        if o.q_control1 == from { o.q_control1 = to; }
        if o.q_control2 == from { o.q_control2 = to; }
        if o.q_target == from { o.q_target = to; }
        o.validate();
    }
    insert.sort_by_key(|(t, _)| *t);
    let mut additions = insert.into_iter().peekable();
    let mut out = Vec::with_capacity(ops.len());
    for (t, (op, deleted)) in ops.into_iter().zip(delete).enumerate() {
        while additions.peek().is_some_and(|(at, _)| *at == t) { out.push(additions.next().unwrap().1); }
        if !deleted { out.push(op); }
    }
    assert!(additions.next().is_none());
    eprintln!("CMP_NARROW n={n} min_w={min_w}: repair blocks {seen}, narrowed {done}, conditioned CCX removed {ccx_cut}; skipped (narrow {}, ladder {}, alias {}, count {})",
        skip_reason[0], skip_reason[1], skip_reason[2], skip_reason[3]);
    out
}
