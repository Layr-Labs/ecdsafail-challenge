//! cmp_extra (w-mult2): a final pass, after every other policy, that narrows chosen windowed phase-repair blocks by
//! `n` more low bits with the same rewrite as `cmp_policy` (predictor v_{n-1}). Rows `<sig> <occ> <n>` key a block by
//! FNV-1a(width, measured target, window wires) of the block as it stands at this point of the stream, and its
//! occurrence. Fail-closed: every listed row must match and narrow. Measurements of the removed carries are kept.
use crate::circuit::{Op, OperationType, QubitId, NO_BIT, NO_QUBIT};
use std::collections::HashSet;

fn qs(o: &Op) -> [QubitId; 3] { [o.q_control1, o.q_control2, o.q_target] }

fn block_sig(k: usize, target: QubitId, u: &[QubitId]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for x in std::iter::once(k as u64).chain(std::iter::once(target.0)).chain(u.iter().map(|q| q.0)) {
        for b in x.to_le_bytes() { h ^= b as u64; h = h.wrapping_mul(0x0100_0000_01b3); }
    }
    h
}

pub(crate) fn run(ops: Vec<Op>, txt: &str) -> Vec<Op> {
    let table: std::collections::HashMap<(u64, usize), usize> = txt.lines().filter(|l| !l.trim().is_empty() && !l.starts_with('#')).map(|l| {
        let f: Vec<&str> = l.split_whitespace().collect();
        ((u64::from_str_radix(f[0], 16).unwrap(), f[1].parse().unwrap()), f[2].parse().unwrap())
    }).collect();
    let mut occ: std::collections::HashMap<u64, usize> = Default::default();
    if table.is_empty() { return ops; }
    use OperationType::*;
    let mut delete = vec![false; ops.len()];
    let mut subst: Vec<(usize, QubitId, QubitId)> = vec![];
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
        let sig = block_sig(k, h.q_target, &u);
        let oc = { let c = occ.entry(sig).or_insert(0); *c += 1; *c - 1 };
        let n = table.get(&(sig, oc)).copied().unwrap_or(0);

        if n == 0 || k < n + 4 { skip_reason[0] += 1; i = e; continue; }
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
        let pivot = u[n - 1]; let repl = v[n - 1];
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
        // keep the deleted carries' measurements and resets (now on zero wires) so every later draw stays aligned
        for t in del { if matches!(ops[t].kind, Hmr | R) && c[..n].contains(&ops[t].q_target) { continue; } delete[t] = true; }
        subst.extend(sub);
        done += 1; ccx_cut += cut;
        i = e;
    }
    assert_eq!(done, table.values().filter(|&&n| n > 0).count(), "cmp_extra: every row must narrow its block");
    let mut ops = ops;
    for (t, from, to) in subst {
        let o = &mut ops[t];
        if o.q_control1 == from { o.q_control1 = to; }
        if o.q_control2 == from { o.q_control2 = to; }
        if o.q_target == from { o.q_target = to; }
        o.validate();
    }
    let out: Vec<Op> = ops.into_iter().zip(delete).filter(|(_, d)| !d).map(|(o, _)| o).collect();
    eprintln!("CMP_EXTRA table={}: repair blocks {seen}, narrowed {done}, conditioned CCX removed {ccx_cut}; skipped (narrow {}, ladder {}, alias {}, count {})", table.len(),
        skip_reason[0], skip_reason[1], skip_reason[2], skip_reason[3]);
    out
}
