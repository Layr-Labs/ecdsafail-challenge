//! The release's 128-row bidirectional cleanup, confined to plain gates.
use super::{cx, ccx, x, Row, NIL};

fn ports(row: &Row) -> (&[u16], u16) {
    let target = match row[0] { 13 => 3, 8 => 2, _ => 1 };
    (&row[1..target], row[target])
}

fn commute(a: &Row, b: &Row) -> bool {
    let (a_ctrl, a_target) = ports(a);
    let (b_ctrl, b_target) = ports(b);
    a[0] == 0 || b[0] == 0 || (!a_ctrl.contains(&b_target) && !b_ctrl.contains(&a_target))
}

fn key(row: &Row) -> u32 {
    let (c, t) = ports(row);
    let a = c.first().copied().unwrap_or(1023);
    let b = c.get(1).copied().unwrap_or(1023);
    (u32::from(t) << 20) | (u32::from(a.min(b)) << 10) | u32::from(a.max(b))
}

fn derivative(a: &Row, b: &Row) -> Option<Row> {
    let (ac, at) = ports(a);
    let (bc, bt) = ports(b);
    let (outer, inner, target, source) = match (bc.contains(&at), ac.contains(&bt)) {
        (true, false) => (bc, ac, bt, at),
        (false, true) => (ac, bc, at, bt),
        _ => return None,
    };
    let mut q = [NIL; 2];
    let mut n = 0;
    for c in outer.iter().copied().filter(|&x| x != source).chain(inner.iter().copied()) {
        if !q[..n].contains(&c) {
            if n == q.len() { return None; }
            q[n] = c;
            n += 1;
        }
    }
    Some(match n {
        0 => x(target),
        1 => cx(q[0], target),
        _ => ccx(q[0], q[1], target),
    })
}

fn rewrite(rows: &mut Vec<Row>) {
    for _ in 0..4 {
        let mut seen = [usize::MAX; 1024];
        let mut removed = false;
        for j in 0..rows.len() {
            if rows[j][0] == 0 { continue; }
            let k = key(&rows[j]);
            let mut h = (k.wrapping_mul(2_654_435_761) >> 22) as usize;
            loop {
                let i = seen[h];
                if i == usize::MAX || rows[i][0] == 0 || key(&rows[i]) == k { break; }
                h = (h + 1) & 1023;
            }
            let i = seen[h];
            seen[h] = j;
            if i == usize::MAX || rows[i][0] == 0 || key(&rows[i]) != k { continue; }
            let mut conflicts = (i + 1..j).filter(|&z| !commute(&rows[i], &rows[z]));
            let Some(z) = conflicts.next() else {
                rows[i][0] = 0;
                rows[j][0] = 0;
                removed = true;
                continue;
            };
            if conflicts.next().is_some() { continue; }
            if let Some(g) = derivative(&rows[i], &rows[z]) {
                if rows[z + 1..j].iter().all(|r| commute(&g, r)) {
                    rows[j] = g;
                    rows[i][0] = 0;
                    removed = true;
                } else if rows[i + 1..z].iter().all(|r| commute(&g, r)) {
                    rows[i] = g;
                    rows[j][0] = 0;
                    removed = true;
                }
            }
        }
        if !removed { break; }
        rows.retain(|r| r[0] != 0);
    }
}

fn frames(rows: &[Row]) -> Vec<Row> {
    let mut pending = [false; 631];
    let mut touched = Vec::new();
    let mut out = Vec::with_capacity(rows.len());
    let toggle = |q: u16, pending: &mut [bool], touched: &mut Vec<_>| {
        if !pending[q as usize] { touched.push(q); }
        pending[q as usize] ^= true;
    };
    let flush = |q: u16, pending: &mut [bool], out: &mut Vec<_>| {
        if pending[q as usize] {
            out.push(x(q));
            pending[q as usize] = false;
        }
    };
    for &r in rows {
        let [kind, a, b, _] = r;
        if kind == 6 {
            toggle(a, &mut pending, &mut touched);
            continue;
        }
        if kind == 8 && pending[a as usize] { toggle(b, &mut pending, &mut touched); }
        if kind == 13 {
            flush(a, &mut pending, &mut out);
            flush(b, &mut pending, &mut out);
        }
        out.push(r);
    }
    for q in touched { flush(q, &mut pending, &mut out); }
    out
}

fn window(rows: &[Row]) -> Vec<Row> {
    let mut best = rows.to_vec();
    for reverse in [false, true] {
        let mut a = rows.to_vec();
        if reverse { a.reverse(); }
        rewrite(&mut a);
        let mut b = frames(&a);
        rewrite(&mut b);
        for mut alt in [a, b] {
            if alt.len() < best.len() {
                if reverse { alt.reverse(); }
                best = alt;
            }
        }
    }
    best
}

pub(super) fn compact(mut rows: Vec<Row>) -> Vec<Row> {
    let (mut read, mut write) = (0, 0);
    let unary = |[k, _, b, c]: Row| k == 13 || (k == 8 && c == NIL) || (k == 6 && b == NIL);
    while read < rows.len() {
        let limit = (read + 128).min(rows.len());
        let end = (read..limit).find(|&i| !unary(rows[i])).unwrap_or(limit);
        if end > read {
            let result = window(&rows[read..end]);
            rows[write..write + result.len()].copy_from_slice(&result);
            write += result.len();
            read = end;
        } else {
            rows[write] = rows[read];
            write += 1;
            read += 1;
        }
    }
    rows.truncate(write);
    rows
}
