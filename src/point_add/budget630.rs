//! The certified budget pass and the frozen budget2 window pass.
use super::{post_pass::values::Values, Row};
use std::collections::HashMap;

const NIL: u16 = u16::MAX;

fn x(q: u16) -> Row {
    [6, q, NIL, NIL]
}

fn cx(a: u16, t: u16) -> Row {
    [8, a, t, NIL]
}

fn ccx(a: u16, b: u16, t: u16) -> Row {
    [13, a, b, t]
}

fn plain([kind, _, b, c]: Row) -> bool {
    kind == 13 || (kind == 8 && c == NIL) || (kind == 6 && b == NIL)
}

fn sandwich(outer: Row, middle: Row) -> Option<Row> {
    if !plain(outer) || !plain(middle) {
        return None;
    }
    let [k, xq, y, _] = outer;
    let [m, u, v, t] = middle;
    let control = |q| q == u || q == v;
    match (k, m) {
        (8, 13) if control(y) && !control(xq) && xq != t => {
            Some(ccx(xq, if u == y { v } else { u }, t))
        }
        (8, 13) if xq == t && !control(y) => Some(ccx(u, v, y)),
        (6, 13) if control(xq) => Some(cx(if u == xq { v } else { u }, t)),
        (8, 8) if y == u && xq != v => Some(cx(xq, v)),
        (8, 8) if xq == v && y != u => Some(cx(u, y)),
        (6, 8) if xq == u => Some(x(v)),
        _ => None,
    }
}

#[derive(Clone, Copy)]
enum Entry {
    Unconditional,
    Outer,
    Guard768,
}

#[derive(Clone, Copy)]
struct Scope {
    may: u8,
    must: u8,
}

fn liveness(rows: &[Row], entry: Entry, unmeasure: bool) -> Vec<u8> {
    let stable = matches!(entry, Entry::Guard768)
        && !rows.iter().any(|&[k, a, b, _]| {
            ((3..=5).contains(&k) && a == 768) || (k == 12 && b == 768)
        });
    let unconditional = Scope { may: 3, must: 3 };
    let mut scope = match entry {
        Entry::Unconditional => unconditional,
        _ if stable => Scope { may: 1, must: 1 },
        _ => Scope { may: 3, must: 0 },
    };
    let guard = |s: Scope, bit: u16| match bit {
        NIL => s,
        768 if stable => Scope { may: s.may & 1, must: s.must & 1 },
        _ => Scope { may: s.may, must: 0 },
    };
    let mut stack = Vec::new();
    if !matches!(entry, Entry::Unconditional) {
        stack.push(unconditional);
    }
    let mut events = Vec::new();
    for (i, &[k, a, _, _]) in rows.iter().enumerate() {
        match k {
            15 => {
                events.push((i, scope));
                stack.push(scope);
                scope = guard(scope, a);
            }
            16 => {
                events.push((i, scope));
                scope = stack.pop().expect("condition stack underflow");
            }
            _ => {}
        }
    }
    let mut live = [3u8; 65536];
    let mut marks = vec![0; rows.len()];
    let mut i = rows.len();
    while i > 0 {
        i -= 1;
        let [k, a, b, c] = rows[i].map(usize::from);
        match k {
            15 | 16 => {
                let (pos, prior) = events.pop().unwrap();
                assert_eq!(pos, i);
                scope = prior;
                if k == 15 {
                    live[a] |= scope.may;
                }
            }
            9 if i > 0 && c != usize::from(NIL) && a != b => {
                let [op, target, bit, _] = rows[i - 1].map(usize::from);
                if op == 12 && bit == c && target != a && target != b {
                    if unmeasure && live[c] & scope.may == 0
                        && (c == 65500 || c == 65534 || (62500..62600).contains(&c))
                    {
                        marks[i - 1] = 2;
                    }
                    live[c] &= !scope.must;
                    i -= 1;
                } else {
                    live[c] |= scope.may;
                }
            }
            3..=5 => {
                let g = guard(scope, b as u16);
                if live[a] & g.may == 0 {
                    marks[i] = 1;
                } else {
                    if k != 3 {
                        live[a] &= !g.must;
                    }
                    if b != usize::from(NIL) {
                        live[b] |= scope.may;
                    }
                }
            }
            12 if b != usize::from(NIL) => live[b] &= !scope.must,
            6 | 7 if b != usize::from(NIL) => live[b] |= scope.may,
            8 | 9 if c != usize::from(NIL) => live[c] |= scope.may,
            _ => {}
        }
    }
    marks
}

fn symbolic(rows: &[Row], first: bool, certify_and: bool, marks: &mut [u8]) {
    let mut values = Values::new(631);
    if !first {
        for q in 0..631 {
            values.unknown(q);
        }
        values.enter();
    }
    let mut last = None;
    for (i, row) in rows.iter().enumerate() {
        let [k, a, b, c] = row.map(usize::from);
        if let Some((target, id, bit)) = last.take() {
            if k == 9 && bit == c && a != target && b != target
                && values.product(values.wire[a], values.wire[b]) == id
                && marks[i - 1] == 2
            {
                marks[i - 1] = 3;
            }
        }
        match k {
            2 => values.unknown(b),
            6 | 8 | 13 => {
                let (target, toggle, conditioned) = match k {
                    6 => (a, 1, b != usize::from(NIL)),
                    8 => (b, values.wire[a], c != usize::from(NIL)),
                    _ => (c, values.product(values.wire[a], values.wire[b]), false),
                };
                if toggle == 0 {
                    marks[i] = 1;
                } else if conditioned {
                    values.unknown(target);
                } else {
                    let next = values.sum(values.wire[target], toggle);
                    values.set(target, next);
                }
            }
            12 => {
                // Compute every symbolic product, including at pairs that liveness
                // retains. The bounded equation cache has deterministic eviction.
                if certify_and {
                    last = Some((a, values.wire[a], b));
                }
                values.set(a, 0);
            }
            15 => values.enter(),
            16 => values.leave(),
            1 | 3..=5 | 7 | 9 | 18 => {}
            _ => panic!("bad budget opcode {k}"),
        }
    }
}

fn local_rules(rows: &mut [Row], marks: &[u8]) -> usize {
    let (mut read, mut write) = (0, 0);
    while read < rows.len() {
        let a = rows[read];
        let next = rows.get(read + 1).copied();
        if marks[read] == 1 {
            read += 1;
            continue;
        }
        if marks[read] == 3 {
            let b = next.unwrap();
            rows[write] = ccx(b[1], b[2], a[1]);
            write += 1;
            read += 2;
            continue;
        }
        if next == Some(a) && plain(a) {
            read += 2;
            continue;
        }
        if rows.get(read + 2) == Some(&a) {
            let middle = next.unwrap();
            if let Some(extra) = sandwich(a, middle) {
                rows[write] = middle;
                rows[write + 1] = extra;
                write += 2;
                read += 3;
                continue;
            }
        }
        if a[0] == 15 && next.is_some_and(|b| b[0] == 16) {
            read += 2;
            continue;
        }
        rows[write] = a;
        write += 1;
        read += 1;
    }
    write
}

pub fn certified(name: &str, mut rows: Vec<Row>) -> Vec<Row> {
    let first = name == "s00";
    let entry = if first { Entry::Unconditional } else { Entry::Guard768 };
    let mut marks = liveness(&rows, entry, true);
    symbolic(&rows, first, true, &mut marks);
    let length = local_rules(&mut rows, &marks);
    rows.truncate(length);
    rows
}

fn guard_field(kind: u16) -> Option<usize> {
    match kind {
        3..=7 => Some(2),
        8 | 9 => Some(3),
        _ => None,
    }
}

fn folds(rows: &[Row]) -> Vec<Row> {
    let mut out = Vec::with_capacity(rows.len());
    let mut i = 0;
    while i < rows.len() {
        let r = rows[i];
        if r[0] == 15 {
            let guard = r[1];
            let mut j = i + 1;
            while let Some(y) = rows.get(j) {
                let Some(field) = guard_field(y[0]) else { break };
                if (y[field] != NIL && y[field] != guard) || (y[0] <= 5 && y[1] == guard) {
                    break;
                }
                j += 1;
            }
            if rows.get(j).is_some_and(|r| r[0] == 16) {
                out.extend(rows[i + 1..j].iter().copied().map(|mut r| {
                    r[guard_field(r[0]).unwrap()] = guard;
                    r
                }));
                i = j + 1;
                continue;
            }
        }
        out.push(r);
        i += 1;
    }
    out
}

fn negative_swap(rows: &[Row], i: usize) -> Option<[u16; 2]> {
    let [first, a, b, last] = rows.get(i..i + 4)? else { unreachable!() };
    if first != last || first[0] != 8 || first[3] != NIL {
        return None;
    }
    let (t, l) = if a[0] == 13 { (*a, *b) } else { (*b, *a) };
    let [_, p, q, _] = *first;
    if t[0] != 13 || t[3] != p || (t[1] != q && t[2] != q) {
        return None;
    }
    let control = if t[1] == q { t[2] } else { t[1] };
    (l == cx(control, p) && control != p && control != q && p != q).then_some([p, q])
}

fn swap_runs(rows: &[Row]) -> Vec<Row> {
    let mut out = Vec::with_capacity(rows.len());
    let mut i = 0;
    while i < rows.len() {
        let mut end = i;
        let mut pivot = NIL;
        if let (Some(first), Some(second)) = (negative_swap(rows, i), negative_swap(rows, i + 4)) {
            for p in first {
                if second.contains(&p) {
                    let mut j = i + 8;
                    while negative_swap(rows, j).is_some_and(|s| s.contains(&p)) {
                        j += 4;
                    }
                    if j > end {
                        end = j;
                        pivot = p;
                    }
                }
            }
        }
        if end < i + 12 {
            out.push(rows[i]);
            i += 1;
            continue;
        }
        out.push(x(pivot));
        for steps in rows[i..end].chunks_exact(4) {
            let middle = if steps[1][0] == 13 { steps[1] } else { steps[2] };
            out.extend([steps[0], middle, steps[3]]);
        }
        out.push(x(pivot));
        i = end;
    }
    out
}

fn operands(row: &Row) -> (&[u16], u16) {
    let end = match row[0] { 13 => 3, 8 => 2, _ => 1 };
    (&row[1..end], row[end])
}

fn commute(a: &Row, b: &Row) -> bool {
    let (ac, at) = operands(a);
    let (bc, bt) = operands(b);
    !ac.contains(&bt) && !bc.contains(&at)
}

fn canonical(mut row: Row) -> Row {
    if row[0] == 13 && row[1] > row[2] {
        row.swap(1, 2);
    }
    row
}

fn conjugate(a: &Row, b: &Row) -> Option<Row> {
    let (ac, at) = operands(a);
    let (bc, bt) = operands(b);
    let (first, second, source, target) = match (bc.contains(&at), ac.contains(&bt)) {
        (true, false) => (ac, bc, at, bt),
        (false, true) => (bc, ac, bt, at),
        _ => return None,
    };
    let mut controls = [NIL; 2];
    let mut len = 0;
    for &q in first.iter().chain(second) {
        if q != source && !controls[..len].contains(&q) {
            if len == 2 {
                return None;
            }
            controls[len] = q;
            len += 1;
        }
    }
    Some(match len {
        0 => x(target),
        1 => cx(controls[0], target),
        _ => ccx(controls[0], controls[1], target),
    })
}

fn motion(mut rows: Vec<Row>) -> Vec<Row> {
    let mut last = HashMap::with_capacity(rows.len());
    let mut first = 0;
    for i in 0..rows.len() {
        let g = rows[i];
        if !plain(g) {
            first = i + 1;
            continue;
        }
        let key = canonical(g);
        let Some(p) = last.insert(key, i) else { continue };
        if p < first || i - p > 1024 || canonical(rows[p]) != key {
            continue;
        }
        let mut changes = (p + 1..i).filter(|&j| rows[j][0] != 0 && !commute(&g, &rows[j]));
        let Some(middle) = changes.next() else {
            rows[p] = [0; 4];
            rows[i] = [0; 4];
            continue;
        };
        if changes.next().is_some() {
            continue;
        }
        if let Some(extra) = conjugate(&g, &rows[middle]) {
            if rows[middle + 1..i].iter().all(|r| r[0] == 0 || commute(&extra, r)) {
                rows[p] = [0; 4];
                rows[i] = extra;
            } else if rows[p + 1..middle].iter().all(|r| r[0] == 0 || commute(&extra, r)) {
                rows[i] = [0; 4];
                rows[p] = extra;
            }
        }
    }
    rows.retain(|r| r[0] != 0);
    rows
}

fn factor_term(r: Row, cc: Row) -> bool {
    r[0] == 8 && r[3] == NIL && r[2] == cc[3] && (r[1] == cc[1] || r[1] == cc[2])
}

#[derive(Default)]
struct Signs {
    state: Vec<u8>,
    dirty: Vec<usize>,
}

impl Signs {
    fn toggle(&mut self, q: usize) {
        if self.state[q] == 0 {
            self.dirty.push(q);
        }
        // Bit 1 marks membership in dirty; bit 0 is the sign.
        self.state[q] = (self.state[q] ^ 1) | 2;
    }

    fn settle(&mut self, out: &mut Vec<Row>) {
        while let Some(q) = self.dirty.pop() {
            if self.state[q] & 1 != 0 {
                out.push(x(q as u16));
            }
            self.state[q] = 0;
        }
    }
}

fn signed_run(rows: &[Row], reverse: bool, strategy: u8) -> Vec<Row> {
    let at = |i| rows[if reverse { rows.len() - 1 - i } else { i }];
    let mut factors: Vec<(Row, [bool; 2])> = Vec::with_capacity(rows.len());
    let mut i = 0;
    while i < rows.len() {
        let r = at(i);
        let mut linear = [false; 2];
        if r[0] == 13 {
            while factors.last().is_some_and(|f| factor_term(f.0, r)) {
                let term = factors.pop().unwrap().0;
                linear[usize::from(term[1] != r[1])] ^= true;
            }
            while i + 1 < rows.len() && factor_term(at(i + 1), r) {
                i += 1;
                linear[usize::from(at(i)[1] != r[1])] ^= true;
            }
        }
        factors.push((r, linear));
        i += 1;
    }
    let mut out = Vec::with_capacity(rows.len());
    let mut signs = Signs { state: vec![0; 631], dirty: Vec::new() };
    for (r, [la, lb]) in factors {
        if !plain(r) {
            signs.settle(&mut out);
            out.push(r);
            continue;
        }
        let [k, a, b, t] = r;
        let sa = signs.state[a as usize] & 1 != 0;
        match k {
            6 => signs.toggle(a as usize),
            8 => {
                out.push(r);
                if sa {
                    signs.toggle(b as usize);
                }
            }
            _ => {
                for (q, required) in [(a, lb), (b, la)] {
                    let sign = signs.state[q as usize] & 1 != 0;
                    if sign != required
                        && (strategy == 0 || (strategy == 1 && sign) || (strategy == 2 && required))
                    {
                        out.push(x(q));
                        signs.toggle(q as usize);
                    }
                }
                let sa = signs.state[a as usize] & 1 != 0;
                let sb = signs.state[b as usize] & 1 != 0;
                out.push(r);
                if sb != la { out.push(cx(a, t)); }
                if sa != lb { out.push(cx(b, t)); }
                if (sa & sb) ^ (la & sa) ^ (lb & sb) {
                    signs.toggle(t as usize);
                }
            }
        }
    }
    signs.settle(&mut out);
    if reverse {
        out.reverse();
    }
    out
}

fn improve(rows: &[Row]) -> Vec<Row> {
    let moved = motion(swap_runs(&folds(rows)));
    let mut best = moved.clone();
    for reverse in [false, true] {
        for strategy in 0..3 {
            let alternative = signed_run(&moved, reverse, strategy);
            if alternative.len() < best.len() {
                best = alternative;
            }
        }
    }
    motion(best)
}

pub fn windowed(mut rows: Vec<Row>, cuts: &[u8]) -> Vec<Row> {
    let mut marks = liveness(&rows, Entry::Guard768, false);
    // The proof lookup changes the symbolic equation cache even when the
    // release keeps HMR. Compute it as in the original symbolic driver.
    symbolic(&rows, false, true, &mut marks);
    let (mut read, mut write) = (0, 0);
    let mut tile = Vec::with_capacity(2048);
    let mut cuts = cuts.chunks_exact(2);
    for chunk in &mut cuts {
        let cut = u16::from_le_bytes(chunk.try_into().unwrap());
        let size = usize::from(cut & 32767);
        let end = read + size;
        assert!((1..=2048).contains(&size) && end <= rows.len());
        if cut & 32768 == 0 {
            tile.clear();
            tile.extend_from_slice(&rows[read..end]);
            let len = local_rules(&mut tile, &marks[read..end]);
            let result = improve(&tile[..len]);
            assert!(result.len() <= size);
            if result.len() < size {
                rows[write..write + result.len()].copy_from_slice(&result);
                write += result.len();
                read = end;
                continue;
            }
        }
        rows.copy_within(read..end, write);
        write += size;
        read = end;
    }
    assert!(cuts.remainder().is_empty());
    assert_eq!(read, rows.len());
    rows.truncate(write);
    rows
}
