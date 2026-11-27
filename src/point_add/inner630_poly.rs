//! Polynomial transport through the chosen inner divider windows.
use super::{plain, raw, Row};
use std::collections::{BTreeSet, HashMap};

type Term = Vec<u16>;
type Poly = BTreeSet<Term>;

fn sorted(mut t: Term) -> Term {
    t.sort_unstable();
    t.dedup();
    t
}

fn join(a: &[u16], b: &[u16]) -> Term {
    sorted([a, b].concat())
}

fn toggle(poly: &mut Poly, t: Term) {
    if !poly.remove(&t) { poly.insert(t); }
}

fn quantum(t: &[u16], q: u16) -> Row {
    if let [a, b] = *t { raw(&[a.min(b), a.max(b), q]) }
    else { raw(&[t, &[q]].concat()) }
}

pub(super) fn multi(out: &mut Vec<Row>, c: &[u16], t: u16, avoid: u16) {
    if c.len() <= 2 {
        out.push(quantum(c, t));
        return;
    }
    let d: Vec<_> = (0..631).filter(|&q| q != avoid && q != t && !c.contains(&q)).take(c.len() - 2).collect();
    assert_eq!(d.len(), c.len() - 2);
    for _ in 0..2 {
        out.push(quantum(&c[..2], d[0]));
        for j in 1..d.len() { out.push(quantum(&[c[j + 1], d[j - 1]], d[j])); }
        out.push(quantum(&[c[c.len() - 1], d[d.len() - 1]], t));
        for j in (1..d.len()).rev() { out.push(quantum(&[c[j + 1], d[j - 1]], d[j])); }
    }
}

fn last(live: &[bool], set: &mut Vec<usize>) -> Option<usize> {
    while set.last().is_some_and(|&i| !live[i]) { set.pop(); }
    set.last().copied()
}

fn reduce(input: &[Row]) -> Vec<Row> {
    let mut live = vec![false; input.len()];
    let mut rd: [Vec<usize>; 631] = std::array::from_fn(|_| Vec::new());
    let mut wr: [Vec<usize>; 631] = std::array::from_fn(|_| Vec::new());
    let mut seen: HashMap<Row, Vec<usize>> = HashMap::new();
    for (i, &r) in input.iter().enumerate() {
        let n = plain(r);
        let q = r[n] as usize;
        let c = &r[1..n];
        let mut bar = last(&live, &mut rd[q]);
        for &a in c { bar = bar.max(last(&live, &mut wr[a as usize])); }
        let found = seen.entry(quantum(c, q as u16)).or_default();
        if let Some(old) = last(&live, found).filter(|&p| Some(p) > bar) {
            live[old] = false;
            found.pop();
        } else {
            live[i] = true;
            found.push(i);
            wr[q].push(i);
            for &a in c { rd[a as usize].push(i); }
        }
    }
    input.iter().zip(live).filter_map(|(&r, keep)| keep.then_some(r)).collect()
}

fn substitute(poly: &mut Poly, t: u16, controls: &[u16]) {
    let mut delta = Poly::new();
    for m in poly.iter() {
        if m.contains(&t) {
            let remainder: Vec<_> = m.iter().copied().filter(|&q| q != t).collect();
            toggle(&mut delta, join(&remainder, controls));
        }
    }
    for term in delta { toggle(poly, term); }
}

fn product(poly: &Poly, controls: &[u16], omitted: u16) -> Poly {
    let rest: Vec<_> = controls.iter().copied().filter(|&q| q != omitted).collect();
    let mut out = Poly::new();
    for m in poly { toggle(&mut out, join(m, &rest)); }
    out
}

fn iterate(rows: &[Row], rev: bool) -> impl Iterator<Item = Row> + '_ {
    (0..rows.len()).map(move |i| rows[if rev { rows.len() - 1 - i } else { i }])
}

pub(super) fn frame(rows: &[Row], h: u16, rev: bool) -> Vec<Row> {
    let mut p = Poly::new();
    let mut out = Vec::with_capacity(rows.len());
    for r in iterate(rows, rev) {
        let n = plain(r);
        let (t, c) = (r[n], &r[1..n]);
        if t == h {
            toggle(&mut p, sorted(c.to_vec()));
        } else {
            out.push(r);
            if c.contains(&h) {
                for term in product(&p, c, h) { multi(&mut out, &term, t, h); }
            } else {
                substitute(&mut p, t, c);
            }
        }
    }
    for term in p { multi(&mut out, &term, h, h); }
    if rev { out.reverse(); }
    out
}

struct Sector {
    c: u16,
    p: Poly,
    sequence: Vec<Row>,
}

impl Sector {
    fn new(c: u16, bit: bool) -> Self {
        let p = if bit { Poly::from([vec![]]) } else { Poly::new() };
        Self { c, p, sequence: Vec::new() }
    }

    fn push(&mut self, r: Row) {
        let n = plain(r);
        let (t, c) = (r[n], &r[1..n]);
        if t == self.c {
            toggle(&mut self.p, sorted(c.to_vec()));
        } else if c.contains(&self.c) {
            for term in product(&self.p, c, self.c) {
                assert!(!term.contains(&t));
                multi(&mut self.sequence, &term, t, self.c);
            }
        } else {
            self.sequence.push(r);
            substitute(&mut self.p, t, c);
        }
    }

    fn finish(self, bit: bool) -> Vec<Row> {
        assert_eq!(self.p.len(), usize::from(bit));
        if bit { assert!(self.p.contains(&vec![])); }
        self.sequence
    }
}

fn rename(mut r: Row, a: u16, b: u16) -> Row {
    let n = plain(r);
    for q in &mut r[1..=n] {
        *q = if *q == a { b } else if *q == b { a } else { *q };
    }
    r
}

pub(super) fn exchange(rows: &[Row], [c, x, y]: [u16; 3], reversed: bool, perm: bool) -> Vec<Row> {
    let input: Vec<_> = iterate(rows, reversed).collect();
    assert_eq!(input[0], raw(&[x, y]));
    assert_eq!(input[2], input[0]);
    assert!(input[1] == raw(&[c, y, x]) || input[1] == raw(&[y, c, x]));
    let mut s = Sector::new(c, !perm);
    let mut out = Vec::with_capacity(rows.len());
    for &r in &input[3..] {
        s.push(r);
        out.push(if perm { rename(r, x, y) } else { r });
    }
    let a = reduce(&s.finish(!perm));
    let b: Vec<_> = a.iter().map(|&r| rename(r, x, y)).collect();
    let (a, b) = if perm { (b, a) } else { (a, b) };
    let diff: Vec<_> = a.iter().rev().chain(&b).copied().collect();
    let diff = reduce(&diff);
    let decorate = perm && !diff.is_empty();
    let mut fix = Vec::new();
    if decorate { fix.push(raw(&[c])); }
    for r in diff {
        let n = plain(r);
        let ctl = sorted([&r[1..n], &[c]].concat());
        multi(&mut fix, &ctl, r[n], u16::MAX);
    }
    if decorate { fix.push(raw(&[c])); }
    out.extend(reduce(&fix));
    out.extend_from_slice(&input[..3]);
    if reversed { out.reverse(); }
    out
}

pub(super) fn replica(rows: &[Row], h: u16, loan: i32) -> Vec<Row> {
    let mut zero = Sector::new(h, false);
    let mut one = Sector::new(h, true);
    let mut used = [false; 631];
    used[h as usize] = true;
    for &r in rows {
        zero.push(r);
        one.push(r);
        for &q in &r[1..=plain(r)] { used[q as usize] = true; }
    }
    let mut a = reduce(&zero.finish(false));
    let b = reduce(&one.finish(true));
    let diff = reduce(&a.iter().rev().chain(&b).copied().collect::<Vec<_>>());
    if diff.is_empty() {
        assert_eq!(loan, -1);
        return a;
    }
    assert!(reduce(&[diff.as_slice(), &diff].concat()).is_empty());
    for &r in &a {
        for &q in &r[1..=plain(r)] { used[q as usize] = true; }
    }
    let d = used.iter().position(|x| !x).unwrap() as u16;
    assert_eq!(loan, i32::from(d));
    let remap = reduce(&rows.iter().map(|&r| rename(r, h, d)).collect::<Vec<_>>());
    a.extend(remap.iter().rev());
    a.push(raw(&[h, d]));
    a.extend(remap);
    a.push(raw(&[h, d]));
    reduce(&a)
}

struct Echo {
    mid: usize,
    end: usize,
    ctl: u16,
    target: u16,
    host: u16,
    loan: u16,
}

fn echo(rows: &[Row], e: Echo) -> Vec<Row> {
    let split = e.ctl >= 631;
    let c = e.ctl % 631;
    let left = &rows[..e.mid];
    let rest = reduce(&[left, &rows[e.end..]].concat());
    let mut calc = Vec::new();
    for r in reduce(left) {
        let n = plain(r);
        let ctl: Vec<_> = r[1..n].iter().copied().filter(|&q| q != c)
            .map(|q| if q == e.host { c } else { q }).collect();
        calc.push(quantum(&ctl, if r[n] == e.host { c } else { r[n] }));
    }
    let center: Vec<_> = rows[e.mid..e.end].iter().map(|&r| {
        let n = plain(r);
        let controls: Vec<_> = r[1..n].iter().copied().filter(|&q| q != c)
            .map(|q| if q == e.host { c } else { q }).collect();
        quantum(&controls, e.loan)
    }).collect();
    let mut f = vec![raw(&[e.host, c]), raw(&[c])];
    f.extend_from_slice(&calc);
    f.extend(center);
    f.extend(calc.iter().rev());
    f.extend([raw(&[c]), raw(&[e.host, c])]);
    let t = quantum(&[c, e.loan], e.target);
    let mut out = f.clone();
    out.push(t);
    out.extend(f);
    out.push(t);
    if split {
        let other = out.clone();
        out.push(raw(&[c]));
        out.extend(other);
        out.push(raw(&[c]));
    }
    out.extend(rest);
    reduce(&out)
}

pub(super) fn park(rows: &[Row], args: &[i32]) -> Vec<Row> {
    match *args {
        [1, h, reverse] => frame(rows, h as u16, reverse != 0),
        [7, x, t] => serial(rows, x as u16, t as u16),
        [kind, mid, end, c, t, h, d, ..] => {
            let mut e = Echo { mid: mid as usize, end: end as usize, ctl: c as u16,
                               target: t as u16, host: h as u16, loan: d as u16 };
            if kind == 0 { return echo(rows, e); }
            assert_eq!(kind, 5);
            let reverse = args[8] != 0;
            let body: Vec<_> = iterate(rows, reverse).collect();
            let mut start = args[7] as usize;
            if reverse {
                (e.mid, e.end) = (rows.len() - e.end, rows.len() - e.mid);
                start = rows.len() - start;
            }
            let mut dependencies = [false; 631];
            dependencies[e.host as usize] = true;
            let mut cone = Vec::new();
            for &r in &body[..start] {
                let n = plain(r);
                if dependencies[r[n] as usize] {
                    cone.push(r);
                    for &q in &r[1..n] { dependencies[q as usize] = true; }
                }
            }
            let cone = reduce(&cone);
            e.mid = e.mid + cone.len() - start;
            e.end = e.end + cone.len() - start;
            let part = [cone.as_slice(), &body[start..]].concat();
            let mut out = body[..start].to_vec();
            out.extend(cone.into_iter().rev());
            out.extend(echo(&part, e));
            let mut out = reduce(&out);
            if reverse { out.reverse(); }
            out
        }
        _ => panic!("bad park window"),
    }
}

fn serial(rows: &[Row], x: u16, t: u16) -> Vec<Row> {
    let cross = raw(&[x, t]);
    let mut parity = rows.iter().filter(|&&r| r == cross).count() & 1 != 0;
    let mut first = Vec::new();
    let mut data = Vec::new();
    let mut last = Vec::new();
    if parity { first.push(cross); }
    for &r in rows {
        if r == cross {
            parity = !parity;
            continue;
        }
        let n = plain(r);
        assert!(!r[1..n].contains(&x) && !r[1..n].contains(&t));
        if r[n] == t {
            first.push(r);
        } else if r[n] == x {
            last.push(r);
            if parity {
                let mut g = r;
                g[n] = t;
                first.push(g);
            }
        } else {
            first.push(r);
            data.push(r);
            last.push(r);
        }
    }
    assert!(!parity);
    first.extend(data.into_iter().rev());
    first.extend(last);
    reduce(&first)
}
