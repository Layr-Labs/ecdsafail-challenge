//! Selected virtual splits and guard packet transformations.
use super::{plain, raw, Row};
use std::collections::{BTreeMap, BTreeSet};

const NIL: u16 = u16::MAX;

fn product(c: &[u16], t: u16, omit: u16) -> Vec<Row> {
    if c.len() < 3 { return vec![raw(&[c, &[t]].concat())]; }
    let d: Vec<_> = (0..631).filter(|&q| q != t && q != omit && !c.contains(&q)).take(c.len() - 2).collect();
    let mut out = vec![raw(&[c[0], c[1], d[0]])];
    for j in 1..d.len() { out.push(raw(&[c[j + 1], d[j - 1], d[j]])); }
    out.push(raw(&[c[c.len() - 1], d[d.len() - 1], t]));
    for j in (1..d.len()).rev() { out.push(raw(&[c[j + 1], d[j - 1], d[j]])); }
    out.extend(out.clone());
    out
}

fn encoding(args: &[i32]) -> Vec<Row> {
    let (method, values) = (args[0], &args[1..]);
    let v: Vec<_> = values.iter().map(|&x| x as u16).collect();
    let mut e = Vec::new();
    if matches!(method, 0 | 3 | 4) {
        let [c, sense, h, a] = v[..4].try_into().unwrap();
        let (h, hs, a, ass) = (h / 2, h & 1, a / 2, a & 1);
        if method == 3 {
            if h != a { e.extend([raw(&[a, h]), raw(&[c, h, a]), raw(&[a, h])]); }
            if hs != 0 { e.push(raw(&[h])); }
            if hs != ass { e.push(raw(&[c, h])); }
            return e;
        }
        if sense == 0 { e.push(raw(&[c])); }
        e.extend([raw(&[h, a]), raw(&[c, a, h]), raw(&[h, a])]);
        if sense == 0 { e.push(raw(&[c])); }
        if (if sense == 0 { hs } else { ass }) != 0 { e.push(raw(&[a])); }
        if hs != ass { e.push(raw(&[c, a])); }
        if method == 4 {
            let (ph, pa) = (values[4], values[5]);
            if ph == pa {
                if ph >= 0 { e.push(raw(&[ph as u16, a])); }
            } else {
                for (side, pred) in [(sense, ph), (1 - sense, pa)] {
                    if pred < 0 { continue; }
                    if side == 0 { e.push(raw(&[pred as u16, a])); }
                    e.push(raw(&[c, pred as u16, a]));
                }
            }
        }
        return e;
    }
    let h = v[0] / 2;
    let p = &v[1..];
    if v[0] & 1 != 0 { e.push(raw(&[h])); }
    if method == 2 {
        for pair in p.chunks_exact(2).rev() {
            let [u, w] = [pair[0] / 2, pair[1] / 2];
            if pair[0] & 1 != 0 { e.push(raw(&[u])); }
            if pair[1] & 1 != 0 { e.push(raw(&[w])); }
            e.extend([raw(&[u, w]), raw(&[u, h]), raw(&[w, h, u]), raw(&[u, h])]);
        }
    } else {
        assert_eq!(method, 1);
        for &q in p {
            if q & 1 != 0 { e.push(raw(&[q / 2])); }
            e.push(raw(&[h, q / 2]));
        }
        e.extend(product(&p.iter().map(|q| q / 2).collect::<Vec<_>>(), h, NIL));
    }
    e
}

fn wires(row: Row) -> Vec<u16> {
    let n = plain(row);
    let mut v = row[1..=n].to_vec();
    v[..n - 1].sort_unstable();
    v
}

fn specialize(rows: &[Row], c: u16, bit: bool, from: u16, to: u16) -> BTreeMap<usize, Vec<u16>> {
    let mut seen: Vec<(usize, Vec<u16>)> = Vec::new();
    for (i, &r) in rows.iter().enumerate() {
        let mut g = wires(r);
        let t = *g.last().unwrap();
        assert_ne!(c, t);
        if g.contains(&c) {
            if !bit { continue; }
            g.retain(|&q| q != c);
        }
        let mut erased = false;
        for j in (seen.len().saturating_sub(12)..seen.len()).rev() {
            let old = &seen[j].1;
            if g == *old {
                seen.remove(j);
                erased = true;
                break;
            }
            if old[..old.len() - 1].contains(&t) || g[..g.len() - 1].contains(old.last().unwrap()) { break; }
        }
        if !erased { seen.push((i, g)); }
    }
    seen.into_iter().map(|(i, mut g)| {
        if bit && from != to {
            for q in &mut g { if *q == from { *q = to; } }
        }
        (i, g)
    }).collect()
}

pub(super) fn vsplit(rows: &[Row], args: &[i32]) -> Vec<Row> {
    let e = encoding(args);
    let mut out = Vec::with_capacity(rows.len() + 2 * e.len());
    let [kind, c, sense, h, a] = if args.len() >= 5 { args[..5].try_into().unwrap() }
        else { [args[0], 0, 0, 0, 0] };
    let (c, h, a) = (c as u16, (h / 2) as u16, (a / 2) as u16);
    if matches!(kind, 0 | 4) && sense == 0 {
        let rename = |q| if q == h { a } else if q == a { h } else { q };
        let mut en = e[1..4].to_vec();
        for &r in &e[5..] {
            let n = plain(r);
            en.push(raw(&r[1..=n].iter().copied().map(rename).collect::<Vec<_>>()));
        }
        out.extend_from_slice(&en);
        for &r in rows {
            out.push(raw(&wires(r).into_iter().map(rename).collect::<Vec<_>>()));
        }
        out.extend(en.into_iter().rev());
        return out;
    }
    out.extend_from_slice(&e);
    if kind == 3 {
        let left = specialize(rows, c, false, h, a);
        let right = specialize(rows, c, true, h, a);
        let positions: BTreeSet<_> = left.keys().chain(right.keys()).copied().collect();
        let mut negative = false;
        for i in positions {
            let cases = [left.get(&i), right.get(&i)];
            if cases[0] == cases[1] {
                out.push(raw(cases[0].unwrap()));
                continue;
            }
            for (s, g) in cases.into_iter().enumerate() {
                if let Some(g) = g {
                    let neg = s == 0;
                    if negative != neg { out.push(raw(&[c])); negative = neg; }
                    let controls = [&[c][..], &g[..g.len() - 1]].concat();
                    out.extend(product(&controls, *g.last().unwrap(), h));
                }
            }
        }
        if negative { out.push(raw(&[c])); }
    } else {
        out.extend_from_slice(rows);
    }
    out.extend(e.into_iter().rev());
    out
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Gate {
    target: u16,
    controls: Vec<u16>,
}

impl Gate {
    fn new(row: Row) -> Self {
        let mut ports = wires(row);
        Self { target: ports.pop().unwrap(), controls: ports }
    }

    fn names(&self, q: u16) -> bool {
        self.target == q || self.controls.contains(&q)
    }

    fn commute(&self, b: &Self) -> bool {
        !self.controls.contains(&b.target) && !b.controls.contains(&self.target)
    }

    fn derivative(a: &Self, b: &Self) -> Option<Self> {
        let mut controls = a.controls.clone();
        controls.extend(b.controls.iter().copied().filter(|&q| q != a.target));
        controls.sort_unstable();
        controls.dedup();
        assert!(!controls.contains(&b.target));
        (controls.len() <= 4).then_some(Self { target: b.target, controls })
    }
}

fn push(packet: &mut Vec<Gate>, gate: &Gate) {
    for (i, prev) in packet.iter().enumerate().rev() {
        if prev == gate { packet.remove(i); return; }
        if !prev.commute(gate) { break; }
    }
    packet.push(gate.clone());
}

fn propagate(packet: &mut Vec<Gate>, gate: &Gate, h: u16) {
    if gate.names(h) {
        push(packet, gate);
        return;
    }
    if packet.iter().all(|p| p.commute(gate)) { return; }
    let mut next = Vec::new();
    for v in packet.iter() {
        let a = v.controls.contains(&gate.target);
        let b = gate.controls.contains(&v.target);
        let extra = match (a, b) {
            (true, false) => Gate::derivative(gate, v),
            (false, true) => Gate::derivative(v, gate),
            _ => None,
        };
        if (a || b) && extra.is_none() {
            push(&mut next, gate);
            push(&mut next, v);
            push(&mut next, gate);
        } else {
            push(&mut next, v);
            if let Some(g) = extra { push(&mut next, &g); }
        }
    }
    *packet = next;
}

fn packet(rows: &[Row], h: u16, reversed: bool, item: u16) -> Vec<Row> {
    let mut suffix = Vec::new();
    for i in 0..rows.len() {
        let row = rows[if reversed { rows.len() - 1 - i } else { i }];
        propagate(&mut suffix, &Gate::new(row), h);
    }
    let d = if item == 4 { 514 } else { 50 };
    let mut lowered = Vec::new();
    for gate in suffix {
        let t = gate.target;
        match gate.controls.as_slice() {
            [a, b, c] => {
                let pair = [raw(&[*a, *b, d]), raw(&[d, *c, t])];
                lowered.extend(pair);
                lowered.extend(pair);
            }
            [a, b, c, e] => {
                let d1 = d + 1;
                let group = [raw(&[*a, *b, d]), raw(&[*c, d, d1]), raw(&[*e, d1, t]), raw(&[*c, d, d1])];
                lowered.extend(group);
                lowered.extend(group);
            }
            c => lowered.push(raw(&[c, &[t]].concat())),
        }
    }
    let retained = rows.iter().copied().filter(|&r| !r[1..=plain(r)].contains(&h));
    if reversed {
        lowered.reverse();
        lowered.extend(retained);
        lowered
    } else {
        retained.chain(lowered).collect()
    }
}

pub(super) fn guard(rows: &[Row], args: &[i32], item: u16) -> Vec<Row> {
    let kind = args[0];
    let h = args[1] as u16;
    if kind == 9 { return packet(rows, h, args[2] != 0, item); }
    let mut code = Vec::new();
    if kind == 4 {
        assert_eq!(args[2] as usize, args.len() - 3);
        for &mask in &args[3..] {
            let a = mask & 1023;
            let b = mask >> 10;
            if a == 0 { code.push(raw(&[h])); }
            else if b == 0 { code.push(raw(&[(a - 1) as u16, h])); }
            else { code.push(raw(&[(a - 1) as u16, (b - 1) as u16, h])); }
        }
    } else {
        let (k, c) = (args[2] as u16, args[3] as u16);
        if kind == 8 {
            let p: Vec<_> = args[4..8].iter().map(|&q| q as u16).collect();
            let d = (0..631).find(|&q| q != h && q != k && q != c && !p.contains(&q)).unwrap();
            for (s, &q) in p.iter().enumerate() {
                let flip = args[8 + s] != 0;
                if q == h && !flip { continue; }
                if s & 1 == 0 { code.push(raw(&[c])); }
                if s & 2 == 0 { code.push(raw(&[k])); }
                if q != h {
                    let cx = raw(&[h, q]);
                    let g = raw(&[c, k, d]);
                    let v = raw(&[d, q, h]);
                    code.extend([cx, g, v, g, v, cx]);
                }
                if flip { code.push(raw(&[c, k, h])); }
                if s & 2 == 0 { code.push(raw(&[k])); }
                if s & 1 == 0 { code.push(raw(&[c])); }
            }
        } else {
            let flags = args[4];
            for (i, q) in [h, k, c].into_iter().enumerate() {
                if flags >> i & 1 != 0 { code.push(raw(&[q])); }
            }
            if kind == 7 { code.extend([raw(&[h, k]), raw(&[h, c]), raw(&[k, c, h])]); }
            else {
                assert_eq!(kind, 5);
                code.extend([raw(&[h, k]), raw(&[c, k, h]), raw(&[h, k])]);
            }
        }
    }
    let mut out = Vec::with_capacity(rows.len() + 2 * code.len());
    out.extend_from_slice(&code);
    out.extend_from_slice(rows);
    out.extend(code.into_iter().rev());
    out
}
