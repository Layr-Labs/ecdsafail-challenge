//! Original divider's mixed coordinates, exact width bookends and stack cuts.
use super::{composition::varint, lzma, Row};
use std::collections::BTreeMap;

const NIL: u16 = u16::MAX;

fn word32(input: &mut &[u8]) -> usize {
    let (v, rest) = input.split_at(4);
    *input = rest;
    u32::from_le_bytes(v.try_into().unwrap()) as usize
}

fn row(ports: &[u16], t: u16) -> Row {
    match ports {
        [] => [6, t, NIL, NIL],
        [a] => [8, *a, t, NIL],
        [a, b] => [13, *a, *b, t],
        _ => panic!("stack bookend requires a dirty loan"),
    }
}

fn read_gate(input: &mut &[u8]) -> Row {
    let arity = varint(input);
    let mut a = [0; 3];
    for q in &mut a[..arity] { *q = varint(input) as u16; }
    row(&a[..arity - 1], a[arity - 1])
}

fn arity(r: Row) -> usize {
    match r[0] { 6 if r[2] == NIL => 1, 8 if r[3] == NIL => 2, 13 => 3, _ => panic!("non-NCT stack window {r:?}") }
}

fn ladder(out: &mut Vec<Row>, c: &[u16], t: u16) {
    if c.len() <= 2 {
        out.push(row(c, t));
        return;
    }
    let d: Vec<_> = (506..540).filter(|&q| !c.contains(&q) && q != t).take(c.len() - 2).collect();
    for _ in 0..2 {
        out.push(row(&c[..2], d[0]));
        for j in 1..d.len() { out.push(row(&[c[j + 1], d[j - 1]], d[j])); }
        out.push(row(&[c[c.len() - 1], d[d.len() - 1]], t));
        for j in (1..d.len()).rev() { out.push(row(&[c[j + 1], d[j - 1]], d[j])); }
    }
}

fn code(a: u16, b: u16, ids: &[u16], signs: usize, inv: usize) -> Vec<Row> {
    let k = ids.len();
    let mask = (1 << k.min(2)) - 1;
    let mut truth: Vec<_> = (0..(1 << k)).map(|i| {
        let v = i ^ inv;
        v & mask == mask || (k == 3 && v & 4 != 0)
    }).collect();
    for j in 0..k {
        for v in 0..truth.len() {
            if v >> j & 1 != 0 { truth[v] ^= truth[v ^ (1 << j)]; }
        }
    }
    let mut out = Vec::new();
    if signs & 1 != 0 { out.push(row(&[], a)); }
    if a == b && (signs == 0 || signs == 3) { return out; }
    if a != b {
        if signs & 2 != 0 { out.push(row(&[], b)); }
        out.push(row(&[a], b));
    }
    for (v, yes) in truth.into_iter().enumerate() {
        if yes {
            let mut c: Vec<_> = ids.iter().enumerate().filter_map(|(j, &q)| (v >> j & 1 != 0).then_some(q)).collect();
            if a != b { c.push(b); }
            ladder(&mut out, &c, a);
        }
    }
    if a != b { out.push(row(&[a], b)); }
    out
}

type Polynomial = Vec<Vec<u16>>;

fn toggle(form: &mut Polynomial, mut term: Vec<u16>) {
    term.sort_unstable();
    term.dedup();
    if let Some(i) = form.iter().position(|v| *v == term) { form.remove(i); }
    else { form.push(term); }
}

fn fix(out: &mut Vec<Row>, ctl: &[u16], t: u16, forbidden: u16) {
    if ctl.len() < 3 { out.push(row(ctl, t)); }
    else {
        assert_eq!(ctl.len(), 3);
        let q = (509..).find(|&q| q != t && q != forbidden && !ctl.contains(&q)).unwrap();
        let pair = [row(&ctl[..2], q), row(&[q, ctl[2]], t)];
        out.extend(pair);
        out.extend(pair);
    }
}

fn frame(out: &mut Vec<Row>, body: &[Row], host: u16) {
    let mut p = Polynomial::new();
    for &r in body {
        let n = arity(r);
        let target = r[n];
        let c = &r[1..n];
        if target == host {
            toggle(&mut p, c.to_vec());
            continue;
        }
        if c.contains(&host) {
            for term in &p {
                assert!(!term.contains(&target));
                let mut v: Vec<_> = term.iter().copied().chain(c.iter().copied().filter(|&q| q != host)).collect();
                v.sort_unstable();
                v.dedup();
                fix(out, &v, target, host);
            }
        } else {
            let mut d = Polynomial::new();
            for v in &p {
                if v.contains(&target) {
                    toggle(&mut d, v.iter().copied().filter(|&q| q != target).chain(c.iter().copied()).collect());
                }
            }
            for v in d { toggle(&mut p, v); }
        }
        out.push(r);
    }
    for c in p { fix(out, &c, host, host); }
}

fn mixed(rows: Vec<Row>, data: &mut &[u8], codes: usize, frames: usize) -> Vec<Row> {
    let mut events: BTreeMap<usize, (Vec<Row>, Vec<Row>, Option<(usize, u16)>)> = BTreeMap::new();
    for _ in 0..codes {
        let l = varint(data);
        let h = l + varint(data);
        let a = varint(data) as u16;
        let b = varint(data) as u16;
        let flags = varint(data);
        let k = flags >> 2 & 3;
        let ids: Vec<_> = (0..k).map(|_| varint(data) as u16).collect();
        let inv = flags >> 5;
        let open = code(a, b, &ids, flags & 3, inv);
        let mut flip = 0;
        for r in &rows[l..h] {
            if r[0] == 6 {
                for (j, &q) in ids.iter().enumerate() { if r[1] == q { flip ^= 1 << j; } }
            }
        }
        let close = code(a, b, &ids, flags & 3, inv ^ flip);
        events.entry(l).or_default().1.extend(open);
        let end = events.entry(h).or_default();
        if flags & 16 != 0 { end.0.extend(close.into_iter().rev()); }
        else { end.1.extend(close.into_iter().rev()); }
    }
    for _ in 0..frames {
        let l = varint(data);
        let h = l + varint(data);
        let q = varint(data) as u16;
        assert!(events.entry(l).or_default().2.replace((h, q)).is_none());
    }
    let mut out = Vec::with_capacity(rows.len() + 250_000);
    let mut at = 0;
    for (cut, (early, normal, window)) in events {
        assert!(cut >= at);
        out.extend_from_slice(&rows[at..cut]);
        out.extend(early);
        out.extend(normal);
        at = cut;
        if let Some((end, q)) = window {
            frame(&mut out, &rows[cut..end], q);
            at = end;
        }
    }
    out.extend_from_slice(&rows[at..]);
    out
}

pub fn generate(item: u16, parent: Vec<Row>) -> Vec<Row> {
    let cfg = if item == 4 { include_bytes!("stack630-4.lzma").as_slice() }
        else { include_bytes!("stack630-12.lzma").as_slice() };
    let bytes = lzma::decode(cfg).expect("decode original divider stack plans");
    let mut d = bytes.as_slice();
    let source_len = word32(&mut d);
    let code_count = word32(&mut d);
    let frame_count = word32(&mut d);
    let width_count = word32(&mut d);
    let cut_count = word32(&mut d);
    let final_rows = word32(&mut d);
    assert_eq!(source_len, parent.len());
    let wrapped = mixed(parent, &mut d, code_count, frame_count);
    let mut at = 0;
    let mut width = Vec::with_capacity(wrapped.len() + 150_000);
    for _ in 0..width_count {
        let a = at + varint(&mut d);
        let b = a + varint(&mut d);
        width.extend_from_slice(&wrapped[at..a]);
        let entry = varint(&mut d);
        width.extend((0..entry).map(|_| read_gate(&mut d)));
        width.extend_from_slice(&wrapped[a..b]);
        let exit = varint(&mut d);
        width.extend((0..exit).map(|_| read_gate(&mut d)));
        at = b;
    }
    width.extend_from_slice(&wrapped[at..]);
    drop(wrapped);
    let mut at = 0;
    let mut output = Vec::with_capacity(final_rows);
    for _ in 0..cut_count {
        let a = at + varint(&mut d);
        let b = a + varint(&mut d);
        output.extend_from_slice(&width[at..a]);
        at = b;
    }
    output.extend_from_slice(&width[at..]);
    assert_eq!(output.len(), final_rows);
    assert!(d.is_empty());
    output
}
