//! Code K divider adapters with frozen signed physical ports and middle cuts.
use super::{lzma, Row};
use std::ops::Range;

#[path = "codek630_data.rs"]
mod data;

const NIL: u16 = u16::MAX;
const PUSH: Row = [15, 768, NIL, NIL];
const POP: Row = [16, NIL, NIL, NIL];

type Signed = i16;

struct Config {
    chain: &'static [u16],
    m: &'static [u16],
    w: &'static [u16],
    h: &'static [u16],
    exit_m: &'static [Signed],
    exit_k: &'static [u16],
    exit_h: &'static [u16],
    decode_cut: usize,
    stack_return: Range<usize>,
    inner_cuts: &'static [usize],
    group_cuts: &'static [usize],
    rank: &'static [Rank],
    edges: &'static [Edge],
    middle: &'static [Window],
}

struct Rank {
    branch: &'static [Signed],
    modulus: &'static [Signed],
    h: &'static [u16],
    v: &'static [u16],
}

struct Edge {
    modulus: &'static [Signed],
    h: [u16; 4],
}

struct Window {
    start: usize,
    end: usize,
    from: [u16; 2],
    to: [u16; 2],
    depth: Option<usize>,
}

fn x(q: u16) -> Row { [6, q, NIL, NIL] }
fn cx(a: u16, t: u16) -> Row { [8, a, t, NIL] }
fn ccx(a: u16, b: u16, t: u16) -> Row { [13, a, b, t] }
fn swap(a: u16, b: u16) -> [Row; 3] { [cx(a, b), cx(b, a), cx(a, b)] }
fn fredkin(e: u16, a: u16, b: u16) -> [Row; 3] { [cx(a, b), ccx(e, b, a), cx(a, b)] }
fn lane(q: Signed) -> u16 { if q < 0 { !q as u16 } else { q as u16 } }
fn sl(q: u16) -> Signed { q as Signed }
fn conditioned(q: u16, positive: bool) -> Signed { if positive { sl(q) } else { !sl(q) } }

fn mcx(g: &mut Vec<Row>, ctl: &[Signed], target: u16, pool: &[u16]) {
    let mut negative = ctl.iter().filter(|&&q| q < 0).map(|&q| x(lane(q)));
    g.extend(negative.by_ref());
    match ctl {
        [] => g.push(x(target)),
        [a] => g.push(cx(lane(*a), target)),
        [a, b] => g.push(ccx(lane(*a), lane(*b), target)),
        _ => {
            let c: Vec<_> = ctl.iter().copied().map(lane).collect();
            let d: Vec<_> = pool.iter().copied().filter(|q| *q != target && !c.contains(q))
                .take(c.len() - 2).collect();
            assert_eq!(d.len(), c.len() - 2);
            for _ in 0..2 {
                g.push(ccx(c[0], c[1], d[0]));
                for j in 1..d.len() { g.push(ccx(c[j + 1], d[j - 1], d[j])); }
                g.push(ccx(c[c.len() - 1], d[d.len() - 1], target));
                for j in (1..d.len()).rev() { g.push(ccx(c[j + 1], d[j - 1], d[j])); }
            }
        }
    }
    g.extend(ctl.iter().filter(|&&q| q < 0).map(|&q| x(lane(q))));
}

fn append_inverse(out: &mut Vec<Row>, rows: &[Row]) {
    out.extend(rows.iter().rev().copied());
}

fn digit(a: &[u16], b: &[u16], top: u16, control: Option<u16>, pool: &[u16]) -> Vec<Row> {
    assert_eq!(a.len(), b.len());
    let n = a.len();
    let mut g = Vec::with_capacity(24 * n);
    let last = n - 1;
    g.extend(b.iter().copied().map(x));
    for i in 1..n { g.push(cx(a[i], b[i])); }
    if let Some(e) = control { g.push(ccx(e, a[last], top)); }
    else { g.push(cx(a[last], top)); }
    for i in (1..last).rev() { g.push(cx(a[i], a[i + 1])); }
    for i in 0..last { g.push(ccx(b[i], a[i], a[i + 1])); }
    if let Some(e) = control {
        mcx(&mut g, &[sl(e), sl(a[last]), sl(b[last])], top, pool);
        g.push(cx(e, top));
    } else { g.extend([ccx(b[last], a[last], top), x(top)]); }
    let tail = |g: &mut Vec<Row>, i: usize| {
        if let Some(e) = control { mcx(g, &[sl(e), sl(top), sl(a[i])], b[i], pool); }
        else { g.push(ccx(top, a[i], b[i])); }
    };
    tail(&mut g, last);
    for i in (0..last).rev() {
        g.push(ccx(b[i], a[i], a[i + 1]));
        tail(&mut g, i);
    }
    for i in 1..last { g.push(cx(a[i], a[i + 1])); }
    for i in 1..n { g.push(cx(a[i], b[i])); }
    g.extend(b.iter().copied().map(x));
    g
}

fn division(m: &[u16], w: &[u16], h: usize) -> Vec<Row> {
    let n = m.len();
    let mut out = Vec::new();
    for j in (0..h).rev() {
        out.extend(digit(m, &w[j..j + n], w[j + n], None, &[]));
    }
    out
}

fn park_ring(chain: &[u16], m: &[u16], final_shift: u16, host: u16, dirty: &[u16]) -> Vec<Row> {
    let n = m.len();
    let carrier = chain[n];
    let mut net = Vec::new();
    for j in (2..n).rev() { net.extend(fredkin(m[n - j], carrier, chain[j])); }
    net.push(cx(carrier, chain[1]));
    mcx(&mut net, &[sl(chain[0]), sl(final_shift), sl(chain[1])], carrier, dirty);
    net.push(cx(carrier, chain[1]));
    let mut out = net.clone();
    out.extend(swap(carrier, host));
    append_inverse(&mut out, &net);
    out
}

fn rotate(g: &mut Vec<Row>, w: &[u16], d: usize, select: u16) {
    let mut order: Vec<_> = (0..w.len()).collect();
    for i in 0..w.len() {
        let want = (i + w.len() - d) % w.len();
        if order[i] != want {
            let j = order.iter().position(|&x| x == want).unwrap();
            g.extend(fredkin(select, w[i], w[j]));
            order.swap(i, j);
        }
    }
}

fn outside(exclude: &[u16]) -> Vec<u16> {
    (0..631).filter(|q| !exclude.contains(q)).collect()
}

fn kernels(cfg: &Config, first: bool) -> (Vec<Row>, Vec<Row>) {
    let (sh, host, select) = if first { ([626, 628, 629, 627], 510, 621) }
        else { ([243, 114, 245, 246], 45, 248) };
    let [a, b, c, d] = sh.map(sl);
    let [p, u, v] = [sl(cfg.chain[0]), sl(cfg.m[0]), sl(cfg.m[1])];
    let avoid = &[cfg.chain, cfg.w, cfg.h, &sh, cfg.m, &[select]].concat();
    let dirty = outside(avoid);
    let park = park_ring(cfg.chain, cfg.m, sh[3], host, &dirty);
    let mut eg = Vec::new();
    for (inputs, target) in [
        (&[p, d, !a, !b, !c][..], v),
        (&[p, d, v], b),
        (&[p, d, !v], u),
        (&[p, u, a], d),
        (&[p, u, !a, b], d),
        (&[p, u, !a, !b, c], d),
        (&[p, !u, v, !a, b, !c], d),
    ] { mcx(&mut eg, inputs, lane(target), &dirty); }
    eg.extend([ccx(lane(p), host, lane(d)), ccx(lane(p), lane(d), host)]);
    if first { eg.extend([x(626), x(629)]); }

    let mut wh = [cfg.w, cfg.h].concat();
    let mut g = park.clone();
    append_inverse(&mut g, &eg);
    append_inverse(&mut g, &division(cfg.m, &wh, cfg.h.len()));
    let last = wh.len() - 1;
    if !first {
        g.extend(swap(wh[last], wh[last - 1]));
        wh.swap(last, last - 1);
    }
    let bank = [dirty.as_slice(), &wh[..last]].concat();
    let mut ring = wh[..last].to_vec();
    ring.push(host);
    let n = cfg.w.len();
    for d in 2..=40 {
        let mut flag = Vec::new();
        for (j, idx, test) in [(d, d - 1, true), (d + 1, d, false)] {
            let mut c = vec![sl(cfg.m[n - j])];
            c.extend(cfg.m[n - j + 1..].iter().map(|&q| !sl(q)));
            c.push(conditioned(cfg.chain[idx], test));
            mcx(&mut flag, &c, select, &bank);
        }
        g.extend_from_slice(&flag);
        rotate(&mut g, &ring, d, select);
        for j in 0..ring.len() - d {
            append_inverse(&mut g, &digit(&cfg.chain[..d], &ring[j..j + d], ring[j + d], Some(select), &dirty));
        }
        append_inverse(&mut g, &flag);
    }
    g.extend(eg);
    append_inverse(&mut g, &park);
    if first { g.extend([ccx(2, 627, 385), ccx(385, 617, 257)]); }

    let mut h = cfg.exit_h.to_vec();
    let n = h.len();
    if !first { h.swap(n - 2, n - 1); }
    let flips: Vec<_> = cfg.exit_m.iter().filter(|&&q| q < 0).map(|&q| x(lane(q))).collect();
    let m: Vec<_> = cfg.exit_m.iter().copied().map(lane).collect();
    let mut dec = flips.clone();
    dec.extend(division(&m, &[cfg.exit_k, &h].concat(), n));
    append_inverse(&mut dec, &flips);
    if !first { dec.extend(swap(h[n - 1], h[n - 2])); }
    (g, dec)
}

fn rank_mcx(g: &mut Vec<Row>, controls: &[Signed], t: u16, dirty: &[u16]) {
    let mut unique = Vec::new();
    for &q in controls {
        if unique.contains(&!q) { return; }
        if !unique.contains(&q) { unique.push(q); }
    }
    assert!(unique.iter().all(|&q| lane(q) != t));
    mcx(g, &unique, t, dirty);
}

fn exchange(g: &mut Vec<Row>, terms: &[Vec<Signed>], host: u16, change: u16, dirty: &[u16]) {
    g.push(cx(host, change));
    for term in terms {
        let mut c = term.clone();
        c.push(sl(change));
        rank_mcx(g, &c, host, dirty);
    }
    g.push(cx(host, change));
}

fn rank_adapter(cfg: &Config, first: bool, slot: usize) -> (Vec<Row>, Vec<Row>) {
    let r = &cfg.rank[slot];
    let host = if first { 625 } else { 254 };
    let (pred, sel): (Vec<Vec<Signed>>, u16) = match (first, slot) {
        (true, 0) => (vec![vec![617, !256, !1], vec![617, 256, 626]], 258),
        (false, 0) => (vec![vec![239, !256, !507], vec![239, 256, 243]], 258),
        (true, 1) => (vec![vec![258]], 626),
        (true, 2) => (vec![vec![129]], 628),
        (true, 3) => (vec![vec![2, 627]], 510),
        (false, 1) => (vec![vec![!258]], 114),
        (false, 2) => (vec![vec![!257, 259]], 258),
        (false, 3) => (vec![vec![513, 246]], 515),
        _ => unreachable!(),
    };
    let tmp = if !first && slot == 2 { 243 } else { cfg.chain[2] };
    let m: Vec<_> = r.modulus.iter().copied().map(lane).collect();
    let pool = outside(&[cfg.chain, r.h, r.v, &[sel, tmp, host], &m].concat());
    let dirty = outside(&[host, sel]);
    let mut borrow = Vec::new();
    if first && slot == 3 {
        let ports = [vec![0, 623], (2..cfg.m.len() - 1).map(|i| 386 - i as u16).collect(), vec![sel]].concat();
        borrow = park_ring(cfg.chain, &ports, 627, sel, &pool);
    }
    let mut out = borrow.clone();
    if first && matches!(slot, 1 | 2) {
        let mut terms = vec![vec![]];
        terms.extend(pred.clone());
        exchange(&mut out, &terms, host, 257, &dirty);
    } else {
        let n = cfg.m.len();
        for j in 2..=40 {
            let mut prefix = vec![r.branch[n - j]];
            prefix.extend(r.branch[n - j + 1..n - 1].iter().map(|&q| !q));
            let mut terms = vec![prefix.clone()];
            for p in &pred { terms.push([prefix.as_slice(), p].concat()); }
            exchange(&mut out, &terms, host, cfg.chain[j + 1], &dirty);
        }
    }
    exchange(&mut out, &pred, host, tmp, &dirty);
    let mut flag = Vec::new();
    for term in &pred { rank_mcx(&mut flag, term, sel, &dirty); }
    out.extend_from_slice(&flag);
    let mut word = [r.v, r.h].concat();
    let n = word.len();
    if first { word[n - 1] = tmp; }
    else {
        let end = r.h[r.h.len() - 1];
        word[n - 2] = end;
        word[n - 1] = tmp;
        out.extend(fredkin(sel, end, tmp));
    }
    let flip: Vec<_> = r.modulus.iter().filter(|&&q| q < 0).map(|&q| x(lane(q))).collect();
    out.extend_from_slice(&flip);
    let mut increment = Vec::new();
    for j in (0..m.len()).rev() {
        let controls: Vec<_> = m[..j].iter().copied().map(sl).collect();
        rank_mcx(&mut increment, &controls, m[j], &dirty);
    }
    out.extend_from_slice(&increment);
    for j in 0..r.h.len() {
        append_inverse(&mut out, &digit(&m, &word[j..j + m.len()], word[j + m.len()], Some(sel), &pool));
    }
    append_inverse(&mut out, &increment);
    append_inverse(&mut out, &flip);
    append_inverse(&mut out, &flag);
    exchange(&mut out, &pred, host, tmp, &dirty);
    append_inverse(&mut out, &borrow);
    (out, borrow)
}

fn group_adapter(cfg: &Config, first: bool, side: usize) -> Vec<Row> {
    let e = &cfg.edges[side];
    let (flag, guard, bank) = if first { (628, 257, 50..59) } else { (114, 243, 60..69) };
    let bank: Vec<_> = bank.collect();
    let dirty = outside(&[]);
    let table = lzma::decode(include_bytes!("codek630-dyadic.lzma")).expect("Code K dyadic table");
    let mut bytes = table.into_iter();
    let groups = bytes.next().unwrap();
    let word = cfg.m.len();
    let mut out = Vec::new();
    for _ in 0..groups {
        let start = usize::from(bytes.next().unwrap());
        let end = usize::from(bytes.next().unwrap());
        let cases = bytes.next().unwrap();
        let mut routes = Vec::new();
        let mut selectors = Vec::new();
        for h in start..=end {
            let t = word - h;
            let j = h + 1;
            let low = h - h.min(4);
            let mut select = vec![e.modulus[t - 1]];
            select.extend(e.modulus[t..].iter().map(|&q| !q));
            let g: Vec<_> = (0..=h).map(|i| {
                let i = if i == 0 { j } else if i == j { 0 } else { i };
                cfg.chain[if i == 1 { j + 1 } else if i == j + 1 { 1 } else { i }]
            }).collect();
            let pins = [&[cfg.chain[j + 5], cfg.chain[j + 4], cfg.chain[j + 3], cfg.chain[j + 2]],
                        &g[low..]].concat();
            let mut head = Vec::new();
            mcx(&mut head, &select, guard, &dirty);
            routes.extend_from_slice(&head);
            for (a, &b) in pins.into_iter().zip(&bank) { routes.extend(fredkin(guard, a, b)); }
            append_inverse(&mut routes, &head);
            selectors.push((t, select, g[..low].to_vec()));
        }
        out.extend_from_slice(&routes);
        let addr = [&e.h[..3], &bank[..5 + start.min(4)]].concat();
        let top = e.h[3];
        for _ in 0..cases {
            let flags = bytes.next().unwrap();
            let count = u16::from_le_bytes([bytes.next().unwrap(), bytes.next().unwrap()]);
            let mut sel = Vec::new();
            for &(t, ref head, ref low_g) in &selectors {
                let mut c = head.clone();
                for i in 0..4 {
                    let q = e.modulus[t - 5 + i];
                    c.push(if flags >> i & 1 != 0 { q } else { !q });
                }
                if flags & 32 == 0 { mcx(&mut sel, &c, flag, &dirty); }
                c.extend(low_g.iter().map(|&q| !sl(q)));
                mcx(&mut sel, &c, flag, &dirty);
            }
            out.extend_from_slice(&sel);
            for _ in 0..count {
                let a = u16::from_le_bytes([bytes.next().unwrap(), bytes.next().unwrap()]);
                let b = u16::from_le_bytes([bytes.next().unwrap(), bytes.next().unwrap()]);
                let k = usize::from(bytes.next().unwrap());
                let d: Vec<_> = addr.iter().enumerate().filter_map(|(i, &q)|
                    (((a ^ b) >> i) & 1 != 0).then_some(cx(top, q))).collect();
                let mut ctrl = vec![sl(flag)];
                ctrl.extend(addr.iter().enumerate().skip(k)
                    .map(|(i, &q)| conditioned(q, (b >> i) & 1 != 0)));
                out.extend_from_slice(&d);
                mcx(&mut out, &ctrl, top, &dirty);
                append_inverse(&mut out, &d);
            }
            append_inverse(&mut out, &sel);
        }
        append_inverse(&mut out, &routes);
    }
    assert!(bytes.next().is_none());
    out
}

fn book(cut: usize, enabled: bool) -> Vec<Row> {
    let Some(&(_, host, ports)) = data::BOOKS.iter().find(|b| enabled && b.0 == cut) else { return vec![] };
    let mut flips = Vec::new();
    flips.extend(ports.iter().filter(|&&q| q < 0).map(|&q| x(lane(q))));
    let mut out = flips.clone();
    for h in 0..4 {
        let a = (1 << 6) | (h << 4);
        let b = 12 | h | (3 << 4);
        let dif: Vec<_> = ports.iter().enumerate().filter(|&(i, _)| (a ^ b) >> i & 1 != 0)
            .map(|(_, &q)| cx(host, lane(q))).collect();
        out.extend_from_slice(&dif);
        let controls: Vec<_> = ports.iter().enumerate().map(|(i, &q)| conditioned(lane(q), b >> i & 1 != 0)).collect();
        mcx(&mut out, &controls, host, &(32..96).collect::<Vec<_>>());
        append_inverse(&mut out, &dif);
    }
    append_inverse(&mut out, &flips);
    out
}

fn protect(out: &mut Vec<Row>, raw: &[Row], w: &Window, first: bool) {
    let [a, b] = w.from.map(|q| q % 1000);
    let inputs = w.from.map(|q| q >= 1000);
    let outputs = w.to.map(|q| q >= 1000);
    let left = book(w.start, first);
    let right = book(w.end, first);
    let mut used = [false; 631];
    for row in raw.iter().chain(&left).chain(&right) {
        for &q in &row[1..] {
            if q < 631 { used[q as usize] = true; }
        }
    }
    for q in [a, b].into_iter().chain(w.to.map(|q| q % 1000)) { used[q as usize] = true; }
    let idle: Vec<_> = (0..631).filter(|&q| !used[q as usize]).take(2).collect();
    let [d0, d1] = idle[..] else { panic!("Code K protected window needs two idle lanes") };
    let pool: Vec<_> = (0..631).filter(|&q| q != a && q != b).take(4).collect();
    let map = |q| if q == a { d0 } else if q == b { d1 } else { q };
    let mut ordered = w.to.map(|q| q % 1000);
    let mut perm = Vec::new();
    for (i, q) in [a, b].into_iter().enumerate() {
        let z = ordered[i];
        if q != z {
            perm.push((q, z));
            for p in &mut ordered { *p = if *p == q { z } else if *p == z { q } else { *p }; }
        }
    }
    let mut depth_out = w.depth;
    let mut has_scope = false;
    for r in raw {
        match r[0] {
            15 => { assert_eq!(depth_out, Some(0)); assert_eq!(*r, PUSH); depth_out = Some(1); has_scope = true; }
            16 => { assert_eq!(depth_out, Some(1)); depth_out = Some(0); has_scope = true; }
            _ => {}
        }
    }
    if has_scope && w.depth == Some(1) { out.push(POP); }
    out.extend_from_slice(&left);
    for (q, sign) in [a, b].into_iter().zip(inputs) {
        if sign { out.push(x(q)); }
    }
    let control = |out: &mut Vec<Row>, r: Row| {
        let [k, p, q, t] = r;
        let (p, q, t) = (map(p), map(q), map(t));
        match k {
            6 => out.push(cx(b, p)),
            8 => out.push(ccx(b, p, q)),
            13 => {
                let d2 = *pool[..3].iter().rev().find(|&&d| d != p && d != q && d != t).unwrap_or(&pool[3]);
                let pair = [ccx(b, p, d2), ccx(d2, q, t)];
                out.extend(pair);
                out.extend(pair);
            }
            15 | 16 => out.push(r),
            _ => panic!("protected Code K opcode {k}"),
        }
    };
    for sector in 0..4 {
        let bits = [sector & 1 != 0, sector & 2 != 0];
        let neg: Vec<_> = [d0, d1].into_iter().zip(bits).filter(|&(_, k)| !k).map(|(q, _)| x(q)).collect();
        let mut select = neg.clone();
        select.push(ccx(d0, d1, b));
        append_inverse(&mut select, &neg);
        out.extend_from_slice(&select);
        for ((q, sign), bit) in [d0, d1].into_iter().zip(inputs).zip(bits) {
            if sign != bit { out.push(cx(b, q)); }
        }
        for &r in left.iter().rev() { control(out, r); }
        if has_scope && w.depth == Some(1) { out.push(PUSH); }
        for &r in raw { control(out, r); }
        if has_scope && depth_out == Some(1) { out.push(POP); }
        for &r in &right { control(out, r); }
        for &(p, q) in &perm { out.extend(fredkin(b, map(p), map(q))); }
        for ((q, sign), bit) in [d0, d1].into_iter().zip(outputs).zip(bits) {
            if sign != bit { out.push(cx(b, q)); }
        }
        out.extend_from_slice(&select);
    }
    for (q, sign) in [a, b].into_iter().zip(outputs) {
        if sign { out.push(x(q)); }
    }
    for &(p, q) in perm.iter().rev() { out.extend(swap(p, q)); }
    append_inverse(out, &right);
    if has_scope && depth_out == Some(1) { out.push(PUSH); }
}

pub fn generate(item: u16, inner: Vec<Row>, stack: &[Row]) -> Vec<Row> {
    let first = item == 4;
    let cfg = data::config(item);
    assert_eq!(inner.len(), cfg.inner_cuts[12]);
    let (g, dec) = kernels(&cfg, first);
    let mut group = Vec::with_capacity(inner.len() + 5_000_000);
    let mut moved = Vec::new();
    for (phase, cut) in cfg.inner_cuts.windows(2).enumerate() {
        let [a, b] = [cut[0], cut[1]];
        match phase {
            3 | 5 => {
                let slot = (phase - 3) / 2 * 2;
                group.extend(rank_adapter(&cfg, first, slot).0);
                group.extend_from_slice(&inner[a..b]);
                let (tail, loan) = rank_adapter(&cfg, first, slot + 1);
                if first && phase == 5 {
                    moved.extend(loan.iter().rev().copied());
                    group.extend(tail[loan.len()..].iter().rev().copied());
                } else {
                    group.extend(tail.into_iter().rev());
                }
            }
            4 => {
                let l = cfg.group_cuts[0];
                let r = cfg.group_cuts[1];
                let passes = if first { swap(625, 32) } else { swap(242, 254) };
                group.extend_from_slice(&inner[a..l]);
                group.extend(group_adapter(&cfg, first, 0));
                group.extend(passes);
                group.extend_from_slice(&inner[l..r]);
                group.extend(passes);
                group.extend(group_adapter(&cfg, first, 1));
                group.extend_from_slice(&inner[r..b]);
            }
            6 => {
                group.extend_from_slice(&inner[a..b]);
                group.extend_from_slice(&moved);
            }
            7 => group.extend_from_slice(&g),
            10 => group.extend_from_slice(&stack[cfg.stack_return.clone()]),
            11 => {
                let c = cfg.decode_cut;
                group.extend_from_slice(&inner[a..c]);
                group.extend_from_slice(&dec);
                group.extend_from_slice(&inner[c..b]);
            }
            _ => group.extend_from_slice(&inner[a..b]),
        }
    }
    drop(inner);
    let mut out = Vec::with_capacity(group.len() + if first { 19_000_000 } else { 8_000_000 });
    let mut at = 0;
    for w in cfg.middle {
        out.extend_from_slice(&group[at..w.start]);
        protect(&mut out, &group[w.start..w.end], w, first);
        at = w.end;
    }
    out.extend_from_slice(&group[at..]);
    out
}
