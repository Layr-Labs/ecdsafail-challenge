//! ITEM 2/10 kernel replacement, nested carrier routing and exact cleanup.
use super::{composition::varint, lzma, ureg630::{donor, multi, Frame}, Row};
use std::collections::BTreeMap;

#[path = "lowerr630_walk.rs"]
mod walk;

const NIL: u16 = u16::MAX;
const LANE_COUNT: u16 = 631;
const PUSH: Row = [15, 768, NIL, NIL];
const POP: Row = [16, NIL, NIL, NIL];

fn u16word(data: &mut &[u8]) -> u16 {
    let (word, tail) = data.split_at(2);
    *data = tail;
    u16::from_le_bytes(word.try_into().unwrap())
}

fn u32word(data: &mut &[u8]) -> usize {
    let (word, tail) = data.split_at(4);
    *data = tail;
    u32::from_le_bytes(word.try_into().unwrap()) as usize
}

fn rows(data: &mut &[u8]) -> Vec<Row> {
    let n = u16word(data);
    (0..n).map(|_| std::array::from_fn(|_| u16word(data))).collect()
}

fn ports(data: &mut &[u8], n: usize) -> Vec<i32> {
    (0..n).map(|_| (u16word(data) as i16).into()).collect()
}

struct Walk {
    start: usize,
    end: usize,
    ports: Vec<i32>,
    entry: Vec<Row>,
    exit: Vec<Row>,
}

impl Walk {
    fn parse(data: &mut &[u8]) -> Self {
        let start = u32word(data);
        let end = u32word(data);
        let n = usize::from(u16word(data));
        Self { start, end, ports: ports(data, n), entry: rows(data), exit: rows(data) }
    }

    fn emit(&self, out: &mut Vec<Row>, item10: bool, reverse: bool) {
        let (n, real) = if item10 { (129, 1) } else { (127, 2) };
        let (l, r) = self.ports[..2 * (n + 1)].split_at(n + 1);
        let p = &self.ports[2 * (n + 1)..];
        let mut tags = p[3..3 + real].to_vec();
        tags.resize(7, -1);
        let cfg = walk::Cfg {
            n, kind: walk::Kind::Inner { real }, tags: 4,
            l: [l, &l[n..]].concat(), r: [r, &r[n..]].concat(),
            sign: p[0], fire: p[1], tst: p[2], ws_tag: tags, aux: -1,
            loan: p[3 + real..].to_vec(),
        };
        let mut gate = Vec::new();
        walk::SHIFT_CAP.store(26, std::sync::atomic::Ordering::Relaxed);
        walk::run(&cfg, &mut |r| gate.push(r)).unwrap();
        if reverse { gate.reverse(); }
        out.push(POP);
        out.extend_from_slice(&self.entry);
        out.push(PUSH);
        out.extend(donor(&gate));
        out.push(POP);
        out.extend_from_slice(&self.exit);
        out.push(PUSH);
    }
}

fn x(q: u16) -> Row { [6, q, NIL, NIL] }
fn cx(a: u16, t: u16) -> Row { [8, a, t, NIL] }
fn ccx(a: u16, b: u16, t: u16) -> Row { [13, a, b, t] }

fn append_inverse(out: &mut Vec<Row>, start: usize, end: usize) {
    for i in (start..end).rev() { out.push(out[i]); }
}

fn stash_add(out: &mut Vec<Row>, a: &[u16], b: &[u16], subtract: bool) {
    assert_eq!(a.len(), b.len());
    let begin = out.len();
    let carry = |i| if i == 0 { 630 } else { a[i - 1] };
    for i in 0..a.len() - 1 {
        out.extend([cx(a[i], b[i]), cx(a[i], carry(i)), ccx(carry(i), b[i], a[i])]);
    }
    let j = a.len() - 1;
    out.extend([ccx(627, a[j], b[j]), ccx(627, carry(j), b[j])]);
    for i in (0..j).rev() {
        out.extend([ccx(carry(i), b[i], a[i]), ccx(627, carry(i), b[i]),
                    cx(a[i], carry(i)), cx(a[i], b[i])]);
    }
    if subtract { out[begin..].reverse(); }
}

fn stash_digit(out: &mut Vec<Row>, t: &[u16], j: usize) {
    let d: Vec<_> = std::iter::once(627)
        .chain((1..631).filter(|&q| q != 627 && !t.contains(&q)))
        .take(j + 1).collect();
    let term = |i: usize| {
        let (h, q) = (t[128 - i], t[j - i]);
        if h == q { cx(h, d[i]) } else { ccx(h, q, d[i]) }
    };
    let branch = |i: usize| [cx(d[i + 1], d[i]), ccx(t[128 - i], d[i + 1], d[i])];
    for signal in [true, false] {
        let start = out.len();
        for i in (1..=j).rev() {
            if signal { out.push(term(i)); }
            if i < j { out.extend(branch(i)); }
        }
        let end = out.len();
        if signal { out.push(term(0)); }
        if j > 0 { out.extend(branch(0)); }
        append_inverse(out, start, end);
    }
}

fn stash_output(out: &mut Vec<Row>, stash: &[i32], t: &[i32], w: &[i32]) {
    let sign_start = out.len();
    let mut polarize = |p: &[i32]| -> Vec<u16> {
        p.iter().map(|&q| {
            if q < 0 { out.push(x(!q as u16)); !q as u16 } else { q as u16 }
        }).collect()
    };
    let mut stash = polarize(&stash[..256]);
    let t = polarize(t);
    let w = polarize(w);
    let sign_end = out.len();
    stash.extend([129, 620]);
    let start = out.len();
    for j in 0..129 {
        let a = out.len();
        stash_digit(out, &t, j);
        let b = out.len();
        let low = &stash[j..];
        let high = &low[129..];
        let pad = &t[..high.len()];
        stash_add(out, &[&w[..], pad].concat(), low, true);
        stash_add(out, pad, high, false);
        append_inverse(out, a, b);
    }
    let end = out.len();
    out.push(x(620));
    multi(out, &[129, 620, 625], 545, 1, 0);
    out.extend([x(620), x(129), cx(625, 545)]);
    multi(out, &[129, 620, 545], 625, 1, 0);
    out.extend([cx(625, 545), x(129)]);
    append_inverse(out, start, end);
    append_inverse(out, sign_start, sign_end);
    out.extend([[7, 625, 64001, NIL], [7, 545, 64002, NIL],
                [4, 64001, NIL, NIL], [4, 64002, NIL, NIL]]);
}

type Carrier = [u16; 3];
const EMPTY: Carrier = [LANE_COUNT, LANE_COUNT, 0];

struct CarrierCode {
    pin: u16,
    digits: [usize; 3],
    slots: [[Carrier; 2]; 8],
    threshold: usize,
}

impl CarrierCode {
    fn new(pin: u16, item10: bool) -> Self {
        Self { pin, digits: if item10 { [627, 628, 629] } else { [245, 246, 247] },
               slots: [[EMPTY; 2]; 8], threshold: if item10 { 4 } else { 2 } }
    }

    fn flip(&self, out: &mut Vec<Row>, controls: &[i16], target: u16) {
        let neg: Vec<_> = controls.iter().filter_map(|&q| (q < 0).then_some(!q as u16)).collect();
        let controls: Vec<_> = controls.iter().map(|&q| (if q < 0 { !q } else { q }) as u16).collect();
        out.extend(neg.iter().copied().map(x));
        multi(out, &controls, target, 0, self.pin);
        out.extend(neg.into_iter().map(x));
    }

    fn toggle_class(&self, out: &mut Vec<Row>, place: &[u16; 631], mask: u8, base: &[i16], target: u16) {
        let mut best = None::<Vec<Row>>;
        for polarity in 0..8 {
            let mut f: [u8; 8] = std::array::from_fn(|g| (mask >> (g ^ polarity)) & 1);
            for bit in [1, 2, 4] {
                for g in 0..8 {
                    if g & bit != 0 { f[g] ^= f[g ^ bit]; }
                }
            }
            let mut trial = Vec::new();
            for (g, &coefficient) in f.iter().enumerate() {
                if coefficient == 0 { continue; }
                let mut controls = base.to_vec();
                for (b, &digit) in self.digits.iter().enumerate() {
                    if g >> b & 1 != 0 {
                        let q = place[digit] as i16;
                        controls.push(if polarity >> b & 1 != 0 { !q } else { q });
                    }
                }
                self.flip(&mut trial, &controls, target);
            }
            if best.as_ref().map_or(true, |b| trial.len() < b.len()) {
                best = Some(trial);
            }
        }
        out.extend(best.unwrap());
    }

    fn value(&self, out: &mut Vec<Row>, place: &[u16; 631], carrier: Carrier, mask: u8, base: &[i16], target: u16) {
        for q in [carrier[0], carrier[1]] {
            if q == LANE_COUNT { continue; }
            let mut c = base.to_vec();
            c.push(place[q as usize] as i16);
            self.toggle_class(out, place, mask, &c, target);
        }
        if carrier[2] != 0 { self.toggle_class(out, place, mask, base, target); }
    }

    fn code(&self, out: &mut Vec<Row>, frame: &Frame, high: usize, reverse: bool) {
        let place = &frame.place;
        let mut seq = Vec::new();
        let h = place[high];
        let [a, b, c] = self.digits.map(|d| place[d]);
        for group in 8 - self.threshold..8 {
            self.toggle_class(&mut seq, place, 1 << group, &[h as i16], place[self.slots[group][1][0] as usize]);
        }
        if self.threshold & 4 != 0 { seq.push(cx(h, c)); }
        if self.threshold & 2 != 0 { seq.extend([ccx(h, b, c), cx(h, b)]); }
        for group in 8 - self.threshold..8 {
            let lo = group + self.threshold - 8;
            let delta = group ^ lo;
            let pivot = delta.trailing_zeros() as usize;
            let d = [a, b, c];
            let mut controls = vec![h as i16];
            for j in 0..3 {
                if j == pivot { continue; }
                let mut val = lo >> j & 1;
                if delta >> j & 1 != 0 {
                    seq.push(cx(d[pivot], d[j]));
                    val ^= lo >> pivot & 1;
                }
                controls.push(if val == 1 { d[j] as i16 } else { !(d[j] as i16) });
            }
            let r = self.slots[group][1];
            for q in [r[0], r[1]] {
                if q == LANE_COUNT { continue; }
                let mut ctrl = controls.clone();
                ctrl.push(place[q as usize] as i16);
                self.flip(&mut seq, &ctrl, d[pivot]);
            }
            if r[2] != 0 { self.flip(&mut seq, &controls, d[pivot]); }
            for j in 0..3 {
                if j != pivot && delta >> j & 1 != 0 { seq.push(cx(d[pivot], d[j])); }
            }
        }
        for group in self.threshold..8 {
            let v = self.slots[group][0];
            self.toggle_class(&mut seq, place, 1 << group, &[h as i16], place[v[0] as usize]);
            self.value(&mut seq, place, v, 1 << group, &[], h);
        }
        if reverse { seq.reverse(); }
        frame.emit_unscoped(out, &seq);
    }

    fn transfer(&mut self, out: &mut Vec<Row>, frame: &Frame, moves: &[(usize, Carrier)]) {
        let mut masks = BTreeMap::<[u16; 10], u8>::new();
        for &(flags, new) in moves {
            let group = flags & 7;
            let slot = flags >> 3 & 1;
            let old = self.slots[group][slot];
            if flags & 32 == 0 && new[0] != old[0] {
                let guard = if slot == 1 { self.slots[group][0] } else { EMPTY };
                let key = [slot as u16, old[0], old[1], old[2], new[0], new[1], new[2],
                           guard[0], guard[1], guard[2]];
                *masks.entry(key).or_default() |= 1 << group;
            }
            self.slots[group][slot] = new;
        }
        let place = &frame.place;
        let mut seq = Vec::new();
        for ([_, from, p1, inv1, to, p2, inv2, car, pred, neg], mask) in masks {
            let old = place[from as usize];
            let to = place[to as usize];
            let align = |seq: &mut Vec<Row>| {
                if p1 != p2 {
                    for p in [p1, p2] {
                        if p != LANE_COUNT { seq.push(cx(place[p as usize], to)); }
                    }
                }
                if inv1 != inv2 { seq.push(x(to)); }
            };
            align(&mut seq);
            seq.push(cx(old, to));
            if car != LANE_COUNT {
                self.value(&mut seq, place, [car, pred, neg], mask, &[to as i16], old);
            } else {
                self.toggle_class(&mut seq, place, mask, &[to as i16], old);
            }
            seq.push(cx(old, to));
            align(&mut seq);
        }
        if !seq.is_empty() { frame.emit_unscoped(out, &seq); }
    }
}

fn lower(input: Vec<Row>, mut data: &[u8], item10: bool) -> Vec<Row> {
    let pin = u16word(&mut data);
    let n = u16word(&mut data);
    let mut route = (0..n).map(|_| {
        let pos = u32word(&mut data);
        let to = u16word(&mut data) as usize;
        let pred = u16word(&mut data) as usize;
        let (&inv, next) = data.split_first().unwrap();
        data = next;
        (pos, to, pred, inv != 0)
    }).collect::<Vec<_>>().into_iter().peekable();
    let n = u16word(&mut data);
    let spans: Vec<_> = (0..n).map(|_| (u32word(&mut data), u32word(&mut data), u16word(&mut data) as usize)).collect();
    let reverse = if item10 { u32word(&mut data) } else { usize::MAX };
    if item10 { data = &data[2 * (258 + 129 + 129)..]; }
    let n = u32word(&mut data);
    let mut pos = 0;
    let mut moves = (0..n).map(|_| {
        pos += varint(&mut data);
        let flags = varint(&mut data);
        let to = varint(&mut data) as u16;
        let p = (varint(&mut data) as u16) ^ LANE_COUNT;
        (pos, flags, [to, p, (flags >> 4 & 1) as u16])
    }).collect::<Vec<_>>().into_iter().peekable();
    assert!(data.is_empty());
    let mut code = CarrierCode::new(pin, item10);
    let mut frame = Frame::new(pin as usize);
    let mut out = Vec::with_capacity(input.len() + 4_000_000);
    let mut span = 0;
    let mut binding = Vec::new();
    for (pos, r) in input.into_iter().enumerate() {
        binding.clear();
        while let Some((_, flags, car)) = moves.next_if(|v| v.0 == pos) {
            binding.push((flags, car));
        }
        if !binding.is_empty() { code.transfer(&mut out, &frame, &binding); }
        let current = spans.get(span);
        if let Some(&(_, _, high)) = current.filter(|s| s.0 == pos) {
            assert!(route.peek().is_some_and(|p| (p.0, p.1) == (pos, high)));
            code.code(&mut out, &frame, high, false);
        }
        if let Some((_, to, pred, inv)) = route.next_if(|v| v.0 == pos) {
            frame.change(&mut out, to, pred, inv);
        }
        if let Some(&(_, _, high)) = current.filter(|s| s.1 == pos) {
            code.code(&mut out, &frame, high, true);
            span += 1;
        }
        if pos == reverse {
            assert_eq!(frame.hole, 629);
            let upper = [242, 243, 244, 245, 246, 247, 248, 500, 501, 502, 503, 543, 621, 548, 547, 626]
                .map(|q| frame.place[q] as i16);
            let mut correction = Vec::new();
            code.flip(&mut correction, &upper, frame.place[630]);
            frame.emit_unscoped(&mut out, &correction);
        }
        for &q in &r[1..1 + super::composition::arity(r[0])] {
            assert_ne!(usize::from(q), frame.hole, "hidden lane at input row {pos}, {r:?}");
        }
        frame.row(&mut out, r);
    }
    assert!(route.next().is_none() && moves.next().is_none() && span == spans.len());
    frame.close(&mut out);
    out
}

#[path = "lowerr630_peephole.rs"]
mod peephole;

fn input_tape(name: &str, parent: Vec<Row>) -> (Vec<Row>, Vec<u8>, usize, bool) {
    let item10 = match name { "s05" => false, "s21" => true, _ => panic!("unknown ITEM block {name}") };
    let bytes = if item10 { include_bytes!("lowerr630-10.lzma").as_slice() }
        else { include_bytes!("lowerr630-2.lzma").as_slice() };
    let data = lzma::decode(bytes).expect("decode ITEM route");
    let mut table = data.as_slice();
    let walks: Vec<_> = (0..if item10 { 2 } else { 3 }).map(|_| Walk::parse(&mut table)).collect();
    let mut out = Vec::with_capacity(parent.len());
    let mut at = 0;
    for (j, walk) in walks.iter().enumerate() {
        if item10 && j == 1 {
            out.extend_from_slice(&parent[at..36_709_796]);
            out.extend([POP, cx(625, 129), cx(545, 129), ccx(625, 545, 129),
                        [12, 625, 64001, NIL], [12, 545, 64002, NIL],
                        cx(129, 625), cx(625, 129), PUSH]);
            out.extend_from_slice(&parent[36_709_796..51_757_800]);
            out.push(POP);
            let mut wires = table;
            let _pin = u16word(&mut wires);
            let n = u16word(&mut wires);
            wires = &wires[usize::from(n) * 9..];
            let n = u16word(&mut wires);
            wires = &wires[usize::from(n) * 10 + 4..];
            let stash = ports(&mut wires, 258);
            let t = ports(&mut wires, 129);
            let w = ports(&mut wires, 129);
            stash_output(&mut out, &stash, &t, &w);
            out.push(PUSH);
            at = 51_757_800;
        }
        out.extend_from_slice(&parent[at..walk.start]);
        walk.emit(&mut out, item10, j + 1 == walks.len());
        at = walk.end;
    }
    out.extend_from_slice(&parent[at..]);
    drop(parent);
    let offset = data.len() - table.len();
    (out, data, offset, item10)
}

pub fn check_input(name: &str, parent: Vec<Row>) -> Vec<Row> {
    input_tape(name, parent).0
}

pub fn check_router(name: &str, parent: Vec<Row>) -> Vec<Row> {
    let (input, table, offset, item10) = input_tape(name, parent);
    lower(input, &table[offset..], item10)
}

pub fn generate(name: &str, parent: Vec<Row>) -> Vec<Row> {
    let (input, table, offset, item10) = input_tape(name, parent);
    let mut routed = lower(input, &table[offset..], item10);
    if item10 {
        for r in &mut routed {
            let n = super::composition::arity(r[0]);
            for q in &mut r[1..1 + n] {
                assert_ne!(*q, 129);
                if *q == 248 { *q = 129; }
            }
        }
    }
    peephole::compact(routed)
}
