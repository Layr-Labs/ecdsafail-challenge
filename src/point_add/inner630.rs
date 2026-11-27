//! Frozen transport, replica, gate-order and joint-code choices for ITEMs 4/12.
use super::{composition::varint, lzma, Row};

#[path = "inner630_donors.rs"]
mod donors;
#[path = "inner630_poly.rs"]
mod poly;

const NIL: u16 = u16::MAX;

fn plain(r: Row) -> usize {
    match r[0] {
        6 if r[2] == NIL => 1,
        8 if r[3] == NIL => 2,
        13 => 3,
        _ => panic!("non-NCT divider window {r:?}"),
    }
}

fn raw(g: &[u16]) -> Row {
    match *g {
        [t] => [6, t, NIL, NIL],
        [c, t] => [8, c, t, NIL],
        [a, b, t] => [13, a, b, t],
        _ => panic!("bad NCT ports {g:?}"),
    }
}

fn signed(d: &mut &[u8]) -> i32 {
    let v = varint(d) as i32;
    (v >> 1) ^ -(v & 1)
}

fn rewrite(
    rows: &[Row],
    d: &mut &[u8],
    mut rule: impl FnMut(usize, &[Row], &mut &[u8], &mut Vec<Row>),
) -> Vec<Row> {
    let count = varint(d);
    let mut out = Vec::with_capacity(rows.len().saturating_add(rows.len() / 16));
    let mut at = 0;
    for _ in 0..count {
        let a = at + varint(d);
        let b = a + varint(d);
        out.extend_from_slice(&rows[at..a]);
        rule(a, &rows[a..b], d, &mut out);
        at = b;
    }
    out.extend_from_slice(&rows[at..]);
    out
}

fn donor_windows(item: u16, rows: &[Row], d: &mut &[u8]) -> Vec<Row> {
    rewrite(rows, d, |at, body, d, out| {
        let count = varint(d);
        let kind = varint(d);
        let n = varint(d);
        let args: Vec<_> = (0..n).map(|_| signed(d)).collect();
        let v = match kind {
            0 => poly::park(body, &args),
            1 => donors::vsplit(body, &args),
            2 => donors::guard(body, &args, item),
            _ => panic!("unknown inner donor"),
        };
        assert_eq!(v.len(), count, "inner donor {kind} at {at}, {args:?}");
        out.extend(v);
    })
}

fn reordered(rows: &mut [Row], bytes: &[u8]) {
    let dec = lzma::decode(bytes).expect("inner gate order");
    let (&format, mut d) = dec.split_first().unwrap();
    let mut at = 0;
    let mut v = Vec::new();
    while !d.is_empty() {
        let a = at + varint(&mut d);
        let n = varint(&mut d);
        let r = &mut rows[a..a + n];
        v.clear();
        let mut prev = -1;
        for i in 0..n {
            let p = match format {
                0 => i as i32 + signed(&mut d),
                1 => prev + 1 + signed(&mut d),
                2 => {
                    let (next, rest) = d.split_at(2);
                    d = rest;
                    u16::from_le_bytes(next.try_into().unwrap()) as i32
                }
                _ => panic!("invalid inner gate order"),
            };
            prev = p;
            v.push(r[p as usize]);
        }
        r.copy_from_slice(&v);
        at = a + n;
    }
}

fn code(d: &mut &[u8]) -> Vec<Row> {
    let n = varint(d);
    let mut gates = Vec::with_capacity(n);
    let mut used = [false; 631];
    for _ in 0..n {
        let n = varint(d);
        let mut ports = Vec::with_capacity(n);
        for _ in 0..n {
            let q = varint(d);
            used[q] = true;
            ports.push(q as u16);
        }
        gates.push(ports);
    }
    let q = used.iter().position(|&x| !x).unwrap() as u16;
    let mut out = Vec::new();
    for g in gates {
        if let [a, b, c, t] = g[..] {
            let pair = [raw(&[a, b, q]), raw(&[q, c, t])];
            out.extend(pair);
            out.extend(pair);
        } else {
            out.push(raw(&g));
        }
    }
    out
}

pub fn generate(item: u16, stack: &[Row]) -> Vec<Row> {
    let (plans, orders) = if item == 4 {
        (include_bytes!("inner630-4.lzma").as_slice(), include_bytes!("inner630-order-4.lzma").as_slice())
    } else {
        (include_bytes!("inner630-12.lzma").as_slice(), include_bytes!("inner630-order-12.lzma").as_slice())
    };
    let data = lzma::decode(plans).expect("inner divider plan");
    let mut d = data.as_slice();
    let spliced = donor_windows(item, stack, &mut d);
    let switched = rewrite(&spliced, &mut d, |at, body, d, out| {
        let [c, x, y] = std::array::from_fn(|_| signed(d) as u16);
        let rev = signed(d) != 0;
        let perm = signed(d) != 0;
        let count = body.len().checked_add_signed(signed(d) as isize).unwrap();
        let v = poly::exchange(body, [c, x, y], rev, perm);
        assert_eq!(v.len(), count, "switch at {at}");
        out.extend(v);
    });
    drop(spliced);
    let framed = rewrite(&switched, &mut d, |at, body, d, out| {
        let h = signed(d) as u16;
        let rev = signed(d) != 0;
        let count = body.len().checked_add_signed(signed(d) as isize).unwrap();
        let v = poly::frame(body, h, rev);
        assert_eq!(v.len(), count, "frame at {at}");
        out.extend(v);
    });
    drop(switched);
    let mut replica = rewrite(&framed, &mut d, |at, body, d, out| {
        let h = signed(d) as u16;
        let loan = signed(d);
        let count = body.len().checked_add_signed(signed(d) as isize).unwrap();
        let v = poly::replica(body, h, loan);
        assert_eq!(v.len(), count, "replica at {at}");
        out.extend(v);
    });
    drop(framed);
    reordered(&mut replica, orders);
    let out = rewrite(&replica, &mut d, |_, body, d, out| {
        let gate = code(d);
        out.extend_from_slice(&gate);
        out.extend_from_slice(body);
        out.extend(gate.into_iter().rev());
    });
    assert!(d.is_empty());
    out
}
