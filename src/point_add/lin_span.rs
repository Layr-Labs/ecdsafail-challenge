//! O9: exact linear-span rewrite rows for our Skywalk stream.
//!
//! A row names a CCX `t ^= a*b` whose product equals, on every state reachable at that op (under its own
//! condition), the XOR of other live wires `w1 ^ .. ^ wk` (plus a constant). The CCX is replaced by the CX chain
//! `CX(w1 -> t) .. CX(wk -> t)` and an `X(t)` for the constant, under the CCX's own condition. Every row was
//! proved by a z3 miter over a window of the stream that starts at an anchor whose wire values are the sound
//! global value-numbering forms (affine over atoms; product atoms bound to the AND of their operand forms); the
//! flipped-constant negative control of every row is SAT. Rows that were only measured are never admitted.
//!
//! Rows are keyed per cap to the exact post-MABSORB stream they were proved on: the header binds the op count and
//! a 64-bit FNV-1a digest of the whole stream, and each row asserts its CCX operands. Any upstream change to the
//! stream fails the build here (re-run the O9 census `scratch/r23/O9/o9-linspan.sh` on the new stream).
//!
//! Row lines: `idx c1 c2 t cst w1,w2,..|-` (whitespace separated, `-` = no wires).

use crate::circuit::{Op, OperationType, QubitId};

/// FNV-1a over every op's seven fields (the ops.bin record layout).
pub(crate) fn stream_digest(ops: &[Op]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    let mut eat = |x: u64| {
        for b in x.to_le_bytes() {
            h ^= b as u64;
            h = h.wrapping_mul(0x0000_0100_0000_01b3);
        }
    };
    for o in ops {
        eat(o.kind as u64);
        eat(o.q_control2.0);
        eat(o.q_control1.0);
        eat(o.q_target.0);
        eat(o.c_target.0);
        eat(o.c_condition.0);
        eat(o.r_target.0);
    }
    h
}

pub(crate) struct Row {
    pub idx: usize,
    pub c1: u64,
    pub c2: u64,
    pub t: u64,
    pub cst: bool,
    pub ws: Vec<u64>,
}

pub(crate) fn parse(text: &str) -> (usize, u64, Vec<Row>) {
    let mut key: Option<(usize, u64)> = None;
    let mut rows = Vec::new();
    for l in text.lines() {
        let l = l.trim();
        if l.is_empty() {
            continue;
        }
        if let Some(h) = l.strip_prefix("# stream ") {
            let mut n = None;
            let mut d = None;
            for f in h.split_whitespace() {
                if let Some(v) = f.strip_prefix("ops=") {
                    n = Some(v.parse::<usize>().unwrap());
                }
                if let Some(v) = f.strip_prefix("fnv=") {
                    d = Some(u64::from_str_radix(v, 16).unwrap());
                }
            }
            key = Some((n.expect("ops="), d.expect("fnv=")));
            continue;
        }
        if l.starts_with('#') {
            continue;
        }
        let f: Vec<&str> = l.split_whitespace().collect();
        assert_eq!(f.len(), 6, "O9_LINSPAN row: {l}");
        let ws = if f[5] == "-" { vec![] } else { f[5].split(',').map(|x| x.parse().unwrap()).collect() };
        rows.push(Row {
            idx: f[0].parse().unwrap(),
            c1: f[1].parse().unwrap(),
            c2: f[2].parse().unwrap(),
            t: f[3].parse().unwrap(),
            cst: f[4] == "1",
            ws,
        });
    }
    let (n, d) = key.expect("O9_LINSPAN: rows file has no '# stream ops=.. fnv=..' header");
    (n, d, rows)
}

fn rows_for_cap(cap: usize) -> &'static str {
    match cap {
        1159 => include_str!("skywalk_data/o9_linspan_q1159.txt"),
        1158 => include_str!("skywalk_data/o9_linspan_q1158.txt"),
        1157 => include_str!("skywalk_data/o9_linspan_q1157.txt"),
        _ => panic!("O9_LINSPAN: no proved rows for cap {cap} (set O9_LINSPAN=0 or run the census)"),
    }
}

/// Replace every row's CCX by its CX chain. Panics unless the stream is exactly the one the rows were proved on.
pub(crate) fn apply_rows(mut ops: Vec<Op>, text: &str) -> Vec<Op> {
    let (n, d, mut rows) = parse(text);
    assert!(
        ops.len() == n && stream_digest(&ops) == d,
        "O9_LINSPAN: rows keyed to stream ops={n} fnv={d:016x}, got ops={} fnv={:016x}; re-run the census",
        ops.len(),
        stream_digest(&ops)
    );
    rows.sort_by(|a, b| b.idx.cmp(&a.idx));
    for w in rows.windows(2) {
        assert!(w[0].idx > w[1].idx, "O9_LINSPAN: duplicate row {}", w[0].idx);
    }
    let count = rows.len();
    for r in rows {
        let o = ops[r.idx];
        assert!(
            o.kind == OperationType::CCX
                && o.q_target.0 == r.t
                && ((o.q_control1.0 == r.c1 && o.q_control2.0 == r.c2) || (o.q_control1.0 == r.c2 && o.q_control2.0 == r.c1)),
            "O9_LINSPAN mismatch at {}",
            r.idx
        );
        let mut rep = Vec::with_capacity(r.ws.len() + 1);
        for &q in &r.ws {
            assert!(q != r.t, "O9_LINSPAN: wire equals target at {}", r.idx);
            rep.push(Op { kind: OperationType::CX, q_control1: QubitId(q), q_target: o.q_target, c_condition: o.c_condition, ..Op::empty() });
        }
        if r.cst {
            rep.push(Op { kind: OperationType::X, q_target: o.q_target, c_condition: o.c_condition, ..Op::empty() });
        }
        ops.splice(r.idx..r.idx + 1, rep);
    }
    eprintln!("O9_LINSPAN rows={count} stream_fnv={d:016x}");
    ops
}

pub(crate) fn apply(ops: Vec<Op>, cap: usize) -> Vec<Op> {
    apply_rows(ops, rows_for_cap(cap))
}
