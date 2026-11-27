//! Schn stage (b788): schnaellstriicher single-sweep exact cancel/sandwich pass (mode 5) over the finished op list, chunked at measurement cuts,
//! 32-bit record fields (this stream has more than 65,535 classical bits).
use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId};
#[allow(dead_code, unused)]
#[path = "schnaell32.rs"]
mod schn;
type Row = [u32; 4];
const N: u32 = u32::MAX;
const PADBIT: u32 = 0xFFFF_FFF0;
// Adapted for the 797 family (adds R, Neg, CCZ pass-through and conditional CCX), exactness-preserving:
// R = Hmr with ignored result: engine kind 12 on a scratch bit nobody reads, marked in r[3].
// Neg = barrier-only record on scratch qubit 1023 (engine kind 12; writes its condition bit, conservative).
// Conditional CCX = three consecutive kind-12 barrier rows, one per qubit, rebuilt after the pass (adjacency asserted).
const DUMMYBIT: u32 = 1_999_999;
const RMARK: u32 = 0xFFFF_FF01;
const NEGMARK: u32 = 0xFFFF_FF02;
const NEGMARKU: u32 = 0xFFFF_FF03;
const CC1: u32 = 0xFFFF_FF11;
const CC2: u32 = 0xFFFF_FF12;
const CC3: u32 = 0xFFFF_FF13;
const NEGQ: u32 = 1023;
fn bit(x: BitId) -> u32 { if x.0 == u64::MAX { N } else { assert!(x.0 < 0xFFFF_0000); x.0 as u32 } }
fn ob(x: u32) -> BitId { if x == N { BitId(u64::MAX) } else { BitId(x as u64) } }
fn row_of(o: &Op) -> Row {
    use OperationType::*;
    let mut r = [0u32, N, N, N];
    match o.kind {
        Register => { r[0] = 1; r[1] = o.r_target.0 as u32; }
        AppendToRegister => { r[1] = o.r_target.0 as u32; if o.c_target.0 != u64::MAX { r[0] = 18; r[2] = bit(o.c_target); } else { r[0] = 2; r[2] = o.q_target.0 as u32; } }
        BitInvert => { r[0] = 3; r[1] = bit(o.c_target); r[2] = bit(o.c_condition); }
        BitStore0 => { r[0] = 4; r[1] = bit(o.c_target); r[2] = bit(o.c_condition); }
        BitStore1 => { r[0] = 5; r[1] = bit(o.c_target); r[2] = bit(o.c_condition); }
        X => { r[0] = 6; r[1] = o.q_target.0 as u32; r[2] = bit(o.c_condition); }
        Z => { r[0] = 7; r[1] = o.q_target.0 as u32; r[2] = bit(o.c_condition); }
        CX => { r[0] = 8; r[1] = o.q_control1.0 as u32; r[2] = o.q_target.0 as u32; r[3] = bit(o.c_condition); }
        CZ => { r[0] = 9; r[1] = o.q_control1.0 as u32; r[2] = o.q_target.0 as u32; r[3] = bit(o.c_condition); }
        Hmr => { r[0] = 12; r[1] = o.q_target.0 as u32; r[2] = bit(o.c_target); }
        Swap => { r[0] = 10; r[1] = o.q_control1.0 as u32; r[2] = o.q_target.0 as u32; r[3] = bit(o.c_condition); }
        CCX => { r[0] = 13; r[1] = o.q_control2.0 as u32; r[2] = o.q_control1.0 as u32; r[3] = o.q_target.0 as u32; }
        PushCondition => { r[0] = 15; r[1] = bit(o.c_condition); }
        PopCondition => { r[0] = 16; }
        R => { assert!(o.c_condition.0 == u64::MAX && o.c_target.0 == u64::MAX && o.q_control1.0 == u64::MAX); r[0] = 12; r[1] = o.q_target.0 as u32; r[2] = DUMMYBIT; r[3] = RMARK; }
        Neg => { r[0] = 12; r[1] = NEGQ; if o.c_condition.0 == u64::MAX { r[2] = DUMMYBIT; r[3] = NEGMARKU; } else { r[2] = bit(o.c_condition); r[3] = NEGMARK; } }
        CCZ => { r[0] = 14; r[1] = o.q_control2.0 as u32; r[2] = o.q_control1.0 as u32; r[3] = o.q_target.0 as u32; }
        k => panic!("row_of: unsupported {:?}", k as u32),
    }
    r
}
fn op_of(r: Row) -> Op {
    use OperationType::*;
    let mut op = Op::empty();
    let (a, b, c) = (r[1], r[2], r[3]);
    op.kind = match r[0] {
        1 => { op.r_target = RegisterId(a as u64); Register }
        2 => { op.r_target = RegisterId(a as u64); op.q_target = QubitId(b as u64); AppendToRegister }
        18 => { op.r_target = RegisterId(a as u64); op.c_target = ob(b); AppendToRegister }
        3 | 4 | 5 => { op.c_target = ob(a); op.c_condition = ob(b); if r[0] == 3 { BitInvert } else if r[0] == 4 { BitStore0 } else { BitStore1 } }
        6 | 7 => { op.q_target = QubitId(a as u64); op.c_condition = ob(b); if r[0] == 6 { X } else { Z } }
        8 | 9 => { op.q_control1 = QubitId(a as u64); op.q_target = QubitId(b as u64); op.c_condition = ob(c); if r[0] == 8 { CX } else { CZ } }
        12 if c == NEGMARK || c == NEGMARKU => { assert!(a == NEGQ); if c == NEGMARK { op.c_condition = ob(b); } else { assert!(b == DUMMYBIT); } Neg }
        12 if c == RMARK => { assert!(b == DUMMYBIT); op.q_target = QubitId(a as u64); R }
        12 => { op.q_target = QubitId(a as u64); op.c_target = ob(b); Hmr }
        14 => { op.q_control2 = QubitId(a as u64); op.q_control1 = QubitId(b as u64); op.q_target = QubitId(c as u64); CCZ }
        10 => { op.q_control1 = QubitId(a as u64); op.q_target = QubitId(b as u64); op.c_condition = ob(c); Swap }
        13 => { op.q_control2 = QubitId(a as u64); op.q_control1 = QubitId(b as u64); op.q_target = QubitId(c as u64); CCX }
        15 => { op.c_condition = ob(a); PushCondition }
        16 => PopCondition,
        k => panic!("op_of {}", k),
    };
    op
}
fn cuts(rows: &[Row]) -> Vec<usize> {
    const LO: usize = 20_000_000; const HI: usize = 25_000_000;
    let nb = rows.len();
    let (mut depth, mut p12, mut p16) = (0i64, false, false);
    let mut cand: Vec<(usize, i64)> = Vec::new();
    for (i, r) in rows.iter().enumerate() {
        if p12 || (p16 && depth == 0) { cand.push((i, depth)); }
        if r[0] == 15 { depth += 1 } else if r[0] == 16 { depth -= 1 }
        p12 = r[0] == 12; p16 = r[0] == 16;
    }
    let mut cu = vec![0usize]; let mut c = 0usize;
    loop {
        if nb - c <= HI { break; }
        let mut best: Option<(i64, usize)> = None;
        for &(p, d) in &cand { if p >= c + LO && p <= c + HI && best.map_or(true, |b| d < b.0) { best = Some((d, p)); } }
        let p = match best { Some((_, p)) => p, None => c + (LO + HI) / 2 };
        cu.push(p); c = p;
    }
    cu.push(nb); cu
}
fn pad(rows: Vec<Row>) -> (Vec<Row>, usize, usize) {
    let (mut d, mut mn) = (0i64, 0i64);
    for r in &rows { if r[0] == 15 { d += 1 } else if r[0] == 16 { d -= 1; mn = mn.min(d); } }
    let lead = (-mn) as usize; let end = (d + lead as i64) as usize;
    let mut v: Vec<Row> = Vec::with_capacity(lead + rows.len() + end);
    v.extend(std::iter::repeat([15u32, PADBIT, N, N]).take(lead)); v.extend(rows);
    v.extend(std::iter::repeat([16u32, N, N, N]).take(end));
    (v, lead, end)
}
fn unpad(mut v: Vec<Row>, lead: usize, end: usize) -> Vec<Row> {
    for i in 0..lead { assert!(v[i] == [15, PADBIT, N, N]); }
    for i in 0..end { assert!(v[v.len() - 1 - i] == [16, N, N, N]); }
    v.truncate(v.len() - end); v.drain(..lead); v
}
fn schn_chunk(rows: Vec<Row>) -> Vec<Row> {
    let (mut rows, lead, end) = pad(rows);
    let mut e = schn::Eng::new(1 << 22, 5, 6); let mut w = 0usize;
    for i in 0..rows.len() { let r = rows[i]; e.push(r, &mut |x: &Row, _| { assert!(w <= i); rows[w] = *x; w += 1; }); }
    e.finish(&mut |x: &Row, _| { rows[w] = *x; w += 1; });
    rows.truncate(w);
    unpad(rows, lead, end)
}
pub fn schn_apply(ops: Vec<Op>) -> Vec<Op> {
    let mut rows: Vec<Row> = Vec::with_capacity(ops.len() + 16);
    let mut n14_in = 0usize;
    for o in ops.iter() {
        if o.kind == OperationType::CCX && o.c_condition.0 != u64::MAX {
            let cb = bit(o.c_condition);
            rows.push([12, o.q_control2.0 as u32, cb, CC1]); rows.push([12, o.q_control1.0 as u32, cb, CC2]); rows.push([12, o.q_target.0 as u32, cb, CC3]);
        } else {
            let r = row_of(o); assert!(op_of(r) == *o, "roundtrip {:?}", o); if r[0] == 14 { n14_in += 1; } rows.push(r);
        }
    }
    drop(ops);
    let cut = cuts(&rows); let nc = cut.len() - 1;
    let mut rows = rows; let mut chunks: Vec<Vec<Row>> = Vec::new();
    for k in (1..nc).rev() { chunks.push(rows.split_off(cut[k])); }
    chunks.push(rows); chunks.reverse();
    let outs: Vec<std::sync::Mutex<Option<Vec<Row>>>> = (0..nc).map(|_| std::sync::Mutex::new(None)).collect();
    let ins: Vec<std::sync::Mutex<Option<Vec<Row>>>> = chunks.into_iter().map(|c| std::sync::Mutex::new(Some(c))).collect();
    let next = std::sync::atomic::AtomicUsize::new(0);
    let threads: usize = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1).min(8);
    let work = || loop {
        let i = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        if i >= nc { break; }
        let inp = ins[i].lock().unwrap().take().unwrap();
        *outs[i].lock().unwrap() = Some(schn_chunk(inp));
    };
    std::thread::scope(|sc| { for _ in 1..threads.min(nc) { std::thread::Builder::new().stack_size(64 << 20).spawn_scoped(sc, &work).unwrap(); } work(); });
    let mut all: Vec<Row> = Vec::new();
    for m in outs { let c = m.into_inner().unwrap().unwrap(); all.extend(c); }
    let n14_out = all.iter().filter(|r| r[0] == 14).count();
    assert!(n14_in == n14_out, "CCZ count changed {} -> {}", n14_in, n14_out);
    let mut out: Vec<Op> = Vec::with_capacity(all.len());
    let mut i = 0usize;
    while i < all.len() {
        let r = all[i];
        if r[0] == 12 && r[3] == CC1 {
            let (r2, r3) = (all[i + 1], all[i + 2]);
            assert!(r2[0] == 12 && r2[3] == CC2 && r3[0] == 12 && r3[3] == CC3 && r2[2] == r[2] && r3[2] == r[2], "conditional CCX triple broken");
            let mut op = Op::empty(); op.kind = OperationType::CCX; op.q_control2 = QubitId(r[1] as u64); op.q_control1 = QubitId(r2[1] as u64); op.q_target = QubitId(r3[1] as u64); op.c_condition = ob(r[2]);
            out.push(op); i += 3;
        } else { assert!(!(r[0] == 12 && (r[3] == CC2 || r[3] == CC3)), "stray CCX triple row"); out.push(op_of(r)); i += 1; }
    }
    out
}
