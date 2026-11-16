//! Schn stage (b788): schnaellstriicher single-sweep exact cancel/sandwich pass (mode 5) over the finished op list, chunked at measurement cuts,
//! 32-bit record fields (this stream has more than 65,535 classical bits).
use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId};
#[allow(dead_code, unused)]
#[path = "schnaell32.rs"]
mod schn;
type Row = [u32; 4];
const N: u32 = u32::MAX;
const PADBIT: u32 = 0xFFFF_FFF0;
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
        12 => { op.q_target = QubitId(a as u64); op.c_target = ob(b); Hmr }
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
    for i in 0..rows.len() { let r = rows[i]; e.push(r, &mut |x: &Row, _| { assert!(w <= i); assert!(x[0] != 14); rows[w] = *x; w += 1; }); }
    e.finish(&mut |x: &Row, _| { assert!(x[0] != 14); rows[w] = *x; w += 1; });
    rows.truncate(w);
    unpad(rows, lead, end)
}
pub fn schn_apply(ops: Vec<Op>) -> Vec<Op> {
    let rows: Vec<Row> = ops.iter().map(row_of).collect();
    for (o, r) in ops.iter().zip(rows.iter()) { assert!(op_of(*r) == *o, "roundtrip"); }
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
    let mut out: Vec<Op> = Vec::new();
    for m in outs { let c = m.into_inner().unwrap().unwrap(); out.extend(c.into_iter().map(op_of)); }
    out
}
