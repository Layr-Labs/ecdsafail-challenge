//! Build-time pass pipeline (build-648, ported from build-646 / build-639).  `build()` = the parent's build (`build_parent`, unchanged)
//! followed by exact Toffoli-reducing passes chunk by chunk on 8-byte rows, then a streaming conversion back to the 56-byte `Op` list.
//!
//! Everything under `passes/` is copied byte for byte from the public compile passes (rotate / group / post: optimize.rs peephole.rs
//! values.rs ladder.rs clean.rs group.rs rotate.rs post.rs); this file is the only glue: ops -> rows (checked), chunk cuts,
//! condition-scope padding, step loop, rows -> ops.  The only lines that differ between the 646 and the 648 tree are marked TREE-SPECIFIC.
//!
//! Change the recipe here (RECIPE) and nowhere else.
use crate::circuit::Op;

#[allow(dead_code, unused)] #[path = "passes/optimize.rs"] mod base;
#[allow(dead_code, unused)] #[path = "passes/values.rs"] mod values;
#[allow(dead_code, unused)] #[path = "passes/ladder.rs"] mod ladder;
#[allow(dead_code, unused)] #[path = "passes/post.rs"] mod post;

pub type Row = [u16; 4];

// ---- TREE-SPECIFIC (648) ------------------------------------------------------------------------------------------
/// lane count of the circuit (ladder passes)
const WIDTH: usize = 648;
/// row -> op, the tree's own `operation`
#[inline] pub fn op_of(r: Row) -> Op { super::operation(r) }
/// op -> row: this tree has no op -> row function in mod.rs, so this is the inverse of `operation` (the same function as
/// `row_of` in the 646 tree and the `OpRows::get` code of rpeephole_hook.rs); every op is round-trip checked in
/// `rows_of_ops` before anything is changed.
#[inline] pub fn row_of(o: &Op) -> Row {
    use crate::circuit::{BitId, OperationType::*, NO_BIT};
    let bit = |x: BitId| if x == NO_BIT { 65535u16 } else { x.0 as u16 };
    let mut r = [0u16, 65535, 65535, 65535];
    match o.kind {
        Register => { r[0] = 1; r[1] = o.r_target.0 as u16; }
        AppendToRegister => { r[1] = o.r_target.0 as u16; if o.c_target != NO_BIT { r[0] = 18; r[2] = bit(o.c_target); } else { r[0] = 2; r[2] = o.q_target.0 as u16; } }
        BitInvert => { r[0] = 3; r[1] = bit(o.c_target); r[2] = bit(o.c_condition); }
        BitStore0 => { r[0] = 4; r[1] = bit(o.c_target); r[2] = bit(o.c_condition); }
        BitStore1 => { r[0] = 5; r[1] = bit(o.c_target); r[2] = bit(o.c_condition); }
        X => { r[0] = 6; r[1] = o.q_target.0 as u16; r[2] = bit(o.c_condition); }
        Z => { r[0] = 7; r[1] = o.q_target.0 as u16; r[2] = bit(o.c_condition); }
        CX => { r[0] = 8; r[1] = o.q_control1.0 as u16; r[2] = o.q_target.0 as u16; r[3] = bit(o.c_condition); }
        CZ => { r[0] = 9; r[1] = o.q_control1.0 as u16; r[2] = o.q_target.0 as u16; r[3] = bit(o.c_condition); }
        Hmr => { r[0] = 12; r[1] = o.q_target.0 as u16; r[2] = bit(o.c_target); }
        CCX => { r[0] = 13; r[1] = o.q_control2.0 as u16; r[2] = o.q_control1.0 as u16; r[3] = o.q_target.0 as u16; }
        PushCondition => { r[0] = 15; r[1] = bit(o.c_condition); }
        PopCondition => { r[0] = 16; }
        _ => panic!("row_of: unsupported operation"),
    }
    r
}
// ---- end TREE-SPECIFIC --------------------------------------------------------------------------------------------

/// One step of the per-chunk pipeline.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Step {
    /// rotate, group, post (the ladder-port driver's `rgp`, padded with its AUTOBAL rules), one run each
    Rgp,
}
/// The recipe applied to every chunk, in order.
pub const RECIPE: &[Step] = &[Step::Rgp];

/// chunk cut window (records): see `cuts_from`
pub const CUT_LO: usize = 20_000_000;
pub const CUT_HI: usize = 25_000_000;
const BLK: usize = 8192;
const PADBIT: u16 = 65533;
const N: u16 = u16::MAX;

/// Chunk boundaries of a body of `nb` rows (record indices, first 0, last nb).  Candidates are positions p where record
/// p-1 is a measurement (kind 12), or record p-1 is a pop (kind 16) and the condition depth is 0.  From the previous cut c
/// take the candidate in [c+LO, c+HI] with the smallest depth (earliest on ties); no candidate: plain cut at c+(LO+HI)/2.
pub fn cuts_from<I: Iterator<Item = Row>>(rows: I, nb: usize) -> Vec<usize> {
    let (mut depth, mut prev12, mut prev16) = (0i64, false, false);
    let mut cand: Vec<(usize, i64)> = Vec::new();
    let mut n = 0usize;
    for (i, r) in rows.enumerate() {
        if prev12 || (prev16 && depth == 0) { cand.push((i, depth)); }
        assert!(r[1] != 65533 && r[1] != 65534 && r[2] != 65533 && r[2] != 65534 && r[3] != 65533 && r[3] != 65534, "reserved bit in stream");
        if r[0] == 15 { depth += 1 } else if r[0] == 16 { depth -= 1 }
        prev12 = r[0] == 12; prev16 = r[0] == 16;
        n += 1;
    }
    assert!(n == nb);
    let mut cuts = vec![0usize];
    let mut c = 0usize;
    loop {
        if nb - c <= CUT_HI { break; }
        let mut best: Option<(i64, usize)> = None;
        for &(p, d) in &cand { if p >= c + CUT_LO && p <= c + CUT_HI && best.map_or(true, |b| d < b.0) { best = Some((d, p)); } }
        let p = match best { Some((_, p)) => p, None => c + (CUT_LO + CUT_HI) / 2 };
        cuts.push(p); c = p;
    }
    cuts.push(nb);
    cuts
}
pub fn cuts(body: &[Row]) -> Vec<usize> { cuts_from(body.iter().copied(), body.len()) }

/// pad open condition scopes (lead pushes on PADBIT, trailing pops); returns (padded rows, lead, trail)
fn pad(rows: Vec<Row>) -> (Vec<Row>, usize, usize) {
    let (mut d, mut mn) = (0i64, 0i64);
    for r in &rows { if r[0] == 15 { d += 1 } else if r[0] == 16 { d -= 1; mn = mn.min(d); } }
    let lead = (-mn) as usize; let end = (d + lead as i64) as usize;
    if lead > 0 { assert!(rows.iter().all(|r| !r[1..].contains(&PADBIT)), "padding bit occurs in chunk"); }
    let mut v: Vec<Row> = Vec::with_capacity(lead + rows.len() + end);
    v.extend(std::iter::repeat([15u16, PADBIT, N, N]).take(lead)); v.extend(rows);
    v.extend(std::iter::repeat([16u16, N, N, N]).take(end));
    (v, lead, end)
}
fn unpad(mut v: Vec<Row>, lead: usize, end: usize) -> Vec<Row> {
    for i in 0..lead { assert!(v[i] == [15, PADBIT, N, N]); }
    for i in 0..end { assert!(v[v.len() - 1 - i] == [16, N, N, N]); }
    v.truncate(v.len() - end); v.drain(..lead); v.shrink_to_fit(); v
}

fn rgp(rows: Vec<Row>) -> Vec<Row> {
    let (mut rows, lead, end) = pad(rows);
    { let mut c = ladder::rotate::Rotation::new(WIDTH, BLK); let mut o = Vec::with_capacity(rows.len());
      for r in rows.drain(..) { c.push(r, &mut |r| o.push(r)); } c.finish(&mut |r| o.push(r)); rows = o; }
    { let mut c = ladder::group::Group::new(WIDTH, BLK); let mut o = Vec::with_capacity(rows.len());
      for r in rows.drain(..) { c.push(r, &mut |r| o.push(r)); } c.finish(&mut |r| o.push(r)); rows = o; }
    { let mut c = post::Post::new(); let mut o = Vec::with_capacity(rows.len());
      for r in rows.drain(..) { c.push(r, &mut |r| o.push(r)); } c.finish(&mut |r| o.push(r)); rows = o; }
    unpad(rows, lead, end)
}

/// one chunk through the recipe
pub fn run_chunk(mut rows: Vec<Row>, recipe: &[Step]) -> Vec<Row> {
    for s in recipe { rows = match *s { Step::Rgp => rgp(rows) }; }
    rows.shrink_to_fit();
    rows
}

/// Chunks 0..nc, chunk i supplied by `take(i)` (called once per chunk, on a worker thread), through the recipe on the calling thread plus up to
/// `threads - 1` helpers (a refused spawn is not an error); the output chunks come back in chunk order, independent of the thread count.
pub fn run_chunks(nc: usize, take: &(dyn Fn(usize) -> Vec<Row> + Sync), recipe: &[Step], threads: usize) -> Vec<Vec<Row>> {
    let outs: Vec<std::sync::Mutex<Option<Vec<Row>>>> = (0..nc).map(|_| std::sync::Mutex::new(None)).collect();
    let next = std::sync::atomic::AtomicUsize::new(0);
    let work = || loop {
        let i = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        if i >= nc { break; }
        let o = run_chunk(take(i), recipe);
        *outs[i].lock().unwrap() = Some(o);
    };
    std::thread::scope(|sc| {
        // helpers: if the sandbox refuses a thread we simply stop spawning; the calling thread runs the same loop itself
        for _ in 1..threads.max(1).min(nc) {
            if std::thread::Builder::new().stack_size(64 << 20).spawn_scoped(sc, &work).is_err() { break; }
        }
        work();
    });
    outs.into_iter().map(|m| m.into_inner().unwrap().unwrap()).collect()
}

/// body rows -> cuts -> chunks (split off from the back, so the body vector shrinks as it is consumed) -> passes.
pub fn pipeline_rows(mut body: Vec<Row>, recipe: &[Step], threads: usize, log: bool) -> Vec<Vec<Row>> {
    let t0 = std::time::Instant::now();
    let cut = cuts(&body);
    let nc = cut.len() - 1;
    if log { eprintln!("[{:?}] {} chunks of {} rows", t0.elapsed(), nc, body.len()); }
    let mut ins: Vec<std::sync::Mutex<Option<Vec<Row>>>> = Vec::with_capacity(nc);
    for _ in 0..nc { ins.push(std::sync::Mutex::new(None)); }
    for k in (1..nc).rev() { let c = body.split_off(cut[k]); body.shrink_to_fit(); *ins[k].lock().unwrap() = Some(c); }
    *ins[0].lock().unwrap() = Some(body);
    let outs = run_chunks(nc, &|i| ins[i].lock().unwrap().take().unwrap(), recipe, threads);
    if log { eprintln!("[{:?}] passes done", t0.elapsed()); }
    outs
}

/// Row -> Op conversion of one chunk: the single place where rows become ops.
pub fn emit_chunk(ops: &mut Vec<Op>, rows: &[Row]) { ops.extend(rows.iter().map(|&r| op_of(r))); }

/// Production conversion.  `sel = None`: every chunk in order (what `finish` uses).  `sel = Some(list)` (test hook,
/// chunk indices): the same Vec<Op> of the full final capacity is allocated, but only the listed chunks are converted
/// (through the same `emit_chunk`) and the rest are dropped unconverted; the returned Vec holds just the selected ops.
pub fn convert_sel(chunks: Vec<Vec<Row>>, sel: Option<&[usize]>) -> Vec<Op> {
    let total: usize = chunks.iter().map(|c| c.len()).sum();
    let mut ops: Vec<Op> = Vec::with_capacity(total);
    for (k, c) in chunks.into_iter().enumerate() {
        if sel.map_or(true, |l| l.contains(&k)) { emit_chunk(&mut ops, &c); }
        drop(c);
    }
    if sel.is_none() { assert!(ops.len() == total); }
    ops
}
pub fn convert(chunks: Vec<Vec<Row>>) -> Vec<Op> { convert_sel(chunks, None) }

/// ops -> rows, every op checked: the tree's own `operation` must give the op back from its row.
pub fn rows_of_ops(ops: &[Op]) -> Vec<Row> {
    let mut rows: Vec<Row> = Vec::with_capacity(ops.len());
    for (i, o) in ops.iter().enumerate() {
        let r = row_of(o);
        assert!(op_of(r) == *o, "op {} does not round-trip through its row", i);
        rows.push(r);
    }
    rows
}

pub fn finish_impl(ops: Vec<Op>, sel: Option<&[usize]>, log: bool) -> Vec<Op> {
    let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    let t0 = std::time::Instant::now();
    let rows = rows_of_ops(&ops);
    drop(ops);
    if log { eprintln!("[{:?}] ops -> rows done, op list dropped ({} rows)", t0.elapsed(), rows.len()); }
    let chunks = pipeline_rows(rows, RECIPE, threads, log);
    let ops = convert_sel(chunks, sel);
    if log { eprintln!("[{:?}] rows -> ops done ({} ops)", t0.elapsed(), ops.len()); }
    ops
}

/// The parent's op list -> the final op list.
pub fn finish(ops: Vec<Op>) -> Vec<Op> { finish_impl(ops, None, false) }
