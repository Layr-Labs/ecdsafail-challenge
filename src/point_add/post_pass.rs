//! Build-time pass pipeline (build-638).  `build()` = the 638 builder unchanged (`build_slots::<R8>`), then exact
//! Toffoli-reducing passes chunk by chunk on the 8-byte rows, then a streaming conversion to the 56-byte `Op` list.
//!
//! Everything under `passes/` is copied byte for byte from the public compile passes (rotate / group / post, files
//! optimize.rs peephole.rs values.rs ladder.rs clean.rs group.rs rotate.rs post.rs); this file is the only glue:
//! chunk cuts, condition-scope padding, step loop, conversion.
//!
//! Change the recipe here (RECIPE, NONCE) and nowhere else.
use super::{build_slots, nonce_row, op_to_row, row_to_op, Row, Slot, TAIL};
use crate::circuit::Op;

#[allow(dead_code, unused)] #[path = "passes/optimize.rs"] mod base;
#[allow(dead_code, unused)] #[path = "passes/values.rs"] mod values;
#[allow(dead_code, unused)] #[path = "passes/ladder.rs"] mod ladder;
#[allow(dead_code, unused)] #[path = "passes/post.rs"] mod post;
#[allow(dead_code, unused)] #[path = "passes/cleanup.rs"] mod cleanup;
#[allow(dead_code, unused)] #[path = "passes/pass.rs"] mod pass;
#[allow(dead_code, unused)] #[path = "passes/affine.rs"] mod affine;
#[allow(dead_code, unused)] #[path = "passes/abstriicher.rs"] mod abst;
#[allow(dead_code, unused)] #[path = "passes/schnaell.rs"] mod schn;
#[allow(dead_code, unused)] #[path = "passes/swaprelabel.rs"] mod swp;
#[allow(dead_code, unused)] #[path = "passes/qmerge.rs"] mod qmerge;

/// Fiat-Shamir nonce of the FINAL circuit: the op list ends with 96 X gates, pair j on qubit (NONCE >> j) & 1.
/// (mod.rs keeps its own NONCE = 1 for the unmodified builder; the gates it appends are dropped and re-made from this.)
pub const NONCE: u64 = 2;

/// One step of the per-chunk pipeline.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Step {
    /// rotate, group, post (rpg of the ladder-port driver, padded with AUTOBAL rules), one run each
    Rgp,
    /// nasqret's record passes (passes/cleanup.rs, pass.rs, affine.rs): AND-uncompute -> X-measurement + conditioned phase fix, affine Toffoli sharing
    Ncomp,
    /// exact record-stream pass abstriicher, version 2 (passes/abstriicher.rs): cancellations and sandwiches, never creates Swap or CCZ
    Abst,
    /// schnaellstriicher's single-sweep record pass (passes/schnaell.rs), mode 5: cancellations and sandwiches, never creates Swap (kind 10) or CCZ (kind 14); fresh engine per chunk
    Schn,
    /// swap relabelling (passes/swaprelabel.rs): CX(x,y) CX(y,x) CX(x,y) deleted by lane relabelling, fix-up swaps before each scope pop (identity at the chunk end)
    Swp,
    /// gadget merging (gadget_merge.rs, almond-lab's exact rewrite of adjacent dirty-borrow gadget chains), per chunk, last
    Gm,
    /// almond-lab's exact cancellation + Toffoli merging (passes/qmerge.rs, port of qopt mode 23), per chunk, after Gm
    Q23,
    /// second round (ours, e633b): gadget merging again after Q23
    Gm2,
    /// second round (ours, e633b): mode 23 again after Gm2
    Q23b,
}
/// The recipe applied to every chunk, in order.
pub const RECIPE: &[Step] = &[Step::Rgp, Step::Ncomp, Step::Schn, Step::Swp, Step::Gm, Step::Q23, Step::Gm2, Step::Q23b];

/// chunk cut window (records): see `cuts`
pub const CUT_LO: usize = 20_000_000;
pub const CUT_HI: usize = 25_000_000;
/// lane count of the 635 circuit (ladder passes), reserved classical bits for padding
const WIDTH: usize = 635;
const BLK: usize = 8192;
const PADBIT: u16 = 65533;
const N: u16 = u16::MAX;

/// 8-byte slot that normalises exactly like the real `Op` slot (row -> Op -> row), so the builder's peephole and
/// copy schedule see the same rows in both forms.
#[derive(Clone, Copy)]
pub struct R8(pub Row);
impl Slot for R8 {
    fn empty() -> Self { R8([0; 4]) }
    fn is_empty(&self) -> bool { self.0[0] == 0 }
    fn from_row(r: Row) -> Self { R8(op_to_row(&row_to_op(r))) }
    fn to_row(&self) -> Row { assert!(self.0[0] != 0, "empty slot read"); self.0 }
}

/// Chunk boundaries of the body (record indices, first 0, last body.len()).  Candidates are positions p where record
/// p-1 is a measurement (kind 12), or record p-1 is a pop (kind 16) and the condition depth is 0.  From the previous cut c
/// take the candidate in [c+LO, c+HI] with the smallest depth (earliest on ties); no candidate: plain cut at c+(LO+HI)/2.
pub fn cuts(body: &[R8]) -> Vec<usize> {
    let nb = body.len();
    let (mut depth, mut prev12, mut prev16) = (0i64, false, false);
    let mut cand: Vec<(usize, i64)> = Vec::new();
    for (i, r) in body.iter().enumerate() {
        let r = r.0;
        if prev12 || (prev16 && depth == 0) { cand.push((i, depth)); }
        assert!(r[1] != 65533 && r[1] != 65534 && r[2] != 65533 && r[2] != 65534 && r[3] != 65533 && r[3] != 65534, "reserved bit in stream");
        if r[0] == 15 { depth += 1 } else if r[0] == 16 { depth -= 1 }
        prev12 = r[0] == 12; prev16 = r[0] == 16;
    }
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

/// classical bit used as scratch by the tracker's measurement triple (HMR, CZ on it, clear); the stream never uses it (`cuts` asserts 65533 / 65534 absent)
pub const NSCRATCH: u16 = 65534;
/// nasqret's Pass (2 optimize rounds + AND-uncompute tracker) and Affine over one chunk.  Chunk-start state: every lane is an UNKNOWN value
/// (declared through the tracker's own register rule), so no zero lane and no present product is assumed; only what the chunk itself proves is used.
fn ncomp(rows: Vec<Row>) -> Vec<Row> {
    let (rows, lead, end) = pad(rows);
    let mut pass = pass::Pass::new(WIDTH, NSCRATCH, 2);
    for q in 0..WIDTH as u16 { pass.cleanup.push([2, 0, q, N], &mut |_| {}); }
    let mut affine = affine::Affine::new();
    let mut out: Vec<Row> = Vec::with_capacity(rows.len() + rows.len() / 64);
    for blk in rows.chunks(base::CHUNK) { pass.chunk(blk.to_vec(), |r| affine.push(r, |g| out.push(g))); }
    pass.finish();
    affine.flush(|g| out.push(g));
    unpad(out, lead, end)
}

/// schnaellstriicher's engine, mode 5 (cancel + sandwich, no Swap / CCZ), in place over one chunk: the engine never emits more rows than it has read
fn schn_step(mut rows: Vec<Row>) -> Vec<Row> {
    let mut e = schn::Eng::new(1 << 22, 5, 6); let (mut w, mut bad) = (0usize, 0u64);
    for i in 0..rows.len() { let r = rows[i]; e.push(r, &mut |x: &Row, _| { assert!(w <= i, "in-place sweep overtook the reader"); if x[0] == 10 || x[0] == 14 { bad += 1; } rows[w] = *x; w += 1; }); }
    e.finish(&mut |x: &Row, _| { if x[0] == 10 || x[0] == 14 { bad += 1; } rows[w] = *x; w += 1; });
    assert!(bad == 0, "Swap / CCZ record produced");
    rows.truncate(w); rows
}

/// gadget merging over one chunk (rows are [kind, a, b, c]; the CX rows it makes are [8, a, b, 65535])
fn gm_step(mut rows: Vec<Row>) -> Vec<Row> {
    super::gadget_merge::gadget_merge(&mut rows, |r: &Row| *r, |r: Row| r);
    rows.shrink_to_fit(); rows
}

/// totals of the Q23 step over all chunks: CCX pairs, other pairs, merges M1, merges M2, CCX records removed
pub static Q23_TOTALS: [std::sync::atomic::AtomicU64; 5] = [const { std::sync::atomic::AtomicU64::new(0) }; 5];
/// mode 23 over one chunk, with the chunk's open condition scopes padded exactly as for ncomp
fn q23_step(rows: Vec<Row>) -> Vec<Row> {
    let (rows, lead, end) = pad(rows);
    let (out, c) = qmerge::mode23(rows);
    for (k, v) in [c.0, c.1, c.2, c.3, c.4].into_iter().enumerate() { Q23_TOTALS[k].fetch_add(v, std::sync::atomic::Ordering::Relaxed); }
    unpad(out, lead, end)
}

/// totals of the second round: [Gm2 chains, Gm2 removed, Q23b CCX pairs, other pairs, M1, M2, CCX removed]
pub static R2_TOTALS: [std::sync::atomic::AtomicU64; 7] = [const { std::sync::atomic::AtomicU64::new(0) }; 7];
fn gm2_step(mut rows: Vec<Row>) -> Vec<Row> {
    let (c, r) = super::gadget_merge::gadget_merge(&mut rows, |r: &Row| *r, |r: Row| r);
    R2_TOTALS[0].fetch_add(c, std::sync::atomic::Ordering::Relaxed); R2_TOTALS[1].fetch_add(r, std::sync::atomic::Ordering::Relaxed);
    rows.shrink_to_fit(); rows
}
fn q23b_step(rows: Vec<Row>) -> Vec<Row> {
    let (rows, lead, end) = pad(rows);
    let (out, c) = qmerge::mode23(rows);
    for (k, v) in [c.0, c.1, c.2, c.3, c.4].into_iter().enumerate() { R2_TOTALS[2 + k].fetch_add(v, std::sync::atomic::Ordering::Relaxed); }
    unpad(out, lead, end)
}

/// one chunk through the recipe
pub fn run_chunk(mut rows: Vec<Row>, recipe: &[Step]) -> Vec<Row> {
    for s in recipe { rows = match *s { Step::Rgp => rgp(rows), Step::Ncomp => ncomp(rows), Step::Abst => abst::abst(rows), Step::Schn => schn_step(rows), Step::Swp => swp::swp(rows), Step::Gm => gm_step(rows), Step::Q23 => q23_step(rows), Step::Gm2 => gm2_step(rows), Step::Q23b => q23b_step(rows) }; }
    rows.shrink_to_fit();
    rows
}

/// builder (unchanged) -> body rows (the 96 nonce rows dropped) -> cuts -> chunks (input freed as split) -> passes on
/// `threads` workers; output chunks in fixed order, independent of the thread count.
pub fn pipeline_rows(recipe: &[Step], threads: usize, log: bool) -> Vec<Vec<Row>> {
    let t0 = std::time::Instant::now();
    let mut body: Vec<R8> = build_slots::<R8>(true);
    assert!(body.len() > TAIL);
    body.truncate(body.len() - TAIL);
    if log { eprintln!("[{:?}] builder done: {} body rows", t0.elapsed(), body.len()); }
    let cut = cuts(&body);
    if log { eprintln!("[{:?}] {} chunks", t0.elapsed(), cut.len() - 1); }
    let nc = cut.len() - 1;
    let mut ins: Vec<std::sync::Mutex<Option<Vec<R8>>>> = Vec::with_capacity(nc);
    for _ in 0..nc { ins.push(std::sync::Mutex::new(None)); }
    for k in (1..nc).rev() { let c = body.split_off(cut[k]); body.shrink_to_fit(); *ins[k].lock().unwrap() = Some(c); }
    *ins[0].lock().unwrap() = Some(body);
    let outs: Vec<std::sync::Mutex<Option<Vec<Row>>>> = (0..nc).map(|_| std::sync::Mutex::new(None)).collect();
    let next = std::sync::atomic::AtomicUsize::new(0);
    let work = || loop {
        let i = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        if i >= nc { break; }
        let inp = ins[i].lock().unwrap().take().unwrap();
        let rows: Vec<Row> = inp.into_iter().map(|r| r.0).collect();
        let o = run_chunk(rows, recipe);
        *outs[i].lock().unwrap() = Some(o);
    };
    std::thread::scope(|sc| {
        // helpers: if the sandbox refuses a thread we simply stop spawning; the calling thread runs the same loop itself
        for _ in 1..threads.max(1).min(nc) {
            if std::thread::Builder::new().stack_size(64 << 20).spawn_scoped(sc, &work).is_err() { break; }
        }
        work();
    });
    if log { eprintln!("[{:?}] passes done", t0.elapsed()); }
    outs.into_iter().map(|m| m.into_inner().unwrap().unwrap()).collect()
}

/// the nonce rows of the final circuit
pub fn tail_rows() -> Vec<Row> { (0..TAIL).map(|i| nonce_row(i, NONCE)).collect() }

/// Row -> Op conversion of one chunk: the single place where rows become ops.
pub fn emit_chunk(ops: &mut Vec<Op>, rows: &[Row]) { ops.extend(rows.iter().map(|&r| row_to_op(r))); }

/// Production conversion.  `sel = None`: every chunk in order, then the 96 nonce rows (this is what `build_final` uses).
/// `sel = Some(list)` (test hook, ascending chunk indices; index chunks.len() = the nonce rows): the same Vec<Op> of the
/// full final capacity is allocated, but only the listed chunks are converted (through the same `emit_chunk`) and the rest
/// are dropped unconverted, so the returned Vec holds just the selected ops, contiguously.
pub fn convert_sel(chunks: Vec<Vec<Row>>, sel: Option<&[usize]>) -> Vec<Op> {
    let nc = chunks.len();
    let total: usize = chunks.iter().map(|c| c.len()).sum::<usize>() + TAIL;
    let mut ops: Vec<Op> = Vec::with_capacity(total);
    for (k, c) in chunks.into_iter().enumerate() {
        if sel.map_or(true, |l| l.contains(&k)) { emit_chunk(&mut ops, &c); }
        drop(c);
    }
    if sel.map_or(true, |l| l.contains(&nc)) { emit_chunk(&mut ops, &tail_rows()); }
    if sel.is_none() { assert!(ops.len() == total); }
    ops
}

/// The final op list: chunks converted one by one with the tree's own `row_to_op` (each chunk's rows freed as soon as
/// converted), nonce gates last.  The Vec is allocated once at its exact final size.
pub fn convert(chunks: Vec<Vec<Row>>) -> Vec<Op> { convert_sel(chunks, None) }

pub fn build_final() -> Vec<Op> {
    let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    let chunks = pipeline_rows(RECIPE, threads, false);
    let q2: Vec<u64> = R2_TOTALS.iter().map(|x| x.load(std::sync::atomic::Ordering::Relaxed)).collect();
    eprintln!("second-round totals {:?}", q2);
    convert(chunks)
}
