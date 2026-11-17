//! Schn stage (b646): schnaellstriicher's single-sweep exact cancel/sandwich record pass (mode 5, no Swap/CCZ), run chunk by chunk
//! (post_pass cuts, condition-scope padding) over a finished op list.  SCHN_STAGE=0 turns every call into the identity.
use crate::circuit::Op;
use super::post_pass::{cuts, pad, unpad, row_of, op_of, Row};
#[allow(dead_code, unused)] #[path = "schnaell.rs"] mod schn;

fn schn_chunk(rows: Vec<Row>) -> Vec<Row> {
    let (mut rows, lead, end) = pad(rows);
    let mut e = schn::Eng::new(1 << 22, 5, 6); let mut w = 0usize;
    for i in 0..rows.len() { let r = rows[i]; e.push(r, &mut |x: &Row, _| { assert!(w <= i); assert!(x[0] != 10 && x[0] != 14); rows[w] = *x; w += 1; }); }
    e.finish(&mut |x: &Row, _| { assert!(x[0] != 10 && x[0] != 14); rows[w] = *x; w += 1; });
    rows.truncate(w);
    unpad(rows, lead, end)
}
pub fn apply(ops: Vec<Op>) -> Vec<Op> {
    if std::env::var("SCHN_STAGE").as_deref() == Ok("0") { return ops; }
    let ops: Vec<Op> = ops.into_iter().filter(|o| o.kind != crate::circuit::OperationType::DebugPrint).collect();
    let rows: Vec<Row> = ops.iter().map(|o| row_of(o)).collect();
    drop(ops);
    let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    let cut = cuts(&rows);
    let nc = cut.len() - 1;
    let mut rows = rows;
    let mut ins: Vec<std::sync::Mutex<Option<Vec<Row>>>> = Vec::with_capacity(nc);
    for _ in 0..nc { ins.push(std::sync::Mutex::new(None)); }
    for k in (1..nc).rev() { let c = rows.split_off(cut[k]); rows.shrink_to_fit(); *ins[k].lock().unwrap() = Some(c); }
    *ins[0].lock().unwrap() = Some(rows);
    let outs: Vec<std::sync::Mutex<Option<Vec<Row>>>> = (0..nc).map(|_| std::sync::Mutex::new(None)).collect();
    let next = std::sync::atomic::AtomicUsize::new(0);
    let work = || loop {
        let i = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        if i >= nc { break; }
        let inp = ins[i].lock().unwrap().take().unwrap();
        *outs[i].lock().unwrap() = Some(schn_chunk(inp));
    };
    std::thread::scope(|sc| {
        for _ in 1..threads.max(1).min(nc) { if std::thread::Builder::new().stack_size(64 << 20).spawn_scoped(sc, &work).is_err() { break; } }
        work();
    });
    let chunks: Vec<Vec<Row>> = outs.into_iter().map(|m| m.into_inner().unwrap().unwrap()).collect();
    let total: usize = chunks.iter().map(|c| c.len()).sum();
    let mut out: Vec<Op> = Vec::with_capacity(total);
    for c in chunks { out.extend(c.iter().map(|&r| op_of(r))); }
    eprintln!("SCHN_STAGE ops {}", out.len());
    out
}
