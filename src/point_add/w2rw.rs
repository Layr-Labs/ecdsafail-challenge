//! w2 record-level rewriter for ITEM 12 / ITEM 2 of the q633a tree (wire space, i.e. the block's own numbering, before
//! the wire map and the segment lane map; insert rows already placed).  Every rewrite here is an EXACT identity of
//! circuits (same unitary / channel on every input), so it needs no precondition; a data-driven SELECTION (which
//! occurrences to rewrite) only decides where the price is paid.
//!
//! Rewrites (name syntax for W2_RW, ';' separated):
//!   negx:<w>[,<w>..]      every X-pair on wire w (X w ... X w with no other X / Z / CZ / Hmr on w, no condition push/pop
//!                         between, both X unconditioned) whose occurrence is SELECTED is removed, and every use of w
//!                         as a control in between becomes a negated-control form:
//!                           CCX(w,a->b) -> CX(a->b) CCX(w,a->b)       CX(w->b) -> X(b) CX(w->b)
//!                         (w as a target in between commutes with X).  Selection: W2_SEL=all, or zero (default): the
//!                         pair is selected when lane(w) is 0 on every sampled shot just before the first X (taken from
//!                         the selection oracle that w2.rs fills from the first snapshot).
//!   negxall:<w>[,<w>..]   the same with every pair selected (purely structural; this is the form the builder hook uses).
//!   toprung:<w>           in every rung  CCX(c4,a->z) CCX(c5,z->w) CCX(c4,a->z)  that toggles wire w through a V-chain lane z
//!                         (W2_ZWIRE restricts z), the rung becomes  CCX(c5,z->w)  +  CCX(c4,a->d) CCX(c5,d->w) CCX(c4,a->d)
//!                         CCX(c5,d->w)  on a borrowed wire d (W2_BORROW): exact for every value of d and of z, and z is no
//!                         longer written.  MEASURED: not useful (the borrowed form leaves transient garbage on w).
//!
//! Builder hook (for a derived tree, see apply_tree.sh): `hook_all(pk)` returns, per item, the rewritten wire-space rows
//! (inserts placed) for the items listed in HOOK; mod.rs then emits those rows instead of the raw block and shifts every
//! later piece by the item's growth (the same Shift mechanism the length-flexible scans use).
use super::*;
/// wire-space rows of item `idx` with its insert rows placed (mod.rs `items` order; no walk regions / unroll in this tree)
pub fn item_rows(pk: &Pack, g: &gir::Girs, idx: usize) -> Vec<Row> {
    let it = &pk.items[idx]; assert!(it.wm != RANGES && !unrollpack::applies(idx) && walkpack::regions(idx).next().is_none(), "hooked item must be plain");
    let ins = pk.ins_of(false, idx); let mut ip = 0usize; let mut k = 0u64; let mut out: Vec<Row> = Vec::with_capacity(it.n as usize); let mut rows = Vec::new();
    for b in it.block0..it.block0 + it.blocks { g.decode(b, &mut rows);
        for &r in rows.iter() { while ip < ins.len() && ins[ip].reg == 0 && ins[ip].off == k { out.push(ins[ip].row); ip += 1; } out.push(r); k += 1; } }
    while ip < ins.len() && ins[ip].reg == 0 && ins[ip].off == k { out.push(ins[ip].row); ip += 1; }
    assert!(ip == ins.len() && out.len() as u64 == it.n, "item {} length", idx); out
}
pub struct Info { pub notes: Vec<String>, pub pre: Vec<(u16, bool)> }
thread_local! {
    /// selection oracle for negx: record indices (in the ORIGINAL wire rows) of X records whose lane is 0 on every sampled shot before them
    pub static ZERO_X: std::cell::RefCell<Option<std::collections::HashSet<usize>>> = std::cell::RefCell::new(None);
    /// borrowed-lane choice for toprung: a wire not touched by the item (or by the window)
    pub static BORROW: std::cell::Cell<u16> = std::cell::Cell::new(NONE);
    /// toprung: only rungs whose V-chain lane is this wire (NONE = any)
    pub static ZWIRE: std::cell::Cell<u16> = std::cell::Cell::new(NONE);
}

pub fn rewrite(_item: usize, name: &str, rows: Vec<Row>, _m: &[u16]) -> (Vec<Row>, Info) {
    let mut info = Info { notes: Vec::new(), pre: Vec::new() };
    let mut rows = rows;
    if name == "none" { return (rows, info); }
    for step in name.split(';') {
        let (op, arg) = step.split_once(':').unwrap_or((step, ""));
        if op == "cap" { rows = c3::cap(rows, arg, &mut info); continue; }
        if op == "apply" { rows = c3::apply(rows, arg, &mut info); continue; }
        let wires: Vec<u16> = arg.split(',').filter(|x| !x.is_empty()).map(|x| x.parse().unwrap()).collect();
        rows = match op { "negx" => negx(rows, &wires, &mut info, false), "negxall" => negx(rows, &wires, &mut info, true), "toprung" => toprung(rows, &wires, &mut info), "echo" => panic!("rewrite step `echo` is not part of the shipped pipeline (stripped)"), "file" => panic!("rewrite step `file` is a measuring tool (stripped from the package)"), "ctr" => c3ctr::ctr(rows, &mut info, wires.first().map_or(0, |&x| x as usize * 1_000_000)), "pad" => c3pad::pad(rows, &mut info), "fold" => c3::fold(rows, &mut info, _m), _ => panic!("unknown rewrite {}", op) };
    }
    (rows, info)
}

/// X-pair removal with negated controls (exact for every input)
fn negx(rows: Vec<Row>, wires: &[u16], info: &mut Info, all: bool) -> Vec<Row> {
    let zero = ZERO_X.with(|z| z.borrow().clone());
    let mut out: Vec<Row> = Vec::with_capacity(rows.len() + rows.len() / 64);
    // for each wire, the index of the next X on it
    let n = rows.len();
    let mut next_x = vec![usize::MAX; n]; { let mut last: std::collections::HashMap<u16, usize> = std::collections::HashMap::new();
        for i in (0..n).rev() { let r = rows[i]; if r[0] == 6 && wires.contains(&r[1]) { if let Some(&j) = last.get(&r[1]) { next_x[i] = j; } last.insert(r[1], i); } } }
    // decide pairs: open[i] = Some(j) when X at i pairs with X at j and the pair is rewritten
    let mut drop_x = vec![false; n]; let mut neg_w = vec![NONE; n]; // neg_w[k] = wire whose control is negated at record k
    let (mut pairs, mut sel, mut uses_cx, mut uses_ccx, mut rej) = (0u64, 0u64, 0u64, 0u64, 0u64);
    let mut i = 0usize; let mut busy: std::collections::HashMap<u16, usize> = std::collections::HashMap::new(); // wire -> end of the pair being rewritten
    while i < n { let r = rows[i];
        if r[0] == 6 && wires.contains(&r[1]) && r[2] == NONE && !drop_x[i] && busy.get(&r[1]).map_or(true, |&e| e < i) {
            let w = r[1]; let j = next_x[i];
            if j != usize::MAX && rows[j][2] == NONE {
                pairs += 1;
                // scan the window
                let mut ok = true; let mut uses: Vec<usize> = Vec::new();
                for k in i + 1..j { let q = rows[k]; let nq = qubits(q[0]);
                    if matches!(q[0], 15 | 16) { ok = false; break; }
                    let has = (1..=nq).any(|t| q[t] == w); if !has { continue; }
                    match q[0] { 13 => { if q[3] != w { if q[1] == w && q[2] == w { ok = false; break; } uses.push(k); } }
                        8 => { if q[1] == w { if q[3] != NONE { ok = false; break; } uses.push(k); } else if q[3] != NONE { /* conditioned toggle of w: still commutes with X */ } }
                        6 => {}
                        _ => { ok = false; break; } } }
                if ok && uses.iter().any(|&k| neg_w[k] != NONE) { ok = false; }
                let chosen = ok && (all || zero.as_ref().map_or(false, |z| z.contains(&i)));
                if chosen { sel += 1; drop_x[i] = true; drop_x[j] = true; for &k in &uses { neg_w[k] = w; if rows[k][0] == 13 { uses_ccx += 1; } else { uses_cx += 1; } } busy.insert(w, j); }
                else if !ok { rej += 1; }
            } }
        i += 1; }
    for k in 0..n { let q = rows[k]; if drop_x[k] { continue; }
        if neg_w[k] != NONE { let w = neg_w[k];
            match q[0] { 13 => { let a = if q[1] == w { q[2] } else { q[1] }; out.push([8, a, q[3], NONE]); out.push(q); }
                8 => { out.push([6, q[2], NONE, NONE]); out.push(q); }
                _ => unreachable!() } }
        else { out.push(q); } }
    info.notes.push(format!("negx {:?}: X-pairs {} (rejected {}), rewritten {} -> -{} X records, negated CCX controls {} (+{} CX), negated CX controls {} (+{} X)", wires, pairs, rej, sel, 2 * sel, uses_ccx, uses_ccx, uses_cx, uses_cx));
    out
}

/// top-rung substitution: a clean V-chain lane z that only carries the last AND of a chain into target w is replaced by a borrowed lane
fn toprung(rows: Vec<Row>, wires: &[u16], info: &mut Info) -> Vec<Row> {
    let d = BORROW.with(|b| b.get()); assert!(d != NONE, "toprung needs a borrowed wire (W2_BORROW)");
    let n = rows.len(); let mut out: Vec<Row> = Vec::with_capacity(n + n / 64); let mut cnt = 0u64; let mut i = 0usize;
    while i < n { let r = rows[i];
        if i + 2 < n && r[0] == 13 && rows[i + 1][0] == 13 && rows[i + 2] == r {
            let (c4, a, z) = (r[1], r[2], r[3]); let t = rows[i + 1];
            let (c5, w) = if t[2] == z { (t[1], t[3]) } else if t[1] == z { (t[2], t[3]) } else { (NONE, NONE) };
            let zok = ZWIRE.with(|zw| zw.get() == NONE || zw.get() == z);
            if c5 != NONE && zok && wires.contains(&w) && ![c4, a, c5, w, z].contains(&d) && c5 != z && c4 != z && a != z {
                // original: w ^= c5*z ^ c5*c4*a, z restored.  New: the c5*z term read-only (a no-op when z is clean), the
                // c5*c4*a term by Barenco's 4-Toffoli form on the borrowed d (exact for every d); z is never written.
                out.push([13, c5, z, w]); out.push([13, c4, a, d]); out.push([13, c5, d, w]); out.push([13, c4, a, d]); out.push([13, c5, d, w]); cnt += 1; i += 3; continue; } }
        out.push(r); i += 1; }
    info.notes.push(format!("toprung {:?} borrow wire {} z-wire {}: {} rungs (+{} CCX)", wires, d, ZWIRE.with(|z| z.get()), cnt, 2 * cnt));
    out
}
