//! q631 / i10 (local research, 2026-11-19; not submitted, not part of any package): ITEM 10 (segment 21, the 129-bit multiply
//! with renewals) without its 632nd lane in the three walk runs.  Switch `ON` (false = the tree unchanged: the builder hook in
//! i1.rs calls c2capgen::generate as before; nothing in this module runs).
//!
//! The rewrite (`generate`): c2capgen.rs (the tree's ITEM 10 generator) with its three stock relay walks re-emitted by an i10
//! copy of the walk generator (i10walkgen.rs + i10walkplan.rs = r3walkgen.rs / r3walkplan.rs + block labels) with ONE CLEAN
//! TAG FEWER: runs 1 and 3 real 3 -> 2 (tag wire 630 unused), run 2 real 1 -> 0 (tag wire 632 unused).  Same sectors' shift
//! coverage [0, 31] (the inherited cap CAP = 31), same results.  real = 0 needs two fixes in the plan (both exact, only active
//! for real = 0): (1) the pre-sector qcond flag qa lives on a DIRTY loan (the run driver maps full[0] there): the consumer
//! (a toggle of tst controlled by qa) is applied a second time after qcond is undone, so tst ^= f(d ^ g) ^ f(d) = f(g)
//! (the dirty-control gadget with W = identity, U an involution); (2) the matching flag tg0 is hosted on R[m], which holds
//! 1 at every sector start: X it to a clean 0 around the matching block.
//! Outside the walks (`generate_c0`, i10c0.rs): the qkit Cuccaro adders' clean carry-in lane c0 (wire 636) is removed by
//! re-emitting each parsed adder as the walk generator's ancilla-free ripple adder (checked instance by instance on random states).
use super::*;

/// the switch (OFF = the tree unchanged)
pub const ON: bool = false;
/// clean walk tags per run in the rewrite (the tree: REAL_TREE = [3, 1, 3])
pub const REAL_ON: [usize; 3] = [2, 0, 2];
/// length of the rewritten ITEM 10 (wire space; i1::HOOK_LEN uses it when ON)
pub const LEN_ON: u64 = 82_374_108;   // e631b B1: cap 24

/// ITEM 10 in wire space: (raw item rows, the tree's hooked rows = c2capgen::generate(raw), wire -> physical lane map before the
/// relabelling: item wire map, then segment lane map; NONE where the wire has no lane)
pub fn wire_rows() -> (Vec<Row>, Vec<Row>, Vec<u16>) {
    let mut pk = Pack::parse(&lzma::decode(include_bytes!("data/pack.lzma")).expect("pack tables"));
    walkpack::apply(&mut pk);
    unrollpack::check(&pk);
    i1::w4_apply(&mut pk);
    let g = gir::Girs::open(include_bytes!("data/blocks.girs"));
    let raw = w2rw::item_rows(&pk, &g, 10);
    let gen = c2capgen::generate(&raw);
    let it = &pk.items[10];
    let seg = pk.seg_of(it.out);
    assert!(seg == pk.seg_of(it.out + it.n - 1), "item 10 crosses a segment");
    let wm = if it.wm > 0 { Some(&pk.wire_maps[it.wm - 1]) } else { None };
    let map: Vec<u16> = (0..1024usize).map(|w| { let id = match wm { Some(m) => m[w], None => w as u16 };
        if id == NONE || id as usize >= 646 { NONE } else { pk.segs[seg].map[id as usize] } }).collect();
    (raw, gen, map)
}
/// the wire -> logical id map of ITEM 10 (NONE = unmapped)
pub fn wire_ids() -> Vec<u16> {
    let pk = Pack::parse(&lzma::decode(include_bytes!("data/pack.lzma")).expect("pack tables"));
    let it = &pk.items[10];
    let wm = if it.wm > 0 { Some(&pk.wire_maps[it.wm - 1]) } else { None };
    (0..1024usize).map(|w| match wm { Some(m) => m[w], None => w as u16 }).collect()
}

// ---------------------------------------------------------------- the ITEM 10 generator (c2capgen.rs with the i10 walk generator)
#[path = "i10walkgen.rs"]
pub mod wg;
#[path = "i10c0.rs"]
pub mod c0;
use super::c2capgen::{A1, R1, MV, A2, R2, A3, R3, C4, LEN, DROP};
/// e631b B1: shift cap of i10's three walks (632d: 24; the tree's c2capgen keeps 31 for the int4 equality check)
pub const CAP: usize = 24;

fn rng_(a: i32, b: i32) -> Vec<i32> { (a..=b).collect() }
fn l_wires() -> Vec<i32> { let mut v = rng_(0, 128); v.extend([619, 619]); v }
fn r_wires() -> Vec<i32> { let mut v = rng_(129, 253); v.extend([637, 635, 634, 624, 626, 626]); v }
fn loan_wires() -> Vec<i32> {
    let mut v = rng_(256, 498); v.extend(rng_(499, 503)); v.extend([504, 505, 506, 623, 622, 512, 255, 254]);
    v.push(543); v.extend(rng_(507, 511)); v.extend(rng_(513, 542)); v.push(544); v.extend(rng_(549, 618)); v
}
/// one walk run of c2capgen (same configuration); `log` receives (start, end, label) per block in the returned row order
pub fn walk(real: usize, tags: [i32; 3], fire: i32, tst: i32, reverse: bool, log: Option<&mut Vec<(usize, usize, u64)>>) -> Vec<Row> {
    let mut ws: Vec<i32> = tags[..real].to_vec(); while ws.len() < 7 { ws.push(-1); }
    let cfg = wg::Cfg { n: 129, kind: wg::Kind::Inner { real }, tags: 4, l: l_wires(), r: r_wires(), loan: loan_wires(), ws_tag: ws, sign: 627, fire, tst, aux: -1 };
    let want = log.is_some();
    if want { wg::LOG.with(|l| *l.borrow_mut() = Some(Vec::new())); }
    let mut rows: Vec<Row> = Vec::new(); wg::run(&cfg, &mut |r| rows.push(r)).expect("walk emission");
    let lg = if want { wg::LOG.with(|l| l.borrow_mut().take()).unwrap() } else { Vec::new() };
    for r in &rows { let nq = match r[0] { 13 => 3, 8 => 2, _ => 1 }; assert!((1..=nq).all(|j| r[j] != DROP), "walk references the dropped wire"); }
    let n = rows.len();
    if reverse { rows.reverse(); }
    if let Some(out) = log { if reverse { for &(s, e, l) in lg.iter().rev() { out.push((n - e, n - s, l)); } } else { out.extend(lg); } }
    rows
}
fn mv(o: &mut Vec<Row>, a: u16, b: u16) { o.push([8, a, b, NONE]); o.push([8, b, a, NONE]); }
fn refs(r: &Row, w: u16) -> bool { (1..=qubits(r[0])).any(|j| r[j] == w) }
fn copy_drop(o: &mut Vec<Row>, m: &[Row], a: usize, b: usize) { for r in &m[a..b] { if refs(r, DROP) { assert!(matches!(r[0], 8 | 13)); } else { o.push(*r); } } }
fn copy_rename(o: &mut Vec<Row>, m: &[Row], a: usize, b: usize, to: u16) { for r in &m[a..b] { assert!(!refs(r, to)); let mut q = *r; for j in 1..=qubits(r[0]) { if q[j] == DROP { q[j] = to; } } o.push(q); } }

/// the switchable rewrite (what the builder hook calls when ON): walks with one clean tag fewer + the ripple adders outside the
/// walks without their clean carry-in lane (generate_c0); see the module comment
pub fn generate(m: &[Row], ann: Option<&mut Vec<(usize, usize, u8, u64)>>) -> Vec<Row> {
    let (o, st) = generate_c0(m, ann); assert!(st.rejected == 0, "i10: a converted adder failed its check");
    assert!(o.len() as u64 == LEN_ON, "i10: rewritten ITEM 10 length {}", o.len()); o }
/// the tree's choice of clean walk tags (c2capgen: runs 1 and 3 with 3, run 2 with 1)
pub const REAL_TREE: [usize; 3] = [3, 1, 3];
/// c2capgen::generate reproduced with the i10 walk generator (byte-identical to the tree; i10ann checks it); `ann` receives
/// (start, end, walk number 1..3, label) per walk block
pub fn generate_ann(m: &[Row], ann: Option<&mut Vec<(usize, usize, u8, u64)>>) -> Vec<Row> { generate_cfg(m, REAL_TREE, ann) }
/// the same with `real` clean tags per walk run (the tree: REAL_TREE; fewer real tags = more relay sectors, one tag wire unused)
pub fn generate_cfg(m: &[Row], real: [usize; 3], mut ann: Option<&mut Vec<(usize, usize, u8, u64)>>) -> Vec<Row> {
    wg::SHIFT_CAP.store(CAP, std::sync::atomic::Ordering::Relaxed);
    assert!(m.len() == LEN, "ITEM 10 length {}", m.len());
    assert!(m[A1 - 1] == [6, 626, NONE, NONE] && m[R3] == [6, 626, NONE, NONE], "walk prelude anchors");
    assert!(m[MV] == [8, 632, 631, NONE] && m[MV + 1] == [8, 631, 632, NONE], "park move anchor");
    assert!(m[C4 - 2] == [8, 631, 147, NONE] && m[C4 - 1] == [8, 147, 631, NONE], "park release anchor");
    let mut o: Vec<Row> = Vec::with_capacity(LEN + 21_000_000);
    let put_walk = |o: &mut Vec<Row>, wn: u8, real: usize, tags: [i32; 3], fire: i32, tst: i32, rev: bool, ann: &mut Option<&mut Vec<(usize, usize, u8, u64)>>| {
        let base = o.len(); let mut lg: Vec<(usize, usize, u64)> = Vec::new();
        let rows = walk(real, tags, fire, tst, rev, if ann.is_some() { Some(&mut lg) } else { None });
        if let Some(a) = ann.as_mut() { for &(s, e, l) in &lg { a.push((base + s, base + e, wn, l)); } }
        o.extend(rows); };
    copy_drop(&mut o, m, 0, A1);
    put_walk(&mut o, 1, real[0], [628, 629, 630], 632, 636, false, &mut ann);
    o.push([6, 274, NONE, NONE]);
    mv(&mut o, 546, 636); mv(&mut o, 625, 546);
    copy_drop(&mut o, m, R1, MV);
    copy_rename(&mut o, m, MV, A2, 629);
    put_walk(&mut o, 2, real[1], [632, -1, -1], 630, 636, false, &mut ann);
    o.push([6, 274, NONE, NONE]);
    mv(&mut o, 629, 632); mv(&mut o, 546, 636); mv(&mut o, 628, 546); mv(&mut o, 636, 628);
    copy_drop(&mut o, m, R2, A3);
    put_walk(&mut o, 3, real[2], [628, 629, 630], 632, 636, true, &mut ann);
    mv(&mut o, 546, 636); mv(&mut o, 625, 546); mv(&mut o, 545, 625); mv(&mut o, 636, 545);
    copy_rename(&mut o, m, R3, C4, 546);
    copy_drop(&mut o, m, C4, LEN);
    for r in &o { assert!(!refs(r, DROP), "output references the dropped wire"); }
    o
}

/// the walk rewrite (REAL_ON) + every parsable Cuccaro ripple adder OUTSIDE the walks re-emitted without its clean carry-in lane
/// c0 (wire 636 = the walks' tst lane), see i10c0.rs: with the multiplier's normalisation count held (its bit 3, wire 630, is set
/// when clz(T) >= 8) those adders were the last 632-lane records.  Returns the rows and the conversion statistics.
pub fn generate_c0(m: &[Row], ann: Option<&mut Vec<(usize, usize, u8, u64)>>) -> (Vec<Row>, c0::Stats) {
    let mut lg: Vec<(usize, usize, u8, u64)> = Vec::new();
    let o = generate_cfg(m, REAL_ON, Some(&mut lg));
    let mut w: Vec<(usize, usize)> = (1..=3u8).map(|k| { let s = lg.iter().filter(|x| x.2 == k).map(|x| x.0).min().unwrap(); let e = lg.iter().filter(|x| x.2 == k).map(|x| x.1).max().unwrap(); (s, e) }).collect();
    w.sort();
    let ranges = vec![(0, w[0].0), (w[0].1, w[1].0), (w[1].1, w[2].0), (w[2].1, o.len())];
    let loans: Vec<u16> = (256..499).chain(0..256).chain(499..547).chain(549..620).collect();   // mapped wires (547, 548, 620, 621 have no lane)
    let (rows, st) = c0::convert(&o, &ranges, 636, &loans);
    if let Some(a) = ann { // walk blocks move by the size change of the converted parts before them
        let shift_at = |pos: usize| -> i64 { let (r2, _) = c0::convert(&o[..pos], &ranges.iter().map(|&(s, e)| (s.min(pos), e.min(pos))).collect::<Vec<_>>(), 636, &loans); r2.len() as i64 - pos as i64 };
        let d: Vec<i64> = w.iter().map(|&(s, _)| shift_at(s)).collect();
        for x in lg.iter() { let k = w.iter().position(|&(s, e)| x.0 >= s && x.0 < e).unwrap(); a.push(((x.0 as i64 + d[k]) as usize, (x.1 as i64 + d[k]) as usize, x.2, x.3)); } }
    (rows, st)
}
