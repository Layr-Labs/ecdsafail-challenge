//! R3: c2gen.rs of (internal) ((internal)) with shift-capped stock walks (r3walkgen.rs, CAP = 31): 76,908,465 records instead of 124,715,346.
//! The cap idea is borrowed from (internal); everything else is C2 unchanged (see the text below).
//! C2: generator of the 632-lane ITEM 10 ("renewal" 129-bit multiply) of the q633a tree, in WIRE space (the block's own
//! numbering, before the item's wire map and the segment lane map), so it survives any lane renumbering.
//!
//! Input : the raw wire-space records of ITEM 10 (103,770,365 records, insert rows placed).
//! Output: the replacement records.  Wire 631 (lane 631 in segment 21) is never referenced by the output.
//!
//! What it does (record offsets are offsets inside the raw item):
//!  1. The three Euclid-walk row stretches are replaced by the stock graded-relay walk of walkgen.rs (`Kind::Inner`):
//!       run 1  rows [A1, R1)  -> Inner, 3 clean tags (8 role wires), forward
//!       run 2  rows [A2, R2)  -> Inner, 1 clean tag  (6 role wires), forward
//!       run 3  rows [A3, R3)  -> Inner, 3 clean tags, reversed record order (all records are self-inverse)
//!     followed by short adapters that put the three displaced passenger bits where the following original records expect them.
//!     The stock walk leaves the parked bits where they are, so the adapters are plain moves (CX a b, CX b a onto a zero wire).
//!  2. The fifth bit of the leading-zero count of the multiplier (wire 631 = [clz(T) >= 16]) is dropped: every original record that
//!     references wire 631 as that bit, or as the fifth walk tag in the few original walk rows that remain, is deleted.  With no
//!     record writing wire 631 the wire is constant 0, so every deleted record was the identity whenever the original had 0 there:
//!     the output equals the stock-walk circuit on every input with clz(T) <= 15 and is wrong for clz(T) >= 16.
//!  3. The parked passenger bit that the original keeps on wire 631 is kept on wire 629 (before run 2) and on wire 546 (after run 3);
//!     both wires are not referenced by the original in those record ranges (asserted).
//! The module depends only on walkgen.rs.  In a tree it is called from a (internal) builder hook (see r2a_hook.rs).
use super::r3walkgen::{self as walkgen, Cfg, Kind};
/// largest shift served by the relay sectors of the three stock walks (the donor walk has a five-bit count)
pub const CAP: usize = 31;
pub type Row = [u16; 4];
const NO: u16 = u16::MAX;

pub const LEN: usize = 103_770_365;
/// first record of the walk rows of run 1 / first original record kept after them
pub const A1: usize = 19_320_846;
pub const R1: usize = 28_380_501;
/// the original's move of the parked bit from wire 632 to wire 631 (two records)
pub const MV: usize = 38_636_177;
pub const A2: usize = 39_624_567;
pub const R2: usize = 88_487_501;
pub const A3: usize = 89_055_001;
pub const R3: usize = 98_115_222;
/// first record after the original's move of the parked bit off wire 631 (CX 631 147, CX 147 631 at C4 - 2, C4 - 1)
pub const C4: usize = 101_819_617;
/// the dropped wire
pub const DROP: u16 = 631;

fn rng(a: i32, b: i32) -> Vec<i32> { (a..=b).collect() }
/// multiplier register T (L of the walk), least significant bit first, then L[n] twice (L[n+1] is not used by Inner)
fn l_wires() -> Vec<i32> { let mut v = rng(0, 128); v.extend([619, 619]); v }
/// working register W (R of the walk), then R[n] twice
fn r_wires() -> Vec<i32> { let mut v = rng(129, 253); v.extend([637, 635, 634, 624, 626, 626]); v }
/// dirty loans: the 256 wires of the product register, then the passenger wires that stay in place
fn loan_wires() -> Vec<i32> {
    let mut v = rng(256, 498); v.extend(rng(499, 503)); v.extend([504, 505, 506, 623, 622, 512, 255, 254]);
    v.push(543); v.extend(rng(507, 511)); v.extend(rng(513, 542)); v.push(544); v.extend(rng(549, 618)); v
}
fn walk(real: usize, tags: [i32; 3], fire: i32, tst: i32, reverse: bool) -> Vec<Row> {
    let mut ws: Vec<i32> = tags[..real].to_vec(); while ws.len() < 7 { ws.push(-1); }
    let cfg = Cfg { n: 129, kind: Kind::Inner { real }, tags: 4, l: l_wires(), r: r_wires(), loan: loan_wires(), ws_tag: ws, sign: 627, fire, tst, aux: -1 };
    let mut rows: Vec<Row> = Vec::new(); walkgen::run(&cfg, &mut |r| rows.push(r)).expect("walk emission");
    for r in &rows { let nq = match r[0] { 13 => 3, 8 => 2, _ => 1 }; assert!((1..=nq).all(|j| r[j] != DROP), "walk references the dropped wire"); }
    if reverse { rows.reverse(); } rows
}
fn mv(o: &mut Vec<Row>, a: u16, b: u16) { o.push([8, a, b, NO]); o.push([8, b, a, NO]); }
fn refs(r: &Row, w: u16) -> bool { let nq = match r[0] { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 }; (1..=nq).any(|j| r[j] == w) }
/// copy m[a..b) without the records that reference wire DROP (they must be CX / CCX: no X, Z or measurement on that wire)
fn copy_drop(o: &mut Vec<Row>, m: &[Row], a: usize, b: usize) { for r in &m[a..b] { if refs(r, DROP) { assert!(matches!(r[0], 8 | 13), "unexpected record kind on the dropped wire"); } else { o.push(*r); } } }
/// copy m[a..b) with wire DROP renamed to `to`, which must not be referenced in the range
fn copy_rename(o: &mut Vec<Row>, m: &[Row], a: usize, b: usize, to: u16) { for r in &m[a..b] { assert!(!refs(r, to), "host wire is referenced in the range"); let mut q = *r; let nq = match r[0] { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 }; for j in 1..=nq { if q[j] == DROP { q[j] = to; } } o.push(q); } }

/// the replacement records of ITEM 10
pub fn generate(m: &[Row]) -> Vec<Row> {
    walkgen::SHIFT_CAP.store(CAP, std::sync::atomic::Ordering::Relaxed);
    assert!(m.len() == LEN, "ITEM 10 length {}", m.len());
    // anchors of the q633a item (guards against use on another block)
    assert!(m[A1 - 1] == [6, 626, NO, NO] && m[R3] == [6, 626, NO, NO], "walk prelude anchors");
    assert!(m[MV] == [8, 632, 631, NO] && m[MV + 1] == [8, 631, 632, NO], "park move anchor");
    assert!(m[C4 - 2] == [8, 631, 147, NO] && m[C4 - 1] == [8, 147, 631, NO], "park release anchor");
    let mut o: Vec<Row> = Vec::with_capacity(LEN + 21_000_000);
    copy_drop(&mut o, m, 0, A1);
    // run 1: role wires L[n] 619, R[n] 626, sign 627, tst 636 (lane 620), tags 628 629 630, fire 632; parks 545, 546, 625 untouched
    o.extend(walk(3, [628, 629, 630], 632, 636, false));
    o.push([6, 274, NO, NO]);          // the original closes an X bracket on loan wire 274 inside its rows
    mv(&mut o, 546, 636); mv(&mut o, 625, 546);
    copy_drop(&mut o, m, R1, MV);
    copy_rename(&mut o, m, MV, A2, 629);   // parked bit on wire 629 instead of 631 (the move itself becomes 632 -> 629)
    // run 2: role wires 619, 626, 627, tst 636, tag 632, fire 630; parks 545, 625 (stash bits), 546, 628, 629 untouched
    o.extend(walk(1, [632, -1, -1], 630, 636, false));
    o.push([6, 274, NO, NO]);
    mv(&mut o, 629, 632); mv(&mut o, 546, 636); mv(&mut o, 628, 546); mv(&mut o, 636, 628);
    copy_drop(&mut o, m, R2, A3);
    // run 3: the reversed walk of run 1
    o.extend(walk(3, [628, 629, 630], 632, 636, true));
    mv(&mut o, 546, 636); mv(&mut o, 625, 546); mv(&mut o, 545, 625); mv(&mut o, 636, 545);
    copy_rename(&mut o, m, R3, C4, 546);   // parked bit on wire 546 instead of 631
    copy_drop(&mut o, m, C4, LEN);
    for r in &o { assert!(!refs(r, DROP), "output references the dropped wire"); }
    o
}
