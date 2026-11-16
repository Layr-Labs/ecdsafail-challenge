//! Item-level splice of the unrolled multiply block (other lane's unroll.rs), version of the second parked 636 (worker uufroller).
//! 635D build (worker foifbau): unroll.rs = the unroll633 kit's unroll4.rs, unchanged.  ARMS maps the item to the kit's arm and to the unrolled length:
//! 635K build (worker kappefoif): unroll.rs = the other lane's unroll5.rs (unroll4 + shift cap) with CMAX_ARM105 = 25 (ITEM 10: 164,245,065 -> 124,157,497 records);
//! CMAX_ARM2 = NOCUT, so ITEM 2 (arm 2) is byte-identical to unroll4's output.
//! ITEM 2 -> arm 2 (the graded 635's partial unroll), ITEM 10 -> arm 105 (FULL unroll: run 3 b2, run 2 b4, run 1 b2).
//! Items 4 and 12 are the wide replacement divides, plain record blocks.  The pack tables hold both items at their unrolled length plus their parking rows,
//! so nothing is shifted here: `check` only asserts the lengths (a changed block or table fails the build instead of shifting the stream silently).
//! Lever switch: ON = false leaves the raw block in place; the build then stops (the tables are those of the unrolled block).
use super::unroll;
use super::{Pack, Row};

const ON: [(usize, bool); 2] = [(2, true), (10, false)];   // erneuert: ITEM 10 is the renewal piece, a plain record block
/// (item, arm of unroll::unroll_item, unrolled length)
const ARMS: [(usize, usize, u64); 1] = [(2, 2, 71_735_247)];
fn on(item: usize) -> bool { ON.iter().any(|&(i, f)| i == item && f) }
pub fn applies(item: usize) -> bool { on(item) }

pub fn transform(item: usize, raw: Vec<Row>) -> Vec<Row> {
    let (_, n0, _) = *unroll::ITEMS.iter().find(|t| t.0 == item).expect("unrolled item");
    let (_, arm, n1) = *ARMS.iter().find(|t| t.0 == item).expect("unroll arm");
    assert!(raw.len() as u64 == n0, "raw item {} length", item);
    let out = unroll::unroll_item(arm, &raw); assert!(out.len() as u64 == n1, "unrolled item {} length", item); out
}

/// pack item length = unrolled length + inserted parking rows
pub fn check(pk: &Pack) {
    for &(item, _arm, n1) in ARMS.iter() { let ni = pk.ins_of(false, item).len() as u64;
        if on(item) { assert!(pk.items[item].n == n1 + ni, "pack tables: item {} is not at its unrolled length", item); } }
    assert!(!on(10) && pk.ins_of(false, 10).is_empty() && pk.items[10].n == 103_770_373, "item 10 must be the renewal piece (103,770,373 records, no parking rows)");
}
