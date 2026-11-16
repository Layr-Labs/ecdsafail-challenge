//! Item-level splice of the unrolled multiply block (other lane's unroll.rs), version of the second parked 636 (worker uufroller).
//! Second 634 build (worker zwoeitbau): ITEM 2 and ITEM 10 take the other lane's FULL unroll (unroll.rs = the unroll633 kit's unroll4.rs, unchanged):
//! ARMS maps the item to the kit's arm (202 = ITEM 2: run 3 b2, run 2 b3, run 1 b2; 105 = ITEM 10: run 3 b2, run 2 b4, run 1 b2) and to the unrolled length.
//! Items 4 and 12 are the wide replacement divides, plain record blocks.  The pack tables hold both items at their unrolled length plus their parking rows,
//! so nothing is shifted here: `check` only asserts the lengths (a changed block or table fails the build instead of shifting the stream silently).
//! 634 K build (worker kappevier): unroll.rs = the other lane's unroll5.rs (unroll4 + shift caps) with CMAX_ARM202 = 23 (ITEM 2) and CMAX_ARM105 = 22 (ITEM 10); the lengths below are the
//! capped lengths (uncut: 120,010,797 / 164,245,065).
//! Lever switch: ON = false leaves the raw block in place; the build then stops (the tables are those of the unrolled block).
use super::unroll;
use super::{Pack, Row};

const ON: [(usize, bool); 2] = [(2, true), (10, false)];   // erneuert: item 10 is a plain record block (the third lane's renewal ITEM 10), not unrolled here
/// (item, arm of unroll::unroll_item, unrolled length)
const ARMS: [(usize, usize, u64); 2] = [(2, 202, 97_245_989), (10, 105, 113_983_114)];
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
    assert!(on(10) || pk.items[10].n == 103_770_369, "pack tables: item 10 is not the renewal block");
    assert!(!on(10) || pk.items[10].n != 103_770_369, "pack tables hold the renewal ITEM 10 but the unroll of item 10 is switched on");
}
