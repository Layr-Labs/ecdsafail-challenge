//! Item-level splice of the unrolled multiply block (other lane's unroll.rs), version of the second parked 636 (worker uufroller).
//! Differences from swarm/cut-630/unrollship/ship/unrollpack.rs: only ITEM 10 is unrolled (items 4 and 12 use walkpack, ITEM 2 stays);
//! the pack tables already hold ITEM 10 at its UNROLLED length plus its parking rows, so nothing is shifted here: `check` only
//! asserts the lengths (a changed block or table fails the build instead of shifting the stream silently).
//! Lever switch: ON = false leaves the raw block in place; the build then stops at `check` (the tables are those of the unrolled block).
use super::unroll;
use super::{Pack, Row};

const ON: [(usize, bool); 1] = [(10, true)];
fn on(item: usize) -> bool { ON.iter().any(|&(i, f)| i == item && f) }
pub fn applies(item: usize) -> bool { on(item) }

pub fn transform(item: usize, raw: Vec<Row>) -> Vec<Row> {
    let (_, n0, n1) = *unroll::ITEMS.iter().find(|t| t.0 == item).expect("unrolled item");
    assert!(raw.len() as u64 == n0, "raw item {} length", item);
    let out = unroll::unroll_item(item, &raw); assert!(out.len() as u64 == n1, "unrolled item {} length", item); out
}

/// pack item length = unrolled length + inserted parking rows
pub fn check(pk: &Pack) {
    for &(item, _n0, n1) in unroll::ITEMS.iter() { let ni = pk.ins_of(false, item).len() as u64;
        if on(item) { assert!(pk.items[item].n == n1 + ni, "pack tables: item {} is not at its unrolled length", item); } }
    assert!(pk.items[10].n > 90_000_000 || !on(10), "item 10 tables");
    assert!(on(10) || pk.items[10].n < 90_000_000, "pack tables hold the unrolled ITEM 10 but the unroll is switched off");
}
