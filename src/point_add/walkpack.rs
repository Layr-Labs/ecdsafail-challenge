//! Replacement walk regions of the two divide blocks, generated at build time.
//! A child module of `point_add`: it reads and shifts the private `Pack` tables and feeds `items()`.
//!
//! The raw divide block of item 4 (divide 1) / item 12 (divide 2) is blocks.girs' own record list.  Two ranges of it are
//! dropped (the inner walk with its 386-record load prelude, and the reverse walk) and replaced by the emission of
//! `walkgen` (explicit BitWonka wires, so the generated records go through the item's `wm` wire map and the segment lane
//! maps exactly like the literal records).  Everything after the region moves by `len - (end - start)` records.
use super::walkgen::{self, Cfg, Kind, V};
use super::{Pack, Row};

/// walk variant: B = inner with 3 clean tags (relay hosting the rest) + reverse with 4 clean tags (5-tag SectorReduced);
/// A = inner with 1 clean tag + reverse with 3 clean tags (D2ReducedImpl).  B is 25.7 M / 24.1 M records, A 54.1 M / 50.9 M.
pub const VARIANT_A: bool = false;

#[derive(Clone, Copy)]
pub enum Which { Inner, Reverse }
pub struct Reg { pub item: usize, pub start: u64, pub end: u64, pub len: u64, pub which: Which, pub d2: bool }

/// the four regions; `start..end` are record offsets inside the raw item, `len` the number of records generated
/// (including the 128 / 126 record entry adapter of the inner walk).  Lengths are asserted at emission.
/// 634 build: both divides are literal replacement pieces (the third lane's wide divides, blocks.girs), so NO region is replaced.
/// Lever switch: the four regions of the 635 tree are listed in its walkpack.rs; with them the pack tables of this tree do not fit (the build stops at an item length).
pub const REGIONS: [Reg; 0] = [];

/// (index in REGIONS, region): the index numbers the region in the insert table (Ins.reg = index + 1)
pub fn regions(item: usize) -> impl Iterator<Item = (usize, &'static Reg)> { REGIONS.iter().enumerate().filter(move |(_, r)| r.item == item) }

fn rng(a: i32, b: i32) -> V { (a..b).collect() }
/// explicit port lists of the two divide blocks (BitWonka's wire layout of the 637-lane stream)
fn cfg(r: &Reg) -> Cfg {
    let n: usize = if r.d2 { 127 } else { 129 };
    let ni = n as i32;
    let mut loan = if r.d2 { rng(254, 383) } else { rng(258, 385) }; loan.extend(if r.d2 { rng(510, 624) } else { rng(514, 624) });
    match r.which {
        Which::Inner => {
            let q0 = if r.d2 { 383 } else { 385 };
            let mut l: V = vec![ni, 634]; l.extend((ni + 2..2 * ni).rev()); l.extend([ni + 1, ni + 1]);
            let mut rr = rng(q0, q0 + ni); rr.extend([0, 0]);
            let (ws_tag, fire, tst, kind) = if VARIANT_A { (vec![626, -1, -1, -1, -1, -1, -1], 628, 629, Kind::Inner { real: 1 }) } else { (vec![626, 628, 629, -1, -1, -1, -1], 630, 637, Kind::Inner { real: 3 }) };
            Cfg { n, kind, tags: 4, l, r: rr, loan, ws_tag, sign: 1, fire, tst, aux: -1 }
        }
        Which::Reverse => {
            let mut l = rng(0, ni); l.extend([632, 633]);
            let mut rr = rng(ni, 2 * ni); rr.extend([634, ni]);
            if VARIANT_A { Cfg { n, kind: Kind::RevImpl, tags: 4, l, r: rr, loan, ws_tag: vec![626, 627, 628, -1, -1, -1, -1], sign: 636, fire: 637, tst: 639, aux: -1 } }
            else { Cfg { n, kind: Kind::RevSector, tags: 5, l, r: rr, loan, ws_tag: vec![626, 627, 628, 629, -1, -1, -1], sign: 636, fire: 637, tst: 639, aux: 633 } }
        }
    }
}

/// emit the replacement records of one region (generator wire numbering); returns the count
pub fn emit(r: &Reg, sink: &mut dyn FnMut(Row)) -> u64 {
    let c = cfg(r); let mut cnt = 0u64;
    if let Which::Inner = r.which { // entry adapter: X on wires n+2 ..= 2n-1, then 634
        let n = c.n as u16; for w in n + 2..2 * n { sink([6, w, u16::MAX, u16::MAX]); cnt += 1; } sink([6, 634, u16::MAX, u16::MAX]); cnt += 1; }
    cnt += walkgen::run(&c, &mut |row| sink(row)).expect("walk emission") as u64;
    assert!(cnt == r.len, "walk region length"); cnt
}

/// Shift every absolute stream position behind each region by its length change (regions processed back to front,
/// so every comparison is made in the unshifted coordinates).
pub fn apply(pk: &mut Pack) {
    let mut order: Vec<&Reg> = REGIONS.iter().collect(); order.sort_by_key(|r| std::cmp::Reverse(pk.items[r.item].out + r.end));
    for r in order {
        let it_out = pk.items[r.item].out; let end_abs = it_out + r.end; assert!(r.end <= pk.items[r.item].n && r.start < r.end, "region inside its item");
        let delta = r.len as i64 - (r.end - r.start) as i64; let sh = |x: u64| (x as i64 + delta) as u64;
        pk.records = sh(pk.records);
        for s in pk.segs.iter_mut() { if s.end >= end_abs { s.end = sh(s.end); } }
        for h in pk.his.iter_mut() { if h.out >= end_abs { h.out = sh(h.out); } }
        for (i, it) in pk.items.iter_mut().enumerate() { if i == r.item { it.n = sh(it.n); } else if it.out >= end_abs { it.out = sh(it.out); } }
        for s in pk.scans.iter_mut() { if s.out >= end_abs { s.out = sh(s.out); s.end = sh(s.end); } }
        for x in pk.wmr.iter_mut() { if x.0 >= end_abs { x.0 = sh(x.0); } }
    }
}
