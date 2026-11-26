//! cap412: shift cap of the two divide-walk phases of ITEM 4 and ITEM 12 (kab share, 22 Nov 2026), a rows-to-rows pass on the
//! SHIPPED item rows of the 632 tree (row 3a88202c), i.e. on the rows the hooks of i1.rs emit:
//!     ITEM 4  = b5gen::generate(raw)                       115,733,065 records, rows hash ed31e0536c9d5363
//!     ITEM 12 = w2rw::rewrite(12, ITEM12_SPEC, raw, &[]).0 110,554,500 records, rows hash 0acf007f8635db40
//! The pass only DELETES records: a table of record ranges [a, b) of the input (wire space, the hook's own positions).  Every
//! range is a "recurrence span" of sector scale (30,000 records or more) inside a walk row: on every sampled entry the original
//! block gets right (natural item entries; engineered entries with Euclid quotients of up to 30 bits, with common factors of
//! 2..37 bits, with 1..15 leading zeros) the full lane state before record a equals the state before record b, so removing the
//! range changes nothing on those entries.  Forward walk: the top sector (64 loop iterations) of rows 0..63; reverse walk: the
//! two top sectors of each row.  Both blocks, shipped and parent alike, are already wrong on every entry with a partial quotient
//! of 33 bits or more; the pass adds one class: operands with a common factor of 38 bits or more (4.4e-12 per shot).
//! Evidence, limits and the hook lines: README-cap412.md.  The table pins length and hash of input and output (b5gen::rows_hash),
//! so other input rows or a damaged table stop the build.  Only X / CX / CCX records without a classical condition may be
//! deleted (asserted): no measurement, phase or classical record is ever removed, so the classical layer is untouched.
//! Credits of the tree travel with this file: jackylee0424, odinfree, almond-lab, BitWonka, nasqret, mochimodev, RealAdii, Khattar-Gidney.
use super::*;

/// cap selector: 0 = pass off (rows returned unchanged), otherwise the table data/cap412_item<N>_c<CAP>.txt must be listed below
pub const CAP: usize = 31;

fn table(item: usize, cap: usize) -> &'static str {
    match (item, cap) {
        (4, 31) => include_str!("data/cap412_item4_c31.txt"),
        (12, 31) => include_str!("data/cap412_item12_c31.txt"),
        _ => panic!("cap412: no table for item {} cap {}", item, cap),
    }
}
pub struct Spans { pub in_n: usize, pub in_hash: u64, pub out_n: usize, pub out_hash: u64, pub del: Vec<(usize, usize)> }
/// table text: `# comment` lines, one header line `cap412 <item> <cap> <in_n> <in_hash hex> <out_n> <out_hash hex>`, then `a b` per range
pub fn parse(txt: &str, item: usize, cap: usize) -> Spans {
    let mut s = Spans { in_n: 0, in_hash: 0, out_n: 0, out_hash: 0, del: Vec::new() }; let mut head = false;
    for l in txt.lines() { let l = l.trim(); if l.is_empty() || l.starts_with('#') { continue; } let f: Vec<&str> = l.split_whitespace().collect();
        if f[0] == "cap412" { assert!(f[1].parse::<usize>().unwrap() == item && f[2].parse::<usize>().unwrap() == cap, "cap412: table of another item / cap");
            s.in_n = f[3].parse().unwrap(); s.in_hash = u64::from_str_radix(f[4], 16).unwrap(); s.out_n = f[5].parse().unwrap(); s.out_hash = u64::from_str_radix(f[6], 16).unwrap(); head = true; continue; }
        s.del.push((f[0].parse().unwrap(), f[1].parse().unwrap())); }
    assert!(head, "cap412: table without a header");
    assert!(s.del.iter().all(|d| d.0 < d.1) && s.del.windows(2).all(|w| w[0].1 <= w[1].0), "cap412: ranges must be sorted and disjoint");
    s
}
/// delete the ranges; `check` = assert the pinned lengths and hashes (the build path); tools may pass false to try a table
pub fn delete(rows: &[Row], s: &Spans, check: bool) -> Vec<Row> {
    if check { assert!(rows.len() == s.in_n && b5gen::rows_hash(rows) == s.in_hash, "cap412: the table was made for other input rows (length {} hash {:016x})", rows.len(), b5gen::rows_hash(rows)); }
    let mut out: Vec<Row> = Vec::with_capacity(rows.len()); let mut p = 0usize;
    for &(a, b) in &s.del { assert!(b <= rows.len(), "cap412: range beyond the item");
        for r in &rows[a..b] { assert!(match r[0] { 13 => true, 8 => r[3] == NONE, 6 => r[2] == NONE, _ => false }, "cap412: range [{}, {}) holds a record that is not a plain X / CX / CCX: {:?}", a, b, r); }
        out.extend_from_slice(&rows[p..a]); p = b; }
    out.extend_from_slice(&rows[p..]);
    if check { assert!(out.len() == s.out_n && b5gen::rows_hash(&out) == s.out_hash, "cap412: output length {} hash {:016x} differ from the table", out.len(), b5gen::rows_hash(&out)); }
    out
}
/// the hook: capped rows of item 4 or 12 from the item's shipped rows
pub fn cap(item: usize, rows: Vec<Row>) -> Vec<Row> { if CAP == 0 { return rows; } delete(&rows, &parse(table(item, CAP), item, CAP), true) }
/// new position of an input position (for re-keying position tables such as the relabelling table): a position inside a deleted
/// range maps to the range's start
pub fn remap(s: &Spans, pos: usize) -> usize { let mut gone = 0usize; for &(a, b) in &s.del { if pos >= b { gone += b - a; } else { if pos > a { gone += pos - a; } break; } } pos - gone }
