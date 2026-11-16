//! E1 (ITEM 2 v2 rows + counts scan from trace): the Lycurgus standalone expander (Q633-EXPANDERS preview E1/E5, e1/expand.rs) with its inputs
//! taken from the tree's data files.  Output = the raw leaf rows (215,702,819); the 6-row exit adapter is a separate patch block.
#![allow(dead_code, unused_imports, unreachable_code, unused_mut)]
mod cl;
mod rns;
mod scan;
mod vm;
mod rows;
use super::gir;
type Row = [u16; 4];
const ITEM_ROWS: usize = 61_369_314;
const SCAN_ROWS: u64 = 154_333_471;
const LEAF_ROWS: usize = 215_702_819;

pub fn emit(out: &mut Vec<Row>) {
    let start = out.len();
    out.extend(rows::rows_of(include_bytes!("entry17.r8")));
    let g = gir::Girs::open(include_bytes!("../data/e1-item.girs"));
    let mut buf: Vec<Row> = Vec::new(); let mut n = 0usize;
    for b in 0..g.blocks.len() { g.decode(b, &mut buf); n += buf.len(); out.extend_from_slice(&buf); }
    assert!(n == ITEM_ROWS, "ITEM 2 rows");
    let ids = rows::lane_map(include_bytes!("id6.map"));
    let ports = rows::lane_map(include_bytes!("physical-scan.map"));
    let map: Vec<u16> = ids.iter().map(|&id| ports.get(id as usize).copied().unwrap_or(u16::MAX)).collect();
    let trace = super::lzma::decode(include_bytes!("../data/e1.trc.lzma")).expect("e1 trace");
    let mut classical = scan::Classical::new();
    classical.cursor([17060, 24600, 26600]);
    let mut scan_rows = 0u64;
    scan::run(&trace, 11138, &mut classical, &mut |row| { out.push(rows::remap(row, &map)); scan_rows += 1; }, 234);
    assert!(scan_rows == SCAN_ROWS, "E1 scan rows");
    out.extend(rows::rows_of(include_bytes!("final17.r8")));
    assert!(out.len() - start == LEAF_ROWS, "E1 leaf rows");
}
