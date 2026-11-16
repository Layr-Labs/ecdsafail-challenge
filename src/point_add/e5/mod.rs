//! E5 (ITEM 10 with renewals + loans scan from trace): the Lycurgus standalone expander (e5/expand.rs) with its inputs from the tree's data files.
//! Output = the raw leaf rows (370,484,040); the 12-row and 21-row exit adapters are a separate patch block.
#![allow(dead_code, unused_imports, unreachable_code, unused_mut)]
mod cl;
mod rns;
mod scan;
mod vm;
mod rows;
use super::gir;
type Row = [u16; 4];
const ITEM_ROWS: usize = 103_770_353;
const SCAN_ROWS: u64 = 266_655_797;

pub fn emit(out: &mut Vec<Row>) {
    let start = out.len();
    out.extend(rows::rows_of(include_bytes!("entry19.r8")));
    let item_lanes = rows::lane_map(include_bytes!("item-relabel.map"));
    let g = gir::Girs::open(include_bytes!("../data/e5-item.girs"));
    let mut buf: Vec<Row> = Vec::new(); let mut n = 0usize;
    for b in 0..g.blocks.len() { g.decode(b, &mut buf); n += buf.len(); out.extend(buf.iter().map(|&r| rows::remap(r, &item_lanes))); }
    assert!(n == ITEM_ROWS, "ITEM 10 rows");
    out.extend(rows::rows_of(&super::lzma::decode(include_bytes!("../data/e5.trans.lzma")).expect("transition")));
    let ids = rows::lane_map(include_bytes!("id23.map"));
    let ports = rows::lane_map(include_bytes!("scan-entry.map"));
    let map: Vec<u16> = ids.iter().map(|&id| ports.get(id as usize).copied().unwrap_or(u16::MAX)).collect();
    let bridge = rows::rows_of(&super::lzma::decode(include_bytes!("../data/e5.bridge.lzma")).expect("bridge"));
    assert!(bridge.len() == 28_178);
    let trace = super::lzma::decode(include_bytes!("../data/e5.trc.lzma")).expect("e5 trace");
    let mut classical = scan::Classical::new();
    classical.cursor([20920, 24600, 26600]);
    let mut scan_rows = 0u64;
    scan::run(&trace, 11628, &mut classical, &mut |row| {
        if scan_rows == 224_512_918 { out.push([12, ports[227], 11686, 65535]); }
        if scan_rows == 266_613_070 { out.extend_from_slice(&bridge); }
        out.push(rows::remap(row, &map)); scan_rows += 1;
    }, 230);
    assert!(scan_rows == SCAN_ROWS, "E5 scan rows");
    out.extend(rows::rows_of(include_bytes!("tail18.r8")));
    assert!(out.len() - start == 370_484_040, "E5 leaf rows");
}
