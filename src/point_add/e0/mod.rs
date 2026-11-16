//! E0 scan (Q633r scan code family: scan.rs / borrow_scan.rs / borrow_rns.rs / rns.rs / vm.rs / cl.rs of the production lowering kit),
//! emitted from its trace; lane map applied to the three-operand gate fields exactly as the kit's main.rs does.
//! Kept in its own module because the base builder's scan / rns / vm are older versions of the same files.
#![allow(dead_code, unused, unused_mut)]
pub type Row = [u16; 4];
mod cl;
mod rns;
mod vm;
mod scan;
mod borrow_rns;
mod borrow_scan;

/// rows of the scan stage of `trace` (with `map` = 1024 little-endian u16 lane map), appended to `out`
pub fn emit(trace: &[u8], map: &[u8], zl: i32, out: &mut Vec<Row>) {
    let mapping: Vec<u16> = map.chunks_exact(2).map(|v| u16::from_le_bytes([v[0], v[1]])).collect();
    let mut cls = scan::Classical::new();
    let mut put = |mut row: Row| {
        let n = match row[0] { 6 | 7 | 12 => 1, 8 | 9 => 2, 13 => 3, _ => 0 };
        for field in &mut row[1..1 + n] { let q = *field; *field = mapping[q as usize]; assert_ne!(*field, 65535, "unmapped quantum lane {q}"); }
        out.push(row);
    };
    borrow_scan::run(trace, 10870, &mut cls, &mut put, zl);
}
