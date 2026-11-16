//! f18 scan: kit Q633-DIVIDER-OPT-PAIR/f18 (scan.rs / opt_scan.rs / opt_rns.rs / rns.rs / vm.rs / cl.rs), emitted from its trace with lane map map.bin.
#![allow(dead_code, unused, unused_mut)]
pub type Row = [u16; 4];
mod cl;
mod rns;
mod vm;
mod scan;
mod opt_rns;
mod opt_scan;

/// rows of the whole stage, appended to `out` (`loan` = last argument of the kit's emitter)
pub fn emit(trace: &[u8], map: &[u8], loan: i32, out: &mut Vec<Row>) {
    let mapping: Vec<u16> = map.chunks_exact(2).map(|v| u16::from_le_bytes([v[0], v[1]])).collect();
    let mut cls = scan::Classical::new();
    cls.stage_start([17316, 24600, 26600]);
    let mut put = |mut row: Row| {
        let n = match row[0] { 6 | 7 | 12 => 1, 8 | 9 => 2, 13 => 3, _ => 0 };
        for field in &mut row[1..1 + n] { let q = *field; *field = mapping[q as usize]; assert_ne!(*field, 65535, "unmapped quantum lane {q}"); }
        out.push(row);
    };
    opt_scan::run(trace, 11293, &mut cls, &mut put, loan);
}
