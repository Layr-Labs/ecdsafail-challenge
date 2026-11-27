//! q631 / si (agent si, 2026-11-19; LOCAL RESEARCH, never part of a package): scans I (index 3) and I' (index 7) rebuilding
//! 15 bits (ids 497..511) for the 631-lane reverse brackets.
//!   * switches SI_SCAN_I / SI_SCAN_IP (both false): when true, `trace_for` (hooked in mod.rs scan_rows, after the q631 / sc
//!     hook) returns this module's 15-bit trace of scan 3 / 7 instead of the shipped 14-bit one.  Both false: the build is the
//!     tree's, byte for byte.  NOTE: a 15-bit trace needs the bracket patch (id 497 erased before the reverse walk, its phase
//!     fix after the scan) and a re-planned relabelling table before a full build; it is tested by scan-level replay here.
//!     data/si631_i.trc  = scan I at 15 bits, our generator's rule (~/Projects/ecdsafail/q631/si/gen3.py) with the sweep two
//!                         dirty lanes wider (A gets L bits 9, 10 = ids 265, 266, D gets L bits 7, 8 = ids 263, 264 below their
//!                         low ends, per-step increment u[197..255]) and 29 tested lanes (r0 30);
//!     data/si631_ip.trc = scan I' at 15 bits (gen7.py) with D's clean part six lanes wider (ids 617..622, residue work lanes
//!                         that are free from D's load to its unload), its run-time constant truncated (no rounding carry-in)
//!                         and 31 tested lanes (r0 32).
//!   * tools (nothing in the build path calls them): `info`, `expand` (scan i's records exactly as scan_rows makes them, in
//!     LOGICAL lanes, for any trace, ranges and inserts handled as scan_rows does), `count_to`.
use super::*;
/// scan I (index 3) with the 15-bit trace in the tree's build: OFF
pub const SI_SCAN_I: bool = false;
/// scan I' (index 7) with the 15-bit trace in the tree's build: OFF
pub const SI_SCAN_IP: bool = false;
/// the 15-bit trace of scan i (3 = I, 7 = I'), decoded
pub fn si_trace(i: usize) -> Vec<u8> {
    let d: &[u8] = match i { 3 => include_bytes!("data/si631_i.trc"), 7 => include_bytes!("data/si631_ip.trc"), _ => panic!("si631 trace: scan {}", i) };
    lzma::decode(d).expect("si631 trace")
}
/// scan_rows hook: the trace that scan i expands (the 15-bit trace when its switch is on, else the given one, unchanged)
pub fn trace_for(i: usize, given: Vec<u8>) -> Vec<u8> {
    if (i == 3 && SI_SCAN_I) || (i == 7 && SI_SCAN_IP) { si_trace(i) } else { given }
}
/// (output start, output end, bit0, segment, ranged, number of inserted rows) of scan i in the pack (pre-shift positions)
pub fn info(pk: &Pack, i: usize) -> (u64, u64, u32, usize, bool, usize) {
    let sp = &pk.scans[i]; let k0 = pk.wmr.partition_point(|x| x.0 < sp.out); let ranged = k0 < pk.wmr.len() && pk.wmr[k0].0 == sp.out;
    (sp.out, sp.end, sp.bit0, pk.seg_of(sp.out), ranged, pk.ins_of(true, i).len()) }
fn run_one(pk: &Pack, i: usize, trace: &[u8], cls: &mut scan::Classical, put: &mut dyn FnMut(Row)) {
    let sp = &pk.scans[i];
    let k0 = pk.wmr.partition_point(|x| x.0 < sp.out); let ranged = k0 < pk.wmr.len() && pk.wmr[k0].0 == sp.out;
    let ins = pk.ins_of(true, i); let fixed = ranged || !ins.is_empty();
    vm::TOP_BIT.with(|t| t.set(!fixed));
    if i == 0 { borrow_scan::run(trace, sp.bit0, cls, put, KG_ZERO[i]); }
    else if i == 4 && i1::BP_NATIVE { bp_scan::run(trace, sp.bit0, cls, put, -1, 214, true); }
    else if fixed { scan::run(trace, sp.bit0, cls, put, KG_ZERO[i]); }
    else { opt_scan::run(trace, sp.bit0, cls, put, KG_ZERO[i], true); }
    vm::TOP_BIT.with(|t| t.set(false));
}
/// the classical layer's state at the entry of scan i (scans 0..i-1 expanded with the traces scan_rows uses, records dropped)
pub fn cls_at(pk: &Pack, i: usize) -> scan::Classical { let mut cls = scan::Classical::new();
    for j in 0..i { let tr = scq631::trace_for(j, scq631::shipped_trace(j)); let mut sink = |_r: Row| {}; run_one(pk, j, &tr, &mut cls, &mut sink); } cls }
/// scan i's records for `trace`, in LOGICAL lanes (inserted rows and range rows placed as scan_rows places them)
pub fn expand_with(pk: &Pack, i: usize, trace: &[u8], cls: &mut scan::Classical) -> Vec<Row> {
    let sp = &pk.scans[i]; let seg = pk.seg_of(sp.out); let map = &pk.segs[seg].map;
    let k0 = pk.wmr.partition_point(|x| x.0 < sp.out); let ranged = k0 < pk.wmr.len() && pk.wmr[k0].0 == sp.out; let mut ri = k0;
    let ins = pk.ins_of(true, i); let mut ip = 0usize; let mut cnt = 0u64; let mut o = sp.out as usize;
    let mut rows: Vec<Row> = Vec::with_capacity(40_000_000);
    { let mut emit = |row: Row, o: &mut usize| { let mut row = row; if ranged { if let Some(w) = pk.map_at(&mut ri, *o as u64) { for j in 1..=qubits(row[0]) { row[j] = w[row[j] as usize]; } } }
            rows.push(map_lanes(row, map)); *o += 1; };
      { let mut put = |row: Row| { while ip < ins.len() && ins[ip].off == cnt { emit(ins[ip].row, &mut o); ip += 1; } emit(row, &mut o); cnt += 1; };
        run_one(pk, i, trace, cls, &mut put); }
      while ip < ins.len() && ins[ip].off == cnt { emit(ins[ip].row, &mut o); ip += 1; } }
    assert!(ip == ins.len(), "si631: scan {} inserts not placed", i);
    rows }
pub fn expand(pk: &Pack, i: usize, trace: &[u8]) -> Vec<Row> { let mut cls = cls_at(pk, i); expand_with(pk, i, trace, &mut cls) }
/// number of records scan i emits before the trace event at byte `at` (the trace cut there, end marker appended); inserted
/// rows not counted (scans 3 and 7 have none, checked by the tools)
pub fn count_to(pk: &Pack, i: usize, trace: &[u8], at: usize) -> u64 {
    let mut t = trace[..at].to_vec(); t.push(0); let mut cls = cls_at(pk, i); let mut n = 0u64;
    { let mut put = |_r: Row| n += 1; run_one(pk, i, &t, &mut cls, &mut put); } n
}
