//! q631 / sc (agent sc, 2026-11-19; LOCAL RESEARCH, never part of a package, nothing in the build path calls it):
//! scan-level tools for the small scans B (index 0) and B' (index 4):
//!   * `shipped_trace(i)`: scan i's trace as shipped (data/scans.trc);
//!   * `expand(i, trace)`: scan i's records exactly as mod.rs `scan_rows` makes them (same pack, same dispatch, the
//!     classical layer's state carried through scans 0..i-1 with the shipped traces), in LOGICAL lanes (segment map
//!     applied, before the relabelling);
//!   * `count_to(i, trace, byte)`: number of records of scan i before the trace event at byte offset `byte`;
//!   * switches SC_SCAN_B / SC_SCAN_BP: the q631 traces (data/q631_b.trc = scan B with one dirty carry in the E load
//!     and A's dirty / clean boundary one lane up, 631 lanes; data/q631_bp.trc = scan B' with the hit written straight
//!     into the target lanes through a CX fan around one MCX, no flag lane, 631 lanes, same Toffoli count) replace the shipped trace of scan 0 / 4 in `scan_rows` (hook
//!     `scq631::trace_for`) only when the switch is true.  Both are false: the build is the tree's, byte for byte.
//!     NOTE: with a switch on, the relabelling table (data/relabel.lzma, bound to the list's positions and hash) must be
//!     re-planned before a full build (i1::apply asserts the hash); the scans themselves are tested by scan-level replay.
use super::*;
/// scan B with the q631 trace (data file q631_b.trc) in the tree's build: OFF
pub const SC_SCAN_B: bool = false;
/// scan B' with the q631 trace (data file q631_bp.trc) in the tree's build: OFF
pub const SC_SCAN_BP: bool = false;
/// the q631 trace of scan i (0 = B, 4 = B'), decoded
pub fn q631_trace(i: usize) -> Vec<u8> {
    let d: &[u8] = match i { 0 => include_bytes!("data/q631_b.trc"), 4 => include_bytes!("data/q631_bp.trc"), _ => panic!("q631 trace: scan {}", i) };
    lzma::decode(d).expect("q631 trace")
}
/// scan_rows hook: the trace that scan i expands (the q631 trace when its switch is on, else the shipped one, unchanged)
pub fn trace_for(i: usize, shipped: Vec<u8>) -> Vec<u8> {
    if (i == 0 && SC_SCAN_B) || (i == 4 && SC_SCAN_BP) { q631_trace(i) } else { shipped }
}
pub fn shipped_trace(i: usize) -> Vec<u8> {
    let data: &[u8] = include_bytes!("data/scans.trc"); assert!(&data[..8] == b"SCANS1\0\0", "scan traces");
    let n = u32::from_le_bytes(data[8..12].try_into().unwrap()) as usize; assert!(i < n); let mut at = 12 + 4 * n;
    for j in 0..n { let len = u32::from_le_bytes(data[12 + 4 * j..16 + 4 * j].try_into().unwrap()) as usize;
        if j == i { return lzma::decode(&data[at..at + len]).expect("scan trace"); } at += len; }
    unreachable!()
}
/// the pack exactly as `assemble` prepares it before `scan_rows`
pub fn pack() -> Pack { let mut pk = Pack::parse(&lzma::decode(include_bytes!("data/pack.lzma")).expect("pack tables"));
    walkpack::apply(&mut pk); unrollpack::check(&pk); i1::w4_apply(&mut pk); pk }
/// (output start, output end, bit0, segment) of scan i in the pack (pre-shift positions)
pub fn scan_info(pk: &Pack, i: usize) -> (u64, u64, u32, usize) { let sp = &pk.scans[i]; (sp.out, sp.end, sp.bit0, pk.seg_of(sp.out)) }
/// the segment map (id -> logical lane) of scan i
pub fn scan_map(pk: &Pack, i: usize) -> Vec<u16> { pk.segs[pk.seg_of(pk.scans[i].out)].map.clone() }
/// one scan through the tree's own expander and dispatch (scan_rows), records in local ids
fn run_one(pk: &Pack, i: usize, trace: &[u8], cls: &mut scan::Classical, put: &mut dyn FnMut(Row)) {
    let sp = &pk.scans[i];
    let k0 = pk.wmr.partition_point(|x| x.0 < sp.out); let ranged = k0 < pk.wmr.len() && pk.wmr[k0].0 == sp.out;
    let ins = pk.ins_of(true, i); let fixed = ranged || !ins.is_empty();
    assert!(!fixed || i != 0 && i != 4, "scq631: B / B' are unranged without inserts");
    vm::TOP_BIT.with(|t| t.set(!fixed));
    if i == 0 { borrow_scan::run(trace, sp.bit0, cls, put, KG_ZERO[i]); }
    else if i == 4 && i1::BP_NATIVE { bp_scan::run(trace, sp.bit0, cls, put, -1, 214, true); }
    else if fixed { scan::run(trace, sp.bit0, cls, put, KG_ZERO[i]); }
    else { opt_scan::run(trace, sp.bit0, cls, put, KG_ZERO[i], true); }
    vm::TOP_BIT.with(|t| t.set(false));
}
/// the classical layer's state at the entry of scan i (scans 0..i-1 expanded with their shipped traces, records dropped)
fn cls_at(pk: &Pack, i: usize) -> scan::Classical { let mut cls = scan::Classical::new();
    for j in 0..i { let tr = shipped_trace(j); let mut sink = |_r: Row| {}; run_one(pk, j, &tr, &mut cls, &mut sink); } cls }
/// scan i's records for `trace` (logical lanes, segment map applied; scans 0 and 4 have no ranges / inserts)
pub fn expand(pk: &Pack, i: usize, trace: &[u8]) -> Vec<Row> {
    let mut cls = cls_at(pk, i); let map = scan_map(pk, i); let mut rows: Vec<Row> = Vec::with_capacity(70_000_000);
    { let mut put = |r: Row| rows.push(map_lanes(r, &map)); run_one(pk, i, trace, &mut cls, &mut put); }
    rows
}
/// number of records that scan i emits before the trace event starting at byte `at` (the trace cut there, end marker appended)
pub fn count_to(pk: &Pack, i: usize, trace: &[u8], at: usize) -> u64 {
    let mut t = trace[..at].to_vec(); t.push(0); let mut cls = cls_at(pk, i); let mut n = 0u64;
    { let mut put = |_r: Row| n += 1; run_one(pk, i, &t, &mut cls, &mut put); } n
}
/// logical -> physical (the relabelling's transposition (632 h) of the stretch)
pub fn to_physical(r: Row, h: u16) -> Row { i1::sigma(r, h) }
