//! q631 / fl (agent fl, 2026-11-19; local research, NOT part of any package; nothing in the builder calls it): ITEM 4 (the first divide)
//! with lane 2 free from the run-1 head through the whole alpha tail.  Switch ON = false.
//!
//! Input: ITEM 4's rows as q631::apply_items_c leaves them (i4g -> i4w R1 -> i4dwalk -> i4ewalk -> sm4; 123,643,268 rows, physical lanes;
//! = the stage-F census list's [509,430,722, 633,073,990), MEASURED byte-identical to agent sm's rows4_sm2.bin).
//!
//! THE ENCODING E2 (lanes: 2 = g bit 0, 617 = A bit 128, 258 = mg bit 128 = G1 := [g == 1]; g mg = M0 in [2^128, 2^129)):
//!   A < mg, and mg < 2^128 unless g = 1, so A bit 128 = 0 unless G1 (DERIVED); g = 1 makes g bit 0 = 1 (DERIVED).  So the pair
//!   (2, 617) holds (g0, 0) when not G1 and (1, A128) when G1: one bit per class.  E2 keeps it in lane 617 alone:
//!   617 := (G1 ? A128 : g0), lane 2 := 0.
//!   * encoder: the run-1 head's move "CX 257 -> 2; CX 2 -> 257" (lane 2 is 0 and free before it; it moves g0 from 257 into 2) is
//!     replaced by a transfer of g0 from 257 into 617 that never touches lane 2 (258 = NOT G1 here: inside the X frame of 258 opened
//!     at item +12,981,288, MEASURED on every pool shot):
//!         CCX 258 257 -> 617; CCX 258 617 -> 257; X 257; CX 258 -> 257      (lane 2 free throughout; 257 = 0 after, as before)
//!   * R1 (agent i4's re-encoding, encoder at +13,047,600, decoder at +37,288,399) is removed: its five lanes stay idle until the alpha
//!     tail anyway, and lane 2 is free over its whole stretch instead of lane 620.
//!   * the seam: agent i4b's E_A encoder (+37,983,246, 80 records; the first records that read lane 2 again) is replaced by the
//!     transcoder flseam (E2 form -> E_A form directly, lane 2 free until its beta gate, lane 258 free from there; 16,429 records),
//!     so there is no E2 decoder and no record of the seam without a free lane.
//!   Between encoder and decoder no record names lane 2 (asserted).  Lane 617 is idle until +37,674,290; from there to the decoder
//!   (alpha row 129 = the G1 row and its sign corrections) it is read and written as J[128]: G1 shots see their true A128; for every
//!   other shot the row's gadgets are controlled off (row flag = mg bit 128 = 0) and each of them restores J whatever J holds (plus /
//!   digit / ltg / incReg with control 0 compute and uncompute on the same operands; two-toggle pairs), so g0 parked in J[128]
//!   comes back unchanged (ARGUED from the published gadgets; MEASURED by the paired replays below).
//! Cost: +16,339 records, +12,120 CCX (R1's encoder + decoder: -12 records / -4 CCX; transfer +2 / +2; seam 84 -> 16,429 records,
//! 24 -> 12,178 CCX).  Freed: lane 2 over [+12,981,424, the seam's beta gate), then lane 258 into i4b's window (NEW coordinates).
//! (the planner's floor in ITEM 4 drops by the alpha tail 694,926 + the run-1 head 66,171 + the R1 seam records).
//! Tests: fl/tools ipair (paired whole-item replay from saved entry states, original vs rewritten, every lane + phase on every good
//! shot): see ~/Projects/ecdsafail/q631/fl/summary.py.
//! Integration note: the item shrinks by 6 records; the relabelling frame 2 records before ITEM 4's end moves with the end (as in
//! q631's own bookkeeping); every later position moves by -6.
use super::super::{Row, NONE};
pub const ON: bool = false;
/// item-relative positions in the INPUT rows (asserted by content)
pub const MOVE_AT: usize = 12_981_424;
pub const R1_ENC_AT: usize = 13_047_600;
pub const R1_DEC_AT: usize = 37_288_399;
pub const DEC_AT: usize = 37_983_246;
pub const IN_LEN: usize = 123_643_268;
pub const OUT_LEN: usize = IN_LEN - 12 + 2 + 16_429 - 80;
fn r1_enc() -> Vec<Row> { let (x0, x2, x3, x4) = (2u16, 620u16, 616u16, 617u16);
    vec![[8, x0, x3, NONE], [8, x2, x4, NONE], [13, x2, x3, x0], [6, x0, NONE, NONE], [13, x0, x4, x2], [6, x0, NONE, NONE]] }
pub fn transfer() -> Vec<Row> { vec![[13, 258, 257, 617], [13, 258, 617, 257], [6, 257, NONE, NONE], [8, 258, 257, NONE]] }
/// the E2 decoder (258 = G1): used only by the variant without the seam transcoder (rewrite_dec)
pub fn decoder() -> Vec<Row> { vec![[8, 617, 2, NONE], [13, 258, 617, 2], [8, 2, 617, NONE], [8, 258, 2, NONE]] }
use super::flseam;
#[inline] fn nq(k: u16) -> usize { match k { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }
fn names(r: &Row, l: u16) -> bool { (1..=nq(r[0])).any(|j| r[j] == l) }
pub struct Stats { pub freed: (usize, usize), pub lane: u16 }
/// the rewritten item and the freed stretch [s, e) of lane 2 in the new coordinates
pub fn rewrite(rows: &[Row]) -> (Vec<Row>, Stats) { rewrite_v(rows, true) }
/// `seam` = false: the E2 decoder in front of the E_A encoder instead of the transcoder (84 records without a free lane remain)
pub fn rewrite_v(rows: &[Row], seam: bool) -> (Vec<Row>, Stats) {
    assert!(rows.len() == IN_LEN, "fli4: ITEM 4 length {}", rows.len());
    assert!(rows[MOVE_AT] == [8, 257, 2, NONE] && rows[MOVE_AT + 1] == [8, 2, 257, NONE], "fli4: the run-1 head move");
    let e = r1_enc(); let mut d = e.clone(); d.reverse();
    assert!(rows[R1_ENC_AT..R1_ENC_AT + 6] == e[..], "fli4: R1 encoder"); assert!(rows[R1_DEC_AT..R1_DEC_AT + 6] == d[..], "fli4: R1 decoder");
    assert!(rows[DEC_AT] == [13, 2, 627, 621] && rows[DEC_AT - 1] == [13, 258, 624, 613], "fli4: the E_A encoder start");
    for i in MOVE_AT + 2..DEC_AT { if (R1_ENC_AT..R1_ENC_AT + 6).contains(&i) || (R1_DEC_AT..R1_DEC_AT + 6).contains(&i) { continue; }
        assert!(!names(&rows[i], 2), "fli4: record +{} names lane 2", i);
        if i < 37_674_290 { assert!(!names(&rows[i], 617), "fli4: record +{} names lane 617 before the alpha row 129", i); }
    }
    let ea = flseam::ea_rows(&flseam::LANES4, &flseam::DIRTY4); assert!(rows[DEC_AT..DEC_AT + ea.len()] == ea[..], "fli4: the E_A encoder");
    let mut out: Vec<Row> = Vec::with_capacity(OUT_LEN);
    out.extend_from_slice(&rows[..MOVE_AT]); out.extend(transfer());
    out.extend_from_slice(&rows[MOVE_AT + 2..R1_ENC_AT]); out.extend_from_slice(&rows[R1_ENC_AT + 6..R1_DEC_AT]);
    let s = MOVE_AT;
    out.extend_from_slice(&rows[R1_DEC_AT + 6..DEC_AT]); let e2 = out.len();
    if seam { out.extend(flseam::seam_rows(&flseam::LANES4, &flseam::DIRTY4)); out.extend_from_slice(&rows[DEC_AT + ea.len()..]); assert!(out.len() == OUT_LEN); }
    else { out.extend(decoder()); out.extend_from_slice(&rows[DEC_AT..]); assert!(out.len() == IN_LEN - 6); }
    (out, Stats { freed: (s, e2), lane: 2 })
}
