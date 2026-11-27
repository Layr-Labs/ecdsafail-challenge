//! q631 / fl (agent fl, 2026-11-19; local research, NOT part of any package; nothing in the builder calls it): ITEM 12 (the second divide,
//! n = 127) with lane 513 free from agent i12's R1 encoder point through alpha row 127.  Switch ON = false.
//!
//! Input: ITEM 12's rows as q631::apply_items_c leaves them (i12w::rewrite_full + sm12; 120,669,154 rows, physical lanes; = the stage-F
//! census list's [1,780,954,785, 1,901,623,939), dumped by fl's flprobe).
//! ENCODING E2 (the ITEM 4 one, transferred; lanes 513 = g bit 0, 239 = A bit 126, 258 = mg bit 126 = G1 := [g == 1]):
//!   A < mg < 2^126 unless g = 1 (g mg = M0 in [2^126, 2^127)), so A bit 126 = 0 unless G1; g = 1 makes g bit 0 = 1 (DERIVED).
//!   239 := (G1 ? A126 : g0), 513 := 0.
//!   * encoder right after the alpha-start E_A decoder's last read of 513 (+12,267,474, before the X of 258 at +475: 258 = G1 there,
//!     MEASURED): CX 258 -> 513; CX 513 -> 239; CX 239 -> 513; CCX 258 239 -> 513 (so the two rail swaps at +476..481, controlled by the
//!     row flag 515, have lane 513 free); i12's R1 encoder (+12,267,482) and decoder (+34,017,089) removed.  Agent sm's row-126 stash (G1 AND 239 into 257) stays: on G1 shots
//!     it sees A126 as before, on the others it is a no-op.
//!   * the seam: i12's ipark E_A encoder (+34,642,139, 80 records, the first records that read 513 again; 258 = G1 there, MEASURED)
//!     is replaced by the transcoder flseam (E2 form -> E_A form, lane 513 free until its beta gate, 258 from there).
//!   Lane 513 is named by no record in between (asserted).  Lane 239 is J[126] of alpha row 127 (the G1 row): for every other shot
//!   the row is controlled off and restores J whatever it holds (ARGUED as for ITEM 4; MEASURED by the paired replays).
//! Cost: +16,341 records, +12,119 CCX.  The planner floor of ITEM 12 drops 49,722 -> 0 on the planner pool and the fresh pool.
use super::super::{Row, NONE};
pub const ON: bool = false;
pub const ENC_AT: usize = 12_267_474;
pub const R1_ENC_AT: usize = 12_267_482;
pub const R1_DEC_AT: usize = 34_017_089;
pub const DEC_AT: usize = 34_642_139;
pub const IN_LEN: usize = 99_306_873;   // e631b B1
pub const OUT_LEN: usize = IN_LEN + 4 - 12 + 16_429 - 80;
use super::flseam;
fn r1_enc() -> Vec<Row> { let (x0, x2, x3, x4) = (513u16, 241u16, 238u16, 239u16);
    vec![[8, x0, x3, NONE], [8, x2, x4, NONE], [13, x2, x3, x0], [6, x0, NONE, NONE], [13, x0, x4, x2], [6, x0, NONE, NONE]] }
pub fn encoder() -> Vec<Row> { vec![[8, 258, 513, NONE], [8, 513, 239, NONE], [8, 239, 513, NONE], [13, 258, 239, 513]] }
pub fn decoder() -> Vec<Row> { vec![[8, 239, 513, NONE], [13, 258, 239, 513], [8, 513, 239, NONE], [8, 258, 513, NONE]] }
#[inline] fn nq(k: u16) -> usize { match k { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }
pub struct Stats { pub freed: (usize, usize), pub lane: u16 }
pub fn rewrite(rows: &[Row]) -> (Vec<Row>, Stats) { rewrite_v(rows, true) }
/// `seam` = false: the E2 decoder in front of the E_A encoder instead of the transcoder (84 records without a free lane remain)
pub fn rewrite_v(rows: &[Row], seam: bool) -> (Vec<Row>, Stats) {
    assert!(rows.len() == IN_LEN, "fli12: ITEM 12 length {}", rows.len());
    let e = r1_enc(); let mut d = e.clone(); d.reverse();
    assert!(rows[R1_ENC_AT..R1_ENC_AT + 6] == e[..], "fli12: R1 encoder"); assert!(rows[R1_DEC_AT..R1_DEC_AT + 6] == d[..], "fli12: R1 decoder");
    assert!(rows[ENC_AT - 1] == [13, 513, 246, 248] && rows[ENC_AT + 1] == [6, 258, NONE, NONE], "fli12: the alpha-start E_A decoder end");
    assert!(rows[DEC_AT] == [13, 513, 246, 248], "fli12: the ipark E_A encoder start");
    for i in ENC_AT..DEC_AT { if (R1_ENC_AT..R1_ENC_AT + 6).contains(&i) || (R1_DEC_AT..R1_DEC_AT + 6).contains(&i) { continue; }
        assert!(!(1..=nq(rows[i][0])).any(|j| rows[i][j] == 513), "fli12: record +{} names lane 513", i); }
    let ea = flseam::ea_rows(&flseam::LANES12, &flseam::DIRTY12); assert!(rows[DEC_AT..DEC_AT + ea.len()] == ea[..], "fli12: the E_A encoder");
    let mut out: Vec<Row> = Vec::with_capacity(OUT_LEN);
    out.extend_from_slice(&rows[..ENC_AT]); out.extend(encoder()); let s = out.len();
    out.extend_from_slice(&rows[ENC_AT..R1_ENC_AT]); out.extend_from_slice(&rows[R1_ENC_AT + 6..R1_DEC_AT]); out.extend_from_slice(&rows[R1_DEC_AT + 6..DEC_AT]);
    let e2 = out.len();
    if seam { out.extend(flseam::seam_rows(&flseam::LANES12, &flseam::DIRTY12)); out.extend_from_slice(&rows[DEC_AT + ea.len()..]); assert!(out.len() == OUT_LEN); }
    else { out.extend(decoder()); out.extend_from_slice(&rows[DEC_AT..]); assert!(out.len() == IN_LEN - 4); }
    (out, Stats { freed: (s, e2), lane: 513 })
}
