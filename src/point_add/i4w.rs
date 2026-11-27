//! i4w (q631 agent i4, 2026-11-19; local research, NOT part of any package; switch ON = false): ITEM 4 (item 4, segment 8, the
//! guest-carrying 129-bit divide Y <- Y R^-1 mod p) in one lane fewer on stretches where a group of IDLE lanes (no record of the
//! stretch names them) holds a value from a structurally small set.  At the stretch start a short reversible circuit re-encodes
//! the group so that one of its lanes is zero for every value of the set; at the stretch end the inverse circuit restores it.
//! Inside the stretch the lane is zero and named by no record, so a relabelling can host another value there.
//!
//! The rows are ITEM 4's records as they stand in the relabelled stream (physical lanes 0..631, the census list of c1 /
//! hybtools::c1_build): `rewrite(rows)` returns the rewritten block; positions are offsets from the item's first record.
//!
//! Re-encodings (each: stretch [t0, t1), lanes, structural set, circuit):
//!  R1  run 1 core [13_047_600, 37_288_393) (24,240,793 records of the 27,925,340-record run at 632 live lanes):
//!      lanes (x0 x1 x2 x3 x4) = (2, 257, 620, 616, 617) hold (g mod 8, A bit 127, A bit 128) where g = gcd(M0, Y mod M0),
//!      M0 = R << clz(R) in [2^128, 2^129), A = 2^256 |v| mod (M0 / g) (alpha accumulator).  A < M0/g < 2^129/g gives
//!      13 values: top = (A >> 127) in {0..3} only for g = 1, in {0, 1} for g in {2, 3}, 0 otherwise (g = 9, 10, 11, ... have
//!      A < 2^126).  Encoder (frees x2 = lane 620): CX(x0->x3) CX(x2->x4) CCX(x2,x3->x0) CCX(~x0,x4->x2); decoder = reverse.
//!      Tested by paired block replay (~/Projects/ecdsafail/q631/i4/tools i4test): exit identical on 6,656 shots, lane 620 zero
//!      inside the stretch on every shot the original computes correctly (report: q631/i4/summary.py).
type Row = [u16; 4];
const NONE: u16 = u16::MAX;
/// builder switch (no builder code reads it yet; see the module comment of i4tools / summary.py for the hook)
pub const ON: bool = false;
/// one re-encoding: stretch, the group's lanes (physical), the encoder rows (decoder = the same rows reversed)
pub struct Reenc { pub name: &'static str, pub t0: usize, pub t1: usize, pub lanes: &'static [u16], pub freed: u16, pub enc: fn() -> Vec<Row> }
fn r1_enc() -> Vec<Row> { let (x0, x2, x3, x4) = (2u16, 620u16, 616u16, 617u16);
    vec![[8, x0, x3, NONE], [8, x2, x4, NONE], [13, x2, x3, x0], [6, x0, NONE, NONE], [13, x0, x4, x2], [6, x0, NONE, NONE]] }
pub const REENC: &[Reenc] = &[
    Reenc { name: "R1 run-1 core: (g mod 8, A bits 127..128) -> lane 620 free", t0: 13_047_600, t1: 37_288_393, lanes: &[2, 257, 620, 616, 617], freed: 620, enc: r1_enc },
];
#[inline] fn nq(k: u16) -> usize { match k { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }
/// the rewritten block (all re-encodings in `sel`, by index into REENC); asserts the structural precondition of each: no record
/// of [t0, t1) names a lane of the group
pub fn rewrite(rows: &[Row], sel: &[usize]) -> Vec<Row> {
    let mut ins: Vec<(usize, Vec<Row>)> = Vec::new();
    for &k in sel { let r = &REENC[k]; assert!(r.t0 <= r.t1 && r.t1 <= rows.len(), "i4w {}: stretch outside the item", r.name);
        for i in r.t0..r.t1 { let w = rows[i]; for j in 1..=nq(w[0]) { assert!(!r.lanes.contains(&w[j]), "i4w {}: record {} names lane {} of the group", r.name, i, w[j]); } }
        let e = (r.enc)(); let mut d = e.clone(); d.reverse();
        ins.push((r.t0, e)); ins.push((r.t1, d)); }
    ins.sort_by_key(|x| x.0);
    let mut out = Vec::with_capacity(rows.len() + ins.iter().map(|x| x.1.len()).sum::<usize>()); let mut p = 0usize;
    for (at, v) in ins { out.extend_from_slice(&rows[p..at]); out.extend_from_slice(&v); p = at; }
    out.extend_from_slice(&rows[p..]);
    out
}
