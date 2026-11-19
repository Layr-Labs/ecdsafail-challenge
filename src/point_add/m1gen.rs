//! M1: generator of the 632-lane ITEM 2 (127-bit multiply "v2") of the q633a tree, in WIRE space (the block's own numbering, after
//! the four insert rows are placed, before the item's wire map and the segment lane map), so it survives any lane renumbering.
//!
//! Input : the raw wire-space records of ITEM 2 (61,369,502 records).   Output: the replacement records (61,903,460).
//! Wire 251 (lane 113 of segment 5) is never referenced by the output (asserted).
//!
//! What it does (record offsets are offsets inside the raw item):
//!  1. The stash S = Zn + V * T' (257 bits: the product register plus wire BW) is idle through run 2 (records TM .. SA: no record
//!     references BW, asserted).  Its top bit b is measured out at TM (HMR into classical bit `mbit`), which frees one lane for the
//!     whole of run 2, the only stretch of the original that needs 633 lanes.
//!  2. Before the original removes the stash (its split starts at SA, with W = V and T normalised), b is recomputed exactly:
//!     b = [S mod 2^256 < V * T'] = [floor((S mod 2^256) / T') < V].  The original's own split records SA .. SB are run on the low part,
//!     a comparator writes [Q < V] onto the clean wire XW, the split records are run backwards, the bit is moved to BW and the phase
//!     of the measurement is repaired by a Z conditioned on `mbit`.  The original then continues unchanged.
//!  3. A hole schedule (table CHAIN, measured) renames wires so that the lane that is free at each moment is always the same physical
//!     wire; FIX undoes the permutation at the exit.
//! Exact on every input on which the stash is valid (0 <= S - V * T' < 2^256); no approximation is added.
use super::m1tab::*;
pub type Row = [u16; 4];
const NO: u16 = u16::MAX;

pub const LEN: usize = 61_369_502;
/// first record after the last reference to the stash top wire before run 2
pub const TM: usize = 34_776_896;
/// first / one-past-last record of the original's split (long division of the stash by T')
pub const SA: usize = 46_834_892;
pub const SB: usize = 47_101_346;
/// default classical bit of the extra measurement: the item's own first HMR bit, dead after the first conditioned-Z batch (asserted)
pub const MBIT: u16 = 10884;

fn nq(k: u16) -> usize { match k { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }
fn refs(r: &Row, w: u16) -> bool { (1..=nq(r[0])).any(|j| r[j] == w) }
/// multi-controlled NOT with borrowed (dirty) loans (walkgen.rs `op`)
fn op(g: &mut Vec<Row>, c: &[u16], z: u16, loans: &[u16]) {
    let n = c.len();
    match n { 0 => { g.push([6, z, NO, NO]); return; } 1 => { g.push([8, c[0], z, NO]); return; } 2 => { g.push([13, c[0], c[1], z]); return; } _ => {} }
    let b = &loans[..n - 2]; assert!(b.iter().all(|q| !c.contains(q) && *q != z));
    for s in 0..2 {
        if s == 0 { g.push([13, c[0], c[1], b[0]]); }
        for i in 1..n - 2 { g.push([13, c[i + 1], b[i - 1], b[i]]); }
        g.push([13, c[n - 1], b[n - 3], z]);
        for i in (1..=n - 3).rev() { g.push([13, c[i + 1], b[i - 1], b[i]]); }
        if s == 0 { g.push([13, c[0], c[1], b[0]]); }
    }
}
/// h ^= AND(c) and [a > b]; a and b are restored (walkgen.rs `lt`)
fn lt(g: &mut Vec<Row>, c: &[u16], a: &[u16], b: &[u16], h: u16, loans: &[u16]) {
    let n = a.len(); let k = n - 1; assert!(b.len() == n && n >= 2);
    let cat = |x: &[u16]| -> Vec<u16> { let mut v = c.to_vec(); v.extend_from_slice(x); v };
    for &q in b { g.push([6, q, NO, NO]); }
    for i in 1..n { g.push([8, a[i], b[i], NO]); }
    op(g, &cat(&[a[k]]), h, loans);
    for i in (1..=n - 2).rev() { g.push([8, a[i], a[i + 1], NO]); }
    for i in 0..n - 1 { g.push([13, b[i], a[i], a[i + 1]]); }
    op(g, &cat(&[b[k], a[k]]), h, loans);
    for i in (0..=n - 2).rev() { g.push([13, b[i], a[i], a[i + 1]]); }
    for i in 1..n - 1 { g.push([8, a[i], a[i + 1], NO]); }
    for i in 1..n { g.push([8, a[i], b[i], NO]); }
    for &q in b { g.push([6, q, NO, NO]); }
}
/// XW ^= [Q < V]: the low 127 quotient wires against V, enabled by the four top quotient wires being zero
pub fn gadget(g: &mut Vec<Row>) {
    let hi = &QW[127..];
    for &q in hi { g.push([6, q, NO, NO]); }
    lt(g, hi, &VW, &QW[..127], XW, &LOANS);
    for &q in hi { g.push([6, q, NO, NO]); }
}

/// the replacement records of ITEM 2; `mbit` = classical bit for the extra measurement (MBIT unless the integrator allocates a fresh one)
pub fn generate(m: &[Row], mbit: u16) -> Vec<Row> {
    assert!(m.len() == LEN, "ITEM 2 length {}", m.len());
    // anchors of the q633a item (guards against use on another block)
    assert!(m[0] == [8, 135, 252, NO] && m[TM - 1] == [6, BW, NO, NO] && m[SA] == [6, 386, NO, NO] && m[SB - 1] == [6, 383, NO, NO] && m[SB] == [6, 512, NO, NO], "anchors");
    // the stash top wire is idle from the measurement to the split; the split is unitary and never touches XW
    assert!(m[TM..SA].iter().all(|r| !refs(r, BW)), "stash top wire referenced during run 2");
    assert!(m[SA..SB].iter().all(|r| matches!(r[0], 6 | 8 | 13) && !(r[0] == 6 && r[2] != NO) && !(r[0] == 8 && r[3] != NO) && !refs(r, XW)), "split records");
    if mbit == MBIT {
        for (i, r) in m.iter().enumerate() {
            let rd = (matches!(r[0], 6 | 7) && r[2] == mbit) || (matches!(r[0], 8 | 9) && r[3] == mbit) || (matches!(r[0], 3 | 4 | 5 | 15) && (r[1] == mbit || r[2] == mbit));
            assert!(!rd || i < TM, "classical bit {} is used after record {}", mbit, TM);
        }
    }
    let mut o: Vec<Row> = Vec::with_capacity(LEN + 540_000);
    o.extend_from_slice(&m[..TM]);
    o.push([12, BW, mbit, NO]);                       // HMR: the stash top bit is measured out
    o.extend_from_slice(&m[TM..SA]);
    o.extend_from_slice(&m[SA..SB]);                  // split of the low 256 bits
    gadget(&mut o);                                   // XW ^= [Q < V]
    o.extend(m[SA..SB].iter().rev());                 // unsplit
    o.push([8, XW, BW, NO]);                          // the recomputed bit goes back to its wire
    o.push([8, BW, XW, NO]);
    o.push([7, BW, mbit, NO]);                        // phase repair of the measurement
    o.extend_from_slice(&m[SA..]);
    // hole schedule: the wire that is free is always the same physical wire
    let x = CHAIN[0].1;
    let mut pi: Vec<u16> = (0..1024u16).collect();
    let mut ci = 0usize;
    assert!(CHAIN[CHAIN.len() - 1].0 as usize == o.len(), "hole table does not match the stream");
    for i in 0..o.len() {
        while ci + 1 < CHAIN.len() && CHAIN[ci].0 as usize <= i { pi.swap(CHAIN[ci].1 as usize, CHAIN[ci + 1].1 as usize); ci += 1; }
        let k = o[i][0];
        for j in 1..=nq(k) { o[i][j] = pi[o[i][j] as usize]; }
    }
    o.extend_from_slice(&FIX);
    for r in &o { assert!(!refs(r, x), "output references the free wire"); }
    o
}
