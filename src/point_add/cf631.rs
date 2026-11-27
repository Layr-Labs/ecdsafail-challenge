//! cf631 (q631 / cf1, 2026-11-19; local research, NOT submitted): the new 631-lane forward upper walk (Codex session,
//! delivered as a code-only generator: research/upperwalk_forward631*.rs, used UNMODIFIED) spliced into walks 1 and 3.
//!
//! WHAT: in each of the two forward walks (segments 2 and 18), everything of his compiled forward walk from our hybrid
//! rows' hand-over P_65 (= the end of hybrid.rs's forward region) to the end of his forward walk (his columns 65..127,
//! his finish, the erasure of the third value U = t_J-1 by measurement, the passenger mask restore) is dropped and the
//! generator's `forward` is written in its place (prefix X H1, columns 65..127, terminal: 127 HMR of U_i into
//! base + i, X on Y0..Y63).  The original reverse walk (and our reverse rows) are unchanged.
//!
//! WHERE: on the assembled list AFTER hybrid::splice (positions below are positions of that list) and BEFORE the i1
//! relabelling, exactly like hybrid.rs.  The generated block is LONGER than the range it replaces (154,519,556 vs his
//! ~112.8M records), so the list grows; the slack comes from hybrid::splice (which shrinks the list by 190.6M records;
//! asserted).  The relabelling table (already re-bound by hybrid::splice) is re-bound once more: entries before a range
//! kept, entries after it moved by the growth, entries strictly inside dropped (there are none: asserted by the survey
//! numbers below and by `rebind`), the frame at both ends must be the same hidden lane, which no generated row names.
//!
//! WIRES (DERIVED from the generator's Frame::new and the delivered INTEGRATION.txt, then MEASURED by the census):
//!   own 0..255 -> X0..X255 (ids 0..255); 256 -> Z0 (512); 257..384 -> Z1..Z128 (513..640); 385 -> H1 (642);
//!   386 -> H2 (643); 387 -> H4 = parity (645); 388..629 -> Y0..Y241 (256..497); 630 -> H3 (644).  H0 (id 641) is NOT
//!   named: that is the lane the new forward frees.  his id -> lane through the segment's map (the same map his records of
//!   that range use).
//! CLASSICAL: the generator measures U_i into base + i (i = 0..126); base = the bit the tree's copy of his reverse reads
//!   in its deferred phase fix [PUSH b; Z X129+i; POP] for i = 0 (survey); his upper-column records are NOT written (the
//!   reverse's conditional repairs on them see 0).
use super::*;
use super::upperwalk_forward631 as uw;
use crate::circuit::{BitId, QubitId};
use super::i1::{self, Relabel, HIDE};

/// THE SWITCH.  false = the tree unchanged (byte-identical op list); true = walks 1 and 3 get the new forward upper walk.
/// Requires hybrid::ON (the new forward starts at our rows' hand-over P_65).
pub const ON: bool = super::FINAL631;

pub struct Region { pub start: u64, pub end: u64, pub seg: usize, pub base: u16 }
/// positions in the hybrid-spliced assembled list (before the relabelling), MEASURED by cfdump + cfscan (cf/summary.py
/// stage 1): start = our forward rows' end P_65 (hybrid::layout end of regions 0 / 2); end = the end of his forward walk =
/// the end of segment 2 / 18 (his pieces 513..737 / 5115..5339; the next record is the first of scan B / B').  Each range
/// is 112,847,319 records = the 633 tree's [128,110,609, 240,957,928).  The relabelling hides lane 632 on lane 498 from
/// 23,372,869 to 196,635,000 / from 1,104,606,068 to 1,293,235,411: no table entry inside or at either end.
/// base = 10098 in both walks: the tree's reverse walks read U_i's record in [PUSH b(10098+i); Z X(129+i); POP] at
/// 876,392,124 + 3i (seg 13) and 1,951,880,826 + 3i (seg 29) and clear 10050..10224 at the end of those segments.
pub const REGIONS: [Region; 2] = [
    Region { start: 83_714_879, end: 196_562_198, seg: 2, base: 10098 },
    Region { start: 1_165_371_475, end: 1_278_218_794, seg: 18, base: 10098 },
];
/// generated records per region (asserted; = the delivered whole-walk count)
pub const GEN_LEN: u64 = 154_519_556;

/// his id of the generator's own wire i (0..630)
pub fn own_id(i: usize) -> usize {
    match i { 0..=255 => i, 256..=384 => 512 + (i - 256), 385 => 642, 386 => 643, 387 => 645, 388..=629 => 256 + (i - 388), 630 => 644, _ => panic!("own wire {}", i) }
}
/// the generator's frame for a segment map (his id -> logical lane)
pub fn frame(seg_map: &[u16]) -> uw::Frame {
    let l = |id: usize| { let v = seg_map[id]; assert!(v != NONE && v < 633, "cf631: id {} has no lane ({})", id, v); QubitId(v as u64) };
    let walk: [QubitId; 389] = std::array::from_fn(|i| l(own_id(if i < 388 { i } else { 630 })));
    let pass: [QubitId; 242] = std::array::from_fn(|k| l(own_id(388 + k)));
    uw::Frame::new(walk, pass)
}
/// the generated rows of one region (logical lanes of the segment map, classical bits base..base+126); returns the count
pub fn gen(seg_map: &[u16], base: u16, put: &mut dyn FnMut(Row)) -> u64 {
    assert!((base as u32) + 127 <= 65533, "cf631: classical base {}", base);
    let fr = frame(seg_map);
    let mut cnt = 0u64;
    let cost = uw::forward(&fr, BitId(base as u64), |op| { let r = op_to_row(&op); assert!(matches!(r[0], 6 | 8 | 12 | 13), "cf631: op kind {}", r[0]); put(r); cnt += 1; });
    assert!(cost.gates == cnt && cnt == GEN_LEN, "cf631: {} generated rows (cost {})", cnt, cost.gates);
    cnt
}

/// fingerprints of the cut points (MEASURED by the survey, rows of the hybrid-spliced list through the segment map)
fn check<S: Slot>(pk: &Pack, out: &[S]) {
    for (i, r) in REGIONS.iter().enumerate() {
        let m = &pk.segs[r.seg].map; let (s, e) = (r.start as usize, r.end as usize);
        assert!(s > 0 && e > s, "cf631 region {} positions not set", i);
        let row = |p: usize| out[p].to_row();
        let l = |id: usize| { let v = m[id]; assert!(v != NONE); v };
        // entry: the last row of our forward rows' exit adapter (X Y63), then his "X Z65; CCX(Z0, Z65 -> X0)"
        assert_eq!(row(s - 1), [6, l(hybrid::y(63)), NONE, NONE], "cf631 region {} entry fingerprint", i);
        assert_eq!(row(s), [6, l(hybrid::z(65)), NONE, NONE], "cf631 region {} first dropped row", i);
        assert_eq!(row(s + 1), [13, l(hybrid::z(0)), l(hybrid::z(65)), l(hybrid::x(0))], "cf631 region {} first dropped rows", i);
        for (k, f) in EXIT_FP[i].iter().enumerate() { let p = e - EXIT_FP[i].len() + k; let mut want = *f;
            for j in 1..=qubits(want[0]) { want[j] = l(want[j] as usize); } assert_eq!(row(p), want, "cf631 region {} exit fingerprint {}", i, k); }
    }
}
/// the last records of each replaced range in his ids (lanes through the segment map at check time): MEASURED by the survey
const EXIT_FP: [&[Row]; 2] = [&[[6, 0, NONE, NONE], [8, 1, 514, NONE], [8, 1, 513, NONE]], &[[6, 0, NONE, NONE], [8, 1, 514, NONE], [8, 1, 513, NONE]]];   // X X0; CX X1 -> Z2; CX X1 -> Z1

/// the i1 hash of out[..n]
fn stream_hash<S: Slot>(out: &[S]) -> u64 { hybrid::stream_hash(out) }

/// re-bind the (hybrid-re-bound) relabelling table to the cf-spliced stream; `named(i, lane)` = generated region i names
/// the (pre-relabel) lane.  Returns the entries and per region (h_s, h_e, dropped).
pub fn rebind(t: &Relabel, named: &dyn Fn(usize, u16) -> bool) -> (Vec<(u64, u16, u8)>, Vec<(u16, u16, usize)>) {
    let mut notes = Vec::new();
    let mut ent: Vec<(u64, u16, u8)> = Vec::with_capacity(t.ent.len());
    let (mut k, m) = (0usize, t.ent.len());
    let mut d = 0i64;   // growth of the regions passed so far
    for (i, r) in REGIONS.iter().enumerate() {
        while k < m && t.ent[k].0 <= r.start { let e = t.ent[k]; ent.push(((e.0 as i64 + d) as u64, e.1, e.2)); k += 1; }
        let hs = hybrid::frame_at(t, r.start); let he = hybrid::frame_at(t, r.end - 1);
        assert!(hs != HIDE && hs == he, "cf631 region {}: hidden lane at the start {} and at the end {} (must be one lane, not 632)", i, hs, he);
        assert!(!named(i, hs), "cf631 region {}: a generated row names the hidden lane {}", i, hs);
        let mut dropped = 0usize;
        while k < m && t.ent[k].0 < r.end { dropped += 1; k += 1; }
        assert!(dropped == 0, "cf631 region {}: {} relabelling entries inside the range", i, dropped);
        d += GEN_LEN as i64 - (r.end - r.start) as i64;
        notes.push((hs, he, dropped));
    }
    while k < m { let e = t.ent[k]; ent.push(((e.0 as i64 + d) as u64, e.1, e.2)); k += 1; }
    assert!(ent.windows(2).all(|w| w[0].0 <= w[1].0), "cf631: re-bound table out of order");
    (ent, notes)
}
/// new position of a position of the hybrid-spliced list outside the replaced ranges (a range end -> end of its block)
pub fn map_pos(p: u64) -> u64 {
    let mut d = 0i64;
    for r in REGIONS.iter() { if p >= r.end { d += GEN_LEN as i64 - (r.end - r.start) as i64; } else { assert!(p <= r.start, "cf631: position inside a replaced range"); } }
    (p as i64 + d) as u64
}
/// (old start, old end, new start, new length) of the two regions
pub fn layout() -> Vec<(u64, u64, u64, u64)> {
    let mut d = 0i64;
    REGIONS.iter().map(|r| { let ns = (r.start as i64 + d) as u64; d += GEN_LEN as i64 - (r.end - r.start) as i64; (r.start, r.end, ns, GEN_LEN) }).collect()
}

/// what the last `splice` did (read by the local tools; the builder prints nothing)
pub static LOG: std::sync::Mutex<String> = std::sync::Mutex::new(String::new());
/// splice the two regions into out[..n] (the hybrid-spliced list) in place, growing it; re-bind the relabelling table
pub fn splice<S: Slot>(pk: &Pack, out: &mut [S], n: usize, rt: Option<Relabel>) -> (usize, Option<Relabel>) {
    assert!(REGIONS.windows(2).all(|w| w[0].end < w[1].start) && (REGIONS[1].end as usize) < n, "cf631: region order");
    check(pk, out);
    if let Some(t) = &rt { let hh = stream_hash(&out[..n]);
        assert!(t.n == n as u64 && t.hash == hh, "cf631: relabel table was bound to another stream (table n {} hash {:016x}, stream n {} hash {:016x})", t.n, t.hash, n, hh); }
    let lay = layout();
    let grow: i64 = REGIONS.iter().map(|r| GEN_LEN as i64 - (r.end - r.start) as i64).sum();
    let nn = (n as i64 + grow) as usize;
    assert!(out.len() >= nn + i1::extra(&rt) + TAIL, "cf631: no room to grow the list ({} slots, need {})", out.len(), nn + i1::extra(&rt) + TAIL);
    let mut lanes: Vec<Vec<bool>> = vec![vec![false; 633]; REGIONS.len()];
    // last region first: move the part after it right, then write its block (never overlaps the unmoved part before it)
    let mut tail = n;
    for i in (0..REGIONS.len()).rev() {
        let r = &REGIONS[i]; let (s, e) = (r.start as usize, r.end as usize);
        let ns = lay[i].2 as usize; let ne = ns + GEN_LEN as usize;
        let shift = ne as i64 - e as i64; assert!(shift >= 0);
        out.copy_within(e..tail, ne);
        let mut w = ns; let ln = &mut lanes[i];
        let cnt = gen(&pk.segs[r.seg].map, r.base, &mut |row| { assert!(w < ne, "cf631: generated rows overrun region {}", i);
            for j in 1..=qubits(row[0]) { ln[row[j] as usize] = true; } out[w] = S::from_row(row); w += 1; });
        assert!(w == ne && cnt == GEN_LEN, "cf631 region {}: {} rows", i, cnt);
        tail = s;
    }
    let rt = rt.map(|t| { let (ent, notes) = rebind(&t, &|i, l| lanes[i][l as usize]);
        let nt = Relabel { n: nn as u64, hash: stream_hash(&out[..nn]), h0: t.h0, ent };
        let named: Vec<usize> = lanes.iter().map(|v| v.iter().filter(|&&b| b).count()).collect();
        *LOG.lock().unwrap() = format!("cf631 rebind: table {} entries -> {}; per region (h_s, h_e, dropped): {:?}; lanes named per region {:?}; new n {} hash {:016x}",
            t.ent.len(), nt.ent.len(), notes, named, nt.n, nt.hash);
        nt });
    (nn, rt)
}
