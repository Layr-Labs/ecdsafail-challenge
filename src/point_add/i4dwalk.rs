//! i4dwalk (q631 agent i4d, 2026-11-19; local research, NOT part of any package; switch ON = false): ITEM 4 (item 4, segment 8,
//! the first divide) with its INNER Euclid walk re-emitted by the tree's own walk generator with two clean tags fewer, so that
//! lane 626 is zero and named by no record over the whole walk.
//!
//! The rows are ITEM 4's records as they stand in the relabelled stream (physical lanes 0..631, the census list of
//! hybtools::c1_build), optionally already rewritten by i4g / i4w (they only change records outside the walk; the walk range is
//! located by content: length, hash, anchors).  `rewrite(rows, sel)` returns the rewritten block and the new walk ranges.
//!
//! Inner walk (agent i4d, stage 1, see ~/Projects/ecdsafail/q631/i4d/summary.py): census offsets [41_078_334, 69_971_981) of the
//! original item = walkgen.rs Kind::Inner{real: 2} on the configuration below (tag0 626, tag1 628, fire 629, sign 257, tst =
//! a fifth clean lane that the 632 stream renames per stretch), entered with L[1..=128] and R[128] complemented.  PROVEN by
//! block replay: the raw generated walk + the entry adapter reproduces the stream's state at the walk end on every lane and
//! shot of 32 sets except the shots on which the original item output is wrong (MEASURED, 8,192 shots).
//! Replacement: the same adapter, then Inner{real: 0} of i4dwalkgen.rs (walkgen.rs copy + two exact fixes for real = 0) with
//! fire 629, tst 628, no clean tag: the relay hosts every count bit; the pre-block scratch tag qa lives on the dirty lane 3
//! (an idle passenger lane of ITEM 4; the fix toggles twice, so its value is irrelevant and restored).
//! Lanes of the replacement: L (130) R (130) sign, loans (126 q lanes, dirty), 627 (= L[n], data), 628 tst, 629 fire, 3 (dirty).
type Row = [u16; 4];
const NONE: u16 = u16::MAX;
#[path = "i4dwalkgen.rs"]
#[allow(dead_code)]
pub mod wg;

/// builder switch (no builder code reads it yet; see summary.py for the hook)
pub const ON: bool = false;
/// the lane freed over the inner walk
pub const FREED_INNER: u16 = 626;
/// the original inner walk: offsets in the census item, length, content hash (rows_hash), first / last records
pub const INNER_START: usize = 41_078_334;
pub const INNER_LEN: usize = 28_893_647;
/// rows_hash of the original walk range (0 = not checked)
pub const INNER_HASH_V: u64 = 0x58da517737aa8abd;

#[inline] fn nq(k: u16) -> usize { match k { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }
pub fn rows_hash(rows: &[Row]) -> u64 { let mut h = 0x243F6A8885A308D3u64;
    for r in rows { let k = (r[0] as u64) | (r[1] as u64) << 16 | (r[2] as u64) << 32 | (r[3] as u64) << 48; let x = (h ^ k).wrapping_mul(0x9E3779B97F4A7C15); h = x ^ (x >> 29); } h }

/// census-lane configuration of the inner walk (stage 1)
pub fn inner_l() -> Vec<i32> { let mut l: Vec<i32> = vec![256, 623]; l.extend((258..=384).rev()); l.extend([627, 627]); l }
pub fn inner_r() -> Vec<i32> { let mut r: Vec<i32> = vec![1, 129, 130, 131, 132, 631, 133, 619, 249]; r.extend(136..=247); r.extend([614, 134, 250, 615, 622, 630, 616, 617, 2, 2]); r }
/// the 126 loans the stream's walk borrows (q lanes), padded to 2n with idle lanes of ITEM 4 (never borrowed: the walk needs at
/// most 126); the LAST one (lane 3) is the dirty host of qa in the pre-blocks of Inner{real: 0}
pub fn inner_loan() -> Vec<i32> { let mut v: Vec<i32> = (385..=502).collect(); v.extend([135, 253, 252, 251, 248, 0, 512, 255]);
    v.extend(4..=128); v.extend([618, 620, 621, 624, 625, 254]); v.push(3); assert!(v.len() == 258); v }

/// the replacement records of the inner walk: entry adapter (X on L[1..=128], R[128]) + Inner{real} (real 0: fire 629, tst 628)
pub fn inner_rows(real: usize) -> Vec<Row> {
    let (l, r) = (inner_l(), inner_r());
    let tags = [626, 628, 627]; let mut ws: Vec<i32> = tags[..real].to_vec(); while ws.len() < 7 { ws.push(-1); }
    let (fire, tst) = if real == 0 { (629, 628) } else { (629, 632) };
    let cfg = wg::Cfg { n: 129, kind: wg::Kind::Inner { real }, tags: 4, l: l.clone(), r: r.clone(), loan: inner_loan(), ws_tag: ws, sign: 257, fire, tst, aux: -1 };
    let mut out: Vec<Row> = Vec::with_capacity(34_000_000);
    for &x in l[1..=128].iter().chain([r[128]].iter()) { out.push([6, x as u16, NONE, NONE]); }
    wg::run(&cfg, &mut |x| out.push(x)).expect("i4dwalk: inner walk emission");
    out
}

#[derive(Clone, Copy, Debug)]
pub struct Sel { pub inner: bool }
#[derive(Debug, Default)]
pub struct Stats { pub inner: Option<(usize, usize)>, pub removed: usize, pub added: usize, pub ccx_removed: usize, pub ccx_added: usize, pub found_at: usize }

/// find the original inner walk in `rows` (exact content), searching around its census offset (other rewrites may have moved it)
pub fn find_inner(rows: &[Row]) -> usize {
    let first: Vec<Row> = { let mut v = Vec::new(); for w in 192..=247u16 { v.push([6, w, NONE, NONE]); } v };
    let last: [Row; 5] = [[8, 627, 2, NONE], [13, 629, 2, 627], [8, 627, 2, NONE], [8, 629, 257, NONE], [8, 623, 629, NONE]];
    let lo = INNER_START.saturating_sub(2_000_000); let hi = (INNER_START + 2_000_000).min(rows.len().saturating_sub(INNER_LEN));
    let mut hits = Vec::new();
    for p in lo..=hi { if rows[p][0] == 6 && rows[p][1] == 192 && rows[p..p + first.len()] == first[..] && rows[p + INNER_LEN - 5..p + INNER_LEN] == last[..] { hits.push(p); } }
    assert!(hits.len() == 1, "i4dwalk: inner walk anchors found {} times", hits.len());
    let p = hits[0];
    if INNER_HASH_V != 0 { assert!(rows_hash(&rows[p..p + INNER_LEN]) == INNER_HASH_V, "i4dwalk: inner walk content differs from the stream it was proven on"); }
    p
}

pub fn rewrite(rows: &[Row], sel: Sel) -> (Vec<Row>, Stats) {
    let mut st = Stats::default();
    if !sel.inner { return (rows.to_vec(), st); }
    let p = find_inner(rows); st.found_at = p;
    let rep = inner_rows(0);
    for r in &rep { for j in 1..=nq(r[0]) { assert!(r[j] != FREED_INNER, "i4dwalk: replacement names the freed lane"); } }
    st.removed = INNER_LEN; st.added = rep.len();
    st.ccx_removed = rows[p..p + INNER_LEN].iter().filter(|r| r[0] == 13).count(); st.ccx_added = rep.iter().filter(|r| r[0] == 13).count();
    let mut out = Vec::with_capacity(rows.len() + rep.len() - INNER_LEN);
    out.extend_from_slice(&rows[..p]); out.extend_from_slice(&rep); out.extend_from_slice(&rows[p + INNER_LEN..]);
    st.inner = Some((p, p + rep.len()));
    (out, st)
}

// ---------------------------------------------------------------- outer walk reverse (stage 3: configuration only, NOT a fix)
/// the original outer walk reverse: census offsets [OUTER_START, OUTER_START + OUTER_LEN) (first record: the reverse class
/// tail's R swap chain CX 626 258; last: CX 384 624 = CX(R[n-1], sign)).  PROVEN (agent i4d, MEASURED on 34 sets): walkgen.rs
/// Kind::RevSector with tags = 4 on the configuration below reproduces the stream's end state from its start state on every
/// lane / shot the original computes correctly, phase included; t0 and t1 have no lane of their own in the stream (it packs
/// t0 with aux on 621 and renames t1 per stretch), so a replay puts them on spare lanes (>= 632).  No variant frees a lane.
pub const OUTER_START: usize = 86_151_441;
pub const OUTER_LEN: usize = 28_919_099;
pub fn outer_l() -> Vec<i32> { let mut l: Vec<i32> = vec![2, 257, 620]; l.extend(3..=128); l.push(618); l.push(621); l }
pub fn outer_r() -> Vec<i32> { let mut r: Vec<i32> = vec![256, 626]; r.extend(258..=384); r.push(623); r.push(256); r }
/// RevSector configuration of the outer walk reverse with t0 / t1 on the given lanes (the stream: none / renamed per stretch)
pub fn outer_cfg(tags: usize, t0: i32, t1: i32) -> wg::Cfg {
    let mut loan: Vec<i32> = (385..=502).collect(); loan.extend([135, 253, 252, 251, 248, 0, 512, 255]); loan.extend(504..=613); loan.truncate(258);
    let tl = [t0, t1, 627, -1, -1]; let ws: Vec<i32> = (0..7).map(|i| if i < tags { tl[i] } else { -1 }).collect();
    wg::Cfg { n: 129, kind: wg::Kind::RevSector, tags, l: outer_l(), r: outer_r(), loan, ws_tag: ws, sign: 624, fire: 628, tst: 629, aux: 621 }
}
