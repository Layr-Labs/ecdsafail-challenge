//! q631 / int4 (agent int4, 2026-11-19; LOCAL RESEARCH, never part of a package): the five finished fixes that change a piece
//! BEFORE the relabelling, put into the checked chain (hybrid splice -> cf631 splice -> relabelling -> q631 -> rb631).
//!   fixes (bit of the mask, piece):  SC_B scan B (V2, scq631) | I2 ITEM 2 (i2) | BS_D scan D, BS_F scan F, BS_FP scan F' (L1s,
//!   bs631) | SC_BP scan B' (W2, scq631) | I10 ITEM 10 (i10).  The fix modules are used as they are (their own switches stay OFF;
//!   this module calls their trace / generator functions).
//! THE SWITCH: `ON` (0) | runtime `FORCE` (local tools).  Mask 0 = `hook` only clears the position map: the list is unchanged.
//! WHERE: on the assembled list AFTER the hybrid and cf631 splices and BEFORE i1::apply (hook in mod.rs assemble_c).  Each
//! selected piece is regenerated (scans: the variant trace expanded with the classical state the list has at that scan, the
//! shipped trace re-expanded from the same state and asserted EQUAL to the list's rows, the allocator state after the variant
//! asserted equal to the one after the shipped trace; items: the tree's generator and the fix's generator on the same raw rows,
//! the tree's output asserted EQUAL to the list's rows) and written in place of the old piece.
//! THE RELABELLING TABLE keeps its frames (same hidden lanes, same order, same move flags); only positions move:
//!   * entries before / after a modified piece: unchanged / shifted by the growth of the modified pieces before them;
//!   * entries strictly INSIDE a modified piece: moved to the same surviving record of the new piece, found by a greedy
//!     minimal-local-edit alignment of the old and new record streams (equal runs; resync by the smallest a + b with a K-gram
//!     match); an entry whose record does not survive goes to the nearest surviving record; then every entry is checked against
//!     the NEW records (the old hidden lane unnamed from the previous entry to it, its lane unnamed from it to the next entry) and,
//!     if needed, moved to the nearest position where both hold (reported).  A stretch whose hidden lane is named by a new record
//!     with no valid position left is a CONFLICT: reported (lane, piece, records), and the build stops (no forcing).
//!   * then n and the i1 hash of the new list are written into the table and i1::apply runs UNCHANGED (its binding check, the
//!     renaming, the moves and the FULL_632 assertion = the first check of the map).
//! THE SHARED POSITION MAP (`map_pos`, `grow_before_item`): pre-relabel positions of the list before this module -> after it.
//! Consulted by the later position-bound pieces through one-line hooks: q631::item4_range_c (ITEM 4 range), q631::apply_items_c
//! (ITEM 4 / ITEM 12 expected ranges), rb631::apply (the W4 rows' frames).  rb631's own anchors are by content.
use super::*;
use super::i1::{self, Relabel};
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Mutex;
use std::fmt::Write as _;

pub const ON: u32 = if super::FINAL631 { 255 } else { 0 };
pub static FORCE: AtomicU32 = AtomicU32::new(0);
/// int6: ITEM 2 from `i2b::generate` (successor of i2's fix) instead of `i2::generate`; default false; env INT4_I2B=1 read once
pub static I2B: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
static I2B_INIT: std::sync::Once = std::sync::Once::new();
pub fn i2b_on() -> bool { I2B_INIT.call_once(|| { if std::env::var("INT4_I2B").map(|v| v == "1").unwrap_or(super::FINAL631) { I2B.store(true, Ordering::Relaxed); } }); I2B.load(Ordering::Relaxed) }
#[inline] pub fn mask() -> u32 { ON | FORCE.load(Ordering::Relaxed) }
pub fn active() -> bool { mask() != 0 }

pub const BS_D: u32 = 1;
pub const BS_F: u32 = 2;
pub const BS_FP: u32 = 4;
pub const SC_BP: u32 = 8;
pub const I10: u32 = 16;
pub const I2: u32 = 32;
pub const SC_B: u32 = 64;
/// pre3: his column 1 of the four walks replaced by our generator (hybrid::X_REGIONS / gen_x); not part of ALL
pub const PRE3: u32 = 128;
pub const ALL: u32 = 127;

pub struct Fix { pub flag: u32, pub kind: u8, pub idx: usize, pub name: &'static str }
/// the modified pieces in list order (kind 1 = item, 2 = scan)
/// fin3 (main session, 2026-11-25): env INT4_ZFOLD=1 (default off).  In the scans' new rows, the top of each hit-test ladder
///   CCX(a,b->z) CX(y->z) CX(z->w) CX(y->z) HMR(z->m) CZ(a,b)[m]      (z = the scan's zero lane, zero before: its previous
///                                                                     naming record is an unconditional HMR on z)
/// computes w ^= (a AND b) xor y with z as a temporary; it is replaced IN PLACE (same length, so no position moves) by
///   CCX(a,b->w) CX(y->w) BitStore0(SCR) x 4
/// Exact: same w, z untouched (0), the HMR / CZ pair cancels its own phase; bit m is not read before its next write (checked).
/// Same Toffoli count.  Frees z over these 6 records (the planner's 5-record uncovered frames in scans D and F').
/// INT4_ZFOLD_RELAX=<scan,...>: in those scans fold even when z's zeroness is not shown by a preceding HMR (MEASURED premise:
/// a nonzero z at the ladder top would already leave the original's MBU with a phase error; user standard "reset + measure")
pub fn zfold_on() -> bool { std::env::var("INT4_ZFOLD").map(|v| v == "1").unwrap_or(super::FINAL631) }
fn zfold(rows: &mut [Row], relax: bool) -> (usize, usize) {
    const B0: Row = [4, 65499, NONE, NONE];
    let n = rows.len(); let (mut done, mut skipped) = (0usize, 0usize);
    let mut last_name: Vec<usize> = vec![usize::MAX; 633];   // last record index naming each lane (before i)
    let mut i = 0usize;
    while i < n {
        let r0 = rows[i];
        if r0[0] == 13 && i + 5 < n {
            let (a, b, z) = (r0[1], r0[2], r0[3]); let (r1, r2, r3, r4, r5) = (rows[i + 1], rows[i + 2], rows[i + 3], rows[i + 4], rows[i + 5]);
            let y = r1[1]; let w = r2[2];
            let tail = r4[0] == 12 && r4[1] == z && r4[3] == NONE && r5[0] == 9 && ((r5[1] == a && r5[2] == b) || (r5[1] == b && r5[2] == a)) && r5[3] == r4[2];
            let shape_y = r1[0] == 8 && r1[2] == z && r1[3] == NONE && r2[0] == 8 && r2[1] == z && r2[3] == NONE && r3 == r1 && tail;
            // variant: X z / CX(z->w) / X z  (w ^= NOT(a AND b)) -> CCX(a,b->w) X(w)
            let shape_x = r1[0] == 6 && r1[1] == z && r1[2] == NONE && r2[0] == 8 && r2[1] == z && r2[3] == NONE && r3 == r1 && tail;
            let y = if shape_x { NONE } else { y };
            if (shape_y || shape_x) && ![a, b, y, w].contains(&z) && ![a, b, y].contains(&w) && (shape_x || ![a, b].contains(&y)) {
                let m = r4[2];
                // z zero before: its previous naming record is an unconditional HMR on z
                let lz = last_name[z as usize];
                let zero_before = lz != usize::MAX && rows[lz][0] == 12 && rows[lz][1] == z && rows[lz][3] == NONE;
                // bit m not read before its next write
                let mut ok_m = false;
                for j in i + 6..n { let q = rows[j];
                    let reads = (q[0] == 9 || q[0] == 14) && q[3] == m || (q[0] == 8 && q[3] == m) || (q[0] == 15 && q[1] == m) || (q[0] == 3 && q[1] == m) || (q[0] == 6 && q[2] == m);
                    if reads { break; }
                    let writes = (q[0] == 12 && q[2] == m) || ((q[0] == 4 || q[0] == 5) && q[1] == m);
                    if writes { ok_m = true; break; } }
                if (zero_before || relax) && ok_m {
                    rows[i] = [13, a, b, w]; rows[i + 1] = if shape_x { [6, w, NONE, NONE] } else { [8, y, w, NONE] }; for k in 2..6 { rows[i + k] = B0; }
                    for k in 0..6 { for j in 1..=qubits(rows[i + k][0]) { last_name[rows[i + k][j] as usize] = i + k; } }
                    done += 1; i += 6; continue;
                } else { skipped += 1; }
            }
        }
        for j in 1..=qubits(rows[i][0]) { last_name[rows[i][j] as usize] = i; }
        i += 1;
    }
    (done, skipped)
}
/// fin3 (main session, 2026-11-25; user decision "reset gadget + measure"): env INT4_RESETS = "item:gap:hole:lane:bit,..."
/// (default empty = off; gap / hole = item-relative offsets in the item's FINAL rows: `lane`'s last write is at gap - 1 and the
/// uncovered frame starts at hole).  SAME-LENGTH: an identity pair (X q ... X q, or CX c->t ... CX c->t, nothing in between naming q / t
/// or writing c) whose first record lies in [gap, hole) is replaced by HMR(lane -> bit) and BitStore0(SCR), so `lane` is zero BY
/// CONSTRUCTION from there and no position moves.  Whether the reset ever changes a result (lane nonzero there) is MEASURED.
pub fn resets() -> Vec<(usize, usize, usize, u16, u16)> {
    std::env::var("INT4_RESETS").ok().or_else(|| if super::FINAL631 { Some(super::FINAL_RESETS.to_string()) } else { None }).map(|v| v.split(',').filter(|x| !x.trim().is_empty()).map(|x| { let f: Vec<u64> = x.trim().split(':').map(|y| y.parse().expect("INT4_RESETS: item:gap:hole:lane:bit")).collect();
        assert!(f.len() == 5, "INT4_RESETS: item:gap:hole:lane:bit"); (f[0] as usize, f[1] as usize, f[2] as usize, f[3] as u16, f[4] as u16) }).collect()).unwrap_or_default()
}
/// apply the resets of `item` to its final rows; returns (lane, gap, slot i, slot j) per reset applied, panics if one finds no slot
pub fn reset_subst(rows: &mut Vec<Row>, item: usize) -> Vec<(u16, usize, usize, usize)> {
    let mut done = Vec::new(); let mut ins: Vec<(usize, u16, u16)> = Vec::new();
    for (ii, gap, hole, lane, bit) in resets() { if ii != item { continue; }
        let tg = |r: &Row| match r[0] { 6 | 11 | 12 => r[1], 8 => r[2], 13 => r[3], _ => NONE };
        assert!(i1::names(&rows[gap - 1], lane), "reset: item {item} row {} = {:?} does not name lane {lane} (gap start mismatch)", gap - 1, rows[gap - 1]);
        assert!((gap..hole.max(gap + 1)).all(|x| !i1::names(&rows[x], lane)), "reset: item {item} lane {lane} named in [{gap}, {hole})");
        let mut slot = None;
        'outer: for i in gap..hole.max(gap + 1) { let r = rows[i];
            let pair_ok = |j: usize| -> bool { if rows[j] != r { return false; }
                match r[0] { 6 => (i + 1..j).all(|x| !i1::names(&rows[x], r[1])) && r[2] == NONE,
                             7 => (i + 1..j).all(|x| tg(&rows[x]) != r[1] && !(rows[x][0] == 10 && (rows[x][1] == r[1] || rows[x][2] == r[1]))) && r[2] == NONE,
                             8 => r[3] == NONE && (i + 1..j).all(|x| !i1::names(&rows[x], r[2]) && tg(&rows[x]) != r[1]),
                             13 => (i + 1..j).all(|x| !i1::names(&rows[x], r[3]) && tg(&rows[x]) != r[1] && tg(&rows[x]) != r[2]),
                             _ => false } };
            if ![6, 7, 8, 13].contains(&r[0]) { continue; }
            if (1..=qubits(r[0])).any(|q| r[q] == lane) { continue; }
            for j in i + 1..(i + 512).min(rows.len()) { if pair_ok(j) { slot = Some((i, j)); break 'outer; }
                if r[0] == 6 && i1::names(&rows[j], r[1]) { break; } if r[0] == 8 && (i1::names(&rows[j], r[2]) || tg(&rows[j]) == r[1]) { break; }
                if r[0] == 13 && (i1::names(&rows[j], r[3]) || tg(&rows[j]) == r[1] || tg(&rows[j]) == r[2]) { break; } if r[0] == 7 && tg(&rows[j]) == r[1] { break; } } }
        match slot { None => { eprintln!("reset: item {item} lane {lane}: no identity pair in [{gap}, {hole}); INSERTED at {gap} (the item grows by 1)"); ins.push((gap, lane, bit)); }
            Some((i, j)) => { rows[i] = [12, lane, bit, NONE]; rows[j] = [4, 65499, NONE, NONE]; done.push((lane, gap, i, j)); } } }
    ins.sort_by(|a, b| b.0.cmp(&a.0));   // highest first, so the offsets stay those of the rows without insertions
    for (gap, lane, bit) in ins { rows.insert(gap, [12, lane, bit, NONE]); done.push((lane, gap, gap, usize::MAX)); }
    done
}
/// dev1 (main session, 2026-11-26): env INT4_SRESETS = "scan:gap:glen:lane:bit,..." (default off): like ITEM 10's resets, an
/// HMR(lane -> bit) INSERTED in a scan's new rows at the start of the lane's zero gap (`gap` = its FINAL-list offset from the scan's
/// start; located by search: the nearest g <= gap with row g-1 naming the lane and the lane unnamed for min(glen - 64, 100k) rows).
/// Zero by construction from there; the premise (zero there on correct shots) is MEASURED.
fn scan_resets(v: &mut Vec<Row>, scan: usize) {
    let spec = std::env::var("INT4_SRESETS").unwrap_or_else(|_| if super::FINAL631 { super::FINAL_SRESETS.to_string() } else { String::new() });
    let mut rs: Vec<(usize, usize, u16, u16)> = spec.split(',').filter(|x| !x.trim().is_empty()).filter_map(|x| { let f: Vec<u64> = x.trim().split(':').map(|y| y.parse().expect("INT4_SRESETS")).collect();
        if f[0] as usize == scan { Some((f[1] as usize, f[2] as usize, f[3] as u16, f[4] as u16)) } else { None } }).collect();
    rs.sort_by(|a, b| b.0.cmp(&a.0));
    for (gap, glen, lane, bit) in rs {
        let check = glen.saturating_sub(64).min(100_000).max(1);
        let g = (gap.saturating_sub(16_384).max(1)..=gap.min(v.len() - 1)).rev().find(|&g| i1::names(&v[g - 1], lane) && (g..(g + check).min(v.len())).all(|x| !i1::names(&v[x], lane)))
            .unwrap_or_else(|| panic!("int4 scan reset: scan {scan} lane {lane}: no gap of {check} rows near offset {gap}"));
        eprintln!("int4 scan reset: scan {scan} lane {lane}: final offset {gap} -> row {g} (delta {})", gap as i64 - g as i64);
        v.insert(g, [12, lane, bit, NONE]); }
}
pub const FIXES: [Fix; 7] = [
    Fix { flag: SC_B, kind: 2, idx: 0, name: "scan B" },
    Fix { flag: I2, kind: 1, idx: 2, name: "ITEM 2" },
    Fix { flag: BS_D, kind: 2, idx: 1, name: "scan D" },
    Fix { flag: BS_F, kind: 2, idx: 2, name: "scan F" },
    Fix { flag: SC_BP, kind: 2, idx: 4, name: "scan B'" },
    Fix { flag: I10, kind: 1, idx: 10, name: "ITEM 10" },
    Fix { flag: BS_FP, kind: 2, idx: 6, name: "scan F'" },
];

/// one table entry strictly inside a modified piece: index in the table, old / new absolute position, hidden lane before (h)
/// and from here (c), flags, whether its record survived, position before the validity adjustment, conflict
#[derive(Clone, Debug)]
pub struct EntMap { pub k: usize, pub old: u64, pub new: u64, pub h: u16, pub c: u16, pub f: u8, pub survivor: bool, pub first: u64, pub conflict: bool }
#[derive(Clone, Debug, Default)]
pub struct Piece {
    pub name: String, pub flag: u32, pub kind: u8, pub idx: usize,
    /// positions in the list before / after this module (pre-relabel)
    pub s_old: u64, pub e_old: u64, pub s_new: u64, pub e_new: u64,
    /// alignment: equal runs (old rel, new rel, len); resync counts per tier (local, 16k window, 16M window, none)
    pub runs: Vec<(u32, u32, u32)>, pub tiers: [u64; 4], pub matched: u64,
    pub ents: Vec<EntMap>, pub conflicts: Vec<String>,
    /// pre3 pieces (kind 3): table entries strictly inside (dropped), and the entry added at the start (position, hidden lane, flags)
    pub dropped: Vec<usize>, pub extra: Option<(u64, u16, u8)>,
    /// logical lanes named by the old / new rows (counts)
    pub named_old: Vec<u64>, pub named_new: Vec<u64>,
}
#[derive(Clone, Debug, Default)]
pub struct PosMap { pub pieces: Vec<Piece>, pub item_grow: Vec<i64>, pub n_old: u64, pub n_new: u64, pub log: String }
static MAP: Mutex<Option<PosMap>> = Mutex::new(None);
/// the map of the last build in this process (None when the mask was 0)
pub fn posmap() -> Option<PosMap> { MAP.lock().unwrap().clone() }
/// growth of the modified pieces that end at or before `p` (p not strictly inside one)
pub fn map_pos(p: u64) -> u64 {
    let g = MAP.lock().unwrap(); let m = match g.as_ref() { Some(m) => m, None => return p };
    let mut d = 0i64;
    for pc in m.pieces.iter() {
        if p >= pc.e_old { d += (pc.e_new - pc.s_new) as i64 - (pc.e_old - pc.s_old) as i64; }
        else { assert!(p <= pc.s_old, "int4: position {p} inside the modified piece {} [{}, {})", pc.name, pc.s_old, pc.e_old); } }
    (p as i64 + d) as u64
}
/// growth of the modified pieces before item `ii` (0 without a map)
pub fn grow_before_item(ii: usize) -> i64 { MAP.lock().unwrap().as_ref().map_or(0, |m| m.item_grow.get(ii).copied().unwrap_or(0)) }

/// the builder hook (mod.rs assemble_c, after the cf631 splice): mask 0 = clear the map, list and table unchanged
pub fn hook<S: Slot + Send>(pk: &Pack, sh: &Shift, out: &mut [S], n: usize, rt: Option<Relabel>, hyb: bool, cf: bool) -> (usize, Option<Relabel>) {
    if !active() { *MAP.lock().unwrap() = None; return (n, rt); }
    let t = rt.expect("int4 needs the relabelling table");
    let (n2, t2, pm) = apply(pk, sh, out, n, t, hyb, cf, true);
    *MAP.lock().unwrap() = Some(pm);
    (n2, Some(t2))
}

// ------------------------------------------------------------------------------------------------ scans
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
fn nexts(c: &scan::Classical) -> [usize; 3] { [c.cl[0].next, c.cl[1].next, c.cl[2].next] }
fn set_nexts(c: &mut scan::Classical, v: [usize; 3]) { for k in 0..3 { c.cl[k].next = v[k]; } }
/// the fix's trace of scan i
pub fn variant_trace(i: usize) -> Vec<u8> { match i { 0 | 4 => scq631::q631_trace(i), 1 | 2 | 6 => bs631::bs_trace(i), _ => panic!("int4: no variant of scan {i}") } }
/// fpc0: env INT4_FPC0=1 (default off) converts scan F''s post-sweep Cuccaro adders (carry-in = the scan's zero lane z, trace id 230)
/// with i10c0::convert right after the variant expansion; everything else untouched
pub fn fpc0_on() -> bool { std::env::var("INT4_FPC0").map(|v| v == "1").unwrap_or(super::FINAL631) }
fn fpc0_convert(pk: &Pack, rows: Vec<Row>, ban: &[u16]) -> (Vec<Row>, Vec<(usize, usize, usize, usize)>) {
    let sp = &pk.scans[6]; let map = &pk.segs[pk.seg_of(sp.out)].map;
    let (c0, ladder) = (map[230], map[248]);   // z lane, the lane the L1s variant frees (its single HMR ends the sweep ladder)
    let hmr = rows.iter().position(|r| r[0] == 12 && r[1] == ladder).expect("fpc0: no HMR on the freed ladder lane");
    let start = (hmr + 1..rows.len()).find(|&i| i1::names(&rows[i], ladder)).expect("fpc0: freed ladder lane never named again");   // end of the sweep
    let loans: Vec<u16> = (256..499).chain(0..256).chain(499..547).chain(549..620).filter(|l| !ban.contains(l)).collect();   // never a lane layer 1 hides anywhere in F'
    i10::c0::STRICT.with(|x| x.set(std::env::var("INT4_FPC0_LOOSE").map(|v| v != "1").unwrap_or(true)));   // strict: only adders whose carry-in lane is provably zero (not loaded with a constant bit)
    i10::c0::DUAL.with(|x| x.set(std::env::var("INT4_FPC0_DUAL").map(|v| v == "1").unwrap_or(super::FINAL631)));
    let (o, st) = i10::c0::convert(&rows, &[(start, rows.len())], c0, &loans);
    eprintln!("int4 fpc0: dual {} dual-converted {} rejects [not-load, no-unload, names-h, no-restore, check] {:?}", i10::c0::DUAL.with(|x| x.get()), i10::c0::DUALN.with(|x| x.get()), i10::c0::DUAL_REJ.with(|x| x.get()));
    eprintln!("int4 fpc0: strict {} skipped adders (c0 loaded / unknown) {}", i10::c0::STRICT.with(|x| x.get()), i10::c0::SKIPPED.with(|x| x.get()));
    assert!(st.rejected == 0 && st.dropped == 0, "fpc0: a converted adder failed its check / records were dropped (the exact position map needs pure replacements)");
    eprintln!("int4 fpc0: carry-in lane {c0} (trace id 230), sweep end = record {start} (first naming of lane {ladder} after its HMR at {hmr}); found {} replaced {} rejected {} left {} dropped {}, records in the adders {} -> {}, scan {} -> {} rows",
        st.found, st.replaced, st.rejected, st.left, st.dropped, st.rec_before, st.rec_after, rows.len(), o.len());
    (o, st.moves)
}
/// compose the alignment old -> variant rows (runs1) with the exact variant -> converted map (moves: variant [s, e) -> converted [ns, ne); identity shifts between them)
fn fpc0_compose(runs1: &[(u32, u32, u32)], moves: &[(usize, usize, usize, usize)], nvar: usize) -> Vec<(u32, u32, u32)> {
    let mut gaps: Vec<(usize, usize, usize)> = Vec::new();   // variant [a, b) -> converted start
    let (mut pe, mut pne) = (0usize, 0usize);
    for &(s, e, ns, ne) in moves { if s > pe { gaps.push((pe, s, pne)); } pe = e; pne = ne; }
    if nvar > pe { gaps.push((pe, nvar, pne)); }
    let mut out = Vec::new(); let mut g = 0usize;
    for &(oa, va, len) in runs1 { let (va, len) = (va as usize, len as usize);
        while g < gaps.len() && gaps[g].1 <= va { g += 1; }
        let mut h = g;
        while h < gaps.len() && gaps[h].0 < va + len { let (a, b) = (gaps[h].0.max(va), gaps[h].1.min(va + len)); if b > a { out.push((oa + (a - va) as u32, (gaps[h].2 + (a - gaps[h].0)) as u32, (b - a) as u32)); } h += 1; } }
    out
}
/// whether scan i has range rows or inserts (then scan_rows keeps its length: a variant could not change it)
pub fn scan_fixed(pk: &Pack, i: usize) -> bool { let sp = &pk.scans[i]; let k0 = pk.wmr.partition_point(|x| x.0 < sp.out); (k0 < pk.wmr.len() && pk.wmr[k0].0 == sp.out) || !pk.ins_of(true, i).is_empty() }

/// ITEM ii: (the tree's hooked rows, the fix's rows), both through emit_hooked (logical lanes, as items() places them)
fn item_pair(pk: &Pack, ii: usize) -> (Vec<Row>, Vec<Row>) {
    let g = gir::Girs::open(include_bytes!("data/blocks.girs")); let raw = w2rw::item_rows(pk, &g, ii);
    let (old, new) = match ii { 2 => (m1gen::generate(&raw, i1::M1_MBIT), if i2b_on() { i2b::generate(&raw) } else { i2::generate(&raw) }), 10 => (c2capgen::generate(&raw), i10::generate(&raw, None)), _ => panic!("int4: item {ii}") };
    drop(raw);
    let emit = |rows: Vec<Row>| -> Vec<Row> { let h = i1::Hooked { rows, ins: Vec::new(), lane_space: false }; let mut v = Vec::with_capacity(h.rows.len()); i1::emit_hooked(pk, ii, &h, &mut |_, r| v.push(r)); v };
    (emit(old), emit(new))
}

// ------------------------------------------------------------------------------------------------ alignment
#[inline] fn hk(x: &[Row]) -> u64 { let mut h = 0xcbf2_9ce4_8422_2325u64; for r in x { h = (h ^ i1::row_key(*r)).wrapping_mul(0x0000_0100_0000_01b3); h ^= h >> 29; } h }
/// resync after a mismatch at (i, j): the smallest (da, db) (by da + db) with a[i + da..][..k] == b[j + db..][..k]; tier 0: da + db
/// <= 64 (k = 8), tier 1: windows of 2^14 (k = 16), tier 2: windows of 2^24 (k = 16, at most `big` times); None = no resync
fn resync(a: &[Row], i: usize, b: &[Row], j: usize, st: &mut [u64; 4], big: &mut u32) -> Option<(usize, usize)> {
    let (na, nb) = (a.len(), b.len());
    { let k = 8usize;
      for d in 1..=64usize { for da in 0..=d { let db = d - da; if i + da + k <= na && j + db + k <= nb && a[i + da..i + da + k] == b[j + db..j + db + k] { st[0] += 1; return Some((da, db)); } } } }
    for (tier, w) in [(1usize, 1usize << 14), (2, 1 << 24)] {
        let k = 16usize;
        if tier == 2 { if *big == 0 { break; } *big -= 1; }
        if nb < j + k || na < i + k { break; }
        let hb = (j + w).min(nb - k + 1); let ha = (i + w).min(na - k + 1);
        let mut m: std::collections::HashMap<u64, u32> = std::collections::HashMap::with_capacity(hb - j);
        for jb in j..hb { m.entry(hk(&b[jb..jb + k])).or_insert(jb as u32); }
        let mut best: Option<(usize, usize)> = None;
        for ia in i..ha { let da = ia - i; if let Some((x, y)) = best { if da >= x + y { break; } }
            if let Some(&jb) = m.get(&hk(&a[ia..ia + k])) { let jb = jb as usize; if a[ia..ia + k] == b[jb..jb + k] { let db = jb - j; if best.map_or(true, |(x, y)| da + db < x + y) { best = Some((da, db)); } } } }
        if best.is_some() { st[tier] += 1; return best; }
    }
    st[3] += 1; None
}
/// equal runs (old rel, new rel, len) of a greedy minimal-local-edit alignment; plus the common suffix if the forward pass gave up
pub fn align(a: &[Row], b: &[Row]) -> (Vec<(u32, u32, u32)>, [u64; 4]) {
    let (na, nb) = (a.len(), b.len()); let mut st = [0u64; 4]; let mut big = 64u32;
    // common suffix (always a valid tail match; the forward pass stops before it)
    let mut suf = 0usize; while suf < na && suf < nb && a[na - 1 - suf] == b[nb - 1 - suf] { suf += 1; }
    let (ea, eb) = (na - suf, nb - suf);
    let mut runs: Vec<(u32, u32, u32)> = Vec::new(); let (mut i, mut j) = (0usize, 0usize);
    loop {
        let (i0, j0) = (i, j);
        while i < ea && j < eb && a[i] == b[j] { i += 1; j += 1; }
        if i > i0 { runs.push((i0 as u32, j0 as u32, (i - i0) as u32)); }
        if i >= ea || j >= eb { break; }
        match resync(&a[..ea], i, &b[..eb], j, &mut st, &mut big) { Some((da, db)) => { i += da; j += db; } None => break }
    }
    if suf > 0 { runs.push((ea as u32, eb as u32, suf as u32)); }
    // merge adjacent runs (the suffix may continue the last forward run)
    let mut m: Vec<(u32, u32, u32)> = Vec::with_capacity(runs.len());
    for r in runs { if let Some(l) = m.last_mut() { if l.0 + l.2 == r.0 && l.1 + l.2 == r.1 { l.2 += r.2; continue; } assert!(r.0 >= l.0 + l.2 && r.1 >= l.1 + l.2, "int4: alignment not monotone"); } m.push(r); }
    (m, st)
}
/// relative old position p -> (relative new position, survivor)
fn map_rel(runs: &[(u32, u32, u32)], p: u32, na: u32, nb: u32) -> (u32, bool) {
    let k = runs.partition_point(|r| r.0 <= p);
    if k > 0 { let r = runs[k - 1]; if p < r.0 + r.2 { return (r.1 + (p - r.0), true); } }
    let (pe_o, pe_n) = if k > 0 { (runs[k - 1].0 + runs[k - 1].2, runs[k - 1].1 + runs[k - 1].2) } else { (0, 0) };
    let (ns_o, ns_n) = if k < runs.len() { (runs[k].0, runs[k].1) } else { (na, nb) };
    // the nearest surviving record: the last one before p (switch right after it) or the first one after p (switch right before it)
    if p - pe_o <= ns_o - p { (pe_n, false) } else { (ns_n, false) }
}

// ------------------------------------------------------------------------------------------------ apply
/// The edit (see the module comment).  `edit` false = survey only (no list change; the returned n / table are the old ones).
pub fn apply<S: Slot + Send>(pk: &Pack, sh: &Shift, out: &mut [S], n: usize, t: Relabel, hyb: bool, cf: bool, edit: bool) -> (usize, Relabel, PosMap) {
    let t0 = std::time::Instant::now(); let m = mask(); let mut log = String::new();
    assert!(hyb, "int4 needs the hybrid splice (the chain it was checked on)");
    { let hh = hybrid::stream_hash(&out[..n]); assert!(t.n == n as u64 && t.hash == hh, "int4: the relabelling table is not bound to this list (table n {} hash {:016x}, list n {} hash {:016x})", t.n, t.hash, n, hh); }
    let pos = |o: u64| -> u64 { let p = (o as i64 + sh.at(o)) as u64; let p = hybrid::map_pos(p); if cf { cf631::map_pos(p) } else { p } };
    let hl = i1::hook_lens(pk);
    let mut pcs: Vec<Piece> = Vec::new();
    for f in FIXES.iter() { if m & f.flag == 0 { continue; }
        let (s, e) = if f.kind == 2 { let sp = &pk.scans[f.idx]; assert!(!scan_fixed(pk, f.idx), "int4: scan {} is fixed-length (ranges / inserts)", f.idx); (pos(sp.out), pos(sp.end)) }
            else { let it = &pk.items[f.idx]; let (s, e) = (pos(it.out), pos(it.out + it.n)); assert!(e - s == hl[f.idx].expect("int4: item not hooked"), "int4: item {} length", f.idx); (s, e) };
        pcs.push(Piece { name: f.name.to_string(), flag: f.flag, kind: f.kind, idx: f.idx, s_old: s, e_old: e, ..Default::default() }); }
    let pre3_set = std::env::var("INT4_PRE3_SET").unwrap_or_else(|_| if super::FINAL631 { "02".to_string() } else { "0123".to_string() });   // pre3: which column-1 ranges (staged tests)
    if m & PRE3 != 0 { for (j, xr) in hybrid::X_REGIONS.iter().enumerate() { if !pre3_set.contains(char::from(b'0' + j as u8)) { continue; }
        let pp = |o: u64| -> u64 { let q = hybrid::map_pos(o); if cf { cf631::map_pos(q) } else { q } };
        let (s, e) = (pp(xr.start), pp(xr.end));
        pcs.push(Piece { name: format!("pre3 {} seg {}", if xr.fwd { "F" } else { "R" }, xr.seg), flag: PRE3, kind: 3, idx: j, s_old: s, e_old: e, ..Default::default() }); } }
    pcs.sort_by_key(|p| p.s_old);
    assert!(pcs.windows(2).all(|w| w[0].e_old <= w[1].s_old) && pcs.last().map_or(true, |p| p.e_old as usize <= n), "int4: pieces out of order");
    writeln!(log, "int4: mask {m} ({}), list n {n} hash {:016x}, table {} entries; pieces (old positions): {}", FIXES.iter().filter(|f| m & f.flag != 0).map(|f| f.name).collect::<Vec<_>>().join(", "), t.hash, t.ent.len(),
        pcs.iter().map(|p| format!("{} [{}, {})", p.name, p.s_old, p.e_old)).collect::<Vec<_>>().join(", ")).unwrap();
    let norm = |r: Row| S::from_row(r).to_row();
    // ---- 1. new rows (normalised as the slots store them); the tree's rows re-generated and compared with the list
    let mut newrows: Vec<Vec<Row>> = vec![Vec::new(); pcs.len()];
    let item_idx: Vec<(usize, usize)> = pcs.iter().enumerate().filter(|(_, p)| p.kind == 1).map(|(k, p)| (k, p.idx)).collect();
    let scan_idx: Vec<(usize, usize)> = pcs.iter().enumerate().filter(|(_, p)| p.kind == 2).map(|(k, p)| (k, p.idx)).collect();
    let mut fpc_runs: Vec<Option<Vec<(u32, u32, u32)>>> = vec![None; pcs.len()];
    {
        let outr: &[S] = &*out;
        let check = |k: usize, rows: &[Row], what: &str| { let p = &pcs[k]; let (s, e) = (p.s_old as usize, p.e_old as usize);
            assert!(rows.len() == e - s, "int4: {} {what}: {} rows, the list has {}", p.name, rows.len(), e - s);
            let bad = rows.iter().zip(outr[s..e].iter()).position(|(r, x)| norm(*r) != x.to_row());
            assert!(bad.is_none(), "int4: {} {what}: row {} differs from the list ({:?} vs {:?})", p.name, bad.unwrap(), rows[bad.unwrap()], outr[s + bad.unwrap()].to_row()); };
        std::thread::scope(|sc| {
            let hs: Vec<_> = item_idx.iter().map(|&(k, ii)| (k, std::thread::Builder::new().stack_size(256 << 20).spawn_scoped(sc, move || item_pair(pk, ii)).expect("int4: item thread"))).collect();
            if !scan_idx.is_empty() {
                let last = scan_idx.iter().map(|x| x.1).max().unwrap();
                let mut cls = scan::Classical::new();
                let fpc0_ban: Vec<u16> = if fpc0_on() { let pf = pcs.iter().find(|p| p.kind == 2 && p.idx == 6).expect("fpc0: scan F' not in the mask"); let k0 = t.ent.partition_point(|x| x.0 <= pf.s_old); let k1 = t.ent.partition_point(|x| x.0 < pf.e_old); let mut b: Vec<u16> = (k0.saturating_sub(1)..k1.min(t.ent.len())).map(|k| t.ent[k].1).collect(); if k0 > 0 { b.push(t.ent[k0 - 1].1); } b.sort(); b.dedup(); eprintln!("int4 fpc0: loan ban (layer-1 hidden lanes in scan F'): {:?}", b); b } else { Vec::new() };
                for j in 0..=last { let tr = rb631::list_trace(j);
                    if let Some(&(k, _)) = scan_idx.iter().find(|x| x.1 == j) {
                        let n0 = nexts(&cls);
                        let r_old = si631::expand_with(pk, j, &tr, &mut cls); let n_old = nexts(&cls);
                        check(k, &r_old, "shipped trace re-expanded"); drop(r_old);
                        set_nexts(&mut cls, n0);
                        let mut r_new = si631::expand_with(pk, j, &variant_trace(j), &mut cls); let n_new = nexts(&cls);
                        if j == 6 && fpc0_on() {
                            let p = &pcs[k]; let (s0, e0) = (p.s_old as usize, p.e_old as usize);
                            let var: Vec<Row> = r_new.iter().map(|r| norm(*r)).collect(); let old: Vec<Row> = outr[s0..e0].iter().map(|x| x.to_row()).collect();
                            let (runs1, _) = align(&old, &var); let nvar = var.len(); drop(var); drop(old);
                            let (o, moves) = fpc0_convert(pk, r_new, &fpc0_ban); r_new = o;
                            fpc_runs[k] = Some(fpc0_compose(&runs1, &moves, nvar));
                        }
                        assert!(n_new == n_old, "int4: scan {j}: classical allocators after the variant {:?} differ from the shipped trace's {:?} (later scans would change)", n_new, n_old);
                        newrows[k] = r_new.into_iter().map(norm).collect();
                        if zfold_on() { let relax = std::env::var("INT4_ZFOLD_RELAX").map(|v| v.split(',').any(|x| x.trim() == j.to_string())).unwrap_or(super::FINAL631 && (j == 1 || j == 6));
                            let (d, sk) = zfold(&mut newrows[k], relax); eprintln!("int4 zfold: scan {j}: folded {d}, shape-matched but skipped {sk} (relaxed zero-before {relax})"); }
                        scan_resets(&mut newrows[k], j);
                    } else { run_one(pk, j, &tr, &mut cls, &mut |_r: Row| {}); } }
            }
            for (k, h) in hs { let (old, new) = h.join().expect("int4: item generator"); check(k, &old, "tree generator"); drop(old); newrows[k] = new.into_iter().map(norm).collect(); }
        });
    }
    for (k, p) in pcs.iter().enumerate() { if p.kind != 3 { continue; }
        let xr = &hybrid::X_REGIONS[p.idx]; let mut v: Vec<Row> = Vec::new();
        hybrid::gen_x_i(p.idx, xr.fwd, &pk.segs[xr.seg].map, hybrid::WX, hybrid::SCR, &mut |r| v.push(norm(r)));
        hybrid::check_x(p.idx, &pk.segs[xr.seg].map, &out[p.s_old as usize - 3..p.e_old as usize + 3], p.e_old - p.s_old);
        newrows[k] = v; }
    // ITEM 10 is an int4 piece (its length may change: int4 re-aligns it and re-binds the table), so its resets are INSERTED:
    // HMR(lane -> bit) right before row `gap` of its new rows (highest gap first, so the offsets stay those of the rows without resets)
    if let Some(k) = pcs.iter().position(|p| p.kind == 1 && p.idx == 10) {
        let mut rs: Vec<_> = resets().into_iter().filter(|r| r.0 == 10).collect(); rs.sort_by(|a, b| b.1.cmp(&a.1));
        let tg = |r: &Row| match r[0] { 6 | 11 | 12 => r[1], 8 => r[2], 13 => r[3], _ => NONE };
        // the offsets are FINAL-list offsets; i1::apply later inserts move rows into ITEM 10, so locate the gap in these rows:
        // the nearest g <= gap with row g-1 naming the lane and the lane unnamed over [g, g + check) (field `hole` = the gap's length)
        for &(_ii, gap, glen, lane, bit) in rs.iter() { let v = &mut newrows[k];
            let check = glen.saturating_sub(64).min(100_000).max(1);
            let g = (gap.saturating_sub(16_384).max(1)..=gap.min(v.len() - 1)).rev().find(|&g| i1::names(&v[g - 1], lane) && (g..(g + check).min(v.len())).all(|x| !i1::names(&v[x], lane)))
                .unwrap_or_else(|| panic!("int4 reset: ITEM 10 lane {lane}: no gap of {check} records found near offset {gap}"));
            eprintln!("int4 reset: ITEM 10 lane {lane}: final offset {gap} -> row {g} (delta {})", gap as i64 - g as i64);
            v.insert(g, norm([12, lane, bit, NONE])); }
        if !rs.is_empty() { writeln!(log, "int4: resets ITEM 10 inserted {:?}", rs).unwrap(); eprintln!("int4: resets ITEM 10 inserted {:?}", rs); } }
    writeln!(log, "int4: new rows generated, old rows re-generated = the list's [{:?}]", t0.elapsed()).unwrap();
    // ---- 2. align, map the entries inside, check every new record against its frame
    let hid = |k: usize| if k == 0 { t.h0 } else { t.ent[k - 1].1 };
    let mut gdelta = 0i64;   // growth of the pieces before
    let mut nconf = 0usize;
    for (pi, p) in pcs.iter_mut().enumerate() {
        let (s, e) = (p.s_old as usize, p.e_old as usize);
        let old: Vec<Row> = out[s..e].iter().map(|x| x.to_row()).collect(); let new = &newrows[pi];
        let (na, nb) = (old.len() as u32, new.len() as u32);
        let (runs, st) = if p.kind == 3 { (Vec::new(), [0u64; 4]) } else { match fpc_runs[pi].take() { Some(r) => (r, [0u64; 4]), None => align(&old, new) } }; p.matched = runs.iter().map(|r| r.2 as u64).sum(); p.tiers = st;
        p.named_old = vec![0; 633]; p.named_new = vec![0; 633];
        for r in old.iter() { for j in 1..=qubits(r[0]) { p.named_old[r[j] as usize] += 1; } }
        for r in new.iter() { for j in 1..=qubits(r[0]) { p.named_new[r[j] as usize] += 1; } }
        drop(old);
        p.s_new = (p.s_old as i64 + gdelta) as u64; p.e_new = p.s_new + nb as u64;
        if p.kind == 3 {
            // pre3: nothing aligns; the table entries strictly inside are dropped; the block runs in the frame in force at its END (hg);
            // if the frame at its start differs, one entry (start, hg, move) is added at the start
            let k0 = t.ent.partition_point(|x| x.0 <= p.s_old); let k1 = t.ent.partition_point(|x| x.0 < p.e_old);
            for k in k0..k1 { assert!(t.ent[k].2 & 2 == 0, "int4: gap entry inside {}", p.name); p.dropped.push(k); }
            let (hs, hg) = (hid(k0), hid(k1));
            assert!(hs != i1::HIDE && hg != i1::HIDE, "int4: {}: lane 632 not hidden at the block (start {hs}, end {hg})", p.name);
            if hs != hg { p.extra = Some((p.s_new, hg, 1)); }
            let bad = new.iter().enumerate().filter(|(_, r)| i1::names(r, hg)).count();
            if bad > 0 { nconf += bad; p.conflicts.push(format!("CONFLICT {}: hidden lane {} named by {} new records", p.name, hg, bad)); }
            writeln!(log, "int4: {}: old [{}, {}) {} rows -> new [{}, {}) {} rows ({:+}); table entries inside dropped {} {:?}; frame at start {hs}, at end {hg}, added entry {:?}; lanes named by the new rows: {}",
                p.name, p.s_old, p.e_old, na, p.s_new, p.e_new, nb, nb as i64 - na as i64, p.dropped.len(), p.dropped.iter().map(|&k| t.ent[k]).collect::<Vec<_>>(), p.extra, p.named_new.iter().filter(|&&c| c > 0).count()).unwrap();
            for c in p.conflicts.iter() { writeln!(log, "  {c}").unwrap(); }
            gdelta += nb as i64 - na as i64;
            continue;
        }
        // entries strictly inside
        let k0 = t.ent.partition_point(|x| x.0 <= p.s_old); let k1 = t.ent.partition_point(|x| x.0 < p.e_old);
        for k in k0..k1 { let (q, sv) = map_rel(&runs, (t.ent[k].0 - p.s_old) as u32, na, nb);
            assert!(t.ent[k].2 & 2 == 0, "int4: gap entry inside {}", p.name);
            p.ents.push(EntMap { k, old: t.ent[k].0, new: q as u64, h: hid(k), c: t.ent[k].1, f: t.ent[k].2, survivor: sv, first: q as u64, conflict: false }); }
        // validity: entry j at q (relative): h unnamed in [q_{j-1}, q), c unnamed in [q, q_{j+1}) (new records); iterate to a fixed point
        let names = |x: usize, l: u16| i1::names(&new[x], l);
        for _round in 0..8 { let mut changed = false;
            for j in 0..p.ents.len() {
                let lo = if j == 0 { 0 } else { p.ents[j - 1].new as usize }; let hi = if j + 1 < p.ents.len() { p.ents[j + 1].new as usize } else { nb as usize };
                let (h, c, q) = (p.ents[j].h, p.ents[j].c, p.ents[j].new as usize);
                let first_h = (lo..hi).find(|&x| names(x, h)).unwrap_or(hi);   // q <= first_h
                let last_c = (lo..hi).rev().find(|&x| names(x, c));            // q > last_c
                let lo_ok = last_c.map_or(lo, |x| x + 1);
                if lo_ok > first_h { if !p.ents[j].conflict { p.ents[j].conflict = true; changed = true; } continue; }
                p.ents[j].conflict = false;
                let q2 = q.clamp(lo_ok, first_h); if q2 != q { p.ents[j].new = q2 as u64; changed = true; } }
            if !changed { break; } }
        // the full check: every new record against the frame in force (old frame before the first entry inside = hid(k0))
        { let mut fk = 0usize; let mut f = hid(k0); let mut bad: Vec<(usize, u16)> = Vec::new();
          for x in 0..nb as usize { while fk < p.ents.len() && p.ents[fk].new as usize <= x { f = p.ents[fk].c; fk += 1; } if i1::names(&new[x], f) { bad.push((x, f)); } }
          // the frame after the piece must be the old one (entries after it are unchanged)
          let fe = hid(k1); assert!(f == fe, "int4: {}: frame at the end {} != {}", p.name, f, fe);
          if !bad.is_empty() { nconf += bad.len();
              let mut by: std::collections::BTreeMap<u16, (usize, usize, usize)> = std::collections::BTreeMap::new();
              for &(x, l) in bad.iter() { let e = by.entry(l).or_insert((x, x, 0)); e.1 = x; e.2 += 1; }
              for (l, (a, b, c)) in by { p.conflicts.push(format!("CONFLICT {}: hidden lane {} named by {} new records, first at +{} (abs {}), last at +{} (abs {})", p.name, l, c, a, p.s_new as usize + a, b, p.s_new as usize + b)); } } }
        // value premise carried by the alignment: the last record naming the incoming hidden lane c before the switch is the same
        // (aligned, surviving) record in the old and the new piece (or none in both), so c holds the same value at both switches
        { let lastpos = |rows: &[Row], at: &[(usize, u16)]| -> Vec<Option<u32>> { let mut last = vec![u32::MAX; 633]; let mut res = vec![None; at.len()]; let mut k = 0usize;
              for x in 0..=rows.len() { while k < at.len() && at[k].0 == x { res[k] = if last[at[k].1 as usize] == u32::MAX { None } else { Some(last[at[k].1 as usize]) }; k += 1; } if x < rows.len() { let r = &rows[x]; for j in 1..=qubits(r[0]) { last[r[j] as usize] = x as u32; } } }
              res };
          let old: Vec<Row> = out[s..e].iter().map(|x| x.to_row()).collect();
          let at_old: Vec<(usize, u16)> = p.ents.iter().map(|x| ((x.old - p.s_old) as usize, x.c)).collect(); let at_new: Vec<(usize, u16)> = p.ents.iter().map(|x| (x.new as usize, x.c)).collect();
          let lo = lastpos(&old, &at_old); let ln = lastpos(new, &at_new); drop(old);
          let mut bad = 0usize;
          for j in 0..p.ents.len() { let same = match (lo[j], ln[j]) { (None, None) => true, (Some(a), Some(b)) => { let (m, sv) = map_rel(&runs, a, na, nb); sv && m == b } _ => false };
              if !same { bad += 1; if bad <= 20 { writeln!(log, "  value premise NOT carried by the alignment: entry #{} in {} (+{} -> +{}), lane {}: last record naming it before the switch old {:?} new {:?}", p.ents[j].k, p.name, p.ents[j].old - p.s_old, p.ents[j].new, p.ents[j].c, lo[j], ln[j]).unwrap(); } } }
          writeln!(log, "  {}: value premise carried by the alignment for {} of {} entries inside", p.name, p.ents.len() - bad, p.ents.len()).unwrap(); }
        for x in p.ents.iter_mut() { x.new += p.s_new; x.first += p.s_new; }
        writeln!(log, "int4: {}: old [{}, {}) {} rows -> new [{}, {}) {} rows ({:+}); aligned {} records in {} runs; resyncs local {} / 16k {} / 16M {} / none {}; entries inside {}: survivors {}, moved to the nearest survivor {}, adjusted by the frame check {}, conflicts {}",
            p.name, p.s_old, p.e_old, na, p.s_new, p.e_new, nb, nb as i64 - na as i64, p.matched, runs.len(), st[0], st[1], st[2], st[3], p.ents.len(),
            p.ents.iter().filter(|x| x.survivor).count(), p.ents.iter().filter(|x| !x.survivor).count(), p.ents.iter().filter(|x| x.new != x.first).count(), p.ents.iter().filter(|x| x.conflict).count()).unwrap();
        for c in p.conflicts.iter() { writeln!(log, "  {c}").unwrap(); }
        { let gone: Vec<u16> = (0..633u16).filter(|&l| p.named_old[l as usize] > 0 && p.named_new[l as usize] == 0).collect(); let came: Vec<u16> = (0..633u16).filter(|&l| p.named_old[l as usize] == 0 && p.named_new[l as usize] > 0).collect();
          writeln!(log, "  lanes named by the old rows only: {:?}; by the new rows only: {:?}", gone, came).unwrap(); }
        p.runs = runs;
        gdelta += nb as i64 - na as i64;
    }
    // per entry inside (survey detail)
    for p in pcs.iter() { for x in p.ents.iter().filter(|x| !x.survivor || x.new != x.first || x.conflict) {
        writeln!(log, "  entry #{} in {}: old {} (+{}) -> new {} (+{}), hidden {} -> {}, flags {}, survivor {}, first choice +{}, conflict {}", x.k, p.name, x.old, x.old - p.s_old, x.new, x.new - p.s_new, x.h, x.c, x.f, x.survivor, x.first - p.s_new, x.conflict).unwrap(); } }
    // ---- 3. the new table
    let mut ent: Vec<(u64, u16, u8)> = Vec::with_capacity(t.ent.len());
    let mut emap: Vec<Option<u64>> = vec![None; t.ent.len()]; for p in pcs.iter() { for x in p.ents.iter() { emap[x.k] = Some(x.new); } }
    let mut dropped = vec![false; t.ent.len()]; for p in pcs.iter() { for &k in p.dropped.iter() { dropped[k] = true; } }
    for (k, e) in t.ent.iter().enumerate() {
        if dropped[k] { continue; }
        let np = match emap[k] { Some(q) => q, None => { let mut d = 0i64; for p in pcs.iter() { if e.0 >= p.e_old { d += (p.e_new - p.s_new) as i64 - (p.e_old - p.s_old) as i64; } else { assert!(e.0 <= p.s_old, "int4: unmapped entry inside {}", p.name); } } (e.0 as i64 + d) as u64 } };
        ent.push((np, e.1, e.2)); }
    for p in pcs.iter() { if let Some(x) = p.extra { ent.push(x); } }
    ent.sort_by_key(|x| x.0);   // stable: an added entry goes after an existing one at the same position
    assert!(ent.windows(2).all(|w| w[0].0 <= w[1].0), "int4: re-bound table out of order");
    let same = ent.windows(2).filter(|w| w[0].0 == w[1].0).count();
    let n_new = (n as i64 + gdelta) as usize;
    let mut item_grow = vec![0i64; pk.items.len()];
    for (ii, it) in pk.items.iter().enumerate() { let s = pos(it.out); let mut d = 0i64; for p in pcs.iter() { if s >= p.e_old { d += (p.e_new - p.s_new) as i64 - (p.e_old - p.s_old) as i64; } } item_grow[ii] = d; }
    writeln!(log, "int4: list {} -> {} ({:+}); entries at equal positions {}; growth before ITEM 4 {}, before ITEM 12 {}; new-record frame conflicts {} [{:?}]", n, n_new, gdelta, same, item_grow[4], item_grow[12], nconf, t0.elapsed()).unwrap();
    eprint!("{log}");
    if !edit { return (n, t, PosMap { pieces: pcs, item_grow, n_old: n as u64, n_new: n_new as u64, log }); }
    assert!(nconf == 0, "int4: {nconf} new records name the hidden lane of their frame (conflicts listed above); not forced");
    // ---- 4. in place: last piece first (each moves the tail after it, then writes its rows)
    let ex: usize = t.ent.iter().map(|e| 2 * ((e.2 & 1) + ((e.2 >> 1) & 1)) as usize).sum::<usize>() + 2 * pcs.iter().filter(|p| p.extra.is_some()).count();   // i1::extra (the flags are kept) + pre3's added entries
    let need = n_new.max(n) + ex + TAIL;
    assert!(out.len() >= need, "int4: no room ({} slots, need {})", out.len(), need);
    let mut cur = n;
    for (pi, p) in pcs.iter().enumerate().rev() { let (s, e) = (p.s_old as usize, p.e_old as usize); let rows = &newrows[pi]; let ne = s + rows.len();
        assert!(ne + (cur - e) <= out.len(), "int4: no room for {}", p.name);
        out.copy_within(e..cur, ne);
        for (j, r) in rows.iter().enumerate() { out[s + j] = S::from_row(*r); }
        cur = (cur as i64 + rows.len() as i64 - (e - s) as i64) as usize; }
    assert!(cur == n_new, "int4: new length");
    drop(newrows);
    let nt = Relabel { n: n_new as u64, hash: hybrid::stream_hash(&out[..n_new]), h0: t.h0, ent };
    writeln!(log, "int4: table re-bound: n {} hash {:016x}, {} entries [{:?}]", nt.n, nt.hash, nt.ent.len(), t0.elapsed()).unwrap();
    eprintln!("int4: table re-bound: n {} hash {:016x}, {} entries [{:?}]", nt.n, nt.hash, nt.ent.len(), t0.elapsed());
    (n_new, nt, PosMap { pieces: pcs, item_grow, n_old: n as u64, n_new: n_new as u64, log })
}

/// survey (tools): the reference list (hybrid + cf631 spliced, mask 0) and `apply` with `mask` in survey mode (no edit, no panic
/// on conflicts); returns the map with every entry inside, the alignment statistics and the conflicts
pub fn survey(m: u32, cf: bool) -> PosMap {
    let keep = FORCE.load(Ordering::Relaxed); FORCE.store(0, Ordering::Relaxed);
    let (pk, sh, mut out, n, rt) = assemble_c::<Row>(true, cf);
    FORCE.store(m, Ordering::Relaxed);
    let (_, _, pm) = apply(&pk, &sh, &mut out, n, rt.expect("relabel table"), true, cf, false);
    FORCE.store(keep, Ordering::Relaxed);
    pm
}

// ------------------------------------------------------------------------------------------------ census list with positions
/// build_slots_hcq(false, hyb 1, cf 1, q 1) with rb631 as its switch says and this module as the mask says, plus every placed
/// piece / segment / relabelling frame in the FINAL positions (kinds: 0 his, 1 item, 2 scan, 3 hybrid region, 4 cf region).
/// Also returns the position map and the per-step log.
pub fn census_build() -> (cftools::CfBuild, Option<PosMap>, Vec<u8>) {
    let t0 = std::time::Instant::now();
    let (pk, sh, mut out, n, rt) = assemble_c::<Row>(true, true);
    let pm = posmap();
    let mut log = format!("{}\n{}\n", hybrid::LOG.lock().unwrap(), cf631::LOG.lock().unwrap());
    if let Some(m) = &pm { log.push_str(&m.log); }
    let t = rt.as_ref().expect("relabel table");
    // pieces / segments in the hybrid-spliced coordinates, then cf631 (cftools::census_list), then this module's map
    let mut pcs = cftools::pieces_hyb(&pk, &sh);
    let at = |o: u64| (o as i64 + sh.at(o)) as u64;
    let mut segs: Vec<(u64, u64)> = Vec::new(); let mut prev = 0u64;
    let mp = |p: u64| -> u64 { let mut q = p; for r in hybrid::REGIONS.iter() { if q > r.start && q < r.end { q = r.end; } } hybrid::map_pos(q) };
    for s in pk.segs.iter() { segs.push((mp(at(prev)), mp(at(s.end)))); prev = s.end; }
    { let lay = cf631::layout(); let mut np: Vec<(u64, u64, u8, u32, u16)> = Vec::new();
      for &(s, e, k, i, sg) in pcs.iter() { let mut parts = vec![(s, e)];
          for r in cf631::REGIONS.iter() { let mut nx = Vec::new(); for &(a, b) in parts.iter() { if b <= r.start || a >= r.end { nx.push((a, b)); continue; } if a < r.start { nx.push((a, r.start)); } if b > r.end { nx.push((r.end, b)); } } parts = nx; }
          for (a, b) in parts { if b > a { np.push((cf631::map_pos(a), cf631::map_pos(b), k, i, sg)); } } }
      for (i, (r, l)) in cf631::REGIONS.iter().zip(lay.iter()).enumerate() { np.push((l.2, l.2 + l.3, 4, i as u32, r.seg as u16)); }
      np.sort(); pcs = np;
      let mpc = |p: u64| -> u64 { let mut q = p; for r in cf631::REGIONS.iter() { if q > r.start && q < r.end { q = r.end; } } cf631::map_pos(q) };
      for s in segs.iter_mut() { *s = (mpc(s.0), mpc(s.1)); } }
    // pre3: his pieces inside the replaced column-1 ranges are removed and one piece (kind 3, index 4 + j) takes each range
    if let Some(m) = &pm { let xs: Vec<(u64, u64, usize, u16)> = m.pieces.iter().filter(|p| p.kind == 3).map(|p| (p.s_old, p.e_old, p.idx, hybrid::X_REGIONS[p.idx].seg as u16)).collect();
        if !xs.is_empty() { let mut np: Vec<(u64, u64, u8, u32, u16)> = Vec::new();
            for &(s, e, k, i, sg) in pcs.iter() { let mut parts = vec![(s, e)];
                for &(xs_, xe, _, _) in xs.iter() { let mut nx = Vec::new(); for &(a, b) in parts.iter() { if b <= xs_ || a >= xe { nx.push((a, b)); continue; } if a < xs_ { nx.push((a, xs_)); } if b > xe { nx.push((xe, b)); } } parts = nx; }
                for (a, b) in parts { if b > a { np.push((a, b, k, i, sg)); } } }
            for &(s, e, j, sg) in xs.iter() { np.push((s, e, 3, 4 + j as u32, sg)); }
            np.sort(); pcs = np; } }
    for p in pcs.iter_mut() { p.0 = map_pos(p.0); p.1 = map_pos(p.1); }
    for s in segs.iter_mut() { *s = (map_pos(s.0), map_pos(s.1)); }
    let fin = |p: u64| p + hybtools::moves_before(t, p);
    for p in pcs.iter_mut() { p.0 = fin(p.0); p.1 = fin(p.1); }
    for s in segs.iter_mut() { *s = (fin(s.0), fin(s.1)); }
    pcs.sort();
    let mut frames: Vec<(u64, u16)> = t.ent.iter().map(|e| (fin(e.0), e.1)).collect();
    let fflags: Vec<u8> = t.ent.iter().map(|e| e.2).collect();
    let inv: Vec<Vec<u16>> = pk.segs.iter().map(|s| s.inv.clone()).collect();
    let h0 = t.h0;
    let mut n = i1::apply(&mut out, n, t);
    log.push_str(&format!("[{:?}] relabelled: {} rows\n", t0.elapsed(), n));
    // q631: ITEM 4 + ITEM 12 (c1_build_cq's position arithmetic)
    { let (s4, e4) = { let p = pcs.iter().find(|p| p.2 == 1 && p.3 == 4).expect("item 4 piece"); (p.0 as usize, p.1 as usize) };
      let (s12, e12) = { let p = pcs.iter().find(|p| p.2 == 1 && p.3 == 12).expect("item 12 piece"); (p.0 as usize, p.1 as usize) };
      let (n2, d4, d12) = q631::apply_items_c(&mut out, n, s4, e4, true, true); n = n2;
      let (d4, d12) = (d4 as u64, d12 as u64);
      let mpq = |p: u64| -> u64 { let mut p2 = p; if p >= e4 as u64 { p2 += d4; } if p >= e12 as u64 { p2 += d12; } p2 };
      for p in pcs.iter_mut() { p.0 = mpq(p.0); p.1 = mpq(p.1); }
      for s in segs.iter_mut() { s.0 = mpq(s.0); s.1 = mpq(s.1); }
      for f in frames.iter_mut() { let p = f.0;
          if p > s4 as u64 && p < e4 as u64 { if p > s4 as u64 + 7_334_962 { assert!(e4 as u64 - p == 2, "int4 census: unexpected frame inside ITEM 4 at {p}"); f.0 = p + d4; } }
          else if p > s12 as u64 && p < e12 as u64 { if p == s12 as u64 + q631::ITEM12_FRAME1 as u64 { f.0 = p + d4; } else { assert!(e12 as u64 - p == 2, "int4 census: unexpected frame inside ITEM 12 at {p}"); f.0 = p + d4 + d12; } }
          else { f.0 = mpq(p); } }
      log.push_str(&format!("[{:?}] q631: ITEM 4 +{d4}, ITEM 12 +{d12}: {} rows\n", t0.elapsed(), n)); }
    // rb631 (rbtool census's arithmetic)
    if rb631::active() {
        let rpk = rb631::pack();
        let item = |idx: u32| -> (u64, u64) { let p = pcs.iter().find(|p| p.2 == 1 && p.3 == idx).expect("item piece"); (p.0, p.1) };
        let frame = |p: u64| -> u16 { let k = frames.partition_point(|f| f.0 <= p); if k == 0 { h0 } else { frames[k - 1].1 } };
        let mut h_at = [[0u16; 2]; 2];
        for (b, &(k, _, _)) in rb631::BRACKETS.iter().enumerate() { let (_, ie) = item(i1::W4_ERASE[k].0 as u32); let (fs, _) = item(i1::W4_FIX[k].0 as u32); h_at[b] = [frame(ie - 1), frame(fs)]; }
        let mut v = std::mem::take(&mut out); v.truncate(n);
        let (nn, info) = rb631::apply_core(&rpk, &mut v, n, h_at); n = nn; out = v;
        for f in frames.iter_mut() { let mut done = false; for b in 0..2 { if f.0 > info.s[b] && f.0 < info.f[b] { assert!(f.0 - info.s[b] == info.p14[b], "frame inside scan {b} not at the switch"); f.0 = info.map(info.s[b]) + info.p15[b]; done = true; } } if !done { f.0 = info.map(f.0); } }
        for p in pcs.iter_mut() { let inside = (0..2).any(|b| p.0 > info.s[b] && p.0 < info.f[b]); if !inside { p.0 = info.map(p.0); p.1 = info.map(p.1); } }
        for s in segs.iter_mut() { *s = (info.map(s.0), info.map(s.1)); }
        log.push_str(&format!("[{:?}] rb631: +{} rows, {} rows\n", t0.elapsed(), info.g, n));
    }
    out.truncate(n); out.reserve_exact(TAIL);
    for i in 0..TAIL { out.push(nonce_row(i, NONCE)); }
    (cftools::CfBuild { rows: out, pieces: pcs, segs, frames, h0, inv, refs: Vec::new(), log }, pm, fflags)
}
