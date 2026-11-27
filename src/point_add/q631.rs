//! q631 / int1 (local research, NOT part of any package): the three ITEM 4 rewrites (i4g, i4w R1, i4dwalk inner walk) applied in
//! the builder after the lane relabelling, in the order of ~/Projects/ecdsafail/q631/i4d/tools/src/bin/dtest.rs (fixes g,gt,ip,r1,iw).
//! Switch `ON` = false: nothing here runs (build_slots_h = build_slots_hq(.., ON || FORCE); FORCE is a runtime flag for local tools).
use super::*;
use super::hybtools::{moves_before, C1Build};
use std::sync::atomic::{AtomicBool, Ordering};
pub const ON: bool = super::FINAL631;
/// runtime override for local tools (default false = switch off)
pub static FORCE: AtomicBool = AtomicBool::new(false);
pub fn forced() -> bool { FORCE.load(Ordering::Relaxed) }
/// int2: runtime override of the cf631 switch for local tools (the cf flag of the builder chain = hyb && (cf631::ON || forced_cf()))
pub static FORCE_CF: AtomicBool = AtomicBool::new(false);
pub fn forced_cf() -> bool { FORCE_CF.load(Ordering::Relaxed) }
#[path = "i4g.rs"] #[allow(dead_code)] mod i4g;
#[path = "i4w.rs"] #[allow(dead_code)] mod i4w;
#[path = "i4dwalk.rs"] #[allow(dead_code)] mod i4dwalk;
#[path = "i4ewalk.rs"] #[allow(dead_code)] mod i4ewalk;
#[path = "sm4.rs"] #[allow(dead_code)] mod sm4;
#[path = "i12w.rs"] #[allow(dead_code)] mod i12w;
#[path = "sm12.rs"] #[allow(dead_code)] mod sm12;
/// ITEM 4 in the relabelled census list (hybrid ON), measured by i4dump (q631/i4/dump/item4_meta.txt)
pub const ITEM4_START: usize = 466_255_797;
pub const ITEM4_END: usize = 581_988_866;
/// records added: i4g +555,439, i4w +12 (= 555,451), i4dwalk +4,489,850 (= 5,045,301, int1), i4ewalk outer +2,864,864 (i4e) -> asserted as the total
pub const ADDED_TOTAL: usize = 5_045_301 + 2_864_864;
/// the cf631 splice grows the list by this much per walk before ITEM 4 (walk 1 only: walk 3 comes after ITEM 4)
pub const CF_GROWTH_BEFORE: usize = 41_672_237;
/// first / last 16 rows of ITEM 4 in the relabelled list with cf off (physical lanes), from i4dump (q631/i4/dump/item4_rows.bin);
/// with cf on the same rows must be found at the moved range (asserted)
pub const FIRST16: [[u16; 4]; 16] = [[8, 0, 249, 65535], [8, 249, 0, 65535], [6, 113, 65535, 65535], [6, 114, 65535, 65535], [6, 115, 65535, 65535], [6, 116, 65535, 65535], [6, 117, 65535, 65535], [6, 118, 65535, 65535], [6, 119, 65535, 65535], [6, 120, 65535, 65535], [6, 121, 65535, 65535], [6, 122, 65535, 65535], [6, 123, 65535, 65535], [6, 124, 65535, 65535], [6, 125, 65535, 65535], [6, 126, 65535, 65535]];
pub const LAST16: [[u16; 4]; 16] = [[8, 618, 255, 65535], [8, 255, 618, 65535], [8, 618, 255, 65535], [8, 133, 254, 65535], [8, 254, 133, 65535], [8, 133, 254, 65535], [8, 621, 626, 65535], [8, 626, 621, 65535], [8, 621, 626, 65535], [8, 621, 2, 65535], [8, 2, 621, 65535], [8, 621, 2, 65535], [8, 0, 614, 65535], [8, 614, 0, 65535], [8, 621, 0, 65535], [8, 0, 621, 65535]];

/// int3: sm4 (ITEM 4 ipark seam + winding decoder, after the four rewrites) adds 34 records (etest4: 123,643,234 -> 123,643,268)
pub const SM4_ADDED: usize = 34;
pub const ITEM4_NEW_LEN: usize = 123_643_268;
/// int3: ITEM 12 (the second divide) in the relabelled census list (hybrid on, cf off, q off; q631/i12/dump/item12_meta.txt)
pub const ITEM12_START: usize = 1_665_416_701;
pub const ITEM12_END: usize = 1_775_971_205;
/// both cf631 regions end before ITEM 12: 2 x 41,672,237 (= 2 x CF_GROWTH_BEFORE)
pub const CF_GROWTH_BEFORE_12: usize = 2 * CF_GROWTH_BEFORE;
/// ITEM 12 after i12w::rewrite_full (ip,up,astart G1 windows, R1, phase B) + sm12 (ip, up, r6): etest12 "rows 110554504 -> 120669154"
pub const ITEM12_NEW_LEN: usize = 120_669_154;
/// the frame (relabelling entry) inside ITEM 12 at this offset precedes every rewrite (common prefix asserted); the other one is 2 records before the end
pub const ITEM12_FRAME1: usize = 7_114_288;
/// first / last 16 rows of ITEM 12 in the relabelled list with cf and q off (physical lanes), from q631/i12/dump/item12_rows.bin
pub const FIRST16_12: [[u16; 4]; 16] = [[8, 20, 120, 65535], [8, 120, 20, 65535], [6, 624, 65535, 65535], [6, 625, 65535, 65535], [6, 626, 65535, 65535], [6, 627, 65535, 65535], [6, 546, 65535, 65535], [6, 545, 65535, 65535], [6, 630, 65535, 65535], [6, 631, 65535, 65535], [6, 228, 65535, 65535], [6, 500, 65535, 65535], [6, 501, 65535, 65535], [6, 502, 65535, 65535], [6, 503, 65535, 65535], [6, 543, 65535, 65535]];
pub const LAST16_12: [[u16; 4]; 16] = [[8, 240, 256, 65535], [8, 256, 240, 65535], [8, 240, 256, 65535], [8, 241, 254, 65535], [8, 254, 241, 65535], [8, 241, 254, 65535], [8, 241, 384, 65535], [8, 384, 241, 65535], [8, 241, 384, 65535], [8, 241, 257, 65535], [8, 257, 241, 65535], [8, 241, 257, 65535], [8, 20, 112, 65535], [8, 112, 20, 65535], [8, 113, 20, 65535], [8, 20, 113, 65535]];

/// [s, e) of ITEM 4 in the relabelled list (same arithmetic as hybtools::c1_build)
pub fn item4_range(pk: &Pack, sh: &Shift, rt: &i1::Relabel, hyb: bool) -> (usize, usize) { item4_range_c(pk, sh, rt, hyb, false) }
/// int2: the same with the cf631 splice in the list (`cf`): positions after the hybrid map are moved by cf631::map_pos (= + the growth of the
/// cf regions that end before ITEM 4) before the relabelling moves of the re-bound table are added
pub fn item4_range_c(pk: &Pack, sh: &Shift, rt: &i1::Relabel, hyb: bool, cf: bool) -> (usize, usize) {
    let hl = i1::hook_lens(pk); let it = &pk.items[4];
    let at = |o: u64| (o as i64 + sh.at(o)) as u64;
    let (mut s, mut e) = (at(it.out), at(it.out + it.n)); assert!(e - s == hl[4].unwrap_or(it.n), "q631: item 4 length");
    if hyb { s = hybrid::map_pos(s); e = hybrid::map_pos(e); }
    if cf { assert!(hyb, "q631: cf needs hyb"); s = cf631::map_pos(s); e = cf631::map_pos(e); }
    let (s, e) = (super::int4::map_pos(s), super::int4::map_pos(e));   // q631 / int4 hook: identity without its map
    let (s, e) = (s + moves_before(rt, s), e + moves_before(rt, e));
    (s as usize, e as usize)
}

/// replace out[s..e) (the relabelled ITEM 4 rows) by the rewritten block; returns the new list length
pub fn apply_item4<S: Slot>(out: &mut Vec<S>, n: usize, s: usize, e: usize, log: bool) -> usize { apply_item4_c(out, n, s, e, log, false) }
/// `cf` = the list carries the cf631 splice: the range must be the cf-off range moved by CF_GROWTH_BEFORE, and its first / last 16 rows
/// must equal the cf-off ones (FIRST16 / LAST16).  int3: this ALSO applies ITEM 12's rewrites (see apply_items_c); name kept for mod.rs.
pub fn apply_item4_c<S: Slot>(out: &mut Vec<S>, n: usize, s: usize, e: usize, log: bool, cf: bool) -> usize { apply_items_c(out, n, s, e, log, cf).0 }

/// ITEM 4: the four rewrites + sm4 on rows[..]; returns the new rows
fn rewrite_item4(rows: &[Row], log: bool) -> Vec<Row> {
    let (r1, st) = i4g::rewrite_sel(rows, i4g::Sel { ipark: true, unpark: true, winding: true });
    if log { eprintln!("q631 i4g: added_records {} added_ccx {}", st.added_records, st.added_ccx); }
    assert!(st.added_records == 555_439, "q631: i4g added records");   // 555,439 + 12 (i4w) = the brief's 555,451
    assert!(r1.len() == rows.len() + 555_439);
    let mut gw: Vec<(usize, usize)> = st.stretches.clone(); assert!(gw.len() >= 2, "q631: i4g windows");
    let l = (i4w::REENC[0].enc)().len(); let t1 = i4w::REENC[0].t1;
    let r2 = i4w::rewrite(&r1, &[0]); assert!(r2.len() == r1.len() + 2 * l, "q631: i4w length"); drop(r1);
    for w in gw.iter_mut() { if w.0 > t1 { w.0 += 2 * l; w.1 += 2 * l; } }
    let (r3, s3) = i4dwalk::rewrite(&r2, i4dwalk::Sel { inner: true });
    if log { eprintln!("q631 i4dwalk inner: found_at {} removed {} added {} ccx_removed {} ccx_added {}", s3.found_at, s3.removed, s3.added, s3.ccx_removed, s3.ccx_added); }
    { let d = s3.added as i64 - s3.removed as i64; for w in gw.iter_mut() { if w.0 >= s3.found_at + s3.removed { w.0 = (w.0 as i64 + d) as usize; w.1 = (w.1 as i64 + d) as usize; } } }
    drop(r2);
    let (r4, s4) = i4ewalk::rewrite(&r3, i4ewalk::Sel { outer: true });
    if log { eprintln!("q631 i4ewalk outer: found_at {} removed {} added {} ccx_removed {} ccx_added {}", s4.found_at, s4.removed, s4.added, s4.ccx_removed, s4.ccx_added); }
    assert!(s4.added - s4.removed == 2_864_864, "q631: i4ewalk outer growth");
    { let d = s4.added as i64 - s4.removed as i64; for w in gw.iter_mut() { if w.0 >= s4.found_at + s4.removed { w.0 = (w.0 as i64 + d) as usize; w.1 = (w.1 as i64 + d) as usize; } } }
    drop(r3);
    assert!(r4.len() == rows.len() + ADDED_TOTAL, "q631: total added records {} (expected {})", r4.len() as i64 - rows.len() as i64, ADDED_TOTAL);
    // int3: the ipark seam + winding decoder (etest4's call: ipark window = i4g stretch 0, unpark window = stretch 1)
    let (r5, ss) = sm4::rewrite_sel(&r4, gw[0], Some(gw[1]), sm4::Sel { ipark: true, wind: true });
    if log { eprintln!("q631 sm4: edits {} dropped reads {} moved HMR {} stretch {:?} wind {:?}", ss.edits.len(), ss.dropped_reads, ss.moved_hmr, ss.stretch, ss.wind); }
    assert!(ss.edits.len() == 19 && ss.dropped_reads == 12 && ss.moved_hmr == 4, "q631: sm4 stats");
    assert!(ss.stretch == Some((37983326, 40991694)) && ss.wind == Some((91196651, 91196742)), "q631: sm4 windows");
    assert!(r5.len() == rows.len() + ADDED_TOTAL + SM4_ADDED, "q631: sm4 added records");
    assert!(r5.len() == ITEM4_NEW_LEN, "q631: ITEM 4 new length {}", r5.len());
    // int5: fl's ITEM 4 fix (E2 + transcoder), then fl2 (phase B, then the unpark head); lengths asserted
    let (r6, fs) = super::fl::fli4::rewrite(&r5); drop(r5);
    if log { eprintln!("q631 fli4: freed {:?} lane {} rows {} -> {}", fs.freed, fs.lane, ITEM4_NEW_LEN, r6.len()); }
    assert!(r6.len() == ITEM4_NEW_LEN + FLI4_GROWTH, "q631: fli4 length {}", r6.len());
    let (r7, s1) = super::fl2::fl2pb::rewrite(&r6); drop(r6);
    assert!(r7.len() == ITEM4_NEW_LEN + FLI4_GROWTH + FL2PB_GROWTH, "q631: fl2pb length {}", r7.len());
    let (r8, s2) = super::fl2::fl2up::rewrite(&r7); drop(r7);
    if log { eprintln!("q631 fl2: pb {:?} up {:?} rows {}", s1, s2, r8.len()); }
    assert!(r8.len() == ITEM4_FINAL_LEN, "q631: ITEM 4 final length {}", r8.len());
    r8
}
/// int5: ITEM 4 growth of fl's fli4 (+16,339), fl2pb (+6,010), fl2up (-13,154); final length of ITEM 4
pub const FLI4_GROWTH: usize = 16_339;
pub const FL2PB_GROWTH: usize = 6_010;
pub const FL2UP_SHRINK: usize = 13_154;
pub const ITEM4_FINAL_LEN: usize = ITEM4_NEW_LEN + FLI4_GROWTH + FL2PB_GROWTH - FL2UP_SHRINK;
/// int5: ITEM 12 growth of fl's fli12 (+16,341)
pub const FLI12_GROWTH: usize = 16_341;
pub const ITEM12_FINAL_LEN: usize = ITEM12_NEW_LEN + FLI12_GROWTH;

/// int5: the walk-row fix (fl::flwalk, length preserving) on the two forward hybrid regions of the relabelled, pre-q list out[..n].
/// Region 0 (walk 1) starts at hybrid::layout()[0].2 (nothing before it changes length); region 2 (walk 3) is located by content in
/// [e4, s12): the first generated rows of the forward walk (hybrid::gen with its segment map), asserted unique; the region length and
/// the 4,516 identity records / 8 Z0 records are asserted by flwalk itself.  Lanes: the segment maps of rb631::pack() (= assemble_c's pack).
fn walk_fix<S: Slot>(out: &mut [S], e4: usize, s12: usize, log: bool) {
    use super::fl::flwalk;
    let pk = super::rb631::pack();
    let lay = hybrid::layout();
    const K: usize = 48;
    // locate both forward regions by content: the first K generated rows of the walk (hybrid::gen with the region's segment map)
    let locate = |ri: usize, lo: usize, hi: usize, out: &[S]| -> usize {
        let r = &hybrid::REGIONS[ri]; assert!(r.fwd, "q631: region {ri} is not a forward region");
        let mut head: Vec<Row> = Vec::with_capacity(K);
        let mut cnt = 0u64; hybrid::gen(true, &pk.segs[r.seg].map, hybrid::W0, hybrid::SCR, &mut |row| { if head.len() < K { head.push(row); } cnt += 1; });
        assert!(cnt == hybrid::FWD_LEN);
        let mut hits: Vec<usize> = Vec::new();
        for i in lo..=hi { if out[i].to_row() == head[0] && (1..K).all(|k| out[i + k].to_row() == head[k]) { hits.push(i); } }
        assert!(hits.len() == 1, "q631: forward region {ri} located {} times", hits.len());
        hits[0] };
    let mut starts: Vec<(usize, usize)> = Vec::new();
    let l0 = super::int4::map_pos(lay[0].2) as usize;   // pre3: the replaced column-1 block before it changes the start (identity without the map); before the relabelling's move rows (a few rows later in the relabelled list)
    starts.push((0, locate(0, l0, l0 + 10_000, out)));
    starts.push((2, locate(2, e4, s12 - hybrid::FWD_LEN as usize, out)));
    let mut tot = 0usize;
    for (ri, st) in starts {
        let r = &hybrid::REGIONS[ri]; let m = &pk.segs[r.seg].map;
        let (h1, z0, sl) = (m[flwalk::ID_H1], m[flwalk::ID_Z0], m[flwalk::ID_S]);
        let len = hybrid::FWD_LEN as usize;
        let mut rows: Vec<Row> = out[st..st + len].iter().map(|x| x.to_row()).collect();
        let stt = flwalk::rewrite_region(&mut rows, h1, z0, sl);
        assert!(stt.noop == 4516 && stt.z0 == 8, "q631: flwalk stats {:?}", stt);
        for (k, r) in rows.into_iter().enumerate() { out[st + k] = S::from_row(r); }
        if log { eprintln!("q631 flwalk: region {} at {} lanes (H1 {} Z0 {} S {}): {:?}", ri, st, h1, z0, sl, stt); }
        tot += 1;
    }
    assert!(tot == 2);
}

/// ITEM 12: i12w::rewrite_full (every switch on) + sm12 (ip, up, r6); returns the new rows (etest12's call sequence)
fn rewrite_item12(rows: &[Row], log: bool) -> Vec<Row> {
    let gsel = i12w::g1::Sel { ipark: true, unpark: true, astart: true };
    let (rw1, _st, gs, _cst) = i12w::rewrite_full(rows, i12w::SEL, gsel, true, true);
    if log { eprintln!("q631 i12w: rows {} -> {}", rows.len(), rw1.len()); }
    let (rw, sms) = sm12::rewrite(&rw1, &gs.stretches, sm12::Sel { ipark: true, unpark: true, row126: true }); drop(rw1);
    if log { eprintln!("q631 sm12: edits {:?} -> {} rows", sms.edits, rw.len()); }
    assert!(rw.len() == ITEM12_NEW_LEN, "q631: ITEM 12 new length {}", rw.len());
    // int5: fl's ITEM 12 fix (E2 + transcoder)
    let (rw2, fs) = super::fl::fli12::rewrite(&rw); drop(rw);
    if log { eprintln!("q631 fli12: freed {:?} lane {} rows {}", fs.freed, fs.lane, rw2.len()); }
    assert!(rw2.len() == ITEM12_FINAL_LEN, "q631: ITEM 12 final length {}", rw2.len());
    rw2
}

/// ITEM 4 (range s..e given by the caller) and ITEM 12 (range found here: ITEM12_START/END + the cf growth + ITEM 4's growth, ASSERTED by
/// the first / last 16 rows and the length).  Returns (new list length, ITEM 4 growth, ITEM 12 growth).  ITEM 12's range in the list BEFORE
/// this call is [s12, e12) = [ITEM12_START + cf growth, ITEM12_END + cf growth); `p12` = (s12, e12).
pub fn apply_items_c<S: Slot>(out: &mut Vec<S>, n: usize, s: usize, e: usize, log: bool, cf: bool) -> (usize, usize, usize) {
    let g = if cf { CF_GROWTH_BEFORE } else { 0 };
    let g = (g as i64 + super::int4::grow_before_item(4)) as usize;   // q631 / int4 hook: 0 without its map
    assert!((s, e) == (ITEM4_START + g, ITEM4_END + g), "q631: ITEM 4 range {s} {e} (expected the hybrid census list, cf {cf})");
    assert!(out[s..s + 16].iter().zip(FIRST16.iter()).all(|(x, y)| x.to_row() == *y), "q631: ITEM 4 first 16 rows differ from the cf-off rows");
    assert!(out[e - 16..e].iter().zip(LAST16.iter()).all(|(x, y)| x.to_row() == *y), "q631: ITEM 4 last 16 rows differ from the cf-off rows");
    // ITEM 12's position in the list as it stands now (before ITEM 4 grows)
    let g12 = if cf { CF_GROWTH_BEFORE_12 } else { 0 };
    let g12 = (g12 as i64 + super::int4::grow_before_item(12)) as usize;   // q631 / int4 hook: 0 without its map
    let (s12, e12) = (ITEM12_START + g12, ITEM12_END + g12);
    assert!(e12 <= n && s12 > e, "q631: ITEM 12 range outside the list");
    assert!(out[s12..s12 + 16].iter().zip(FIRST16_12.iter()).all(|(x, y)| x.to_row() == *y), "q631: ITEM 12 first 16 rows differ from the cf-off rows");
    assert!(out[e12 - 16..e12].iter().zip(LAST16_12.iter()).all(|(x, y)| x.to_row() == *y), "q631: ITEM 12 last 16 rows differ from the cf-off rows");
    // ---- int5: fl's forward walk-row fix (walk 1 before ITEM 4, walk 3 between ITEM 4 and ITEM 12), length preserving
    walk_fix(&mut out[..n], e, s12, log);
    // ---- ITEM 4
    let rows: Vec<Row> = out[s..e].iter().map(|x| x.to_row()).collect();
    let mut r3 = rewrite_item4(&rows, log);
    { let r = super::int4::reset_subst(&mut r3, 4); if !r.is_empty() { eprintln!("q631: resets ITEM 4 {:?}", r); } }
    drop(rows);
    let d4 = r3.len() - (e - s); let nn = n + d4; let need = nn + TAIL;
    if out.len() < need { out.reserve_exact(need - out.len()); out.resize(need, S::empty()); }
    out.copy_within(e..n, e + d4);
    for (i, r) in r3.iter().enumerate() { out[s + i] = S::from_row(*r); }
    drop(r3);
    if log { eprintln!("q631: ITEM 4 done, list {} -> {} records", n, nn); }
    // ---- ITEM 12, now at [s12 + d4, e12 + d4): the same rows (asserted again), walks / windows by content
    let (s12, e12) = (s12 + d4, e12 + d4);
    assert!(out[s12..s12 + 16].iter().zip(FIRST16_12.iter()).all(|(x, y)| x.to_row() == *y), "q631: ITEM 12 first 16 rows differ after ITEM 4's growth");
    assert!(out[e12 - 16..e12].iter().zip(LAST16_12.iter()).all(|(x, y)| x.to_row() == *y), "q631: ITEM 12 last 16 rows differ after ITEM 4's growth");
    assert!(e12 - s12 == ITEM12_END - ITEM12_START, "q631: ITEM 12 length");
    let rows: Vec<Row> = out[s12..e12].iter().map(|x| x.to_row()).collect();
    let mut r12 = rewrite_item12(&rows, log);
    { let r = super::int4::reset_subst(&mut r12, 12); if !r.is_empty() { eprintln!("q631: resets ITEM 12 {:?}", r); } }
    // the relabelling frame at ITEM12_FRAME1 precedes every rewrite: the first rewrite starts after it
    { let cp = rows.iter().zip(r12.iter()).take_while(|(a, b)| a == b).count(); assert!(cp > ITEM12_FRAME1 + 1, "q631: ITEM 12 common prefix {} does not cover the frame at +{}", cp, ITEM12_FRAME1); }
    drop(rows);
    let d12 = r12.len() - (e12 - s12); let n2 = nn + d12; let need = n2 + TAIL;
    if out.len() < need { out.reserve_exact(need - out.len()); out.resize(need, S::empty()); }
    out.copy_within(e12..nn, e12 + d12);
    for (i, r) in r12.iter().enumerate() { out[s12 + i] = S::from_row(*r); }
    if log { eprintln!("q631: ITEM 12 done, list {} -> {} records", nn, n2); }
    (n2, d4, d12)
}

/// the census build (hybtools::c1_build) with the ITEM 4 rewrite applied when `q`; pieces / segments / frames after ITEM 4 shifted
pub fn c1_build_q(hyb: bool, q: bool) -> C1Build {
    let (pk, sh, mut out, n, rt) = assemble::<Row>(hyb);
    let hl = i1::hook_lens(&pk);
    let at = |o: u64| (o as i64 + sh.at(o)) as u64;
    let mut pcs: Vec<(u64, u64, u8, u32, u16)> = Vec::new();
    for (k, p) in pk.his.iter().enumerate() { let s = at(p.out); pcs.push((s, s + (p.to - p.from), 0, k as u32, p.seg as u16)); }
    for (k, it) in pk.items.iter().enumerate() { let s = at(it.out); let e = at(it.out + it.n); assert!(e - s == hl[k].unwrap_or(it.n), "c1: item {} length", k); pcs.push((s, e, 1, k as u32, pk.seg_of(it.out) as u16)); }
    for (k, sp) in pk.scans.iter().enumerate() { pcs.push((at(sp.out), at(sp.end), 2, k as u32, pk.seg_of(sp.out) as u16)); }
    let mut segs: Vec<(u64, u64)> = Vec::new(); let mut prev = 0u64;
    for s in pk.segs.iter() { segs.push((at(prev), at(s.end))); prev = s.end; }
    if hyb {
        let lay = hybrid::layout();
        let mut np: Vec<(u64, u64, u8, u32, u16)> = Vec::new();
        for &(s, e, k, i, sg) in pcs.iter() {
            let mut parts = vec![(s, e)];
            for r in hybrid::REGIONS.iter() { let mut nx = Vec::new(); for &(a, b) in parts.iter() { if b <= r.start || a >= r.end { nx.push((a, b)); continue; } if a < r.start { nx.push((a, r.start)); } if b > r.end { nx.push((r.end, b)); } } parts = nx; }
            for (a, b) in parts { if b > a { np.push((hybrid::map_pos(a), hybrid::map_pos(b), k, i, sg)); } }
        }
        for (i, (r, l)) in hybrid::REGIONS.iter().zip(lay.iter()).enumerate() { np.push((l.2, l.2 + l.3, 3, i as u32, r.seg as u16)); }
        pcs = np;
        for s in segs.iter_mut() { *s = (hybrid::map_pos(s.0), hybrid::map_pos(s.1)); }
    }
    let t = rt.as_ref().expect("relabel table");
    let fin = |p: u64| p + moves_before(t, p);
    for p in pcs.iter_mut() { p.0 = fin(p.0); p.1 = fin(p.1); }
    for s in segs.iter_mut() { *s = (fin(s.0), fin(s.1)); }
    pcs.sort();
    let mut frames: Vec<(u64, u16)> = t.ent.iter().map(|e| (fin(e.0), e.1)).collect();
    let inv: Vec<Vec<u16>> = pk.segs.iter().map(|s| s.inv.clone()).collect();
    let h0 = t.h0;
    let (s4, e4) = item4_range(&pk, &sh, t, hyb);
    assert!(pcs.iter().any(|p| p.2 == 1 && p.3 == 4 && p.0 as usize == s4 && p.1 as usize == e4), "q631: item 4 piece = range");
    let mut n = i1::apply(&mut out, n, t);
    if q {
        let n2 = apply_item4(&mut out, n, s4, e4, true); let d = (n2 - n) as u64; n = n2;
        let sh1 = |p: &mut u64| { if *p >= e4 as u64 { *p += d; } };
        for p in pcs.iter_mut() { sh1(&mut p.0); sh1(&mut p.1); }
        for s in segs.iter_mut() { sh1(&mut s.0); sh1(&mut s.1); }
        // frames inside ITEM 4: the one at +7,334,962 precedes every rewrite (unchanged); the later one (2 records before the end) moves with the end
        for f in frames.iter_mut() { if f.0 >= e4 as u64 || (f.0 > s4 as u64 + 7_334_962 && f.0 < e4 as u64) { f.0 += d; } }
    }
    for i in 0..TAIL { out[n + i] = nonce_row(i, NONCE); }
    out.truncate(n + TAIL);
    C1Build { rows: out, pieces: pcs, segs, frames, h0, inv }
}

/// int2: the census build with the cf631 splice (`cf`, hybrid on) and the ITEM 4 rewrites (`q`, four rewrites): cftools::census_list(cf) (assemble,
/// hybrid splice, cf631 splice, relabelling, nonce rows; pieces / segments / frames in its positions) with ITEM 4 (located as piece kind 1 idx 4)
/// replaced and everything at or after its end shifted.  Returns the rows, pieces (kind 4 = cf regions), segs, frames, h0, inv.
pub fn c1_build_cq(cf: bool, q: bool) -> cftools::CfBuild {
    let mut cb = cftools::census_list(cf);
    if q {
        let (s4, e4) = { let p = cb.pieces.iter().find(|p| p.2 == 1 && p.3 == 4).expect("q631: item 4 piece"); (p.0 as usize, p.1 as usize) };
        let (s12, e12) = { let p = cb.pieces.iter().find(|p| p.2 == 1 && p.3 == 12).expect("q631: item 12 piece"); (p.0 as usize, p.1 as usize) };
        assert!((s12, e12) == (ITEM12_START + if cf { CF_GROWTH_BEFORE_12 } else { 0 }, ITEM12_END + if cf { CF_GROWTH_BEFORE_12 } else { 0 }), "q631: ITEM 12 piece range");
        let n0 = cb.rows.len() - TAIL;
        let (n, d4, d12) = apply_items_c(&mut cb.rows, n0, s4, e4, true, cf);
        for i in 0..TAIL { cb.rows[n + i] = nonce_row(i, NONCE); }
        cb.rows.truncate(n + TAIL);
        let (d4, d12) = (d4 as u64, d12 as u64);
        // old position -> new position; positions strictly inside an item are frames (handled below)
        let mp = |p: u64| -> u64 { let mut p2 = p; if p >= e4 as u64 { p2 += d4; } if p >= e12 as u64 { p2 += d12; } p2 };
        for p in cb.pieces.iter_mut() { p.0 = mp(p.0); p.1 = mp(p.1); }
        for s in cb.segs.iter_mut() { s.0 = mp(s.0); s.1 = mp(s.1); }
        // frames inside ITEM 4: the one at +7,334,962 precedes every rewrite (unchanged); the later one (2 records before the end) moves with the end.
        // frames inside ITEM 12: the one at +ITEM12_FRAME1 precedes every rewrite (d4 only); the one 2 records before the end moves with the end.
        for f in cb.frames.iter_mut() {
            let p = f.0;
            if p > s4 as u64 && p < e4 as u64 { if p > s4 as u64 + 7_334_962 { assert!(e4 as u64 - p == 2, "q631: unexpected frame inside ITEM 4 at {p}"); f.0 = p + d4; } }
            else if p > s12 as u64 && p < e12 as u64 {
                if p == s12 as u64 + ITEM12_FRAME1 as u64 { f.0 = p + d4; }
                else { assert!(e12 as u64 - p == 2, "q631: unexpected frame inside ITEM 12 at {p}"); f.0 = p + d4 + d12; } }
            else { f.0 = mp(p); }
        }
    }
    cb
}

/// int2, READ-ONLY listing for the main session (step 8): the relabelling-table entries strictly inside each piece of the census list
/// (hybtools::c1_build's piece table, switches cf / q off; `hyb` = hybrid splice).  Positions are in the FINAL relabelled list (move rows
/// included, nonce rows last), the same list as c1_build's pieces.  Per entry: position relative to the piece start of the first record AFTER
/// its move rows, the pre-relabel position, target lane, flags, number of move rows.  Returns the text.
pub fn relabel_listing(hyb: bool) -> String {
    use std::fmt::Write as _;
    let (pk, sh, out, _n, rt) = assemble::<Row>(hyb);
    drop(out);
    let hl = i1::hook_lens(&pk);
    let at = |o: u64| (o as i64 + sh.at(o)) as u64;
    let mut pcs: Vec<(u64, u64, u8, u32, u16)> = Vec::new();
    for (k, p) in pk.his.iter().enumerate() { let s = at(p.out); pcs.push((s, s + (p.to - p.from), 0, k as u32, p.seg as u16)); }
    for (k, it) in pk.items.iter().enumerate() { let s = at(it.out); let e = at(it.out + it.n); assert!(e - s == hl[k].unwrap_or(it.n), "c1: item {} length", k); pcs.push((s, e, 1, k as u32, pk.seg_of(it.out) as u16)); }
    for (k, sp) in pk.scans.iter().enumerate() { pcs.push((at(sp.out), at(sp.end), 2, k as u32, pk.seg_of(sp.out) as u16)); }
    if hyb {
        let lay = hybrid::layout();
        let mut np: Vec<(u64, u64, u8, u32, u16)> = Vec::new();
        for &(s, e, k, i, sg) in pcs.iter() {
            let mut parts = vec![(s, e)];
            for r in hybrid::REGIONS.iter() { let mut nx = Vec::new(); for &(a, b) in parts.iter() { if b <= r.start || a >= r.end { nx.push((a, b)); continue; } if a < r.start { nx.push((a, r.start)); } if b > r.end { nx.push((r.end, b)); } } parts = nx; }
            for (a, b) in parts { if b > a { np.push((hybrid::map_pos(a), hybrid::map_pos(b), k, i, sg)); } }
        }
        for (i, (r, l)) in hybrid::REGIONS.iter().zip(lay.iter()).enumerate() { np.push((l.2, l.2 + l.3, 3, i as u32, r.seg as u16)); }
        pcs = np;
    }
    let t = rt.as_ref().expect("relabel table");
    let fin = |p: u64| p + moves_before(t, p);
    for p in pcs.iter_mut() { p.0 = fin(p.0); p.1 = fin(p.1); }
    pcs.sort();
    let kn = |k: u8| match k { 0 => "his", 1 => "item", 2 => "scan", _ => "hybrid-region" };
    let mut s = String::new();
    writeln!(s, "# relabelling-table entries strictly inside each piece; list = hybrid {} cf off q off, final relabelled positions (c1_build's)", if hyb { "ON" } else { "OFF" }).unwrap();
    writeln!(s, "# table: n {} h0 {} entries {}.  entry: pos_final (first record after its move rows), pos_pre (pre-relabel position), lane c (hidden lane from here), flags (bit0 move data h->c, bit1 gap move), moves (rows)", t.n, t.h0, t.ent.len()).unwrap();
    writeln!(s, "# piece lines: PIECE kind idx seg start end len count ; then ENTRY rel_to_start pos_final pos_pre lane flags moves").unwrap();
    let mut total_inside = 0usize; let mut tmp: Vec<String> = Vec::new(); let mut npieces = 0usize; let mut with = 0usize;
    for p in pcs.iter() {
        npieces += 1;
        let mut es: Vec<String> = Vec::new();
        for e in t.ent.iter() { let pf = fin(e.0); if pf > p.0 && pf < p.1 { let mv = 2 * ((e.2 & 1) + ((e.2 >> 1) & 1)) as u64;
            es.push(format!("ENTRY {} {} {} {} {} {}", pf - p.0, pf, e.0, e.1, e.2, mv)); } }
        total_inside += es.len(); if !es.is_empty() { with += 1; }
        tmp.push(format!("PIECE {} {} seg {} [{}, {}) len {} count {}", kn(p.2), p.3, p.4, p.0, p.1, p.1 - p.0, es.len())); tmp.extend(es);
    }
    writeln!(s, "# {} pieces, {} contain entries, {} entries strictly inside (of {} in the table)", npieces, with, total_inside, t.ent.len()).unwrap();
    for l in tmp { writeln!(s, "{}", l).unwrap(); }
    s
}
