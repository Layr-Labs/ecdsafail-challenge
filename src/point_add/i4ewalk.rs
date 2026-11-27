//! i4ewalk (q631 agent i4e, 2026-11-19; local research, NOT part of any package; switch ON = false): ITEM 4 (item 4, segment 8,
//! the first divide) with its OUTER walk reverse re-emitted from the relay walk class, so that lane 627 is zero and named by no
//! record over the whole walk.
//!
//! The rows are ITEM 4's records as they stand in the relabelled stream (physical lanes 0..631, the census list of
//! hybtools::c1_build), optionally already rewritten by i4g / i4w / i4dwalk (they only change records before the outer walk; the
//! walk range is located by content: anchors, exact length, rows_hash).  `rewrite(rows, sel)` returns the rewritten block and the
//! new walk range.
//!
//! Original (agent i4d, PROVEN by block replay on 34 sets): census offsets [86_151_441, 115_070_540) = walkgen.rs Kind::RevSector
//! with 4 tags (the gate inverse of [SectorReduced prelude, SectorReduced steps, X(sign), class tail]), its six control roles
//! (t0, t1, t2, fire, tst, aux) packed by the 632 team into lanes 621, 627, 628, 629.
//! Replacement (agent i4e): i4ewalkgen.rs Kind::RevRelay { real: 1, guard: 7 } = the gate inverse of [the same prelude, nasqret's
//! relay steps (the inner walk's class) with the reduced class's three guards (select on r != 0, end-of-sector fire uncompute
//! guarded by r != 0, pre-block tst uncompute controlled by fire), X(sign), the same class tail].  Roles: tag0 on 621 (= L[n+1],
//! which the relay steps never use and which is zero between the class tail and the prelude), fire 628, tst 629, every other
//! count bit relayed on r's base-rotation zeros / the height port; loans = 258 distinct dirty lanes outside L, R and the roles.
//! The generated walk is then run through an exact peephole (cancel identical X / CX / CCX pairs across commuting records).
//! MEASURED (tools rproof / etest, ~/Projects/ecdsafail/q631/i4e): equal to the stream's end state on every lane and every shot
//! the original computes correctly on 37 sets, phase identical; lane 627 named by no record of the replacement.
type Row = [u16; 4];
const NONE: u16 = u16::MAX;
#[path = "i4ewalkgen.rs"]
#[allow(dead_code)]
pub mod wg;

/// builder switch (no builder code reads it yet; see ~/Projects/ecdsafail/q631/i4e/summary.py for the hook)
pub const ON: bool = false;
/// the lane freed over the outer walk reverse
pub const FREED_OUTER: u16 = 627;
/// the original outer walk reverse: census offsets of the original item, length, content hash (rows_hash)
pub const OUTER_START: usize = 86_151_441;
pub const OUTER_LEN: usize = 28_919_099;
pub const OUTER_HASH_V: u64 = 0x8766e25d5e303ad2;
/// relay class configuration of the replacement: clean tags (1: tag0 on 621; 0: none, frees 621 too inside the steps), guards
pub const REAL: usize = 1;
pub const GUARD: u8 = 7;
/// exact peephole post-pass on the generated walk (0 = off): cancel two identical X / CX / CCX records when every record between
/// them commutes with them (neither target is a control of the other); scan back at most PEEP_WINDOW live records
pub const PEEP_WINDOW: usize = 100_000;

#[inline] fn nq(k: u16) -> usize { match k { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }
pub fn rows_hash(rows: &[Row]) -> u64 { let mut h = 0x243F6A8885A308D3u64;
    for r in rows { let k = (r[0] as u64) | (r[1] as u64) << 16 | (r[2] as u64) << 32 | (r[3] as u64) << 48; let x = (h ^ k).wrapping_mul(0x9E3779B97F4A7C15); h = x ^ (x >> 29); } h }

/// census-lane registers of the outer walk (agent i4d's recovered configuration): L = the g / |v| packed register (L[n+1] = 621),
/// R = the mg register (R[1] = 626, R[n+1] = R[0])
pub fn outer_l() -> Vec<i32> { let mut l: Vec<i32> = vec![2, 257, 620]; l.extend(3..=128); l.push(618); l.push(621); l }
pub fn outer_r() -> Vec<i32> { let mut r: Vec<i32> = vec![256, 626]; r.extend(258..=384); r.push(623); r.push(256); r }
pub const SIGN: i32 = 624;
pub const FIRE: i32 = 628;
pub const TST: i32 = 629;
pub const TAG0: i32 = 621;
/// 258 distinct dirty loans outside L, R, sign and the roles (and never the freed lane): the stream's own loans (q lanes) first,
/// then V / SIGN lanes, then U-region lanes (idle passengers of the outer walk)
pub fn outer_loan(excl: &[i32]) -> Vec<i32> {
    let mut v: Vec<i32> = (385..=502).collect(); v.extend([135, 253, 252, 251, 248, 0, 512, 255]);
    let more: Vec<i32> = (503..=613).chain(129..=134).chain(136..=247).chain([249, 250, 1, 614, 615, 616, 617, 619, 622, 625, 630, 631]).collect();
    for x in more { if !v.contains(&x) && !excl.contains(&x) { v.push(x); } }
    let (l, r) = (outer_l(), outer_r());
    v.retain(|x| !l.contains(x) && !r.contains(x) && !excl.contains(x) && *x != FREED_OUTER as i32);
    assert!(v.len() >= 258, "i4ewalk: loans {}", v.len()); v.truncate(258); v
}
pub fn outer_cfg(real: usize, guard: u8) -> wg::Cfg {
    let ws: Vec<i32> = (0..7).map(|i| if i < real { [TAG0, -1, -1][i] } else { -1 }).collect();
    let roles: Vec<i32> = [FIRE, TST, SIGN].iter().copied().chain(ws.iter().copied().filter(|&x| x >= 0)).collect();
    wg::Cfg { n: 129, kind: wg::Kind::RevRelay { real, guard }, tags: 4, l: outer_l(), r: outer_r(), loan: outer_loan(&roles), ws_tag: ws, sign: SIGN, fire: FIRE, tst: TST, aux: -1 }
}
/// the replacement records of the outer walk reverse (no adapters: the relay steps sit between the same prelude and class tail)
pub fn outer_rows(real: usize, guard: u8) -> Vec<Row> {
    let cfg = outer_cfg(real, guard);
    let mut out: Vec<Row> = Vec::with_capacity(36_000_000);
    wg::run(&cfg, &mut |x| out.push(x)).expect("i4ewalk: outer walk emission");
    out
}

#[inline] fn ctl(r: &Row) -> [u16; 2] { match r[0] { 13 => [r[1], r[2]], 8 => [r[1], NONE], _ => [NONE, NONE] } }
#[inline] fn tgt(r: &Row) -> u16 { match r[0] { 13 => r[3], 8 => r[2], _ => r[1] } }
/// X / CX / CCX records commute when neither target is a control of the other (t ^= f(c) updates with disjoint reads)
#[inline] fn commute(a: &Row, b: &Row) -> bool { let (ta, tb) = (tgt(a), tgt(b)); !ctl(b).contains(&ta) && !ctl(a).contains(&tb) }
#[inline] fn same(a: &Row, b: &Row) -> bool { a[0] == b[0] && match a[0] { 13 => a[3] == b[3] && ((a[1] == b[1] && a[2] == b[2]) || (a[1] == b[2] && a[2] == b[1])), _ => a == b } }
/// exact peephole (algebra: self-inverse gates, commutation of updates with disjoint reads); repeated until nothing cancels.  Only
/// X / CX / CCX records may be passed (the walk has no other kind; asserted).
pub fn peephole(rows: &[Row], win: usize) -> Vec<Row> {
    assert!(rows.iter().all(|r| matches!(r[0], 6 | 8 | 13)), "i4ewalk: peephole on a record that is not X / CX / CCX");
    let mut cur: Vec<Row> = rows.to_vec();
    for _ in 0..8 {
        let mut out: Vec<Row> = Vec::with_capacity(cur.len()); let mut dead: Vec<bool> = Vec::with_capacity(cur.len()); let mut ncan = 0usize;
        for r in &cur {
            let mut hit = None; let mut seen = 0usize; let mut j = out.len();
            while j > 0 && seen < win { j -= 1; if dead[j] { continue; } seen += 1; let p = &out[j]; if same(p, r) { hit = Some(j); break; } if !commute(p, r) { break; } }
            if let Some(j) = hit { dead[j] = true; ncan += 1; } else { out.push(*r); dead.push(false); }
        }
        let nxt: Vec<Row> = out.into_iter().zip(dead).filter(|x| !x.1).map(|x| x.0).collect();
        cur = nxt; if ncan == 0 { break; }
    }
    cur
}

#[derive(Clone, Copy, Debug)]
pub struct Sel { pub outer: bool }
#[derive(Debug, Default)]
pub struct Stats { pub outer: Option<(usize, usize)>, pub removed: usize, pub added: usize, pub ccx_removed: usize, pub ccx_added: usize, pub found_at: usize }

/// find the original outer walk reverse in `rows` (exact content), searching after its census offset (the earlier rewrites move it
/// by at most a few million records)
pub fn find_outer(rows: &[Row]) -> usize {
    let first: [Row; 3] = [[8, 626, 258, NONE], [8, 258, 626, NONE], [8, 626, 258, NONE]];
    let last: [Row; 2] = [[6, 384, NONE, NONE], [8, 384, 624, NONE]];
    let lo = OUTER_START.saturating_sub(1_000_000); let hi = (OUTER_START + 12_000_000).min(rows.len().saturating_sub(OUTER_LEN));
    let mut hits = Vec::new();
    for p in lo..=hi { if rows[p] == first[0] && rows[p..p + 3] == first[..] && rows[p + OUTER_LEN - 2..p + OUTER_LEN] == last[..] { hits.push(p); } }
    assert!(hits.len() == 1, "i4ewalk: outer walk anchors found {} times", hits.len());
    let p = hits[0];
    if OUTER_HASH_V != 0 { assert!(rows_hash(&rows[p..p + OUTER_LEN]) == OUTER_HASH_V, "i4ewalk: outer walk content differs from the stream it was proven on"); }
    p
}

pub fn rewrite(rows: &[Row], sel: Sel) -> (Vec<Row>, Stats) {
    let mut st = Stats::default();
    if !sel.outer { return (rows.to_vec(), st); }
    let p = find_outer(rows); st.found_at = p;
    let raw = outer_rows(REAL, GUARD);
    let rep = if PEEP_WINDOW > 0 { peephole(&raw, PEEP_WINDOW) } else { raw };
    for r in &rep { for j in 1..=nq(r[0]) { assert!(r[j] != FREED_OUTER && r[j] < 632, "i4ewalk: replacement names the freed lane or a lane >= 632"); } }
    st.removed = OUTER_LEN; st.added = rep.len();
    st.ccx_removed = rows[p..p + OUTER_LEN].iter().filter(|r| r[0] == 13).count(); st.ccx_added = rep.iter().filter(|r| r[0] == 13).count();
    let mut out = Vec::with_capacity(rows.len() + rep.len() - OUTER_LEN);
    out.extend_from_slice(&rows[..p]); out.extend_from_slice(&rep); out.extend_from_slice(&rows[p + OUTER_LEN..]);
    st.outer = Some((p, p + rep.len()));
    (out, st)
}
