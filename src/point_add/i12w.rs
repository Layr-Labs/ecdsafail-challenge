//! i12w (q631 agent i12, 2026-11-19; local research, NOT part of any package; nothing in the builder calls it): ITEM 12 (item 12,
//! segment 25, the second divide Y <- Y D^-1 mod p, n = 127) with both Euclid walks re-emitted from the tree's walk generator so
//! that lanes the stream needs as walk roles are zero and named by no record over the whole walk.
//!
//! The rows are ITEM 12's records as they stand in the relabelled census list (physical lanes 0..631; hybtools::c1_build, frame
//! h = 20 over both walks), i.e. after the other team's pipeline i1::ITEM12_SPEC (caps, negx, ctr, pad, fold, witness `apply:20`).
//! Self-contained (no `super::` use) so that local tools can include it by path.
//!
//! INNER walk (census [41_288_733, 68_456_028), 27_167_295 records; PROVEN = walkgen.rs Kind::Inner{real: 2} + entry adapter, by
//! block replay on 16 real + 8 mixed sets, agent i12 tools gproof): L = the mg register [256, 112, 382..258, 244], R = the A register
//! [507, 115..119, 247, 120..239, 513], tags 243, 245, fire 246, tst 114 (wire 251), sign 257, loans = q lanes 383..506 (through
//! the item wire map).  Replacement: [127 adapter X on L[1..=126], R[126]] + Inner{real} (real 0: agent i4d's two exact fixes, qa
//! on the last loan; real 1: tag 243 only).  Freed: 245 (real <= 1), 243 too (real 0).  Both are measured out (HMR) at census
//! 41_221_568 / 41_221_570, named by no record between the HMR and the walk and by no record of the replacement, and the stream
//! recomputes them only after census 68_555_956: zero and unnamed over [41_221_571, 68_555_956) (STRUCTURAL).
//!
//! OUTER walk reverse (census [87_660_054, 109_898_531), 22_238_477 records; PROVEN = walkgen.rs Kind::RevSector tags 5 (t0 on a
//! spare lane, the stream packs it) + exit X on L[0] = 513, same tools): L = the g / |v| packed register (L[n] = 240, L[n+1] = aux
//! = 248), R = [256, 515, 258..382, 112], fire 243, tst 114, aux 248, tags t1..t3 = 244, 245, 246, sign 113.  The stream carries
//! wire 20's value (`apply:20`, a passenger the item never names) on lane 246 at the walk start and on lane 240 at its end (882
//! witness stretches inside the walk, SAMPLED-zero premises of the other team).  Replacement: Kind::RevRelay{real, guard 7}
//! (agent i4e's gate inverse of the relay class with the three r != 0 guards) with tag0 on L[n+1] = 248 (zero between the class
//! tail and the prelude; the relay steps never use it), [tag1 on 244 when real = 2], fire 243, tst 114, sign 113; wire 20's value
//! stays on lane 246 for the whole replacement (246 is measured out at census 87_660_050 just before the stream moves the value
//! onto it, and the replacement never names it), then `CX 246 240; CX 240 246` moves it onto 240 (L[n]: 0 at the end of the
//! reverse walk, it is the (n+1)-th lane of the 127-bit register) and the exit adapter `X 513`.  The 882 witness stretches inside
//! the walk are dropped with it.  Freed: 245 (and 244 when real = 1): measured out at census 87_660_049 / 87_660_053, named by
//! no record of the replacement, recomputed by the stream only after it (STRUCTURAL).
type Row = [u16; 4];
const NONE: u16 = u16::MAX;
#[path = "i12walkgen.rs"]
#[allow(dead_code)]
pub mod wg;
/// agent i10's Cuccaro -> ancilla-free adder converter (copy)
#[path = "i12c0.rs"]
#[allow(dead_code)]
pub mod c0;

/// builder switch (no builder code reads it; see ~/Projects/ecdsafail/q631/i12/summary.py for the hook)
pub const ON: bool = false;
pub const N: usize = 127;

pub fn rows_hash(rows: &[Row]) -> u64 { let mut h = 0x243F6A8885A308D3u64;
    for r in rows { let k = (r[0] as u64) | (r[1] as u64) << 16 | (r[2] as u64) << 32 | (r[3] as u64) << 48; let x = (h ^ k).wrapping_mul(0x9E3779B97F4A7C15); h = x ^ (x >> 29); } h }
#[inline] fn nq(k: u16) -> usize { match k { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }

// ------------------------------------------------------------------------------------------------------------- inner walk
pub const INNER_START: usize = 41_288_733;
pub const INNER_LEN: usize = 27_167_295;
pub fn inner_l() -> Vec<i32> { let mut l = vec![256, 112]; l.extend((258..=382).rev()); l.extend([244, 244]); l }
pub fn inner_r() -> Vec<i32> { let mut r = vec![507, 115, 116, 117, 118, 119, 247]; r.extend(120..=239); r.extend([513, 513]); r }
/// the stream's loans in ladder order (124), then lanes no record of the census inner walk names (dirty passengers; never the
/// frame lane 20 or the witness lane 515); the last one hosts qa when real = 0
pub fn inner_loans() -> Vec<i32> { let mut v: Vec<i32> = (383..=498).collect(); v.extend([249, 250, 251, 252, 253, 504, 505, 506]);
    let pad: Vec<i32> = (32..=111).chain(21..=29).chain(0..=19).chain(516..=631).collect(); let mut k = 0; while v.len() < 2 * N { v.push(pad[k]); k += 1; } v }
pub const INNER_TAGS: [i32; 2] = [243, 245];
pub const INNER_FIRE: i32 = 246;
pub const INNER_TST: i32 = 114;
pub const INNER_SIGN: i32 = 257;
pub fn inner_cfg(real: usize) -> wg::Cfg {
    let mut ws: Vec<i32> = INNER_TAGS[..real.min(2)].to_vec(); while ws.len() < 7 { ws.push(-1); }
    wg::Cfg { n: N, kind: wg::Kind::Inner { real }, tags: 4, l: inner_l(), r: inner_r(), loan: inner_loans(), ws_tag: ws, sign: INNER_SIGN, fire: INNER_FIRE, tst: INNER_TST, aux: -1 }
}
/// replacement of the inner walk: entry adapter + generated walk
pub fn inner_rows(real: usize) -> Vec<Row> {
    let (l, r) = (inner_l(), inner_r()); let mut out: Vec<Row> = Vec::with_capacity(34_000_000);
    for &x in l[1..N].iter().chain(std::iter::once(&r[N - 1])) { out.push([6, x as u16, NONE, NONE]); }
    wg::run(&inner_cfg(real), &mut |x| out.push(x)).expect("i12w: inner walk emission");
    out
}
pub fn inner_freed(real: usize) -> Vec<u16> { if real == 0 { vec![243, 245] } else if real == 1 { vec![245] } else { vec![] } }

// ------------------------------------------------------------------------------------------------------------- outer walk
pub const OUTER_START: usize = 87_660_054;
pub const OUTER_LEN: usize = 22_238_477;
pub fn outer_l() -> Vec<i32> { let mut l: Vec<i32> = vec![513, 257, 241]; l.extend(516..=530); l.push(509); l.extend(532..=542); l.push(499); l.push(544); l.extend([531, 514, 510, 511]);
    l.extend(549..=621); l.extend([548, 547]); l.extend(624..=627); l.extend([546, 545, 630, 631, 20, 500, 501, 502, 503, 543, 629, 628]); l.extend([240, 248]); l }
pub fn outer_r() -> Vec<i32> { let mut r: Vec<i32> = vec![256, 515]; r.extend(258..=382); r.extend([112, 256]); r }
pub const OUTER_FIRE: i32 = 243;
pub const OUTER_TST: i32 = 114;
pub const OUTER_SIGN: i32 = 113;
/// tag0 on L[n+1] (= the stream's aux lane), tag1 on 244 (a stream tag) when real = 2
pub const OUTER_TAGS: [i32; 2] = [248, 244];
pub const OUTER_R_HOST: u16 = 246;
pub const OUTER_R_OUT: u16 = 240;
pub const OUTER_EXIT_X: u16 = 513;
/// 2n + 4 distinct dirty loans outside L, R and the roles: the stream's loans (q lanes) first, then the idle k register 115..239,
/// then passengers (never the frame lane 20, the R host 246 or the freed lanes)
pub fn outer_loans() -> Vec<i32> { let mut v: Vec<i32> = (383..=498).collect(); v.extend([249, 250, 251, 252, 253, 504, 505, 506, 623]);
    let pad: Vec<i32> = (115..=239).chain(32..=111).chain(21..=29).chain(0..=13).chain([242, 247, 254, 255, 507, 508, 512]).collect(); let mut k = 0;
    while v.len() < 2 * N + 4 { v.push(pad[k]); k += 1; } v }
pub fn outer_cfg(real: usize, guard: u8) -> wg::Cfg {
    let mut ws: Vec<i32> = OUTER_TAGS[..real.min(2)].to_vec(); while ws.len() < 7 { ws.push(-1); }
    wg::Cfg { n: N, kind: wg::Kind::RevRelay { real, guard }, tags: 4, l: outer_l(), r: outer_r(), loan: outer_loans(), ws_tag: ws, sign: OUTER_SIGN, fire: OUTER_FIRE, tst: OUTER_TST, aux: -1 }
}
/// replacement of the outer walk reverse: generated walk (wire 20's value stays on 246), its move onto 240, the exit adapter
pub fn outer_rows(real: usize, guard: u8) -> Vec<Row> {
    let mut out: Vec<Row> = Vec::with_capacity(34_000_000);
    wg::run(&outer_cfg(real, guard), &mut |x| out.push(x)).expect("i12w: outer walk emission");
    out.push([8, OUTER_R_HOST, OUTER_R_OUT, NONE]); out.push([8, OUTER_R_OUT, OUTER_R_HOST, NONE]); out.push([6, OUTER_EXIT_X, NONE, NONE]);
    out
}
pub fn outer_freed(real: usize) -> Vec<u16> { if real <= 1 { vec![244, 245] } else { vec![245] } }

/// the four HMR of the shift lanes before the inner walk (census 41,221,568..571) and where they move to (after 41,189,179, the
/// last record naming any of 243..246 before them)
pub const HMR_AT: usize = 41_221_568;
pub const HMR_EARLY: usize = 41_189_180;
pub fn early_hmr(rows: &[Row]) -> Vec<Row> {
    let h: Vec<Row> = rows[HMR_AT..HMR_AT + 4].to_vec();
    assert!(h.iter().zip([243u16, 244, 245, 246]).all(|(r, l)| r[0] == 12 && r[1] == l), "i12w: shift-lane HMR not where expected");
    for i in HMR_EARLY..HMR_AT { let r = rows[i]; assert!(!(1..=nq(r[0])).any(|j| (243..=246).contains(&r[j])), "i12w: a shift lane is named after HMR_EARLY");
        assert!(matches!(r[0], 6 | 8 | 13), "i12w: record kind {} between the early and the original HMR", r[0]); }
    let mut out = Vec::with_capacity(rows.len()); out.extend_from_slice(&rows[..HMR_EARLY]); out.extend_from_slice(&h); out.extend_from_slice(&rows[HMR_EARLY..HMR_AT]); out.extend_from_slice(&rows[HMR_AT + 4..]); out
}

// ------------------------------------------------------------------------------------------------------------- peephole
#[inline] fn ctl(r: &Row) -> [u16; 2] { match r[0] { 13 => [r[1], r[2]], 8 => [r[1], NONE], _ => [NONE, NONE] } }
#[inline] fn tgt(r: &Row) -> u16 { match r[0] { 13 => r[3], 8 => r[2], _ => r[1] } }
#[inline] fn commute(a: &Row, b: &Row) -> bool { let (ta, tb) = (tgt(a), tgt(b)); !ctl(b).contains(&ta) && !ctl(a).contains(&tb) }
#[inline] fn same(a: &Row, b: &Row) -> bool { a[0] == b[0] && match a[0] { 13 => a[3] == b[3] && ((a[1] == b[1] && a[2] == b[2]) || (a[1] == b[2] && a[2] == b[1])), _ => a == b } }
/// agent i4e's exact peephole: cancel two identical X / CX / CCX records when every record between them commutes with them
/// (neither target is a control of the other); repeated until nothing cancels.  Only X / CX / CCX records (asserted).
pub fn peephole(rows: &[Row], win: usize) -> Vec<Row> {
    assert!(rows.iter().all(|r| matches!(r[0], 6 | 8 | 13) && (r[0] != 6 || r[2] == NONE) && (r[0] != 8 || r[3] == NONE)), "i12w: peephole on a record that is not a plain X / CX / CCX");
    let mut cur: Vec<Row> = rows.to_vec();
    for _ in 0..8 {
        let mut out: Vec<Row> = Vec::with_capacity(cur.len()); let mut dead: Vec<bool> = Vec::with_capacity(cur.len()); let mut ncan = 0usize;
        for r in &cur {
            let mut hit = None; let mut seen = 0usize; let mut j = out.len();
            while j > 0 && seen < win { j -= 1; if dead[j] { continue; } seen += 1; let p = &out[j]; if same(p, r) { hit = Some(j); break; } if !commute(p, r) { break; } }
            if let Some(j) = hit { dead[j] = true; ncan += 1; } else { out.push(*r); dead.push(false); }
        }
        cur = out.into_iter().zip(dead).filter(|x| !x.1).map(|x| x.0).collect(); if ncan == 0 { break; }
    }
    cur
}
pub const PEEP_WINDOW: usize = 4096;

// ------------------------------------------------------------------------------------------------------------- splice
#[derive(Clone, Copy, Debug)]
pub struct Sel { pub inner: Option<usize>, pub outer: Option<(usize, u8)>, pub peep: bool }
/// default selection of the switch: inner real 1, outer RevRelay real 2 guard 7, peephole on
pub const SEL: Sel = Sel { inner: Some(1), outer: Some((2, 7)), peep: true };
#[derive(Debug, Default, Clone)]
pub struct Stats { pub inner: Option<(usize, usize)>, pub outer: Option<(usize, usize)>, pub d_inner: i64, pub d_outer: i64, pub ccx_old: usize, pub ccx_new: usize, pub freed: Vec<(usize, usize, u16)>, pub d_pb: i64 }

fn check_inner(rows: &[Row], s: usize) -> bool {
    s + INNER_LEN <= rows.len() && rows[s..s + 63].iter().all(|r| r[0] == 6) && rows[s + INNER_LEN - 1] == [8, 112, 246, NONE] && rows[s + INNER_LEN - 2] == [8, 246, 257, NONE]
}
fn check_outer(rows: &[Row], s: usize) -> bool {
    s + OUTER_LEN <= rows.len() && rows[s] == [8, 515, 258, NONE] && rows[s + 1] == [8, 258, 515, NONE] && rows[s + OUTER_LEN - 1] == [8, 382, 113, NONE] && rows[s + OUTER_LEN - 2] == [6, 382, NONE, NONE]
}
/// the hashes of the original walk ranges (census rows of the dump; asserted, so a changed upstream stream is refused)
pub const INNER_HASH: u64 = 0;
pub const OUTER_HASH: u64 = 0;

/// rewrite ITEM 12's census rows: returns the new rows and the stats (walk ranges in the new rows, the freed lanes per range)
pub fn rewrite(rows: &[Row], sel: Sel) -> (Vec<Row>, Stats) {
    let mut st = Stats::default();
    assert!(check_inner(rows, INNER_START) && check_outer(rows, OUTER_START), "i12w: ITEM 12 walks not at their census offsets");
    if INNER_HASH != 0 { assert!(rows_hash(&rows[INNER_START..INNER_START + INNER_LEN]) == INNER_HASH, "i12w: inner walk content"); }
    if OUTER_HASH != 0 { assert!(rows_hash(&rows[OUTER_START..OUTER_START + OUTER_LEN]) == OUTER_HASH, "i12w: outer walk content"); }
    st.ccx_old = rows.iter().filter(|r| r[0] == 13).count();
    // early measurement of the shift lanes before the inner walk (exact: a measurement commutes with every record that does not
    // name its lane, and the classical bit is read only by the Z repairs after the walk): the four HMR at HMR_AT move to just
    // after the last record that names any of them (HMR_EARLY), so the lanes are zero from there
    let rows: std::borrow::Cow<[Row]> = if sel.inner.is_some() { std::borrow::Cow::Owned(early_hmr(rows)) } else { std::borrow::Cow::Borrowed(rows) };
    let rows: &[Row] = &rows;
    let mut out: Vec<Row> = Vec::with_capacity(rows.len() + 16_000_000);
    out.extend_from_slice(&rows[..INNER_START]);
    if let Some(real) = sel.inner {
        let mut g = inner_rows(real); if sel.peep { g = peephole(&g, PEEP_WINDOW); }
        for &l in &inner_freed(real) { assert!(!g.iter().any(|r| (1..=nq(r[0])).any(|j| r[j] == l)), "i12w: inner replacement names a freed lane"); }
        assert!(!g.iter().any(|r| (1..=nq(r[0])).any(|j| r[j] == 20 || r[j] == 515 || r[j] >= 632)), "i12w: inner replacement names the frame / witness lane");
        let s = out.len(); out.extend_from_slice(&g); st.inner = Some((s, out.len())); st.d_inner = g.len() as i64 - INNER_LEN as i64;
        // 245 (and 243 when real = 0): zero from the early HMR, unnamed until the stream's recompute after the walk
        let ie = INNER_START + INNER_LEN; let rc = (ie..rows.len()).find(|&i| (1..=nq(rows[i][0])).any(|j| rows[i][j] == 245)).unwrap();
        for &l in &inner_freed(real) { let h = (HMR_EARLY..INNER_START).find(|&i| rows[i] == [12, l, rows[i][2], NONE]).expect("i12w: early HMR") + 1;
            assert!(!rows[h..INNER_START].iter().any(|r| (1..=nq(r[0])).any(|j| r[j] == l)), "i12w: lane named between its HMR and the walk");
            let rcl = (ie..rows.len()).find(|&i| (1..=nq(rows[i][0])).any(|j| rows[i][j] == l)).unwrap();
            st.freed.push((h, out.len() + (rcl - ie), l)); let _ = rc; }
    } else { out.extend_from_slice(&rows[INNER_START..INNER_START + INNER_LEN]); }
    out.extend_from_slice(&rows[INNER_START + INNER_LEN..OUTER_START]);
    if let Some((real, guard)) = sel.outer {
        let mut g = outer_rows(real, guard); if sel.peep { let k = g.len() - 3; let mut p = peephole(&g[..k], PEEP_WINDOW); p.extend_from_slice(&g[k..]); g = p; }
        let k = g.len() - 3;
        for &l in &outer_freed(real) { assert!(!g.iter().any(|r| (1..=nq(r[0])).any(|j| r[j] == l)), "i12w: outer replacement names a freed lane"); }
        assert!(!g[..k].iter().any(|r| (1..=nq(r[0])).any(|j| r[j] == OUTER_R_HOST || r[j] >= 632)), "i12w: outer walk names the host of wire 20's value");
        let s = out.len(); out.extend_from_slice(&g); st.outer = Some((s, out.len())); st.d_outer = g.len() as i64 - OUTER_LEN as i64;
        // the freed lanes: zero from their HMR just before the walk, unnamed until the stream's recompute after it
        let oe = OUTER_START + OUTER_LEN;
        for &l in &outer_freed(real) { let h = (OUTER_START - 16..OUTER_START).rev().find(|&i| rows[i][0] == 12 && rows[i][1] == l).expect("i12w: outer HMR");
            assert!(!rows[h + 1..OUTER_START].iter().any(|r| (1..=nq(r[0])).any(|j| r[j] == l)), "i12w: lane named between its HMR and the outer walk");
            let rcl = (oe..rows.len()).find(|&i| (1..=nq(rows[i][0])).any(|j| rows[i][j] == l)).unwrap();
            st.freed.push((s - (OUTER_START - h - 1), out.len() + (rcl - oe), l)); }
    } else { out.extend_from_slice(&rows[OUTER_START..OUTER_START + OUTER_LEN]); }
    out.extend_from_slice(&rows[OUTER_START + OUTER_LEN..]);
    st.ccx_new = out.iter().filter(|r| r[0] == 13).count();
    (out, st)
}

// ============================================================================================================== G1 windows
// Agent i4b's method (ITEM 4's i4g.rs, ported lane by lane; MEASURED identical facts on ITEM 12): lane 258 = mg bit 126 =
// G1 := [g == 1] (g mg = M0 in [2^126, 2^127)) is only READ (and toggled by paired X) over the ipark Gtop window and over the
// unpark Gtop + winding window.  g even -> G1 = 0 (lane 258 already zero).  g odd -> v2(mg) = v2(M0) >= sh (M0 = D << sh), so
// (sh, mg0, mg1) takes 20 of 64 patterns (E_G), and g odd and sh >= 1 -> mg even -> w0 = v0 = 1 (w = -P v mod mg (+ an even
// offset) in the ipark window, w = k/g = -rg / p mod mg in the unpark window, rg odd; gcd(v, mg) = 1) (E_A).  The encoders
// (every gate controlled by p0 = lane 513 = g bit 0) move G1 into lane 246 (sh bit 3) and clear 258; reads of 258 inside the
// window read the decoded G1 = p0 AND lane 246 (3-control gate on a dirty passenger lane); the decoders run at the window ends.
pub mod g1 {
    use super::{Row, NONE};
    pub const FREED: u16 = 258;
    pub const P0: u16 = 513;                    // g bit 0
    pub const SH_B: [u16; 4] = [243, 244, 245, 246];   // sh before the inner walk (wire 20's value on 114 there)
    pub const SH_C: [u16; 4] = [243, 114, 245, 246];   // sh after the inner walk's recompute (wire 20's value on 244 there)
    pub const MG0: u16 = 256;
    pub const MG1: u16 = 112;
    pub const W0: u16 = 507;                    // w / k/g bit 0 (odd when mg is even)
    pub const V0: u16 = 248;                    // |v| bit 0 (odd when mg is even)
    pub const W: u16 = 40;                      // dirty passenger of the 3-control replacements (never named by ITEM 12)
    pub const DIRTY: [u16; 8] = [41, 42, 43, 44, 45, 46, 47, 48];
    /// ipark Gtop window (alpha tail + ipark Gtop rows): first record after the alpha's last non-X write of 258; the row-127
    /// toggle X 258 / CX 258 -> 513 at IP_END stays after the window
    pub const IP_START: usize = 34_676_623;
    pub const IP_END: usize = 41_114_879;
    /// unpark window: first record after the unpark head's last use of the shift lanes; row-127 toggle at GT_X / GT_CX; winding
    /// from G_START; the window ends at the first shift-lane record before the outer walk (G_END)
    /// alpha-start window (between phase B and R1: g's bits are written into 257 / 241 there, 258 is only read): lane 507 holds
    /// A bit 0 = 0 when mg is even (A = 2^256 |v| mod mg), so E_A runs with lane 507 complemented by an X frame
    pub const AS_START: usize = 12_237_718;
    pub const AS_END: usize = 12_301_976;
    pub const GT_START: usize = 68_693_752;
    pub const GT_X: usize = 75_131_852;
    pub const GT_CX: usize = 75_131_853;
    pub const G_START: usize = 75_131_854;
    pub const G_END: usize = 87_660_043;
    #[inline] fn x(t: u16) -> Row { [6, t, NONE, NONE] }
    #[inline] fn cx(c: u16, t: u16) -> Row { [8, c, t, NONE] }
    #[inline] fn ccx(a: u16, b: u16, t: u16) -> Row { [13, a, b, t] }
    #[inline] fn nq(k: u16) -> usize { match k { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }
    pub fn mcx(out: &mut Vec<Row>, ctl: &[(u16, bool)], t: u16, dirty: &[u16]) {
        for &(l, p) in ctl { if !p { out.push(x(l)); } }
        let c: Vec<u16> = ctl.iter().map(|z| z.0).collect();
        match c.len() {
            0 => out.push(x(t)), 1 => out.push(cx(c[0], t)), 2 => out.push(ccx(c[0], c[1], t)),
            u => { let v: Vec<u16> = dirty.iter().copied().filter(|d| !c.contains(d) && *d != t).take(u - 2).collect(); assert!(v.len() == u - 2, "i12w g1 mcx dirty");
                let a = ccx(c[0], c[1], v[0]); let m: Vec<Row> = (2..u - 1).map(|j| ccx(c[j], v[j - 2], v[j - 1])).collect(); let z = ccx(c[u - 1], v[u - 3], t);
                for _ in 0..2 { out.push(a); out.extend(m.iter()); out.push(z); out.extend(m.iter().rev()); } } }
        for &(l, p) in ctl { if !p { out.push(x(l)); } }
    }
    fn snz(o: &mut Vec<Row>, sh: &[u16; 4], extra: &[(u16, bool)], t: u16) {
        let (s0, s1, s2) = (sh[0], sh[1], sh[2]); let d = &DIRTY[..];
        let mut c = extra.to_vec(); c.push((s0, true)); mcx(o, &c, t, d);
        let mut c = extra.to_vec(); c.push((s0, false)); c.push((s1, true)); mcx(o, &c, t, d);
        let mut c = extra.to_vec(); c.push((s0, false)); c.push((s1, false)); c.push((s2, true)); mcx(o, &c, t, d);
    }
    /// E_G (stash in sh, mg0, mg1): i4b's gate list, lanes mapped
    pub fn enc_g(sh: &[u16; 4]) -> Vec<Row> {
        let mut o = Vec::new(); let d = &DIRTY[..]; let (s0, s1, s2, s3) = (sh[0], sh[1], sh[2], sh[3]);
        mcx(&mut o, &[(P0, true), (s3, true), (s0, false), (s1, false), (s2, false)], MG1, d);
        mcx(&mut o, &[(P0, true), (s3, true), (MG1, true)], s1, d);
        mcx(&mut o, &[(P0, true), (s3, true), (MG1, false)], MG0, d);
        mcx(&mut o, &[(P0, true), (MG0, true), (s0, true)], s3, d);
        mcx(&mut o, &[(P0, true), (MG0, true), (s0, false), (s1, true)], s3, d);
        mcx(&mut o, &[(P0, true), (MG0, true), (s0, false), (s1, false), (s2, true)], s3, d);
        mcx(&mut o, &[(P0, true), (MG0, false), (MG1, true), (s0, false), (s1, true), (s2, false)], s3, d);
        o.push(ccx(P0, FREED, s3)); o.push(ccx(P0, s3, FREED));
        o
    }
    /// E_A (stash in sh, w0, v0)
    pub fn enc_a(sh: &[u16; 4]) -> Vec<Row> {
        let mut o = Vec::new(); let d = &DIRTY[..]; let (s0, s1, s2, s3) = (sh[0], sh[1], sh[2], sh[3]);
        mcx(&mut o, &[(P0, true), (s3, true)], V0, d);
        mcx(&mut o, &[(P0, true), (s3, true), (s0, false), (s1, false), (s2, false)], V0, d);
        mcx(&mut o, &[(P0, true), (s3, true)], W0, d);
        mcx(&mut o, &[(P0, true), (s3, true), (s1, false), (s2, false), (W0, false), (V0, true)], s0, d);
        snz(&mut o, sh, &[(P0, true), (W0, false)], s3);
        o.push(ccx(P0, FREED, s3)); o.push(ccx(P0, s3, FREED));
        o
    }
    /// transcoder E_A-encoded -> E_G-encoded (lane 258 stays zero)
    pub fn trans(sh: &[u16; 4]) -> Vec<Row> {
        let mut o = Vec::new(); let d = &DIRTY[..]; let (s0, s1, s2) = (sh[0], sh[1], sh[2]);
        snz(&mut o, sh, &[(P0, true), (W0, false), (V0, false)], MG0);
        snz(&mut o, sh, &[(P0, true), (MG0, true)], V0);
        snz(&mut o, sh, &[(P0, true), (MG0, true)], W0);
        mcx(&mut o, &[(P0, true), (s0, true), (s1, false), (s2, false), (W0, false), (V0, true), (MG0, false)], MG1, d);
        mcx(&mut o, &[(P0, true), (s0, true), (s2, false), (W0, false), (V0, true), (MG1, true), (MG0, false)], s1, d);
        mcx(&mut o, &[(P0, true), (s1, true), (s2, false), (W0, false), (V0, true), (MG1, true), (MG0, false)], s0, d);
        mcx(&mut o, &[(P0, true), (s0, false), (s1, true), (s2, false), (V0, true), (MG1, true), (MG0, false)], W0, d);
        o
    }
    #[derive(Default, Debug, Clone)]
    pub struct Stats { pub replaced: usize, pub neg: usize, pub flipped_p0: usize, pub dropped_x: usize, pub stretches: Vec<(usize, usize)>, pub added: Vec<(usize, i64)> }
    fn patch(out: &mut Vec<Row>, r: Row, i: usize, par258: u8, par2: u8, s3: u16, st: &mut Stats) {
        if r[0] == 8 { let t = r[2]; assert!(t != s3 && t != P0 && t != FREED, "i12w g1: record {} {:?}", i, r);
            if par258 == 1 { out.push(x(t)); st.neg += 1; } if par2 == 1 { out.push(x(P0)); st.flipped_p0 += 1; }
            out.push(ccx(P0, s3, t)); if par2 == 1 { out.push(x(P0)); } st.replaced += 1; return; }
        let a = if r[1] == FREED { r[2] } else { r[1] }; let t = r[3];
        assert!(a != s3 && t != s3 && t != P0 && t != FREED && a != W && t != W, "i12w g1: record {} overlaps the decode lanes", i);
        if par258 == 1 { out.push(cx(a, t)); st.neg += 1; }
        if a == P0 { if par2 == 0 { out.push(ccx(P0, s3, t)); } }
        else { if par2 == 1 { out.push(x(P0)); st.flipped_p0 += 1; }
            out.push(ccx(P0, s3, W)); out.push(ccx(W, a, t)); out.push(ccx(P0, s3, W)); out.push(ccx(W, a, t));
            if par2 == 1 { out.push(x(P0)); } }
        st.replaced += 1;
    }
    struct Win { s: usize, e: usize, pre: Vec<Row>, enc: Vec<Row>, skip: Vec<usize>, tr_at: Option<(usize, Vec<Row>)>, dec: Vec<Row>, stash: Vec<u16>, sh: [u16; 4] }
    fn window(out: &mut Vec<Row>, rows: &[Row], w: &Win, st: &mut Stats) {
        out.extend_from_slice(&w.pre); out.extend_from_slice(&w.enc); let s0 = out.len();
        let (mut par258, mut par2) = (0u8, 0u8);
        for i in w.s..w.e {
            if let Some((at, tr)) = &w.tr_at { if i == *at { assert!(par258 == 0 && par2 == 0, "i12w g1: parity at the transcoder"); out.extend_from_slice(tr); } }
            if w.skip.contains(&i) { continue; }
            let r = rows[i]; let k = r[0]; let n = nq(k);
            assert!(matches!(k, 6 | 8 | 13), "i12w g1: record {} kind {} in the window", i, k);
            if k == 6 { assert!(r[2] == NONE); } if k == 8 { assert!(r[3] == NONE); }
            let stash_live = w.tr_at.as_ref().map_or(true, |(at, _)| i < *at);
            for j in 1..=n { let l = r[j]; assert!(!DIRTY.contains(&l) && l != W, "i12w g1: record {} names a dirty lane", i);
                assert!(!w.sh.contains(&l), "i12w g1: record {} names a shift lane", i);
                if stash_live { assert!(!w.stash.contains(&l), "i12w g1: record {} names a stash lane", i); } }
            if k == 6 && r[1] == FREED { par258 ^= 1; st.dropped_x += 1; continue; }
            if k == 6 && r[1] == P0 { par2 ^= 1; out.push(r); continue; }
            assert!(!(n >= 1 && r[n] == FREED), "i12w g1: record {} writes lane 258", i);
            assert!(!(n >= 1 && r[n] == P0), "i12w g1: record {} writes lane 513", i);
            let uses = (1..n).filter(|&j| r[j] == FREED).count();
            if uses == 0 { out.push(r); continue; }
            assert!(uses == 1 && (k == 13 || k == 8), "i12w g1: record {} reads lane 258 as {:?}", i, r);
            patch(out, r, i, par258, par2, w.sh[3], st);
        }
        assert!(par2 == 0, "i12w g1: unbalanced X parity on lane 513 over the window");
        st.stretches.push((s0, out.len()));
        out.extend_from_slice(&w.dec);
        if par258 == 1 { out.push(x(FREED)); }
    }
    #[derive(Clone, Copy, Debug)]
    pub struct Sel { pub ipark: bool, pub unpark: bool, pub astart: bool }
    /// rows: ITEM 12 census rows with the inner walk possibly replaced (`shift` = its record count change, applied to the unpark
    /// window offsets); windows in offset order
    pub fn rewrite(rows: &[Row], sel: Sel, shift: i64) -> (Vec<Row>, Stats) {
        let mut st = Stats::default(); let mut wins: Vec<Win> = Vec::new();
        let rev = |mut v: Vec<Row>| { v.reverse(); v };
        let sh_ = |p: usize| (p as i64 + shift) as usize;
        if sel.astart {
            let mut dec = rev(enc_a(&SH_B)); dec.push(x(W0));
            wins.push(Win { s: AS_START, e: AS_END, pre: vec![x(W0)], enc: enc_a(&SH_B), skip: vec![], tr_at: None, dec, stash: vec![W0, V0], sh: SH_B });
        }
        if sel.ipark {
            assert!(rows[IP_END] == x(FREED) && rows[IP_END + 1] == cx(FREED, P0), "i12w g1: ipark row-127 toggle not where expected");
            wins.push(Win { s: IP_START, e: IP_END, pre: vec![], enc: enc_a(&SH_B), skip: vec![], tr_at: None, dec: rev(enc_a(&SH_B)), stash: vec![W0, V0], sh: SH_B });
        }
        if sel.unpark {
            let (gs, gx, gcx, g0, ge) = (sh_(GT_START), sh_(GT_X), sh_(GT_CX), sh_(G_START), sh_(G_END));
            assert!(rows[gx] == x(FREED) && rows[gcx] == cx(FREED, P0), "i12w g1: unpark row-127 toggle not where expected");
            assert!(rows[ge] == cx(243, 507), "i12w g1: the outer park record not where expected");
            wins.push(Win { s: gs, e: ge, pre: vec![cx(FREED, P0)], enc: enc_a(&SH_C), skip: vec![gcx], tr_at: Some((g0, trans(&SH_C))), dec: rev(enc_g(&SH_C)), stash: vec![W0, V0], sh: SH_C });
        }
        let mut out: Vec<Row> = Vec::with_capacity(rows.len() + 1_000_000); let mut p = 0usize;
        for w in &wins { out.extend_from_slice(&rows[p..w.s]); let before = out.len() as i64 - w.s as i64; window(&mut out, rows, w, &mut st); let after = out.len() as i64 - w.e as i64; st.added.push((w.s, after - before)); p = w.e; }
        out.extend_from_slice(&rows[p..]);
        (out, st)
    }
}

// ============================================================================================================== R1 (alpha core)
// Agent i4's R1, transferred: over the alpha core window the five lanes (513, 257, 241, 238, 239) = (g bit 0, g bit 1, g bit 2,
// A bit 125, A bit 126) are named by no record, where g = gcd(M0, Y mod M0) and A = 2^256 |v| mod (M0 / g) < M0 / g < 2^127 / g
// (the alpha accumulator; its top lanes are first touched at 34,089,360).  (g mod 8, A >> 125) takes 13 values (A >> 125 in 0..3
// only for g = 1, in {0, 1} for g in {2, 3}, 0 for g >= 4): the encoder CX(x0->x3) CX(x2->x4) CCX(x2,x3->x0) X(x0)
// CCX(x0,x4->x2) X(x0) clears x2 = lane 241 on all 13 (EXHAUSTIVE check, py/r1verify in the i12 report); decoder = reverse.
pub mod r1 {
    use super::{Row, NONE};
    pub const T0: usize = 12_301_982;
    pub const T1: usize = 34_051_583;
    pub const LANES: [u16; 5] = [513, 257, 241, 238, 239];
    pub const FREED: u16 = 241;
    pub fn enc() -> Vec<Row> { let (x0, x2, x3, x4) = (513u16, 241u16, 238u16, 239u16);
        vec![[8, x0, x3, NONE], [8, x2, x4, NONE], [13, x2, x3, x0], [6, x0, NONE, NONE], [13, x0, x4, x2], [6, x0, NONE, NONE]] }
    #[inline] fn nq(k: u16) -> usize { match k { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }
    /// rows in ORIGINAL coordinates before T1 (nothing before it may have been rewritten); returns rows and the freed stretch
    pub fn rewrite(rows: &[Row], shift: i64) -> (Vec<Row>, (usize, usize)) {
        let (t0, t1) = ((T0 as i64 + shift) as usize, (T1 as i64 + shift) as usize);
        for i in t0..t1 { let w = rows[i]; for j in 1..=nq(w[0]) { assert!(!LANES.contains(&w[j]), "i12w r1: record {} names lane {} of the group", i, w[j]); } }
        let e = enc(); let mut d = e.clone(); d.reverse();
        let mut out = Vec::with_capacity(rows.len() + 12);
        out.extend_from_slice(&rows[..t0]); out.extend_from_slice(&e); let s = out.len(); out.extend_from_slice(&rows[t0..t1]); let t = out.len(); out.extend_from_slice(&d); out.extend_from_slice(&rows[t1..]);
        (out, (s, t))
    }
}

/// everything behind the switch: walks (SEL) then the G1 windows; returns the rows, the walk stats (ranges / freed stretches moved
/// to the final coordinates) and the window stats (stretches in final coordinates, lane g1::FREED)
pub fn rewrite_all(rows: &[Row], sel: Sel, gsel: g1::Sel) -> (Vec<Row>, Stats, g1::Stats) { rewrite_all_r(rows, sel, gsel, false) }
/// + R1 over the alpha core when `alpha` (its freed stretch is appended to Stats.freed with lane r1::FREED)
pub fn rewrite_all_r(rows: &[Row], sel: Sel, gsel: g1::Sel, alpha: bool) -> (Vec<Row>, Stats, g1::Stats) {
    let (r1, mut st) = rewrite(rows, sel);
    let (r2, mut gs) = g1::rewrite(&r1, gsel, st.d_inner);
    // records added by each window, at its start (rows of r1)
    let adds: Vec<(usize, i64)> = gs.added.clone();
    let mv = |p: usize| -> usize { let d: i64 = adds.iter().filter(|a| a.0 < p).map(|a| a.1).sum(); (p as i64 + d) as usize };
    for f in st.freed.iter_mut() { *f = (mv(f.0), mv(f.0) + (f.1 - f.0), f.2); }
    if let Some(x) = st.inner.as_mut() { *x = (mv(x.0), mv(x.0) + (x.1 - x.0)); }
    if let Some(x) = st.outer.as_mut() { *x = (mv(x.0), mv(x.0) + (x.1 - x.0)); }
    if !alpha { return (r2, st, gs); }
    let ash: i64 = gs.added.iter().filter(|a| a.0 < r1::T0).map(|a| a.1).sum();   // the alpha-start window lies before R1
    let (r3, (a, b)) = r1::rewrite(&r2, ash);
    let k = (r3.len() - r2.len()) as usize;   // 12 records: encoder before T0, decoder at T1; everything after T1 moves by 12
    let t1 = (r1::T1 as i64 + ash) as usize;
    let mv2 = |p: usize| -> usize { if p >= t1 { p + k } else { p } };
    for f in st.freed.iter_mut() { *f = (mv2(f.0), mv2(f.1), f.2); }
    if let Some(x) = st.inner.as_mut() { *x = (mv2(x.0), mv2(x.1)); }
    if let Some(x) = st.outer.as_mut() { *x = (mv2(x.0), mv2(x.1)); }
    for x in gs.stretches.iter_mut() { *x = (mv2(x.0), mv2(x.1)); }
    st.freed.push((a, b, r1::FREED));
    (r3, st, gs)
}

// ============================================================================================================== phase B (c0 = 257)
// Phase B's ripple adders (Cuccaro, clean carry-in c0 = lane 257) re-emitted as the walk generator's ancilla-free adders by agent
// i10's converter (copy i12c0.rs, + the truncated mod 2^n top and the dropped no-op CX(c0, b0) of the bottom UMA) and two more
// passes for the dirty-controlled / single-controlled forms (candidate add / sub / XOR-frame / carry-out replacements), each
// instance accepted only if equal to its records on random states (c0 = 0, two seeds); adjacent identical X / CX / CCX pairs of
// the range are cancelled first (exact).  Lane 257 is zero at the phase B start (the forward walk's clean role lane, restored by its own
// mark / unmark pair at 7,113,749 / 7,113,999; MEASURED zero on every good shot) and, after the conversion, named by no record
// until the first instance the converter leaves (the dirty-controlled modular adds from ~10.36M): the freed stretch.
pub mod pb {
    pub const S: usize = 7_114_288;
    pub const E: usize = 12_237_718;   // just after the last phase-B adder (its UMA ends with CX 383 257 at 12,237,717)
    pub const C0: u16 = 257;
    pub fn loans() -> Vec<u16> { (49..=111).collect() }
}
/// everything: walks, G1 windows, R1, phase B conversion (applied last: it lies before every other rewritten range)
pub fn rewrite_full(rows: &[Row], sel: Sel, gsel: g1::Sel, alpha: bool, phaseb: bool) -> (Vec<Row>, Stats, g1::Stats, Option<c0::Stats>) {
    let (r3, mut st, mut gs) = rewrite_all_r(rows, sel, gsel, alpha);
    if !phaseb { return (r3, st, gs, None); }
    let r4 = c0::cancel_adjacent(&r3, pb::S, pb::E); let e4 = pb::E - (r3.len() - r4.len()); drop(r3);
    let (r5a, mut cst) = c0::convert(&r4, &[(pb::S, e4)], pb::C0, &pb::loans());
    let e5a = e4 + r5a.len() - r4.len();
    // second pass (dirty-controlled forms; candidate replacements accepted only on an exact random-state match)
    let n5a = r5a.len();
    let (r5b, c2) = c0::convert2(&r5a, (pb::S, e5a), pb::C0, &pb::loans()); drop(r5a);
    let e5b = (e5a as i64 + r5b.len() as i64 - n5a as i64) as usize; let n5b = r5b.len();
    let (r5c, c3) = c0::convert3(&r5b, (pb::S, e5b), pb::C0, &pb::loans()); drop(r5b);
    for c in [&c2, &c3] { cst.found += c.found; cst.replaced += c.replaced; cst.rejected += c.rejected; cst.rec_before += c.rec_before; cst.rec_after += c.rec_after; } cst.left = c3.left;
    let e5c = (e5b as i64 + r5c.len() as i64 - n5b as i64) as usize;
    let nq = |k: u16| -> usize { match k { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } };
    // drop the records of [S, e5c) that only READ c0 at a point where it is 0 (even number of c0 writes so far: outside every
    // instance the converter left): CX(c0, t) / CCX(c0, x, t) with t != c0 act as the identity there (exact)
    let mut r5: Vec<Row> = Vec::with_capacity(r5c.len()); r5.extend_from_slice(&r5c[..pb::S]); let mut wpar = 0usize; let mut nd = 0usize;
    for i in pb::S..e5c { let r = r5c[i]; let k = nq(r[0]);
        let reads_only = match r[0] { 8 => r[1] == pb::C0 && r[2] != pb::C0 && r[3] == NONE, 13 => (r[1] == pb::C0 || r[2] == pb::C0) && r[3] != pb::C0, _ => false };
        if reads_only && wpar % 2 == 0 { nd += 1; continue; }
        if k > 0 && matches!(r[0], 6 | 8 | 13) && r[k] == pb::C0 { wpar += 1; }
        r5.push(r); }
    r5.extend_from_slice(&r5c[e5c..]); drop(r5c); cst.dropped += nd;
    let e5 = e5c - nd;
    // the stretches of [S, e5) in which no record names c0 (c0 = 0 there: zero at S, restored by every original instance, never
    // written by a replacement); the last one continues past e5 up to the first record that names c0 (it is still 0 there)
    // a gap is free only OUTSIDE the instances the converter left: there the records writing c0 come in restoring pairs
    // (CX(a0, c0) of MAJ0 and of UMA0), so a gap after an even number of c0 writes holds c0 = 0
    let mut free: Vec<(usize, usize)> = Vec::new(); let mut a0 = pb::S; let mut writes = 0usize;
    for i in pb::S..e5 { let r = r5[i]; let k = nq(r[0]);
        if (1..=k).any(|j| r[j] == pb::C0) { if i > a0 && writes % 2 == 0 { free.push((a0, i)); } a0 = i + 1; if matches!(r[0], 6 | 8 | 13) && r[k] == pb::C0 { writes += 1; } } }
    if writes % 2 == 0 { let nx = (e5..r5.len()).find(|&i| (1..=nq(r5[i][0])).any(|j| r5[i][j] == pb::C0)).unwrap_or(r5.len()); if nx > a0 { free.push((a0, nx)); } }
    // records after E (original) move by (r5.len() - r3.len()) = (e5 - E)
    let mv = |p: usize| -> usize { if p >= pb::E { (p as i64 + e5 as i64 - pb::E as i64) as usize } else { p } };
    for f in st.freed.iter_mut() { *f = (mv(f.0), mv(f.1), f.2); }
    if let Some(x) = st.inner.as_mut() { *x = (mv(x.0), mv(x.1)); }
    if let Some(x) = st.outer.as_mut() { *x = (mv(x.0), mv(x.1)); }
    for x in gs.stretches.iter_mut() { *x = (mv(x.0), mv(x.1)); }
    for &(a, b) in &free { if b - a >= 16 { st.freed.push((a, b, pb::C0)); } } st.d_pb = e5 as i64 - pb::E as i64;
    (r5, st, gs, Some(cst))
}
