//! i4g (q631 agent i4b, 2026-11-19; local research, NOT part of any package; switch ON = false): ITEM 4 (segment 8, the
//! guest-carrying 129-bit divide Y <- Y R^-1 mod p) in one lane fewer across the winding ("G rows", w <- g * w, item offsets
//! [73_177_175, 86_151_432) of the census list) and both Gtop stages (ipark [37_983_234, 40_906_761), unpark
//! [70_262_581, 73_177_175)), by exact gadget-level rewrites that free lane 258.  Entry point rewrite_sel(rows, Sel{..});
//! Stats.stretches = the freed stretches in rewritten coordinates.  Composes with i4w (R1): apply this module to the ORIGINAL
//! item rows first (it only touches offsets >= 37_983_234), then i4w::rewrite.  The Gtop windows use the encoder E_A (stash in
//! sh, w bit 0 = lane 1, |v| bit 0 = lane 621: g odd and sh >= 1 => mg even => both are 1); the unpark window hands over to
//! the winding's encoder E_G through the transcoder T at 73_177_175 (lane 258 stays zero), and moves the unpark Gtop's row-129
//! toggle (CX 258 -> 2, offset 73_177_174) to the window start.  The section below describes the winding window.
//!
//! Roles in the G rows (MEASURED on the stream, see ~/Projects/ecdsafail/q631/i4b/summary.py): w = k/g -> k (129 lanes),
//! mg = M0/g bit-reversed in (256, 623, 384..258) (read-only: row predicates "bitlen(mg) = t"), g / |v| packed (lanes 2, 257,
//! 620, 3..128, 618, 621; g from lane 2 up), q (dirty ladders), V (lane 504 = dirty flag host), sh (626, 628, 629, 627: idle).
//! Lane 258 = mg bit 128 = G1 := [g == 1] (g mg = M0 in [2^128, 2^129)); it is read by every row (131,300 CCX controls) and
//! written only by two X (offsets 73_177_430 and 86_149_231).
//!
//! The rewrite frees lane 258 on the whole stretch:
//!   * g even  -> G1 = 0: lane 258 is already zero.
//!   * g odd   -> v2(mg) = v2(M0) >= sh (M0 = R << sh), so (sh, mg bit 0, mg bit 1) takes 20 of 64 patterns and fits in 5 lanes;
//!     the encoder E (all gates controlled by p0 = lane 2 = g bit 0) compresses it into (626, 628, 629, 256, 623), moves G1
//!     into lane 627 (sh bit 3) and clears lane 258.  Decoded G1 = p0 AND lane 627 on every valid input.
//!   * every CCX that reads lane 258 is replaced by the same gate with the decoded control (one CX when the stream holds
//!     not-G1 there, plus a 3-control gate on (2, 627, other control) with dirty lane 506: 4 CCX); the two X on 258 are dropped.
//!   * rows 1 and 2 read mg bits 0 and 1 (predicates of bitlen(mg) <= 2); the encoder changes those lanes only on inputs with
//!     sh >= 8, where v2(mg) >= 8 makes mg >= 256 and both predicates false anyway.
//!   * the decoder (E reversed) runs before the parkOuter record 86_151_432; the encoded lanes are unchanged in between
//!     (626..629 unnamed, 256 / 623 read-only with paired X, lane 2 read-only with paired X).
type Row = [u16; 4];
const NONE: u16 = u16::MAX;
/// builder switch (no builder code reads it yet; see summary.py for the hook)
pub const ON: bool = false;
/// first record of the G rows / first record after them (item offsets of the census list)
pub const G_START: usize = 73_177_175;
pub const G_END: usize = 86_151_432;
pub const FREED: u16 = 258;
const P0: u16 = 2;          // g bit 0
const SH: [u16; 4] = [626, 628, 629, 627];
const MG0: u16 = 256;
const MG1: u16 = 623;
const W: u16 = 506;         // dirty lane of the 3-control replacements (V passenger, unnamed in the G rows)
const DIRTY: [u16; 8] = [506, 507, 508, 509, 510, 511, 513, 514];   // dirty lanes of the encoders' multi-controlled gates (V passengers, unnamed in both windows)
#[inline] fn x(t: u16) -> Row { [6, t, NONE, NONE] }
#[inline] fn cx(c: u16, t: u16) -> Row { [8, c, t, NONE] }
#[inline] fn ccx(a: u16, b: u16, t: u16) -> Row { [13, a, b, t] }
/// t ^= AND of controls (lane, polarity); Barenco ladder on dirty lanes (as the published MCX), negated controls by X wrap
pub fn mcx(out: &mut Vec<Row>, ctl: &[(u16, bool)], t: u16, dirty: &[u16]) {
    for &(l, p) in ctl { if !p { out.push(x(l)); } }
    let c: Vec<u16> = ctl.iter().map(|z| z.0).collect();
    match c.len() {
        0 => out.push(x(t)), 1 => out.push(cx(c[0], t)), 2 => out.push(ccx(c[0], c[1], t)),
        u => { let v: Vec<u16> = dirty.iter().copied().filter(|d| !c.contains(d) && *d != t).take(u - 2).collect(); assert!(v.len() == u - 2, "mcx dirty");
            let a = ccx(c[0], c[1], v[0]); let m: Vec<Row> = (2..u - 1).map(|j| ccx(c[j], v[j - 2], v[j - 1])).collect(); let z = ccx(c[u - 1], v[u - 3], t);
            for _ in 0..2 { out.push(a); out.extend(m.iter()); out.push(z); out.extend(m.iter().rev()); } } }
    for &(l, p) in ctl { if !p { out.push(x(l)); } }
}
/// t ^= extra AND (sh0 | sh1 | sh2) as three disjoint cubes
fn snz(o: &mut Vec<Row>, extra: &[(u16, bool)], t: u16) {
    let (s0, s1, s2) = (SH[0], SH[1], SH[2]); let d = &DIRTY[..];
    let mut c = extra.to_vec(); c.push((s0, true)); mcx(o, &c, t, d);
    let mut c = extra.to_vec(); c.push((s0, false)); c.push((s1, true)); mcx(o, &c, t, d);
    let mut c = extra.to_vec(); c.push((s0, false)); c.push((s1, false)); c.push((s2, true)); mcx(o, &c, t, d);
}
/// the winding encoder E_G (self-inverse gates; the decoder is the same list reversed); verified exhaustively on its 212 valid
/// lane configurations by ~/Projects/ecdsafail/q631/i4b/py/encverify.py
pub fn enc() -> Vec<Row> {
    let mut o = Vec::new(); let d = &DIRTY[..];
    let (s0, s1, s2, s3) = (SH[0], SH[1], SH[2], SH[3]);
    // E1-E3 (g odd, sh >= 8, valid => mg bits 0, 1 = 0): j = sh - 8; j = 0 -> (sh0..2, mg0, mg1) = (2, 0, 1); j >= 1 -> (j, 1, 0)
    mcx(&mut o, &[(P0, true), (s3, true), (s0, false), (s1, false), (s2, false)], MG1, d);
    mcx(&mut o, &[(P0, true), (s3, true), (MG1, true)], s1, d);
    mcx(&mut o, &[(P0, true), (s3, true), (MG1, false)], MG0, d);
    // E4: clear lane 627 (= sh bit 3) for g odd: indicator of the images of sh >= 8 (disjoint cubes)
    mcx(&mut o, &[(P0, true), (MG0, true), (s0, true)], s3, d);
    mcx(&mut o, &[(P0, true), (MG0, true), (s0, false), (s1, true)], s3, d);
    mcx(&mut o, &[(P0, true), (MG0, true), (s0, false), (s1, false), (s2, true)], s3, d);
    mcx(&mut o, &[(P0, true), (MG0, false), (MG1, true), (s0, false), (s1, true), (s2, false)], s3, d);
    // E5, E6: lane 627 <- G1 (g odd), lane 258 <- 0
    o.push(ccx(P0, FREED, s3));
    o.push(ccx(P0, s3, FREED));
    o
}
/// lanes of the unpark-Gtop stash: w bit 0 (k/g, odd when mg is even) and |v| bit 0 (odd when mg is even)
const W0: u16 = 1;
const V0: u16 = 621;
/// the unpark-Gtop encoder E_A (g odd: sh >= 1 => mg even => w0 = v0 = 1; stash sh bit 3 into (sh0..2, w0, v0), G1 into 627)
pub fn enc_a() -> Vec<Row> {
    let mut o = Vec::new(); let d = &DIRTY[..];
    let (s0, s1, s2, s3) = (SH[0], SH[1], SH[2], SH[3]);
    mcx(&mut o, &[(P0, true), (s3, true)], V0, d);
    mcx(&mut o, &[(P0, true), (s3, true), (s0, false), (s1, false), (s2, false)], V0, d);   // v0 flipped iff sh0..2 != 0
    mcx(&mut o, &[(P0, true), (s3, true)], W0, d);                                          // w0 -> 0
    mcx(&mut o, &[(P0, true), (s3, true), (s1, false), (s2, false), (W0, false), (V0, true)], s0, d);  // sh = 8 -> (1, 0, 1)
    snz(&mut o, &[(P0, true), (W0, false)], s3);                                            // clear sh bit 3
    o.push(ccx(P0, FREED, s3));
    o.push(ccx(P0, s3, FREED));
    o
}
/// transcoder E_A-encoded -> E_G-encoded (lane 258 stays zero; lane 627 = G1 for g odd in both)
pub fn trans() -> Vec<Row> {
    let mut o = Vec::new(); let d = &DIRTY[..];
    let (s0, s1, s2) = (SH[0], SH[1], SH[2]);
    snz(&mut o, &[(P0, true), (W0, false), (V0, false)], MG0);
    snz(&mut o, &[(P0, true), (MG0, true)], V0);
    snz(&mut o, &[(P0, true), (MG0, true)], W0);
    mcx(&mut o, &[(P0, true), (s0, true), (s1, false), (s2, false), (W0, false), (V0, true), (MG0, false)], MG1, d);
    mcx(&mut o, &[(P0, true), (s0, true), (s2, false), (W0, false), (V0, true), (MG1, true), (MG0, false)], s1, d);
    mcx(&mut o, &[(P0, true), (s1, true), (s2, false), (W0, false), (V0, true), (MG1, true), (MG0, false)], s0, d);
    mcx(&mut o, &[(P0, true), (s0, false), (s1, true), (s2, false), (V0, true), (MG1, true), (MG0, false)], W0, d);
    o
}
/// unpark-Gtop window: first record after the last use of the shift lanes; the row-129 toggle (X 258, CX 258 -> 2) at its end
pub const GT_START: usize = 70_262_581;
const GT_X: usize = 73_177_173;
const GT_CX: usize = 73_177_174;
#[inline] fn nq(k: u16) -> usize { match k { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }
/// statistics of the rewrite
#[derive(Default, Debug)]
pub struct Stats { pub replaced: usize, pub neg: usize, pub flipped_p0: usize, pub dropped_x: usize, pub added_records: i64, pub added_ccx: i64,
    /// freed stretches in rewritten coordinates (after the encoder, before the decoder)
    pub stretches: Vec<(usize, usize)> }
/// replace one record that reads lane 258 (stream value G1 xor par258) by its decoded form (G1 = p0 AND lane 627)
fn patch(out: &mut Vec<Row>, r: Row, i: usize, par258: u8, par2: u8, st: &mut Stats) {
    let k = r[0];
    if k == 8 {                                    // t ^= B = par258 (+) p0 c
        let t = r[2]; assert!(t != SH[3] && t != P0 && t != FREED, "i4g: record {} {:?}", i, r);
        if par258 == 1 { out.push(x(t)); st.neg += 1; }
        if par2 == 1 { out.push(x(P0)); st.flipped_p0 += 1; }
        out.push(ccx(P0, SH[3], t));
        if par2 == 1 { out.push(x(P0)); }
        st.replaced += 1; return;
    }
    let a = if r[1] == FREED { r[2] } else { r[1] }; let t = r[3];
    assert!(a != SH[3] && t != SH[3] && t != P0 && t != FREED, "i4g: record {} overlaps the decode lanes", i);
    // t ^= A B with B = G1 xor par258, G1 = p0 AND c (c = lane 627), lane 2 = p0 xor par2:  t ^= A par258 (+) A p0 c
    if par258 == 1 { out.push(cx(a, t)); st.neg += 1; }
    if a == P0 { if par2 == 0 { out.push(ccx(P0, SH[3], t)); } }   // A p0 = p0 if par2 == 0, else 0
    else {
        if par2 == 1 { out.push(x(P0)); st.flipped_p0 += 1; }
        out.push(ccx(P0, SH[3], W)); out.push(ccx(W, a, t)); out.push(ccx(P0, SH[3], W)); out.push(ccx(W, a, t));
        if par2 == 1 { out.push(x(P0)); }
    }
    st.replaced += 1;
}
/// ipark-Gtop window (forward Gtop of the inner park, rows 1..129; lane 2 = g0 throughout; the row-129 toggle X 258 /
/// CX 258 -> 2 at 40_906_761 / 40_906_762 stays after the window): first record after the alpha's last use of lane 258
pub const IP_START: usize = 37_983_234;
pub const IP_END: usize = 40_906_761;
/// one window: records [s, e) with lane 258 freed; `pre` emitted before the encoder; `skip` offsets dropped (moved records);
/// optional transcoder inserted before offset `tr_at` (lane-258 parity must be 0 there); decoder `dec` after the window, then an
/// X on 258 when the stream holds not-G1 there
struct Win { s: usize, e: usize, pre: Vec<Row>, enc: Vec<Row>, skip: Vec<usize>, tr_at: Option<(usize, Vec<Row>)>, dec: Vec<Row>, stash: Vec<u16> }
fn window(out: &mut Vec<Row>, rows: &[Row], w: &Win, st: &mut Stats) {
    out.extend_from_slice(&w.pre); out.extend_from_slice(&w.enc); let s0 = out.len();
    let (mut par258, mut par2) = (0u8, 0u8);
    for i in w.s..w.e {
        if let Some((at, tr)) = &w.tr_at { if i == *at { assert!(par258 == 0 && par2 == 0, "i4g: parity at the transcoder"); out.extend_from_slice(tr); } }
        if w.skip.contains(&i) { continue; }
        let r = rows[i]; let k = r[0]; let n = nq(k);
        assert!(matches!(k, 6 | 8 | 13), "i4g: record {} kind {} in the window", i, k);
        if k == 6 { assert!(r[2] == NONE); } if k == 8 { assert!(r[3] == NONE); }
        let stash_live = w.tr_at.as_ref().map_or(true, |(at, _)| i < *at);
        for j in 1..=n { let l = r[j]; assert!(!DIRTY.contains(&l), "i4g: record {} names a dirty lane", i);
            assert!(!SH.contains(&l), "i4g: record {} names a shift lane", i);
            if stash_live { assert!(!w.stash.contains(&l), "i4g: record {} names a stash lane", i); } }
        if k == 6 && r[1] == FREED { par258 ^= 1; st.dropped_x += 1; continue; }
        if k == 6 && r[1] == P0 { par2 ^= 1; out.push(r); continue; }
        assert!(!(n >= 1 && r[n] == FREED), "i4g: record {} writes lane 258", i);
        assert!(!(n >= 1 && r[n] == P0), "i4g: record {} writes lane 2", i);
        let uses = (1..n).filter(|&j| r[j] == FREED).count();
        if uses == 0 { out.push(r); continue; }
        assert!(uses == 1 && (k == 13 || k == 8), "i4g: record {} reads lane 258 as {:?}", i, r);
        patch(out, r, i, par258, par2, st);
    }
    assert!(par2 == 0, "i4g: unbalanced X parity on lane 2 over the window");
    st.stretches.push((s0, out.len()));
    out.extend_from_slice(&w.dec);
    if par258 == 1 { out.push(x(FREED)); }
}
/// which windows to rewrite
#[derive(Clone, Copy, Debug)]
pub struct Sel { pub ipark: bool, pub unpark: bool, pub winding: bool }
/// ITEM 4 rows (census list, item offsets) -> rewritten rows (windows in offset order; disjoint from R1 = i4w's [13.05M, 37.29M));
/// asserts the structural preconditions of every window
pub fn rewrite_sel(rows: &[Row], sel: Sel) -> (Vec<Row>, Stats) {
    assert!(rows.len() > G_END);
    let mut st = Stats::default();
    let mut wins: Vec<Win> = Vec::new();
    let rev = |mut v: Vec<Row>| { v.reverse(); v };
    if sel.ipark {
        assert!(rows[IP_END] == x(FREED) && rows[IP_END + 1] == cx(FREED, P0), "i4g: ipark row-129 toggle not where expected");
        wins.push(Win { s: IP_START, e: IP_END, pre: vec![], enc: enc_a(), skip: vec![], tr_at: None, dec: rev(enc_a()), stash: vec![W0, V0] });
    }
    if sel.unpark {
        assert!(sel.winding, "i4g: the unpark window hands over to the winding window");
        assert!(rows[GT_X] == x(FREED) && rows[GT_CX] == cx(FREED, P0), "i4g: unpark row-129 toggle not where expected");
        // lane 2 = g0 from the window start: the row-129 toggle moved there (the stream holds G1 on 258, positive, here)
        wins.push(Win { s: GT_START, e: G_END, pre: vec![cx(FREED, P0)], enc: enc_a(), skip: vec![GT_CX], tr_at: Some((G_START, trans())), dec: rev(enc()), stash: vec![W0, V0] });
    } else if sel.winding {
        wins.push(Win { s: G_START, e: G_END, pre: vec![], enc: enc(), skip: vec![], tr_at: None, dec: rev(enc()), stash: vec![] });
    }
    let mut out: Vec<Row> = Vec::with_capacity(rows.len() + 1_200_000);
    let mut p = 0usize;
    for w in &wins { out.extend_from_slice(&rows[p..w.s]); window(&mut out, rows, w, &mut st); p = w.e; }
    out.extend_from_slice(&rows[p..]);
    st.added_records = out.len() as i64 - rows.len() as i64;
    let cc = |v: &[Row]| v.iter().filter(|r| r[0] == 13).count() as i64;
    st.added_ccx = cc(&out) - cc(rows);
    (out, st)
}
/// the winding (+ optionally the unpark Gtop) only
pub fn rewrite_x(rows: &[Row], with_gtop: bool) -> (Vec<Row>, Stats) { rewrite_sel(rows, Sel { ipark: false, unpark: with_gtop, winding: true }) }
pub fn rewrite(rows: &[Row]) -> (Vec<Row>, Stats) { rewrite_x(rows, false) }
