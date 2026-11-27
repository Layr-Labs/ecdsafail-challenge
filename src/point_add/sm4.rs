//! sm4 (q631 agent sm, 2026-11-19; local research, NOT part of any package; nothing in the builder calls it): ITEM 4's ipark
//! seam (delta / bias / mark / mask of the inner park, after agent i4b's ipark Gtop window) with lane 258 free, on top of the
//! earlier ITEM 4 fixes (i4g ipark + unpark + winding, i4w R1, i4dwalk inner, i4ewalk outer).  Self-contained (no `super::`).
//!
//! THE FACT (E4).  Lane 258 = mg bit 128 = G1 := [g == 1], lane 259 = mg bit 127 (m127), lanes 2 / 257 / 620 = L[0..2] of the
//! g / |v| packed register, lane 617 = A bit 128 (agent i4's R1: nonzero only when g = 1).  g mg = M0 in [2^128, 2^129) and
//! |v| <= mg / 2 give (as ITEM 12's E2): g = 1 -> L1 = L2 = 0; g != 1 and m127 = 1 -> g in {2, 3} -> L1 = L2 = 0 (after Gtop
//! row 128).  The other team's ITEM 4 seam already uses part of this slack: right after the row-129 toggle it re-encodes
//! (L0, L1, L2, A128) with G1 as side information so that lane 2 is free for the park flag D:
//!     CX 2 257; CX 2 617; CX 2 620; CX 617 2; CCX 258 617 2; [CCX 257 258 40; CCX 40 620 2] x 2
//! (after it: G1 = 0 -> (617, 257, 620) = (L0, L1 ^ L0, L2 ^ L0), lane 2 = 0; G1 = 1 -> (617, 257, 620) = (A128, 0, 0)).
//! In that encoding a G1 = 0 state with m127 = 1 has 257 = 620 (= L0), so the codes m127 = 1, 257 != 620 are unused and hold
//! G1 = 1:  E4: if G1 then (259, 257, 620) := (1, m127, NOT m127);  G1 = 259 AND (257 XOR 620).
//! THE REWRITE (ipark seam only):
//!  * agent i4b's window decoder rev(E_A) + its parity X + the stream's row-129 toggle [X 258, CX 258 2] are replaced by T4
//!    (G1 = p0 AND s3 in the E_A form -> E4 codes, s3 cleared, rest of the E_A decoder) + the toggle with G1 decoded;
//!  * in the other team's encoding CCX 258 617 2 reads the decoded G1; the term [CCX 257 258 40; CCX 40 620 2] x 2 is
//!    dropped (with G1 decoded it is 257 AND 620 AND 259 AND (257 XOR 620) = 0 for every state);
//!  * inside the seam the 12 records that read 258 (all in D-controlled mark gadgets; D = 0 when g is odd) are dropped:
//!    lane 258 is 0 there (exact for G1 = 0; for G1 = 1 the gadget's net effect is nil, ARGUED + MEASURED non-interference);
//!  * the four HMR of the shift lanes (626..629) move from after the park's `move` to right after `mask` (their last use;
//!    exact: a measurement commutes with every record that does not name its lane, and no record in between reads a
//!    classical bit); E4 is decoded right after them (4 lanes free there).
type Row = [u16; 4];
const NONE: u16 = u16::MAX;

pub const ON: bool = false;
pub const G: u16 = 258;
pub const M127: u16 = 259;
pub const L1: u16 = 257;
pub const L2: u16 = 620;
pub const A128: u16 = 617;
pub const P0: u16 = 2;
pub const SH: [u16; 4] = [626, 628, 629, 627];
pub const W0: u16 = 1;
pub const V0: u16 = 621;
/// agent i4b's dirty lanes (V passengers, unnamed in the windows) for the E_A gates; mine for the E4 gates
pub const DIRTY: [u16; 8] = [506, 507, 508, 509, 510, 511, 513, 514];

#[inline] fn x(t: u16) -> Row { [6, t, NONE, NONE] }
#[inline] fn cx(c: u16, t: u16) -> Row { [8, c, t, NONE] }
#[inline] fn ccx(a: u16, b: u16, t: u16) -> Row { [13, a, b, t] }
#[inline] fn nq(k: u16) -> usize { match k { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }
#[inline] fn names(r: &Row, l: u16) -> bool { (1..=nq(r[0])).any(|j| r[j] == l) }
pub fn mcx(out: &mut Vec<Row>, ctl: &[(u16, bool)], t: u16, dirty: &[u16]) {
    for &(l, p) in ctl { if !p { out.push(x(l)); } }
    let c: Vec<u16> = ctl.iter().map(|z| z.0).collect();
    match c.len() {
        0 => out.push(x(t)), 1 => out.push(cx(c[0], t)), 2 => out.push(ccx(c[0], c[1], t)),
        u => { let v: Vec<u16> = dirty.iter().copied().filter(|d| !c.contains(d) && *d != t).take(u - 2).collect(); assert!(v.len() == u - 2, "sm4 mcx dirty");
            let a = ccx(c[0], c[1], v[0]); let m: Vec<Row> = (2..u - 1).map(|j| ccx(c[j], v[j - 2], v[j - 1])).collect(); let z = ccx(c[u - 1], v[u - 3], t);
            for _ in 0..2 { out.push(a); out.extend(m.iter()); out.push(z); out.extend(m.iter().rev()); } } }
    for &(l, p) in ctl { if !p { out.push(x(l)); } }
}
fn snz(o: &mut Vec<Row>, extra: &[(u16, bool)], t: u16) {
    let (s0, s1, s2) = (SH[0], SH[1], SH[2]); let d = &DIRTY[..];
    let mut c = extra.to_vec(); c.push((s0, true)); mcx(o, &c, t, d);
    let mut c = extra.to_vec(); c.push((s0, false)); c.push((s1, true)); mcx(o, &c, t, d);
    let mut c = extra.to_vec(); c.push((s0, false)); c.push((s1, false)); c.push((s2, true)); mcx(o, &c, t, d);
}
/// agent i4b's E_A (i4g::enc_a), byte for byte
pub fn enc_a() -> Vec<Row> {
    let mut o = Vec::new(); let d = &DIRTY[..];
    let (s0, s1, s2, s3) = (SH[0], SH[1], SH[2], SH[3]);
    mcx(&mut o, &[(P0, true), (s3, true)], V0, d);
    mcx(&mut o, &[(P0, true), (s3, true), (s0, false), (s1, false), (s2, false)], V0, d);
    mcx(&mut o, &[(P0, true), (s3, true)], W0, d);
    mcx(&mut o, &[(P0, true), (s3, true), (s1, false), (s2, false), (W0, false), (V0, true)], s0, d);
    snz(&mut o, &[(P0, true), (W0, false)], s3);
    o.push(ccx(P0, G, s3)); o.push(ccx(P0, s3, G));
    o
}
/// t ^= (extra controls) AND G1, G1 decoded from E4: 259 AND (257 XOR 620)
fn with_g1(o: &mut Vec<Row>, extra: &[(u16, bool)], t: u16) {
    o.push(cx(L1, L2)); let mut c = extra.to_vec(); c.push((M127, true)); c.push((L2, true)); mcx(o, &c, t, &DIRTY); o.push(cx(L1, L2));
}
/// T4: E_A-encoded (pre-toggle, lane 258 = 0, G1 = p0 AND s3) -> plain (sh, w0, v0) + E4-pre codes; never names 258
pub fn t4() -> Vec<Row> {
    let s3 = SH[3]; let d = &DIRTY[..]; let mut o = Vec::new();
    mcx(&mut o, &[(P0, true), (s3, true), (M127, true)], L1, d);      // 257 ^= G1 AND m127
    mcx(&mut o, &[(P0, true), (s3, true), (M127, false)], L2, d);     // 620 ^= G1 AND NOT m127
    mcx(&mut o, &[(P0, true), (s3, true), (L2, true)], M127, d);      // 259 ^= G1 AND 620  (-> 1 when G1)
    with_g1(&mut o, &[(P0, true)], s3);                                // s3 ^= p0 AND G1: s3 = 0 when g is odd
    let ea = enc_a(); o.extend(ea[..ea.len() - 2].iter().rev());      // rest of the E_A decoder
    o
}
/// the row-129 toggle CX 258 2 with G1 decoded
pub fn toggle4() -> Vec<Row> { let mut o = Vec::new(); with_g1(&mut o, &[], P0); o }
/// E4 decoder (after the other team's encoding; writes 258 = G1, restores (259, 257, 620) to (m127, 0, 0) when G1)
pub fn dec4() -> Vec<Row> { let mut o = Vec::new(); with_g1(&mut o, &[], G); o.push(ccx(G, L2, M127)); o.push(x(M127)); o.push(ccx(G, M127, L2)); o.push(x(M127)); o.push(ccx(G, M127, L1)); o }
pub fn enc4() -> Vec<Row> { let mut v = dec4(); v.reverse(); v }

// ---------------------------------------------------------------------------------------------------- winding end (E5)
pub const MG0: u16 = 256;
pub const MG1: u16 = 623;
/// agent i4b's winding encoder E_G (i4g::enc), byte for byte
pub fn enc_g() -> Vec<Row> {
    let mut o = Vec::new(); let d = &DIRTY[..];
    let (s0, s1, s2, s3) = (SH[0], SH[1], SH[2], SH[3]);
    mcx(&mut o, &[(P0, true), (s3, true), (s0, false), (s1, false), (s2, false)], MG1, d);
    mcx(&mut o, &[(P0, true), (s3, true), (MG1, true)], s1, d);
    mcx(&mut o, &[(P0, true), (s3, true), (MG1, false)], MG0, d);
    mcx(&mut o, &[(P0, true), (MG0, true), (s0, true)], s3, d);
    mcx(&mut o, &[(P0, true), (MG0, true), (s0, false), (s1, true)], s3, d);
    mcx(&mut o, &[(P0, true), (MG0, true), (s0, false), (s1, false), (s2, true)], s3, d);
    mcx(&mut o, &[(P0, true), (MG0, false), (MG1, true), (s0, false), (s1, true), (s2, false)], s3, d);
    o.push(ccx(P0, G, s3)); o.push(ccx(P0, s3, G));
    o
}
/// E5 (state after the winding: L holds the full g): g = 1 -> L1 = L2 = 0; g != 1 and m127 = 1 -> g in {2, 3} -> L2 = 0.
/// Code: if G1 then (259, 257, 620) := (1, m127, 1); G1 = 259 AND 620.  T5 = E_G-encoded (G1 = p0 AND s3) -> plain + E5 codes
/// (never names 258); dec5 writes G1 back into 258 once the shift lanes are measured out.
pub fn t5() -> Vec<Row> {
    let s3 = SH[3]; let d = &DIRTY[..]; let mut o = Vec::new();
    mcx(&mut o, &[(P0, true), (s3, true), (M127, true)], L1, d);       // 257 ^= G1 AND m127
    o.push(ccx(P0, s3, L2));                                          // 620 ^= G1
    mcx(&mut o, &[(P0, true), (s3, true), (L1, false)], M127, d);      // 259 ^= G1 AND NOT 257 (-> 1 when G1)
    mcx(&mut o, &[(P0, true), (M127, true), (L2, true)], s3, d);       // s3 ^= p0 AND G1: s3 = 0 when g is odd
    let eg = enc_g(); o.extend(eg[..eg.len() - 2].iter().rev());       // rest of the E_G decoder
    o
}
pub fn dec5() -> Vec<Row> { vec![ccx(M127, L2, G), x(L1), ccx(G, L1, M127), x(L1), cx(G, L2), ccx(G, M127, L1)] }

#[derive(Default, Debug, Clone)]
pub struct Stats { pub edits: Vec<(usize, usize, usize)>, pub stretch: Option<(usize, usize)>, pub dropped_reads: usize, pub moved_hmr: usize,
    /// winding end: (input position of the E_G decoder, input position of dec5)
    pub wind: Option<(usize, usize)> }
impl Stats {
    pub fn map(&self, p: usize) -> usize { let mut d: i64 = 0; for &(at, rm, ins) in &self.edits { if at + rm <= p { d += ins as i64 - rm as i64; } else if at < p { panic!("sm4 map: position {} inside an edit at {}", p, at); } } (p as i64 + d) as usize }
}
/// the other team's lane-2 encoding (9 records), as it stands after the toggle and the first delta records
pub fn their_enc() -> Vec<Row> { vec![cx(P0, L1), cx(P0, A128), cx(P0, L2), cx(A128, P0), ccx(G, A128, P0), ccx(L1, G, 40), ccx(40, L2, P0), ccx(L1, G, 40), ccx(40, L2, P0)] }

/// rows = ITEM 4 with every earlier fix (any order of the walk splices; located by content).  Returns new rows + stats; the
/// lane-258 stretch (output coordinates) runs from agent i4b's ipark window start to the E4 decoder after the moved HMR.
#[derive(Clone, Copy, Debug)]
pub struct Sel { pub ipark: bool, pub wind: bool }
pub const SEL: Sel = Sel { ipark: true, wind: true };
pub fn rewrite(rows: &[Row], ipark_window: (usize, usize)) -> (Vec<Row>, Stats) { rewrite_sel(rows, ipark_window, None, Sel { ipark: true, wind: false }) }
/// unpark_window = agent i4b's unpark Gtop + winding window (input coordinates), needed when sel.wind
pub fn rewrite_sel(rows: &[Row], ipark_window: (usize, usize), unpark_window: Option<(usize, usize)>, sel: Sel) -> (Vec<Row>, Stats) {
    let mut st = Stats::default();
    let mut ed: Vec<(usize, usize, Vec<Row>)> = Vec::new();
    if sel.wind {
        let (_us, ue) = unpark_window.expect("sm4: the winding window");
        let mut dg = enc_g(); dg.reverse();
        assert!(rows[ue..ue + dg.len()] == dg[..], "sm4: winding decoder not at the window end");
        let d1 = ue + dg.len();
        // parkOuter CX's then the five HMR (626, 628, 629, 627, 627)
        let h = (d1..d1 + 64).find(|&i| rows[i][0] == 12 && rows[i][1] == SH[0]).expect("sm4: outer park HMR");
        assert!(rows[h + 1][0] == 12 && rows[h + 1][1] == SH[1] && rows[h + 2][0] == 12 && rows[h + 2][1] == SH[2] && rows[h + 3][0] == 12 && rows[h + 3][1] == SH[3] && rows[h + 4][0] == 12 && rows[h + 4][1] == SH[3], "sm4: outer park HMR block");
        for i in d1..h + 5 { for &l in &[G, M127, L1, L2] { assert!(!names(&rows[i], l), "sm4: record {} names lane {} between the winding decoder and the outer park HMR", i, l); } }
        ed.push((ue, dg.len(), t5())); ed.push((h + 5, 0, dec5()));
        st.wind = Some((ue, h + 5));
    }
    if !sel.ipark {
        ed.sort_by_key(|e| e.0);
        let mut out: Vec<Row> = Vec::with_capacity(rows.len() + 1000); let mut q = 0usize;
        for (at, rm, ins) in &ed { out.extend_from_slice(&rows[q..*at]); out.extend_from_slice(ins); q = at + rm; st.edits.push((*at, *rm, ins.len())); }
        out.extend_from_slice(&rows[q..]);
        return (out, st);
    }
    let (ws, we) = ipark_window;
    let mut dec = enc_a(); dec.reverse();
    assert!(rows[we..we + dec.len()] == dec[..], "sm4: ipark window decoder not at the window end");
    let mut p = we + dec.len(); let mut nx = 0; while rows[p] == x(G) { nx += 1; p += 1; }
    assert!(nx % 2 == 0 && rows[p] == cx(G, P0), "sm4: row-129 toggle not after the decoder");
    let tog = p;
    // the other team's encoding within the next 64 records
    let te = their_enc();
    let e0 = (tog + 1..tog + 64).find(|&i| rows[i..i + te.len()] == te[..]).expect("sm4: the other team's lane-2 encoding");
    for i in tog + 1..e0 { assert!(!names(&rows[i], G) && !names(&rows[i], P0) && !names(&rows[i], L1) && !names(&rows[i], L2) && !names(&rows[i], A128) && !names(&rows[i], M127), "sm4: record {} between the toggle and the encoding", i); }
    // mask = the last record naming a shift lane before the HMR block; HMR block = HMR 626, 4 CX on (2, 626), HMR 627, 628, 629
    let hb = (e0..e0 + 400_000).find(|&i| rows[i][0] == 12 && rows[i][1] == SH[0] && rows[i + 1] == cx(P0, SH[0]) && rows[i + 5][0] == 12 && rows[i + 5][1] == SH[3] && rows[i + 6][0] == 12 && rows[i + 6][1] == SH[1] && rows[i + 7][0] == 12 && rows[i + 7][1] == SH[2]).expect("sm4: shift-lane HMR block");
    let mk = (e0..hb).rev().find(|&i| SH.iter().any(|&l| names(&rows[i], l))).unwrap();
    let mut me = mk + 1; while rows[me] == x(P0) { me += 1; }   // the mask's closing X frame on lane 2
    for i in me..hb { let r = rows[i]; assert!(!SH.iter().any(|&l| names(&r, l)), "sm4: record {} names a shift lane before the HMR", i);
        assert!(matches!(r[0], 6 | 8 | 13) && (r[0] != 6 || r[2] == NONE) && (r[0] != 8 || r[3] == NONE), "sm4: record {} is conditioned / not a plain gate", i); }
    // edits
    let mut a = t4(); a.extend(toggle4()); ed.push((we, tog + 1 - we, a));
    let mut b = vec![cx(P0, L1), cx(P0, A128), cx(P0, L2), cx(A128, P0)]; with_g1(&mut b, &[(A128, true)], P0); ed.push((e0, te.len(), b));
    // the seam: drop records reading 258 (X parity on 258 must stay 0: asserted), assert no write of 258 / 259
    for i in e0 + te.len()..me { let r = rows[i]; let k = nq(r[0]);
        if r[0] == 6 && r[1] == G { panic!("sm4: X 258 inside the seam at {}", i); }
        if k > 0 && matches!(r[0], 8 | 13) && (r[k] == G || r[k] == M127) { panic!("sm4: record {} writes 258 / 259 inside the seam", i); }
        if names(&r, G) { assert!(r[0] == 13 || r[0] == 8, "sm4: record {} reads 258 as {:?}", i, r); ed.push((i, 1, vec![])); st.dropped_reads += 1; } }
    let h: Vec<Row> = vec![rows[hb], rows[hb + 5], rows[hb + 6], rows[hb + 7]];
    let mut ins = h.clone(); ins.extend(dec4()); ed.push((me, 0, ins));
    ed.push((hb, 1, vec![])); ed.push((hb + 5, 3, vec![])); st.moved_hmr = 4;
    ed.sort_by_key(|e| e.0);
    let mut out: Vec<Row> = Vec::with_capacity(rows.len() + 1000); let mut q = 0usize;
    for (at, rm, ins) in &ed { assert!(*at >= q, "sm4: overlapping edits"); out.extend_from_slice(&rows[q..*at]); out.extend_from_slice(ins); q = at + rm; st.edits.push((*at, *rm, ins.len())); }
    out.extend_from_slice(&rows[q..]);
    let s = st.map(ws); let e = st.map(me) - dec4().len();
    assert!(!out[s..e].iter().any(|r| names(r, G)), "sm4: lane 258 named inside its stretch");
    st.stretch = Some((s, e));
    (out, st)
}
