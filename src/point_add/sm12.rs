//! sm12 (q631 agent sm, 2026-11-19; local research, NOT part of any package; nothing in the builder calls it): ITEM 12's two
//! park seams (the ipark seam after the ipark Gtop window and the unpark head before the unpark Gtop window) with lane 258 free,
//! on top of agent i12's rewrite (i12w::rewrite_full with every switch on).  Self-contained (no `super::` use) so that local
//! tools can include it by path.
//!
//! THE FACT (E2).  Lane 258 = mg bit 126 = G1 := [g == 1], lane 259 = mg bit 125 (m125), lanes 257 / 241 = L[1] / L[2] of the
//! g / |v| packed register (g from L[0] = 513 up, |v| from L[n + 1] down).  g mg = M0 in [2^126, 2^127) and |v| <= mg / 2, so:
//!   (F1) g = 1:                    mg >= 2^126, |v| < 2^126 reaches at most L[3]; g' (g after the Gtop toggles) = 0
//!                                  -> L[1] = L[2] = 0;
//!   (F2) g != 1 and m125 = 1:      mg in [2^125, 2^126) -> g in {2, 3} -> g' = g - 2 in {0, 1}; |v| < 2^125 -> L[1] = 0.
//! These hold from Gtop row 126 of the ipark Gtop (which clears g's bit 1 for g in {2, 3}) to the park's `move` (which puts the
//! park flag D into L[n - bitlen(mg)] = L[1] when bitlen(mg) = 126), and again from the unpark's `move` to row 126 of the
//! unpark Gtop.  The park's `mark` writes L[1] / L[2] only through D-controlled gates; D = [v2(mg) < sh] = 0 when g is odd
//! (v2(mg) = v2(M0) >= sh), so (F1), (F2) survive it.  Hence (G1, m125, L1, L2) takes 7 values and the 3 lanes (259, 257, 241)
//! hold G1 too:  E2: if G1 then (m125, L1, L2) := (1, 1, m125); decode G1 = m125' AND L1'.
//!   enc2 (from lane 258):  CCX(258, 259, 241); CX(258, 257); X(241) CCX(258, 241, 259) X(241); CCX(259, 257, 258).
//! While E2 is active the encoded lanes may be read only where the read cannot matter for a G1 = 1 shot: every read of
//! 257 / 241 / 259 in the two seams is a control inside a park / unpark gadget that is also controlled by D (bias, mark, the
//! first part of extract), and D = 0 on every G1 = 1 shot (g = 1 is odd).  (ARGUED from the generator's parkInner; MEASURED by
//! the paired replays and the non-interference replays of the sm tools.)
//!
//! THE REWRITE.
//!  ipark: agent i12's window decoder rev(E_A) + [X 258] + the stream's row-127 toggle [X 258, CX 258 513] are replaced by
//!    T_ip (E_A -> E2 transcoder that never names 258: G1 = p0 AND s3 in the E_A form) + CCX(259, 257, 513) (the toggle with
//!    G1 decoded from E2); E2 is decoded (rev enc2, writes 258) right after the four HMR of the shift lanes, where 4 lanes are free.
//!  unpark: enc2 right after the unpark's `move` (the last record naming 258 before the window; the shift lanes are still
//!    zero there); agent i12's window head [CX 258 513] + E_A(SH_C) is replaced by CCX(259, 257, 513) + T_up (= T_ip^-1 on
//!    SH_C).
//!  Lane 258 is then zero and unnamed from agent i12's ipark window start to the E2 decoder after the HMR, and from enc2 after
//!  the unpark's move to the end of agent i12's unpark window.
type Row = [u16; 4];
const NONE: u16 = u16::MAX;

pub const ON: bool = false;
pub const G: u16 = 258;
pub const M125: u16 = 259;
pub const L1: u16 = 257;
pub const L2: u16 = 241;
pub const P0: u16 = 513;
pub const SH_B: [u16; 4] = [243, 244, 245, 246];
pub const SH_C: [u16; 4] = [243, 114, 245, 246];
pub const W0: u16 = 507;
pub const V0: u16 = 248;
pub const DIRTY: [u16; 8] = [41, 42, 43, 44, 45, 46, 47, 48];

#[inline] fn x(t: u16) -> Row { [6, t, NONE, NONE] }
#[inline] fn cx(c: u16, t: u16) -> Row { [8, c, t, NONE] }
#[inline] fn ccx(a: u16, b: u16, t: u16) -> Row { [13, a, b, t] }
#[inline] fn nq(k: u16) -> usize { match k { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }
#[inline] fn names(r: &Row, l: u16) -> bool { (1..=nq(r[0])).any(|j| r[j] == l) }
/// multi-controlled X with polarities (agent i12's g1::mcx, copied): dirty-lane ladder, 4 (u - 2) CCX for u >= 3 controls
pub fn mcx(out: &mut Vec<Row>, ctl: &[(u16, bool)], t: u16, dirty: &[u16]) {
    for &(l, p) in ctl { if !p { out.push(x(l)); } }
    let c: Vec<u16> = ctl.iter().map(|z| z.0).collect();
    match c.len() {
        0 => out.push(x(t)), 1 => out.push(cx(c[0], t)), 2 => out.push(ccx(c[0], c[1], t)),
        u => { let v: Vec<u16> = dirty.iter().copied().filter(|d| !c.contains(d) && *d != t).take(u - 2).collect(); assert!(v.len() == u - 2, "sm12 mcx dirty");
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
/// agent i12's E_A (= agent i4b's, lanes mapped), byte for byte: stash G1 in (sh, w0, v0) when g is odd
pub fn enc_a(sh: &[u16; 4]) -> Vec<Row> {
    let mut o = Vec::new(); let d = &DIRTY[..]; let (s0, s1, s2, s3) = (sh[0], sh[1], sh[2], sh[3]);
    mcx(&mut o, &[(P0, true), (s3, true)], V0, d);
    mcx(&mut o, &[(P0, true), (s3, true), (s0, false), (s1, false), (s2, false)], V0, d);
    mcx(&mut o, &[(P0, true), (s3, true)], W0, d);
    mcx(&mut o, &[(P0, true), (s3, true), (s1, false), (s2, false), (W0, false), (V0, true)], s0, d);
    snz(&mut o, sh, &[(P0, true), (W0, false)], s3);
    o.push(ccx(P0, G, s3)); o.push(ccx(P0, s3, G));
    o
}
/// E2 encoder from lane 258 (see the module doc)
pub fn enc2() -> Vec<Row> { vec![ccx(G, M125, L2), cx(G, L1), x(L2), ccx(G, L2, M125), x(L2), ccx(M125, L1, G)] }
pub fn dec2() -> Vec<Row> { let mut v = enc2(); v.reverse(); v }
/// T_ip: E_A-encoded (G1 = p0 AND s3 when g is odd, 258 = 0) -> plain (sh, w0, v0) + E2-encoded (259, 257, 241); never names 258
pub fn t_ip(sh: &[u16; 4]) -> Vec<Row> {
    let s3 = sh[3]; let d = &DIRTY[..]; let mut o = Vec::new();
    mcx(&mut o, &[(P0, true), (s3, true), (M125, true)], L2, d);     // L2 ^= G1 AND m125
    o.push(ccx(P0, s3, L1));                                        // L1 ^= G1
    mcx(&mut o, &[(P0, true), (s3, true), (L2, false)], M125, d);    // m125 ^= G1 AND NOT L2 (= NOT m125 when G1)
    mcx(&mut o, &[(P0, true), (M125, true), (L1, true)], s3, d);     // s3 ^= p0 AND (E2 says G1): s3 = 0 when g is odd
    let ea = enc_a(sh); let core = &ea[..ea.len() - 2]; o.extend(core.iter().rev());   // rest of the E_A decoder
    o
}
pub fn t_up(sh: &[u16; 4]) -> Vec<Row> { let mut v = t_ip(sh); v.reverse(); v }
/// the toggle of Gtop row 127 (CX 258 513: g's bit 0 for g = 1) with G1 decoded from E2
pub fn toggle_e2() -> Row { ccx(M125, L1, P0) }

#[derive(Default, Debug, Clone)]
pub struct Stats {
    /// edits in INPUT coordinates: (input position, records removed, records inserted)
    pub edits: Vec<(usize, usize, usize)>,
    /// lane-258 stretches in OUTPUT coordinates (merged with agent i12's ipark / unpark windows)
    pub stretches: Vec<(usize, usize)>,
    pub ip_tr: usize, pub ip_dec: usize, pub up_enc: usize, pub up_tr: usize,
    /// row-126 stash / unstash insertion points (input coordinates)
    pub r126: Option<(usize, usize)>,
}
impl Stats {
    /// output position of an input position that is not inside a replaced block
    pub fn map(&self, p: usize) -> usize { let mut d: i64 = 0; for &(at, rm, ins) in &self.edits { if at + rm <= p { d += ins as i64 - rm as i64; } else if at < p { panic!("sm12 map: position {} inside an edit at {}", p, at); } } (p as i64 + d) as usize }
}
#[derive(Clone, Copy, Debug)]
pub struct Sel { pub ipark: bool, pub unpark: bool, pub row126: bool }
pub const SEL: Sel = Sel { ipark: true, unpark: true, row126: true };

// ---------------------------------------------------------------------------------------------- alpha row 126 (lane 239)
// Lane 239 = A bit 126 (the alpha accumulator's top lane J[126]) is named by no record between agent i12's R1 decoder and the
// row-127 shears; A < mg (modular accumulator) and mg < 2^126 unless g = 1, so 239 = 0 unless G1.  Lane 257 = g bit 1 = 0 when
// g = 1 and is named by no record there either.  So, with G1 (lane 258, only read there):  stash  257 ^= G1 AND 239;
// 239 ^= G1 AND 257  (239 -> 0 on every valid input); unstash = reverse, before the first record naming 257.
pub const A126: u16 = 239;
pub fn stash126() -> Vec<Row> { vec![ccx(G, A126, L1), ccx(G, L1, A126)] }
pub fn unstash126() -> Vec<Row> { let mut v = stash126(); v.reverse(); v }
/// agent i4's / i12's R1 decoder (the reverse of the R1 encoder on (513, 241, 238, 239))
pub fn r1_dec() -> Vec<Row> { let (x0, x2, x3, x4) = (513u16, 241u16, 238u16, 239u16);
    let mut v = vec![cx(x0, x3), cx(x2, x4), ccx(x2, x3, x0), x(x0), ccx(x0, x4, x2), x(x0)]; v.reverse(); v }

/// rows = ITEM 12 after i12w::rewrite_full (every switch on); g258 = its lane-258 window stretches in order (alpha start,
/// ipark, unpark), as returned in g1::Stats.stretches.  Returns the new rows and the stats.
pub fn rewrite(rows: &[Row], g258: &[(usize, usize)], sel: Sel) -> (Vec<Row>, Stats) {
    assert!(g258.len() == 3, "sm12: expected the three lane-258 windows of agent i12");
    let mut st = Stats::default();
    let (ips, ipe) = g258[1]; let (ups, upe) = g258[2];
    // --- ipark: window decoder + parity X + row-127 toggle
    let mut ed: Vec<(usize, usize, Vec<Row>)> = Vec::new();
    if sel.ipark {
        let mut dec = enc_a(&SH_B); dec.reverse();
        assert!(rows[ipe..ipe + dec.len()] == dec[..], "sm12: ipark window decoder not at the window end");
        let mut p = ipe + dec.len(); let mut nx = 0;
        while rows[p] == x(G) { nx += 1; p += 1; }
        assert!(nx % 2 == 0 && rows[p] == cx(G, P0), "sm12: ipark row-127 toggle not after the decoder ({} X)", nx);
        let rm = p + 1 - ipe;
        let mut ins = t_ip(&SH_B); st.ip_tr = ins.len(); ins.push(toggle_e2());
        ed.push((ipe, rm, ins));
        // the four HMR of the shift lanes (agent i12's early HMR) after the seam
        let h = (p + 1..p + 200_000).find(|&i| rows[i][0] == 12 && rows[i][1] == SH_B[0] && (1..4).all(|k| rows[i + k][0] == 12 && rows[i + k][1] == SH_B[k])).expect("sm12: ipark shift-lane HMR");
        for i in p + 1..h + 4 { let r = rows[i];
            assert!(!names(&r, G), "sm12: record {} names 258 inside the ipark seam", i);
            if nq(r[0]) > 0 && matches!(r[0], 6 | 8 | 13) && (r[nq(r[0])] == M125) { panic!("sm12: record {} writes 259 inside the ipark seam", i); } }
        let d = dec2(); st.ip_dec = d.len(); ed.push((h + 4, 0, d));
    }
    if sel.unpark {
        let mut enc = enc_a(&SH_C); let hs = ups - enc.len() - 1;
        assert!(rows[hs] == cx(G, P0) && rows[hs + 1..ups] == enc[..], "sm12: unpark window head not where expected");
        // the last record naming 258 before the window head: the unpark move's last Fredkin (CX 515 513, CCX 258 513 515, CX 515 513)
        let m = (0..hs).rev().find(|&i| names(&rows[i], G)).unwrap();
        assert!(rows[m] == ccx(G, P0, 515) && rows[m + 1] == cx(515, P0), "sm12: unpark move's last Fredkin not where expected");
        let at = m + 2;
        for i in at..hs { let r = rows[i]; if nq(r[0]) > 0 && matches!(r[0], 6 | 8 | 13) && r[nq(r[0])] == M125 { panic!("sm12: record {} writes 259 inside the unpark head", i); } }
        let e = enc2(); st.up_enc = e.len(); ed.push((at, 0, e));
        let mut ins = vec![toggle_e2()]; let t = t_up(&SH_C); st.up_tr = t.len(); ins.extend(t);
        ed.push((hs, 1 + enc.len(), ins)); enc.clear();
    }
    if sel.row126 {
        let d = r1_dec(); let ds = (0..ips).rev().find(|&i| rows[i..i + d.len()] == d[..]).expect("sm12: R1 decoder");
        let a = ds + d.len();
        let u = (a..ips).find(|&i| names(&rows[i], L1)).expect("sm12: first use of 257 after R1");
        let mut par = 0u8;
        for i in a..u { let r = rows[i]; assert!(!names(&r, A126), "sm12: record {} names 239 in the row-126 stretch", i);
            if r == x(G) { par ^= 1; continue; } let k = nq(r[0]); assert!(!(k > 0 && matches!(r[0], 8 | 13) && r[k] == G), "sm12: record {} writes 258", i); }
        assert!(par == 0, "sm12: X parity of 258 not 0 at the unstash point");
        ed.push((a, 0, stash126())); ed.push((u, 0, unstash126())); st.r126 = Some((a, u));
    }
    ed.sort_by_key(|e| e.0);
    let mut out: Vec<Row> = Vec::with_capacity(rows.len() + 1000); let mut p = 0usize;
    for (at, rm, ins) in &ed { out.extend_from_slice(&rows[p..*at]); out.extend_from_slice(ins); p = at + rm; st.edits.push((*at, *rm, ins.len())); }
    out.extend_from_slice(&rows[p..]);
    // lane-258 stretches in output coordinates
    let alpha = (st.map(g258[0].0), st.map(g258[0].1)); st.stretches.push(alpha);
    if sel.ipark { let dpos = st.edits.iter().filter(|e| e.1 == 0 && e.0 > ipe && e.0 < ups).map(|e| e.0).min().unwrap(); let s = st.map(ips); let e = st.map(dpos) - st.ip_dec; st.stretches.push((s, e)); }
    else { st.stretches.push((st.map(ips), st.map(ipe))); }
    if sel.unpark { let epos = st.edits.iter().filter(|e| e.1 == 0 && e.0 < ups && e.0 > ipe).map(|e| e.0).max().unwrap(); let s = st.map(epos); let e = st.map(upe); st.stretches.push((s, e)); }
    else { st.stretches.push((st.map(ups), st.map(upe))); }
    for &(s, e) in &st.stretches { assert!(!out[s..e].iter().any(|r| names(r, G)), "sm12: lane 258 named inside its stretch [{}, {})", s, e); }
    (out, st)
}
