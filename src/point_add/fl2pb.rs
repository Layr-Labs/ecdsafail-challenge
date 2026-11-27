//! q631 / fl2 (agent fl2, 2026-11-20; local research, NOT part of any package; nothing in the builder calls it): ITEM 4's phase B
//! (A = 2^256 |v| mod mg by aligned doublings / halvings, item offsets ~[7.33M, 12.98M)) with lane 2 free at every record.
//! Switch ON = false.
//!
//! Input: ITEM 4's rows as fl::fli4::rewrite leaves them (or the stage-F rows: phase B is byte-identical in both, MEASURED).
//!
//! ROLES (MEASURED from the records, DERIVED from sub640build/alpha/alpha.cjs alphaFull + modk alDouble2, which the block descends from):
//!   X = the accumulator J, 129 lanes (bit 0 = lane 1, ..., bit 128 = T = 617); K = mg, 129 lanes (bit 0 = 256, bit 1 = 623, bit i =
//!   386 - i), read-only (a TTK adder modifies its lanes only transiently); G = 258 = K bit 128 = G1 := [g == 1] (g mg = M0 in
//!   [2^128, 2^129)); OV = 2 = the doubling's 130th bit / reduction flag (zero between doublings); f = 620 (Horner bit / halving
//!   mask); Z = 257 holds g bit 0 (moved there from lane 249 at the start of the first doubling's rotation), idle in phase B.
//!   512 doubling units: 128 Horner (X <- 2X + f 2^a mod K), 256 plain (X <- 2X mod K), 128 halvings (the reverse of a doubling
//!   controlled by f, emitted in reverse order).  Each forward doubling: R = rotation of [X, OV] (OV <- X128), S = X -= K with the
//!   borrow XORed into OV (OV only a target in S), A = X += K controlled by OV (OV only a control), N = OV ^= c (c = 1, or f for
//!   halvings), L = OV ^= c X[ctz K] (Horner: then B = OV ^= f).  OV = 0 before R and after L / B.
//!
//! THE G1-SPLIT (DERIVED): for G1 = 0, K < 2^128 and X < K, so X128 = 0 before R, 2X fits in X's 129 lanes, and after S the bit X128
//!   equals the borrow (2X - K lies in (-2^128, 2^128)): OV is redundant.  For G1 = 1, g = 1 so g bit 0 = 1, i.e. Z XOR G1 = 0.
//!   So Z' := Z XOR G1 (= 0 on G1 shots, = g0 otherwise) plays OV for G1 shots, and the G1 = 0 shots never need it:
//!     R:  the swap (X128, OV) becomes a swap (X128, Z) controlled by G (and f for halvings): non-G1 shots rotate X alone (X128 = 0
//!         goes to X0, as before);
//!     S:  unchanged with OV -> Z; on G1 = 0 shots it XORs the borrow = X128 into Z (Z only a target there);
//!     FIX1 (after S, K restored): under NOT G: Z ^= X128 (Z = g0 again), then exchange: X128 <- g0, Z <- sign (2 CCX);
//!     A, N, L: unchanged with OV -> Z (Z = sign for both classes).  On G1 = 0 shots X128 now holds g0 instead of the sign: A is a
//!         controlled adder mod 2^129 (correct for every X), so only bit 128 differs, by sign (the carry into bit 128 is 1 when the
//!         sign is 1); L reads X128 only through K's bit 128 / (K-1)'s bit 128, both 0 when G1 = 0 (K >= 1);
//!     AFIX (before N): under NOT G: X128 ^= Z (X128 = g0 again);
//!     SW2 (at a clean point after the unit, before the next one): under NOT G: Z <- X128 = g0, X128 <- 0 (2 CCX).
//!   Halvings are handled as the same forward doubling (f-controlled; the swap's 3-control gate uses dirty lane 385) and emitted in
//!   reverse.  Between units the shots sit either in the rest state (Z = g0, X128 = 0) or, around the halvings' masks, in the parked
//!   state (Z = 0, X128 = g0); records there name neither lane (asserted).  Phase start: Z ^= G (CX 258 -> 257) right after g0 arrives
//!   in 257; phase end: the same gate after the last halving.
//!   Lane 2 is then never named in phase B and is zero there (it is the rail-zeroed OV lane before, and nothing writes it): FREE.
//! Cost (DERIVED): per unit 1 (HF) / 4 (halving) CCX for the swap instead of 0 / 1, + 2 + 1 + 2 CCX for FIX1 / AFIX / SW2, + 6 X;
//!   see Stats.
use super::super::{Row, NONE};
pub const ON: bool = false;
const OV: u16 = 2;
const Z: u16 = 257;
const G: u16 = 258;
const T: u16 = 617;
const F: u16 = 620;
const D: u16 = 385;
/// X lanes, bit 0 .. 128
pub const XL: [u16; 129] = {
    let mut a = [0u16; 129]; let head: [u16; 10] = [1, 129, 130, 131, 132, 631, 133, 619, 249, 136];
    let mut i = 0; while i < 10 { a[i] = head[i]; i += 1; }
    let mut l = 137u16; while (l as usize) < 248 { a[i] = l; i += 1; l += 1; }
    let tail: [u16; 8] = [614, 134, 250, 615, 622, 630, 616, 617]; let mut j = 0; while j < 8 { a[i] = tail[j]; i += 1; j += 1; }
    a
};
#[inline] fn nq(k: u16) -> usize { match k { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }
fn names(r: &Row, l: u16) -> bool { (1..=nq(r[0])).any(|j| r[j] == l) }
fn relabel(r: &Row, from: u16, to: u16) -> Row { let mut o = *r; for j in 1..=nq(r[0]) { if o[j] == from { o[j] = to; } } o }
const fn x(t: u16) -> Row { [6, t, NONE, NONE] }
const fn cx(c: u16, t: u16) -> Row { [8, c, t, NONE] }
const fn ccx(a: u16, b: u16, t: u16) -> Row { [13, a, b, t] }
/// swap (T, Z) controlled by G (Horner / plain doublings): replaces "CX T OV; CX OV T; CX T OV"
pub fn r_hf() -> Vec<Row> { vec![cx(T, Z), ccx(G, Z, T), cx(T, Z)] }
/// swap (T, Z) controlled by f AND G (halvings; self-inverse as a list): replaces "CX T OV; CCX f OV T; CX T OV"
pub fn r_v() -> Vec<Row> { vec![cx(T, Z), ccx(D, Z, T), ccx(F, G, D), ccx(D, Z, T), ccx(F, G, D), cx(T, Z)] }
/// FIX1 (forward): under NOT G: X128 ^= Z; Z ^= X128
pub fn fix1() -> Vec<Row> { vec![x(G), ccx(G, Z, T), ccx(G, T, Z), x(G)] }
/// AFIX: under NOT G: X128 ^= Z
pub fn afix() -> Vec<Row> { vec![x(G), ccx(G, Z, T), x(G)] }
/// SW2 (forward): under NOT G: Z ^= X128; X128 ^= Z   (= FIX1 reversed)
pub fn sw2() -> Vec<Row> { vec![x(G), ccx(G, T, Z), ccx(G, Z, T), x(G)] }
fn rev(v: Vec<Row>) -> Vec<Row> { let mut v = v; v.reverse(); v }
fn is_hf(r: &[Row], i: usize) -> bool { r[i] == cx(T, OV) && r[i + 1] == cx(OV, T) && r[i + 2] == cx(T, OV) }
fn is_v(r: &[Row], i: usize) -> bool { r[i] == cx(T, OV) && r[i + 1] == ccx(F, OV, T) && r[i + 2] == cx(T, OV) }
fn is_xrun(r: &[Row], i: usize, fwd: bool, base: usize) -> bool {
    // 129 consecutive X gates on the 129 X lanes (any order); fwd = false: file indices base - i - k
    let mut seen = [false; 129];
    for k in 0..129 { let rr = if fwd { r[i + k] } else { r[base - (i + k)] }; if rr[0] != 6 { return false; }
        match XL.iter().position(|&l| l == rr[1]) { Some(p) if !seen[p] => seen[p] = true, _ => return false } }
    true
}
#[derive(Debug, Default, Clone)]
pub struct Stats { pub units_hf: usize, pub units_v: usize, pub phase: (usize, usize), pub free: (usize, usize), pub added_rows: i64,
    pub added_ccx: i64, pub relabelled: usize, pub inserts: Vec<usize> }
/// rewrite phase B; returns the new rows, the stats (free = [s, e) of lane 2 in NEW coordinates) and the edit positions (input coords)
pub fn rewrite(rows: &[Row]) -> (Vec<Row>, Stats) {
    let n = rows.len();
    // landmarks
    let lo = 7_000_000usize.min(n); let hi = 13_200_000usize.min(n);
    let mut hf: Vec<usize> = Vec::new(); let mut vm: Vec<usize> = Vec::new();
    for i in lo..hi - 2 { if is_hf(rows, i) { hf.push(i); } else if is_v(rows, i) { vm.push(i); } }
    assert!(hf.len() == 384 && vm.len() == 128, "fl2pb: units {} {}", hf.len(), vm.len());
    assert!(hf[383] < vm[0], "fl2pb: unit order");
    let b0 = hf[0];
    let mv = (b0..b0 + 2000).find(|&i| rows[i] == cx(249, Z) && rows[i + 1] == cx(Z, 249)).expect("fl2pb: the move of g0 into 257");
    let pend = vm[127] + 3;
    // nothing in [b0, pend) names Z, except the move; nothing names OV before b0 inside [mv - 2000, b0)
    for i in b0..pend { if i == mv || i == mv + 1 { continue; } assert!(!names(&rows[i], Z), "fl2pb: +{} names 257", i); }
    // edits: rep[i] = replacement rows for input record i (empty = delete); ins[i] = rows inserted before input record i
    let mut rep: std::collections::BTreeMap<usize, Vec<Row>> = Default::default();
    let mut ins: std::collections::BTreeMap<usize, Vec<Row>> = Default::default();
    let add_ins = |ins: &mut std::collections::BTreeMap<usize, Vec<Row>>, at: usize, v: Vec<Row>| { ins.entry(at).or_default().extend(v); };
    add_ins(&mut ins, mv + 2, vec![cx(G, Z)]);
    let mut relab = 0usize;
    // Horner / plain units
    for k in 0..384 {
        let s = hf[k]; let e = if k + 1 < 384 { hf[k + 1] } else { s + 7568 };
        let horner = k < 128;
        for j in 0..3 { rep.insert(s + j, if j == 0 { r_hf() } else { vec![] }); }
        let c = (s..e).filter(|&i| rows[i] == ccx(G, T, OV)).collect::<Vec<_>>(); assert!(c.len() == 1, "fl2pb: unit {} carry-out", k);
        let c = c[0];
        // the first X run after the carry-out: S's complement-back
        let send = (c + 1..e - 129).find(|&i| is_xrun(rows, i, true, 0)).expect("fl2pb: S complement-back") + 129;
        let nn = (s..e).filter(|&i| rows[i] == x(OV)).collect::<Vec<_>>(); assert!(nn.len() == 1 && nn[0] > send, "fl2pb: unit {} N", k);
        let nn = nn[0];
        let bb = (s..e).filter(|&i| rows[i] == cx(F, OV)).collect::<Vec<_>>();
        if horner { assert!(bb.len() == 1 && bb[0] > nn, "fl2pb: unit {} B", k); } else { assert!(bb.is_empty(), "fl2pb: unit {} B", k); }
        // every other OV use in the unit is relabelled.  Roles asserted: in S (R end .. S end) OV is only a target, in A (S end .. N)
        // only a control, after N only a target
        for i in s + 3..e { if names(&rows[i], OV) {
            let r = &rows[i]; let tgt = r[nq(r[0])] == OV && (1..nq(r[0])).all(|j| r[j] != OV);
            if i < send || i >= nn { assert!(tgt, "fl2pb: unit {} +{} OV not a target", k, i); } else { assert!(!tgt, "fl2pb: unit {} +{} OV a target in A", k, i); }
            rep.insert(i, vec![relabel(&rows[i], OV, Z)]); relab += 1; } }
        add_ins(&mut ins, send, fix1()); add_ins(&mut ins, nn, afix());
        if k + 1 < 384 { add_ins(&mut ins, e, sw2()); }
        else {
            // last plain unit: its SW2 cancels the first halving's SW2^-1; between its end and the first halving no record names Z / T
            assert!(rows[e - 1] != rows[e], "fl2pb: last plain unit end");
        }
        if horner {
            // gaps: between B and the next unit's R no record names Z or T (the parked state is never seen; SW2 sits at the next R)
            for i in bb[0] + 1..e { assert!(!names(&rows[i], T) && !names(&rows[i], Z), "fl2pb: unit {} tail +{} names T / Z", k, i); }
        }
    }
    // halvings (file order: mask, D^-1, mask ...); forward index q <-> file index m + 2 - q
    let mut prev_end = hf[383] + 7568;
    for (j, &m) in vm.iter().enumerate() {
        let fw = |q: usize| rows[m + 2 - q];
        // the forward unit: carry-out pieces "CCX f K0 OV" x2 and "CCX f K128 OV"
        let mut q = 3usize; let lim = m + 3 - prev_end;
        while q < lim && fw(q) != ccx(F, G, OV) { q += 1; } assert!(q < lim, "fl2pb: halving {} CCX f K128 OV", j);
        let sq = (q + 1..lim - 129).find(|&p| is_xrun(rows, p, false, m + 2)).expect("fl2pb: halving S complement-back") + 129;
        let nq_ = (sq..lim).find(|&p| fw(p) == cx(F, OV)).expect("fl2pb: halving N");
        for p in sq..nq_ { assert!(fw(p) != cx(F, OV)); }
        rep.insert(m, vec![]); rep.insert(m + 1, vec![]); rep.insert(m + 2, r_v());
        for i in prev_end..m { if names(&rows[i], OV) {
            let r = &rows[i]; let tgt = r[nq(r[0])] == OV && (1..nq(r[0])).all(|jj| r[jj] != OV); let qf = m + 2 - i;
            if qf < sq || qf >= nq_ { assert!(tgt, "fl2pb: halving {} +{} OV not a target", j, i); } else { assert!(!tgt, "fl2pb: halving {} +{} OV a target in A", j, i); }
            rep.insert(i, vec![relabel(&rows[i], OV, Z)]); relab += 1; } }
        // FIX1 forward before fwd sq  ->  file: rev(FIX1) before file index m + 3 - sq;  AFIX forward before fwd nq_ -> after file m + 2 - nq_
        add_ins(&mut ins, m + 3 - sq, rev(fix1()));
        add_ins(&mut ins, m + 3 - nq_, afix());
        if j > 0 { add_ins(&mut ins, prev_end, rev(sw2())); }
        // the masks between units name neither Z nor T
        if j > 0 { let first_ov = (prev_end..m).find(|&i| names(&rows[i], OV)).unwrap();
            for i in prev_end..first_ov { assert!(!names(&rows[i], T) && !names(&rows[i], Z), "fl2pb: mask before halving {} names T / Z at +{}", j, i); } }
        prev_end = m + 3;
    }
    {   // the gap between the last plain unit and the first halving's first OV use
        let s = hf[383] + 7568; let first_ov = (s..vm[0]).find(|&i| names(&rows[i], OV)).unwrap();
        for i in s..first_ov { assert!(!names(&rows[i], T) && !names(&rows[i], Z), "fl2pb: gap before halving 0 names T / Z at +{}", i); }
    }
    add_ins(&mut ins, pend, vec![cx(G, Z)]);
    // OV must not be named in [b0, pend) after the edits
    let mut out: Vec<Row> = Vec::with_capacity(n + 40_000);
    let mut st = Stats { units_hf: 384, units_v: 128, ..Default::default() };
    let mut free_s = 0usize;
    for i in 0..=n {
        if let Some(v) = ins.get(&i) { out.extend_from_slice(v); st.inserts.push(i); }
        if i == n { break; }
        if i == b0 { free_s = out.len(); }
        match rep.get(&i) { Some(v) => out.extend_from_slice(v), None => out.push(rows[i]) }
        if i == pend - 1 { st.free = (free_s, out.len()); }
    }
    for i in st.free.0..st.free.1 { assert!(!names(&out[i], OV), "fl2pb: output +{} names lane 2", i); }
    st.phase = (b0, pend); st.relabelled = relab;
    st.added_rows = out.len() as i64 - n as i64;
    let cc = |v: &[Row]| v.iter().filter(|r| r[0] == 13).count() as i64;
    st.added_ccx = cc(&out) - cc(rows);
    (out, st)
}
