//! q631 / fl2 (agent fl2, 2026-11-20; local research, NOT part of any package; nothing in the builder calls it): ITEM 4's unpark head
//! (the published parkInner(rev = true) after the move: extract, phase fixes, mask, mark, bias, delta; ~186k records ending at agent
//! i4b's E_A encoder of the unpark-Gtop window) with lane 258 free at every record.  Switch ON = false.
//!
//! Input: ITEM 4's rows after fl2pb (or fl::fli4); located by content.
//!
//! ROLES (MEASURED on pools, DERIVED from d655_src.txt parkInner and agent i4b's i4g.rs): 258 = mg bit 128 = G1 := [g == 1], read only
//! (13,201 controls in the region; its only write is i4b's E_A encoder at the end); 617 = A bit 128 for G1 and the park flag D (from
//! the other team's re-encoding inside part 1) for G1 = 0; 2, 257, 620 = L0..L2 = the low bits of g' (g with its top bit toggled off
//! by the ipark Gtop), so (2, 257, 620) = 0 on G1 shots; 259 = mg bit 127 and 616 = A bit 127 are named by NO record of the region;
//! S = (626, 628, 629, 627) is zero before the extract.  Every gadget reads the park flag through the other team's formula
//! D = 617 AND NOT 258 XOR 258 AND (terms in 2, 257, 620): on G1 shots D = 0 (g odd => v2(mg) = v2(M0) >= sh).
//!
//! THE CODE (DERIVED): G1 = 0 => mg < 2^128 => (A < mg) A bit 127 = 1 only if mg bit 127 = 1: (259, 616) never = (0, 1).  So on G1
//!   shots the encoder E (before the extract's first S write; S lanes zero = free) moves A128 -> lane 2, m127 -> 257, A127 -> 620
//!   (all three zero on G1 shots), sets (259, 616) := (0, 1) (G1 marker C = NOT 259 AND 616) and clears 617 and 258.
//!   Then 258 = 0 on every shot, so every record of the region with 258 as a control is the identity and is dropped: 258 is FREE.
//!   G1 shots now look to every remaining gadget like G1 = 0 shots with D = 617 = 0 (the formula reads 617 only once 258 = 0); their
//!   L lanes carry the code, which the D-gated gadgets (D = 0) never use and the linear conjugations (CX 2 617 / CX 2 620 / X 2) only
//!   shuffle and undo (ARGUED; MEASURED by the paired replays).
//!   The end transcoder T replaces the moved row-129 toggle "CX 258 2" and E_A's last two gates: A128 back to 617, lane 2 := g0 = 1
//!   (C), E_A's own stash gates unchanged, 627 ^= C (E_A's G1 stash), then (259, 616, 257, 620) restored under E_A's decoded
//!   G1' = 2 AND 627.  The result is E_A's form exactly; 258 stays 0 and unnamed throughout T (free).
//! Free lane during E: 626 (S lane, zero before the extract).  Cost: see Stats.
use super::super::{Row, NONE};
pub const ON: bool = false;
const G: u16 = 258;
const D617: u16 = 617;
const L0: u16 = 2;
const L1: u16 = 257;
const L2: u16 = 620;
const M127: u16 = 259;
const A127: u16 = 616;
const S3: u16 = 627;
const DIRTY: [u16; 8] = [506, 507, 508, 509, 510, 511, 513, 514];
#[inline] fn nq(k: u16) -> usize { match k { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }
fn names(r: &Row, l: u16) -> bool { (1..=nq(r[0])).any(|j| r[j] == l) }
const fn x(t: u16) -> Row { [6, t, NONE, NONE] }
const fn cx(c: u16, t: u16) -> Row { [8, c, t, NONE] }
const fn ccx(a: u16, b: u16, t: u16) -> Row { [13, a, b, t] }
/// t ^= AND of (lane, polarity); Barenco ladder on dirty lanes; negative controls by X wraps (as i4g::mcx)
pub fn mcx(out: &mut Vec<Row>, ctl: &[(u16, bool)], t: u16) {
    for &(l, p) in ctl { if !p { out.push(x(l)); } }
    let c: Vec<u16> = ctl.iter().map(|z| z.0).collect();
    match c.len() {
        0 => out.push(x(t)), 1 => out.push(cx(c[0], t)), 2 => out.push(ccx(c[0], c[1], t)),
        u => { let v: Vec<u16> = DIRTY.iter().copied().filter(|d| !c.contains(d) && *d != t).take(u - 2).collect(); assert!(v.len() == u - 2);
            let a = ccx(c[0], c[1], v[0]); let m: Vec<Row> = (2..u - 1).map(|j| ccx(c[j], v[j - 2], v[j - 1])).collect(); let z = ccx(c[u - 1], v[u - 3], t);
            for _ in 0..2 { out.push(a); out.extend(m.iter()); out.push(z); out.extend(m.iter().rev()); } } }
    for &(l, p) in ctl { if !p { out.push(x(l)); } }
}
/// the encoder E (G1 = 258 on input; every gate but the last controlled by 258)
pub fn enc() -> Vec<Row> {
    vec![ccx(G, D617, L0), ccx(G, L0, D617), ccx(G, M127, L1), ccx(G, A127, L2), ccx(G, L1, M127),
         x(L2), ccx(G, L2, A127), x(L2), x(M127), ccx(M127, A127, G), x(M127)]
}
/// T part 1 (replaces "CX 258 2"): A128 back to 617, lane 2 := 1 on coded shots (C = NOT 259 AND 616)
pub fn t_head() -> Vec<Row> {
    let mut o = Vec::new();
    mcx(&mut o, &[(M127, false), (A127, true), (L0, true)], D617);
    mcx(&mut o, &[(M127, false), (A127, true), (D617, true)], L0);
    o.push(x(M127)); o.push(ccx(M127, A127, L0)); o.push(x(M127));
    o
}
/// T part 2 (replaces "CCX 2 258 627; CCX 2 627 258"): 627 ^= C, then (259, 257, 616, 620) restored under G1' = 2 AND 627
pub fn t_tail() -> Vec<Row> {
    let mut o = Vec::new();
    o.push(x(M127)); o.push(ccx(M127, A127, S3)); o.push(x(M127));
    mcx(&mut o, &[(L0, true), (S3, true), (L1, true)], M127);
    mcx(&mut o, &[(L0, true), (S3, true), (M127, true)], L1);
    mcx(&mut o, &[(L0, true), (S3, true), (L2, false)], A127);
    mcx(&mut o, &[(L0, true), (S3, true), (A127, true)], L2);
    o
}
#[derive(Debug, Default, Clone)]
pub struct Stats { pub e_at: usize, pub t_at: usize, pub t2_at: usize, pub dropped: usize, pub added_rows: i64, pub added_ccx: i64, pub free: (usize, usize) }
pub fn rewrite(rows: &[Row]) -> (Vec<Row>, Stats) {
    let n = rows.len(); let (lo, hi) = (60_000_000usize.min(n), 90_000_000usize.min(n));
    let anchor = [cx(629, 257), cx(629, L0), ccx(G, L0, 629), cx(629, L0), cx(385, 626)];
    let es: Vec<usize> = (lo..hi - 5).filter(|&i| rows[i..i + 5] == anchor[..]).map(|i| i + 4).collect();
    assert!(es.len() == 1, "fl2up: E anchor {}", es.len()); let e = es[0];
    let t = (e..e + 400_000).find(|&i| rows[i] == cx(G, L0)).expect("fl2up: the moved toggle CX 258 2");
    assert!(rows[t + 1] == ccx(L0, S3, 621), "fl2up: E_A start");
    let t2 = (t..t + 400).find(|&i| rows[i] == ccx(L0, G, S3)).expect("fl2up: E_A's G1 stash");
    assert!(rows[t2 + 1] == ccx(L0, S3, G), "fl2up: E_A's 258 clear");
    // 259 / 616 named by no record of [e, t2 + 2); 258 only as a control in [e, t) and not at all in (t, t2)
    for i in e..t2 + 2 { if i == t || i == t2 || i == t2 + 1 { continue; } let r = &rows[i];
        assert!(!names(r, M127) && !names(r, A127), "fl2up: +{} names 259 / 616", i);
        if names(r, G) { assert!(i < t && r[nq(r[0])] != G, "fl2up: +{} writes 258 / names it after the toggle", i); } }
    let mut out: Vec<Row> = Vec::with_capacity(n);
    out.extend_from_slice(&rows[..e]); out.extend(enc());
    let free_s = out.len() - 1;   // the last gate of E clears 258
    let mut dropped = 0;
    for i in e..t { if names(&rows[i], G) { dropped += 1; } else { out.push(rows[i]); } }
    out.extend(t_head()); out.extend_from_slice(&rows[t + 1..t2]); out.extend(t_tail());
    let free_e = out.len();
    out.extend_from_slice(&rows[t2 + 2..]);
    for i in free_s + 1..free_e { assert!(!names(&out[i], G), "fl2up: output +{} names 258", i); }
    let cc = |v: &[Row]| v.iter().filter(|r| r[0] == 13).count() as i64;
    let st = Stats { e_at: e, t_at: t, t2_at: t2, dropped, added_rows: out.len() as i64 - n as i64, added_ccx: cc(&out) - cc(rows), free: (free_s + 1, free_e) };
    (out, st)
}
