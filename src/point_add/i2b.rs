//! q631 / i2b (local research, 2026-11-20; not submitted, not part of any package): ITEM 2 (segment 5, the 127-bit multiply
//! Y <- Y * T mod p) with a DECLARED free lane at every record (a lane that is zero and named by no record for a stated structural
//! reason), on top of agent i2's rewrite (i2.rs).  Switch `ON` (false = nothing here runs; the builder hook in i1.rs is untouched).
//! Report: ~/Projects/ecdsafail/q631/i2b/summary.py.
//!
//! What it adds to i2::generate (stage C): every qkit Cuccaro adder whose clean carry-in is wire 243 in the three non-walk ranges
//! `CONV` (between walk runs 1 and 2, between runs 2 and 3, the tail) is re-emitted as the ancilla-free ripple adder of i2's
//! converter (i2c0.rs = agent i10's i10c0.rs; every instance checked against its original records on random states), so wire 243
//! is named by no record over those ranges.  Then m1gen's hole schedule with its positions moved through all three rewrites
//! (the free wire never named: asserted) and m1gen's exit FIX, exactly as i2::generate does.
//!
//! The declared stretches (census lane, physical wire, logical wire, first, end, class) are the table `tab::STR`
//! (i2btab.rs, generated); `check_declared` verifies statically that every stretch lane is named by no record inside its stretch,
//! is not the free wire 251, and that every record of the output lies inside at least one stretch.
//!
//! To use (integrator, NOT done here): in i1.rs's ITEM 2 hook call `super::i2b::generate(&raw)` when `super::i2b::ON` (it replaces
//! i2::generate; it calls i2's rewrite itself) and use `i2b::LEN_ON` in HOOK_LEN; the relabel table must be re-planned (as for i2).

/// the switch (OFF = the tree unchanged)
pub const ON: bool = false;
/// length of the rewritten ITEM 2 (wire space, incl. the 2 FIX records)
pub const LEN_ON: u64 = 64_802_535;

#[path = "i2btab.rs"]
pub mod tab;

type R4 = [u16; 4];
const NO: u16 = u16::MAX;
/// the carry-in wire of the converted adders (m1gen's logical numbering, before the hole renaming)
pub const C0: u16 = 243;
/// stage C ranges, positions of i2::generate_unperm's stream (i2's rw7): run 1 exit .. the first walk use of 243 in run 2;
/// after run 2's move of 243 into wire 0 and the next (unparsed) c0 = 243 adder .. the move of wire 252 into 243 before run 3;
/// after the tail comparator that computes / uncomputes a flag in 243 .. the item end
pub const CONV: [(usize, usize); 3] = [(28_978_207, 40_043_164), (48_458_483, 49_536_404), (57_949_753, 63_532_474)];
/// adders converted by stage C
pub const N_STAGE_C: usize = 16_739;
/// length of the stream before the hole renaming
pub const UNPERM_LEN: usize = 64_802_533;

fn nq(k: u16) -> usize { match k { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }
fn refs(r: &R4, w: u16) -> bool { (1..=nq(r[0])).any(|j| r[j] == w) }
/// stage-C position map (old position -> new; inside a replaced instance: its new start)
fn conv_map(mv: &[(usize, usize, usize, usize)], p: usize) -> usize {
    let k = mv.partition_point(|m| m.0 <= p); if k == 0 { return p; }
    let m = mv[k - 1]; if p >= m.1 { p + m.3 - m.1 } else { m.2 } }

/// i2's rewrite + stage C, before the hole renaming; returns the rows and the position map m1_unperm -> this stream
pub fn generate_unperm(raw: &[R4]) -> (Vec<R4>, Box<dyn Fn(usize) -> usize>) {
    let (o, shift, st) = super::i2::generate_unperm(raw);
    assert!(o.len() == 63_532_474, "i2b: i2 stream length {}", o.len());
    let loans: Vec<u16> = (256..504).chain(504..632).chain(115..242).chain(2..111).chain(632..637).filter(|l| !super::i2::HOLE_WIRES.contains(l)).collect();
    let (o2, st2) = super::i2::c0::convert(&o, &CONV, C0, &loans);
    assert!(st2.rejected == 0 && st2.replaced == N_STAGE_C && st2.dropped == 0 && st2.left == 0,
        "i2b: stage C found {} replaced {} rejected {} dropped {} left {}", st2.found, st2.replaced, st2.rejected, st2.dropped, st2.left);
    assert!(o2.len() == UNPERM_LEN, "i2b: stream length {}", o2.len());
    for &(a, b) in CONV.iter() { let (a2, b2) = (conv_map(&st2.moves, a), if b >= o.len() { o2.len() } else { conv_map(&st2.moves, b) });
        assert!(o2[a2..b2].iter().all(|r| !refs(r, C0)), "i2b: 243 still named inside a stage C range"); }
    let mv = st.moves; let mv2 = st2.moves;
    // m1_unperm position -> i2 stream (merge shift, prologue adder moves; i2::generate's map) -> this stream (stage C moves)
    let map = move |p: usize| -> usize {
        let p2 = { let k = shift.partition_point(|x| x.0 <= p); if k == 0 { p } else { p + shift[k - 1].1 } };
        let k = mv.partition_point(|m| m.0 <= p2);
        let p3 = if k == 0 { p2 } else { let m = mv[k - 1]; if p2 >= m.1 { p2 + m.3 - m.1 } else { m.2 } };
        conv_map(&mv2, p3) };
    (o2, Box::new(map))
}

/// the switchable rewrite: generate_unperm, then m1gen's hole schedule (positions moved), then m1gen's FIX; asserts the free wire is
/// never named, the output length and the declared-stretch table
pub fn generate(raw: &[R4]) -> Vec<R4> {
    use super::m1tab::{CHAIN, FIX};
    let (mut o, map) = generate_unperm(raw);
    let x = CHAIN[0].1;
    assert!(CHAIN[CHAIN.len() - 1].0 as usize == super::i2::UNPERM_LEN, "i2b: hole table does not match the stream");
    let chain: Vec<(usize, u16)> = CHAIN.iter().map(|c| (map(c.0 as usize), c.1)).collect();
    for w in chain.windows(2) { assert!(w[0].0 <= w[1].0, "i2b: hole table out of order after the rewrite"); }
    assert!(chain[chain.len() - 1].0 == o.len(), "i2b: hole table end {} vs stream {}", chain[chain.len() - 1].0, o.len());
    let mut pi: Vec<u16> = (0..1024u16).collect(); let mut ci = 0usize;
    for i in 0..o.len() {
        while ci + 1 < chain.len() && chain[ci].0 <= i { pi.swap(chain[ci].1 as usize, chain[ci + 1].1 as usize); ci += 1; }
        let k = o[i][0]; for j in 1..=nq(k) { o[i][j] = pi[o[i][j] as usize]; }
    }
    o.extend_from_slice(&FIX);
    for r in &o { assert!(!refs(r, x), "i2b: output references the free wire"); }
    assert!(o.len() as u64 == LEN_ON, "i2b: rewritten ITEM 2 length {}", o.len());
    let (named, outside) = check_declared(&o);
    assert!(named == 0 && outside == 0, "i2b: declared table: {} records name their stretch lane, {} records outside every stretch", named, outside);
    let _ = NO;
    o
}

/// static check of the declared table on the hooked rows: (records naming their stretch's physical wire inside it, records outside
/// every stretch); stretches on the free wire 251 panic
pub fn check_declared(o: &[R4]) -> (usize, usize) {
    let n = o.len(); let mut cov = vec![0i32; n + 1]; let mut named = 0usize;
    for s in tab::STR.iter() { let (w, a, b) = (s.1, s.3 as usize, s.4 as usize); assert!(w != 251 && a <= b && b <= n, "i2b: bad stretch {:?}", s);
        named += o[a..b].iter().filter(|r| refs(r, w)).count(); cov[a] += 1; cov[b] -= 1; }
    let mut c = 0i32; let mut outside = 0usize; for i in 0..n { c += cov[i]; if c == 0 { outside += 1; } }
    (named, outside)
}

/// the declared stretches as (census lane, first record, one past the last record, class name, reason)
pub fn declared() -> Vec<(u16, u32, u32, &'static str, &'static str)> {
    tab::STR.iter().map(|s| (s.0, s.3, s.4, tab::CLASS[s.5 as usize], tab::REASON[s.5 as usize])).collect()
}
