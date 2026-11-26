//! q631 / i2 (local research, 2026-11-19; not submitted, not part of any package): ITEM 2 (segment 5, the 127-bit multiply
//! Y <- Y * T mod p) without its 632nd lane.  Switch `ON` (false = the tree unchanged: the builder hook in i1.rs calls
//! m1gen::generate as before; nothing in this module runs).
//!
//! What binds ITEM 2 at 632 lanes (agent i2, report ~/Projects/ecdsafail/q631/i2/summary.py):
//!  (a) inside the three inverter walk runs, every lane is live during the step's main part (loops 1 and 2, the digit, the carry
//!      block): the walk's lane 251 (fire / loop enable) is held while all others hold data;
//!  (b) before the walk runs, the qkit Cuccaro adders of the inverter prologue use the clean carry-in lane c0 = wire 243.
//! The rewrite (`generate`), on m1gen's stream before its hole renaming (`m1_unperm`), then m1gen's hole schedule re-applied:
//!  (a) FIRE MERGE, one segment per walk step (table i2tab.rs): z_act = R[m] (the step's top port: 0 on every shot whose step is
//!      active; named by no record of the segment) and z_off = L[m] (the u-top lane: 0 on every shot whose walk has finished).  At the
//!      segment start (lane 251 = the step's fire bit f there): CX(z_off -> z_act), CCX(251, z_act, z_off): z_act now carries z_off's
//!      value on active shots and z_off = 0 on every shot (the freed lane); every record of the segment that names z_off names
//!      z_act instead; at the segment end (251 = f again): CCX(251, z_act, z_off), CX(z_off -> z_act).
//!  (b) every parsable Cuccaro instance with carry-in c0 = 243 in [0, PRE_END) is re-emitted as the ancilla-free ripple adder of the
//!      tree's walk generator (i2c0.rs = agent i10's i10c0.rs), each instance checked against its original records on random states.
use super::*;
use super::m1tab::*;

/// the switch (OFF = the tree unchanged)
pub const ON: bool = false;
/// length of the rewritten ITEM 2 (wire space; i1::HOOK_LEN uses it when ON)
pub const LEN_ON: u64 = 63_532_476;

#[path = "i2c0.rs"]
pub mod c0;
#[path = "i2tab.rs"]
pub mod tab;

/// the walk's fire / loop-enable lane (m1gen's logical wire numbering)
pub const F: u16 = 251;
/// the clean carry-in lane of the prologue's qkit adders
pub const C0: u16 = 243;
/// end of the converted prologue (position in m1_unperm's stream; the first walk run starts after it)
pub const PRE_END: usize = 18_900_000;
/// number of Cuccaro instances converted in [0, PRE_END)
pub const N_ADDERS: usize = 17_562;
/// every wire the m1gen hole schedule uses (never chosen as a dirty loan)
pub const HOLE_WIRES: [u16; 14] = [243, 247, 253, 252, 246, 248, 250, 249, 244, 0, 251, 241, 116, 1];
/// length of m1gen's stream before its hole renaming (= m1gen output without the two FIX records)
pub const UNPERM_LEN: usize = 61_903_458;

fn nq(k: u16) -> usize { match k { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }
fn refs(r: &Row, w: u16) -> bool { (1..=nq(r[0])).any(|j| r[j] == w) }

/// m1gen::generate's records BEFORE its hole renaming (same anchors and assertions; the CHAIN / FIX part is left out)
pub fn m1_unperm(m: &[Row], mbit: u16) -> Vec<Row> {
    use super::m1gen::{LEN, TM, SA, SB, MBIT, gadget};
    assert!(m.len() == LEN, "ITEM 2 length {}", m.len());
    assert!(m[0] == [8, 135, 252, NONE] && m[TM - 1] == [6, BW, NONE, NONE] && m[SA] == [6, 386, NONE, NONE] && m[SB - 1] == [6, 383, NONE, NONE] && m[SB] == [6, 512, NONE, NONE], "anchors");
    assert!(m[TM..SA].iter().all(|r| !refs(r, BW)), "stash top wire referenced during run 2");
    assert!(m[SA..SB].iter().all(|r| matches!(r[0], 6 | 8 | 13) && !(r[0] == 6 && r[2] != NONE) && !(r[0] == 8 && r[3] != NONE) && !refs(r, XW)), "split records");
    if mbit == MBIT {
        for (i, r) in m.iter().enumerate() {
            let rd = (matches!(r[0], 6 | 7) && r[2] == mbit) || (matches!(r[0], 8 | 9) && r[3] == mbit) || (matches!(r[0], 3 | 4 | 5 | 15) && (r[1] == mbit || r[2] == mbit));
            assert!(!rd || i < TM, "classical bit {} is used after record {}", mbit, TM);
        }
    }
    let mut o: Vec<Row> = Vec::with_capacity(LEN + 540_000);
    o.extend_from_slice(&m[..TM]);
    o.push([12, BW, mbit, NONE]);
    o.extend_from_slice(&m[TM..SA]);
    o.extend_from_slice(&m[SA..SB]);
    gadget(&mut o);
    o.extend(m[SA..SB].iter().rev());
    o.push([8, XW, BW, NONE]);
    o.push([8, BW, XW, NONE]);
    o.push([7, BW, mbit, NONE]);
    o.extend_from_slice(&m[SA..]);
    o
}

/// (a) the fire merge on m1_unperm's stream; returns the rows and, per input position p, the number of records inserted before
/// p (as a sorted list of (position, inserted so far) at every segment boundary)
pub fn merge(o: &[Row]) -> (Vec<Row>, Vec<(usize, usize)>) {
    let seg = &tab::SEG;
    for w in seg.windows(2) { assert!(w[0].1 <= w[1].0, "i2: segments overlap"); }
    let mut out: Vec<Row> = Vec::with_capacity(o.len() + 4 * seg.len());
    let mut shift: Vec<(usize, usize)> = Vec::with_capacity(2 * seg.len());
    let mut pos = 0usize;
    for &(s, e, za, zo) in seg.iter() { let (s, e) = (s as usize, e as usize);
        // structural preconditions (exact checks on the records): the toggles op(fire, z_act) bound the segment, z_act is named by
        // no record inside, 251 is written by no record between the toggles' neighbourhood ... (the fire value at both ends is a
        // walk invariant, MEASURED by the replays)
        assert!(o[s - 1] == [8, F, za, NONE] && o[e] == [8, F, za, NONE], "i2: segment [{}, {}) is not bounded by op(251, {})", s, e, za);
        assert!(o[s..e].iter().all(|r| !refs(r, za)), "i2: z_act {} named inside [{}, {})", za, s, e);
        out.extend_from_slice(&o[pos..s]);
        out.push([8, zo, za, NONE]); out.push([13, F, za, zo]); shift.push((s, out.len() - s));
        for r in &o[s..e] { let mut q = *r; for j in 1..=nq(q[0]) { if q[j] == zo { q[j] = za; } } out.push(q); }
        out.push([13, F, za, zo]); out.push([8, zo, za, NONE]); shift.push((e, out.len() - e));
        pos = e; }
    out.extend_from_slice(&o[pos..]);
    (out, shift)
}

/// the rewrite before the hole renaming (tools and tests): fire merge + ancilla-free prologue adders; returns the rows, the merge
/// shift table and the adder conversion statistics
pub fn generate_unperm(raw: &[Row]) -> (Vec<Row>, Vec<(usize, usize)>, c0::Stats) {
    let o = m1_unperm(raw, i1::M1_MBIT);
    assert!(o.len() == UNPERM_LEN, "i2: m1gen stream length {}", o.len());
    let (o2, shift) = merge(&o);
    assert!(shift.first().map_or(true, |x| x.0 >= PRE_END), "i2: a segment starts inside the converted prologue");
    let loans: Vec<u16> = (256..504).chain(504..632).chain(115..242).chain(2..111).chain(632..637).filter(|l| !HOLE_WIRES.contains(l)).collect();
    let (o3, st) = c0::convert(&o2, &[(0, PRE_END)], C0, &loans);
    assert!(st.rejected == 0 && st.replaced == N_ADDERS && st.dropped == 0, "i2: prologue adders: found {} replaced {} rejected {} dropped {}", st.found, st.replaced, st.rejected, st.dropped);
    (o3, shift, st)
}

/// the switchable rewrite (what the builder hook calls when ON): generate_unperm, then m1gen's hole schedule with its positions
/// moved through both rewrites, then m1gen's exit fix; the free wire (m1gen's physical wire 251) is named by no record (asserted)
pub fn generate(raw: &[Row]) -> Vec<Row> {
    let (mut o, shift, st) = generate_unperm(raw);
    // position map: m1_unperm position p -> position in o.  Merge: + records inserted at segment boundaries <= p (the hole moves
    // after the inserted records); adders (all before PRE_END, so before every merge insert): moves (old start, old end, new start, new end)
    let mv = &st.moves;
    let map = |p: usize| -> usize {
        let p2 = { let k = shift.partition_point(|x| x.0 <= p); if k == 0 { p } else { p + shift[k - 1].1 } };
        let k = mv.partition_point(|m| m.0 <= p2);   // last instance starting at or before p2
        if k == 0 { return p2; }
        let m = mv[k - 1];
        if p2 >= m.1 { p2 + m.3 - m.1 } else { m.2 }   // inside an instance: its new start (checked by the free-wire assertion)
    };
    let x = CHAIN[0].1;
    let mut pi: Vec<u16> = (0..1024u16).collect();
    let mut ci = 0usize;
    assert!(CHAIN[CHAIN.len() - 1].0 as usize == UNPERM_LEN, "hole table does not match the stream");
    let chain: Vec<(usize, u16)> = CHAIN.iter().map(|c| (map(c.0 as usize), c.1)).collect();
    for w in chain.windows(2) { assert!(w[0].0 <= w[1].0, "i2: hole table out of order after the rewrite"); }
    assert!(chain[chain.len() - 1].0 == o.len(), "i2: hole table end {} vs stream {}", chain[chain.len() - 1].0, o.len());
    for i in 0..o.len() {
        while ci + 1 < chain.len() && chain[ci].0 <= i { pi.swap(chain[ci].1 as usize, chain[ci + 1].1 as usize); ci += 1; }
        let k = o[i][0];
        for j in 1..=nq(k) { o[i][j] = pi[o[i][j] as usize]; }
    }
    o.extend_from_slice(&FIX);
    for r in &o { assert!(!refs(r, x), "i2: output references the free wire"); }
    assert!(o.len() as u64 == LEN_ON, "i2: rewritten ITEM 2 length {}", o.len());
    o
}

/// the tree's hooked ITEM 2 with the switch OFF (m1gen::generate), for the tools
pub fn m1gen_off(raw: &[Row]) -> Vec<Row> { m1gen::generate(raw, i1::M1_MBIT) }
fn pack() -> Pack {
    let mut pk = Pack::parse(&lzma::decode(include_bytes!("data/pack.lzma")).expect("pack tables"));
    walkpack::apply(&mut pk);
    unrollpack::check(&pk);
    i1::w4_apply(&mut pk);
    pk
}
/// raw wire-space rows of ITEM 2 (as the builder hook receives them)
pub fn raw_rows() -> Vec<Row> {
    let pk = pack();
    let g = gir::Girs::open(include_bytes!("data/blocks.girs"));
    w2rw::item_rows(&pk, &g, 2)
}
/// ITEM 2 in wire space: (raw item rows, the tree's hooked rows = m1gen::generate(raw, M1_MBIT), wire -> physical lane map before
/// the relabelling: item wire map, then segment lane map; NONE where the wire has no lane)
pub fn wire_rows() -> (Vec<Row>, Vec<Row>, Vec<u16>) {
    let pk = pack();
    let g = gir::Girs::open(include_bytes!("data/blocks.girs"));
    let raw = w2rw::item_rows(&pk, &g, 2);
    let gen = m1gen::generate(&raw, i1::M1_MBIT);
    let it = &pk.items[2];
    let seg = pk.seg_of(it.out);
    assert!(seg == pk.seg_of(it.out + it.n - 1), "item 2 crosses a segment");
    let wm = if it.wm > 0 { Some(&pk.wire_maps[it.wm - 1]) } else { None };
    let map: Vec<u16> = (0..1024usize).map(|w| { let id = match wm { Some(m) => m[w], None => w as u16 };
        if id == NONE || id as usize >= 646 { NONE } else { pk.segs[seg].map[id as usize] } }).collect();
    (raw, gen, map)
}
/// the wire -> logical id map of ITEM 2 (NONE = unmapped)
pub fn wire_ids() -> Vec<u16> {
    let pk = Pack::parse(&lzma::decode(include_bytes!("data/pack.lzma")).expect("pack tables"));
    let it = &pk.items[2];
    let wm = if it.wm > 0 { Some(&pk.wire_maps[it.wm - 1]) } else { None };
    (0..1024usize).map(|w| match wm { Some(m) => m[w], None => w as u16 }).collect()
}
