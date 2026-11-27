//! q631 / i12 (local research, 2026-11-19; NOT part of any package): ITEM 12 (item 12, segment 25, the second divide, n = 127).
//! Switch `ON` = false: nothing in the builder calls this module while it is off (the build is unchanged).
//! Tools: `wire12()` = ITEM 12 in WIRE space (raw block with inserts placed, then the rows after every step of
//! i1::ITEM12_SPEC, and the wire -> logical lane map = item wire map then the segment lane map).
use super::*;

pub const ON: bool = false;
/// the ITEM 12 rewrite on census-frame rows (walks re-emitted; self-contained so local tools include it by path)
#[path = "i12w.rs"]
#[allow(dead_code)]
pub mod w;

pub struct Item12W { pub raw: Vec<Row>, pub map: Vec<u16>, pub item_out: u64, pub item_n: u64, pub seg: usize, pub inv: Vec<u16> }

/// the raw block of ITEM 12 and its wire -> lane map (no rewrite step applied)
pub fn wire12() -> Item12W {
    let mut pk = Pack::parse(&lzma::decode(include_bytes!("data/pack.lzma")).expect("pack tables"));
    walkpack::apply(&mut pk);
    unrollpack::check(&pk);
    i1::w4_apply(&mut pk);
    let g = gir::Girs::open(include_bytes!("data/blocks.girs"));
    let raw = w2rw::item_rows(&pk, &g, 12);
    let it = &pk.items[12];
    let seg = pk.seg_of(it.out);
    assert!(seg == pk.seg_of(it.out + it.n - 1), "item 12 crosses a segment");
    let wm = if it.wm > 0 { Some(&pk.wire_maps[it.wm - 1]) } else { None };
    let map: Vec<u16> = (0..1024usize).map(|w| { let id = match wm { Some(m) => m[w], None => w as u16 };
        if id == NONE || id as usize >= 646 { NONE } else { pk.segs[seg].map[id as usize] } }).collect();
    Item12W { raw, map, item_out: it.out, item_n: it.n, seg, inv: pk.segs[seg].inv.clone() }
}

/// apply the steps of i1::ITEM12_SPEC one by one (same thread-local set-up as i1::hook_sel); `f(step name, rows)` after each
pub fn pipeline12(raw: Vec<Row>, f: &mut dyn FnMut(&str, &[Row])) -> Vec<Row> {
    c3::FOLD_PIVOTS.with(|p| *p.borrow_mut() = Some(include_str!("data/fold_item12.sel").split_whitespace().map(|x| x.parse().unwrap()).collect()));
    c3::APPLY_COVER.with(|p| *p.borrow_mut() = Some(c3::parse_cover(include_str!("data/witness_item12.txt"))));
    let mut rows = raw;
    for step in i1::ITEM12_SPEC.split(';') {
        let (r, info) = w2rw::rewrite(12, step, rows, &[]); rows = r;
        for n in &info.notes { eprintln!("i12 pipeline step {}: {}", step, n); }
        f(step, &rows);
    }
    rows
}

/// ITEM 12 in the relabelled census list (hybrid ON; hybtools::c1_build(true)), measured by i12dump (q631/i12/dump/item12_meta.txt)
pub const ITEM12_START: usize = 1_665_416_701;
pub const ITEM12_END: usize = 1_775_971_205;
/// the full ITEM 12 rewrite behind the switch: walks (w::SEL: inner Inner{real 1}, outer RevRelay{real 2, guard 7}, peephole), the
/// two G1 windows (lane 258 freed), R1 (lane 241 freed over the alpha core) and the phase B adder conversion (lane 257 freed)
pub const GSEL: w::g1::Sel = w::g1::Sel { ipark: true, unpark: true, astart: true };
pub const ALPHA_R1: bool = true;
pub const PHASE_B: bool = true;
/// hook for a 631 build (NOT called by the builder; the integrator calls it after the relabelling, like q631::apply_item4, and must
/// re-plan the relabel table so that the hidden lane sits on the freed lanes of w::Stats.freed / g1 stretches): replaces out[s..e)
/// (the relabelled ITEM 12 rows) by the rewritten block; returns the new list length
pub fn apply_item12<S: Slot>(out: &mut Vec<S>, n: usize, s: usize, e: usize) -> usize {
    assert!(ON, "i12: the ITEM 12 rewrite is switched off");
    let rows: Vec<Row> = out[s..e].iter().map(|x| x.to_row()).collect();
    let (r, _st, _gs, _cs) = w::rewrite_full(&rows, w::SEL, GSEL, ALPHA_R1, PHASE_B);
    drop(rows);
    let delta = r.len() - (e - s); let nn = n + delta; let need = nn + TAIL;
    if out.len() < need { out.resize(need, S::empty()); }
    out.copy_within(e..n, e + delta);
    for (i, x) in r.iter().enumerate() { out[s + i] = S::from_row(*x); }
    nn
}
