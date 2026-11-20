//! (internal) ((internal), 2026-11-17): the integration layer of the t632w tree.  A child module of `point_add`.
//!
//! 1. ONE place for the switches of every 632 piece (each piece frees one lane in its own segment):
//!      HOOK_ITEM2   ITEM 2 = (internal) M1 (exact; wire 251 = lane 113 of segment 5 never referenced)          ready
//!      HOOK_ITEM10  ITEM 10 = (internal) C2cap (approximate; wire 631 = lane 631 of segment 21 never referenced) ready
//!      HOOK_ITEM12  ITEM 12 = (internal) final capped pipeline (peak 632 on its panel; rotating witness lane)  ready
//!      HOOK_ITEM4   ITEM 4  = merged block, re-derived from the original block by b5gen.rs (lane 0 of segment 8: entry / exit moves only)  ready
//!      SCAN_B_KG_OFF  scan B (segment 3) with the borrowed-lane V-chain (KG_ZERO[0] = -1): peak 632 at 13 bits   ready
//!      W4_WALKS     (internal) route B (erase id 498 at the four bracket entries, 158 clusters re-hosted, phase fix after
//!                   the small scans): lane 498 free in segments 2, 12, 13, 18, 28, 29.  REQUIRES the four 14-bit small-scan
//!                   traces in data/scans.trc ((internal); tools/mkscans.py swaps them in)                         slot (pending)
//!      RELABEL      the per-stretch physical relabelling (below), table data/relabel.lzma                         ready
//!      FULL_632     final switch: post_pass WIDTH = 632 and a syntactic assertion that no record names lane 632
//! 2. The item hooks of w2 (Shift-style: a hooked item may change length, every later piece moves), generalised to one
//!    list for all pieces (two length-changing hooks no longer need two `hook_all`s) and to small insert hooks on items that
//!    cross a segment boundary (the W4 erase / phase-fix rows).
//! 3. RELABEL: after assembly and before the builder's peephole, every record is renamed by a frame sigma_h = the
//!    transposition (632 h) of physical lanes, where h is the lane hidden on lane 632 in that stretch.  h changes at the
//!    table's positions; h is always a lane that is zero (on the planner's sample) and that no record of the stretch names,
//!    so lane 632 is unreferenced in the stretch.  At a change h -> c the value of lane 632's own data, which lives on lane
//!    h, is moved to lane c with two CX (flag of the entry; never needed when h or c is 632 itself).  Scans keep their
//!    levers because the renaming acts on the expanded rows (no range rows, `fixed` stays false).  Where the planner found
//!    no free lane (a "gap": all 633 lanes live or named) the frame stays and the record names lane 632: those are exactly
//!    the binding stretches of the pieces that are not integrated yet.  The planner is `i1census` (route tool, not in the
//!    package); the table records the length and a hash of the stream it was planned on and the builder asserts both.
use super::*;

pub const HOOK_ITEM2: bool = true;
pub const HOOK_ITEM10: bool = true;
pub const HOOK_ITEM12: bool = true;
pub const HOOK_ITEM4: bool = true;
pub const SCAN_B_KG_OFF: bool = true;
pub const W4_WALKS: bool = true;
pub const RELABEL: bool = true;
pub const FULL_632: bool = true;
/// second-round totals asserted by post_pass::build_final (the package's own build path) and by stream_build: they must be
/// the FINAL stream's totals (set by mk_t632w.sh R2EXPECT=..., read from the first build's log), never left at the parent's
pub const R2_EXPECT: [u64; 7] = [0,0,0,213507,77,99,176];

/// KG_ZERO of the tree (mod.rs uses this one): scan B's Khattar-Gidney zero lane off when SCAN_B_KG_OFF
pub const KG_ZERO: [i32; 8] = [if SCAN_B_KG_OFF { -1 } else { 249 }, 226, 235, -1, 214, 230, 230, -1];
/// classical bit of M1's extra measurement (the item's own first Hmr bit; i1census checks that no other piece reads it)
pub const M1_MBIT: u16 = 10884;
/// (internal)'s final pipeline for ITEM 12
pub const ITEM12_SPEC: &str = "cap:244,68581537,68649734;cap:244,68418620,68579271;cap:251,41087759,41155903;negxall:251;ctr:87;pad;negxall:246,244;fold;apply:20";   // (internal) final (capped count: about +0.18 failing shots / 9,024)
const FOLD_SEL_12: &str = include_str!("data/fold_item12.sel");
/// (internal) witness cover of the `apply` step (section 0b): wire 20 hosted on the stretch witnesses, never named inside the item
const WITNESS_12: &str = include_str!("data/witness_item12.txt");
/// W4: erase rows [12, 498, bit] appended at the END of items 0, 6, 8, 14 (next to their 13 erase Hmr rows) and the phase fix
/// [7, 498, bit] at offset 0 of items 1, 7, 9, 15 (right after the small scans B, I, B', I').  Bits: w4's proposal, MEASURED free
/// in the base stream ((internal) logs/bits-zc2-bp2-s632.tsv).  Items 0..15 of this list have wire map 0 (logical ids).
pub const W4_ERASE: [(usize, u16); 4] = [(0, 11887), (6, 11888), (8, 11889), (14, 11890)];
pub const W4_FIX: [(usize, u16); 4] = [(1, 11887), (7, 11888), (9, 11889), (15, 11890)];
pub const W4_ID: u16 = 498;
/// W4 per bracket (a 14-bit scan is valid only when the erase of its bracket is in): bracket k = (erase item, segments, fix item):
/// 1 = item 0 -> walk 1 (seg 2) -> scan B (3) / item 1;  2 = item 6 -> stage + walk 2 (12, 13) -> scan I (14) / item 7;
/// 3 = item 8 -> walk 3 (18) -> scan B' (19) / item 9;  4 = item 14 -> stage + walk 4 (28, 29) -> scan I' (30) / item 15.
/// The scan of an enabled bracket MUST be the 14-bit trace (SCANS), the scan of a disabled one the 13-bit trace.
pub const W4_BRACKET3: bool = true;
pub const W4_BRACKETS: [bool; 4] = [true, true, W4_BRACKET3, true];
/// scan B' (index 4) through (internal)'s native expander bp_scan.rs (KG off, carry host 214 freed); needs its native 14-bit
/// trace in SCANS 4=... and W4_BRACKET3
pub const BP_NATIVE: bool = true;
const W4_SEGS: [&[usize]; 4] = [&[2], &[12, 13], &[18], &[28, 29]];

/// one hooked item: replacement rows (wire space); `ins` = output indices of inserted rows (insert hooks only: their
/// segment is taken from the raw position, so the item may cross a segment boundary)
pub struct Hooked { pub rows: Vec<Row>, pub ins: Vec<usize>, pub lane_space: bool }

pub fn hook_sel(pk: &Pack, want: &dyn Fn(usize) -> bool) -> Vec<Option<Hooked>> {
    let g = gir::Girs::open(include_bytes!("data/blocks.girs"));
    let mut v: Vec<Option<Hooked>> = (0..pk.items.len()).map(|_| None).collect();
    let one_seg = |ii: usize| { let it = &pk.items[ii]; assert!(pk.seg_of(it.out) == pk.seg_of(it.out + it.n - 1), "hooked item {} crosses a segment", ii); };
    if HOOK_ITEM2 && want(2) { one_seg(2); let raw = w2rw::item_rows(pk, &g, 2); v[2] = Some(Hooked { rows: tap::item(2, || m1gen::generate(&raw, M1_MBIT)), ins: Vec::new(), lane_space: false }); }
    if HOOK_ITEM10 && want(10) { one_seg(10); let raw = w2rw::item_rows(pk, &g, 10); v[10] = Some(Hooked { rows: tap::item(10, || c2capgen::generate(&raw)), ins: Vec::new(), lane_space: false }); }
    if HOOK_ITEM12 && want(12) { one_seg(12); let raw = w2rw::item_rows(pk, &g, 12);
        c3::FOLD_PIVOTS.with(|p| *p.borrow_mut() = Some(FOLD_SEL_12.split_whitespace().map(|x| x.parse().unwrap()).collect()));
        if ITEM12_SPEC.contains("apply") { c3::APPLY_COVER.with(|p| *p.borrow_mut() = Some(c3::parse_cover(WITNESS_12))); }
        v[12] = Some(Hooked { rows: tap::item(12, || w2rw::rewrite(12, ITEM12_SPEC, raw, &[]).0), ins: Vec::new(), lane_space: false }); }
    if HOOK_ITEM4 && want(4) { one_seg(4); let raw = w2rw::item_rows(pk, &g, 4);
        let mut rows4 = tap::item(4, || b5gen::generate(&raw)); tap::rehost(pk, 4, &mut rows4);
        v[4] = Some(Hooked { rows: rows4, ins: Vec::new(), lane_space: false }); }
    if W4_WALKS && want(usize::MAX) {
        let mut add = |ii: usize, at_end: bool, row: Row| { assert!(pk.items[ii].wm == 0, "W4 insert on item {}", ii);
            let (mut rows, mut ins) = match v[ii].take() { Some(h) => (h.rows, h.ins), None => (w2rw::item_rows(pk, &g, ii), Vec::new()) }; let j = if at_end { rows.len() } else { let mut st = 0usize; while st < ins.len() && ins[st] == st { st += 1; } if st == ins.len() && rows.len() == ins.len() { st = ins.iter().filter(|&&x| x < rows.len()).count().min(st); } st }; for x in ins.iter_mut() { if *x >= j { *x += 1; } } rows.insert(j, row); let q = ins.partition_point(|&x| x < j); ins.insert(q, j); v[ii] = Some(Hooked { rows, ins, lane_space: false }); };
        for k in 0..4 { if !W4_BRACKETS[k] { continue; } let (ii, b) = W4_ERASE[k]; add(ii, true, [12, W4_ID, b, NONE]); let (ij, b2) = W4_FIX[k]; add(ij, false, [7, W4_ID, b2, NONE]);
            if let Some(b4) = tap::erase497(k) { add(ii, true, [12, 497, b4, NONE]); if !tap::nofix() { add(ij, false, [7, 497, b4, NONE]); } } }
        for (id, bit, e, r) in tap::glue() { add(e, true, [12, id, bit, NONE]); if r != usize::MAX { add(r, false, [7, id, bit, NONE]); } }
    }
    v
}

/// emit a hooked item through its wire map and the segment lane maps, in output order: put(segment, lane row)
pub fn emit_hooked(pk: &Pack, ii: usize, h: &Hooked, put: &mut dyn FnMut(usize, Row)) {
    let it = &pk.items[ii]; assert!(it.wm != RANGES, "hooked item with range rows");
    let wm = if it.wm > 0 { Some(&pk.wire_maps[it.wm - 1]) } else { None };
    let mut seg = pk.seg_of(it.out); let mut k = 0usize;
    for (j, &r) in h.rows.iter().enumerate() {
        if !h.ins.is_empty() { while k < h.ins.len() && h.ins[k] < j { k += 1; } let raw = it.out + ((j - k) as u64).min(it.n - 1); while raw >= pk.segs[seg].end { seg += 1; } }
        if h.lane_space { put(seg, r); continue; }
        let mut row = r; if let Some(w) = wm { for q in 1..=qubits(row[0]) { row[q] = w[row[q] as usize]; } }
        put(seg, map_lanes(row, &pk.segs[seg].map)); }
}

/// W4 lane table without the six `map S <helper id> 498` lines of (internal)' patch: the relabelling hides the freed lane 498
/// instead (same effect, and the boundary moves of id 632 that w4's map change needed are then the relabelling's own moves)
pub fn w4_apply(pk: &mut Pack) { if !W4_WALKS { return; }
    // keep only the lines of the enabled brackets (split / sub / resub by the segment of the his piece at that input position)
    let keep = |seg: usize| (0..4).any(|k| W4_BRACKETS[k] && W4_SEGS[k].contains(&seg));
    let mut t = String::new();
    for line in include_str!("data/w4i1.patch").lines() { let f: Vec<&str> = line.split_whitespace().collect();
        let ok = match f.first() { Some(&"split") | Some(&"sub") | Some(&"resub") => { let x: u64 = f[1].parse().unwrap(); let k = pk.piece_of(x).expect("w4 line outside the pieces"); keep(pk.his[k].seg) }
            Some(&"map") => keep(f[1].parse().unwrap()), _ => true };
        if ok { t.push_str(line); t.push_str("\n"); } }
    w4patch::apply(pk, &t); }

/// every hook (census and tools); the builder uses with_hooks
pub fn hook_all(pk: &Pack) -> Vec<Option<Hooked>> { hook_sel(pk, &|_| true) }
/// fixed lengths of the hooked items (the builder allocates the slot vector before the hooks are generated; check_hook_lens asserts)
pub const HOOK_LEN: [(usize, u64); 4] = [(2, 61_903_460), (10, 76_908_465), (12, 110_554_500), (4, 115_733_065)];
pub fn hook_lens(pk: &Pack) -> Vec<Option<u64>> {
    let mut v: Vec<Option<u64>> = vec![None; pk.items.len()];
    for &(ii, l) in HOOK_LEN.iter() { if (ii == 2 && HOOK_ITEM2) || (ii == 10 && HOOK_ITEM10) || (ii == 12 && HOOK_ITEM12) || (ii == 4 && HOOK_ITEM4) { v[ii] = Some(tap::len_override(ii, l).unwrap_or(l)); } }
    if W4_WALKS { for k in 0..4 { if W4_BRACKETS[k] { for ii in [W4_ERASE[k].0, W4_FIX[k].0] { v[ii] = Some(pk.items[ii].n + 1 + (tap::erase497(k).is_some() && !(tap::nofix() && ii == W4_FIX[k].0)) as u64); } } } }
    { let mut inc = vec![0u64; pk.items.len()]; for (_, _, e, r) in tap::glue() { inc[e] += 1; if r != usize::MAX { inc[r] += 1; } }
      for ii in 0..pk.items.len() { if inc[ii] > 0 { v[ii] = Some(v[ii].unwrap_or(pk.items[ii].n) + inc[ii]); } } }
    v }
pub fn check_hook_lens(h: &[Option<Hooked>], l: &[Option<u64>]) {
    for (ii, (a, b)) in h.iter().zip(l.iter()).enumerate() { assert!(a.as_ref().map(|x| x.rows.len() as u64) == *b, "hooked item {}: length differs from i1::HOOK_LEN", ii); } }
/// generate the hooks on helper threads (one per large item, one for the small inserts; thread-local state is per thread) while
/// `main` runs on the calling thread; a helper that cannot be spawned is run on the calling thread afterwards
pub fn with_hooks<R>(pk: &Pack, main: impl FnOnce() -> R) -> (R, Vec<Option<Hooked>>) {
    let groups: Vec<Vec<usize>> = vec![vec![12], vec![4], vec![10], vec![2], vec![usize::MAX]];
    std::thread::scope(|sc| {
        let hs: Vec<_> = groups.iter().map(|gr| { let gr = gr.clone(); std::thread::Builder::new().stack_size(256 << 20).spawn_scoped(sc, move || hook_sel(pk, &|k| gr.contains(&k))).ok() }).collect();
        let r = main();
        let mut v: Vec<Option<Hooked>> = (0..pk.items.len()).map(|_| None).collect();
        for (gi, h) in hs.into_iter().enumerate() {
            let part = match h { Some(h) => h.join().expect("hook thread"), None => { let gr = &groups[gi]; hook_sel(pk, &|k| gr.contains(&k)) } };
            for (i, x) in part.into_iter().enumerate() { if x.is_some() { v[i] = x; } } }
        (r, v)
    })
}
/// run `f(chunk, first index)` over `xs` in chunks on all cores (the calling thread works too; no helper is required)
pub fn par_chunks<T: Send>(xs: &mut [T], f: &(dyn Fn(&mut [T], usize) + Sync)) {
    let nt = std::thread::available_parallelism().map(|v| v.get()).unwrap_or(1).max(1);
    let cs = (xs.len() / (4 * nt)).max(1 << 20);
    let work: std::sync::Mutex<Vec<(usize, &mut [T])>> = std::sync::Mutex::new(xs.chunks_mut(cs).enumerate().map(|(i, c)| (i * cs, c)).rev().collect());
    let job = || loop { let c = work.lock().unwrap().pop(); match c { Some((b, c)) => f(c, b), None => break } };
    std::thread::scope(|sc| { for _ in 1..nt { if std::thread::Builder::new().spawn_scoped(sc, &job).is_err() { break; } } job(); });
}

// ---------------------------------------------------------------- relabelling
pub const HIDE: u16 = 632;
/// entry (pos, c, flags): before record pos the hidden lane becomes c.  flags bit 0: move lane 632's data from lane h (the
/// previous hidden lane) to lane c (2 CX); bit 1 (leaving a gap, where lane 632 physically holds data): move the content of
/// physical lane 632 to lane h (or to c when h = 632) (2 CX that name lane 632; only ever emitted inside a gap)
pub struct Relabel { pub n: u64, pub hash: u64, pub h0: u16, pub ent: Vec<(u64, u16, u8)> }
/// the move rows of one entry, in stream order (physical lanes)
pub fn moves(hp: u16, c: u16, f: u8) -> Vec<Row> { let mut v = Vec::new();
    if f & 1 == 1 { assert!(hp != HIDE && c != HIDE, "relabel move"); v.push([8, hp, c, NONE]); v.push([8, c, hp, NONE]); }
    if f & 2 == 2 { let t = if hp == HIDE { c } else { hp }; assert!(t != HIDE); v.push([8, HIDE, t, NONE]); v.push([8, t, HIDE, NONE]); }
    v }
fn varint(d: &[u8], p: &mut usize) -> u64 { let mut v = 0u64; let mut s = 0; loop { let b = d[*p]; *p += 1; v |= ((b & 127) as u64) << s; if b < 128 { return v; } s += 7; } }
pub fn parse_table(d: &[u8]) -> Relabel {
    assert!(&d[..8] == b"I1RELAB1", "relabel table"); let u64at = |p: usize| u64::from_le_bytes(d[p..p + 8].try_into().unwrap());
    let n = u64at(8); let hash = u64at(16); let h0 = u16::from_le_bytes([d[24], d[25]]); let m = u32::from_le_bytes(d[26..30].try_into().unwrap()) as usize;
    let mut p = 30usize; let mut pos = 0u64; let mut ent = Vec::with_capacity(m);
    for _ in 0..m { pos += varint(d, &mut p); let c = u16::from_le_bytes([d[p], d[p + 1]]); let f = d[p + 2]; p += 3; ent.push((pos, c, f)); }
    assert!(p == d.len(), "relabel table length"); Relabel { n, hash, h0, ent }
}
pub fn table() -> Option<Relabel> {
    if let Some(d) = tap::table_override(1) { return Some(parse_table(&d)); }
    if !RELABEL { return None; } let d = lzma::decode(include_bytes!("data/relabel.lzma")).expect("relabel table");
    if d.len() <= 8 { return None; } Some(parse_table(&d))
}
pub fn extra(t: &Option<Relabel>) -> usize { t.as_ref().map_or(0, |t| t.ent.iter().map(|e| 2 * ((e.2 & 1) + ((e.2 >> 1) & 1)) as usize).sum()) }
#[inline] pub fn sigma(mut r: Row, h: u16) -> Row { if h == HIDE { return r; }
    let f = |l: u16| if l == HIDE { h } else if l == h { HIDE } else { l }; for j in 1..=qubits(r[0]) { r[j] = f(r[j]); } if r[0] == 2 { r[2] = f(r[2]); } r }
#[inline] pub fn row_key(r: Row) -> u64 { (r[0] as u64) | (r[1] as u64) << 16 | (r[2] as u64) << 32 | (r[3] as u64) << 48 }
#[inline] pub fn hash_step(h: u64, r: Row) -> u64 { let x = (h ^ row_key(r)).wrapping_mul(0x9E3779B97F4A7C15); x ^ (x >> 29) }
pub const HASH0: u64 = 0x243F6A8885A308D3;
/// rows that name a physical lane
#[inline] pub fn names(r: &Row, l: u16) -> bool { (1..=qubits(r[0])).any(|j| r[j] == l) || (r[0] == 2 && r[2] == l) }

/// in place: out[..n] -> relabelled stream of n + extra rows (moves inserted); returns the new length
pub fn moves_top(hp: u16, c: u16, f: u8, top: u16) -> Vec<Row> { let mut v = Vec::new();
    if f & 1 == 1 { assert!(hp != top && c != top, "relabel move"); v.push([8, hp, c, NONE]); v.push([8, c, hp, NONE]); }
    if f & 2 == 2 { let t = if hp == top { c } else { hp }; assert!(t != top); v.push([8, top, t, NONE]); v.push([8, t, top, NONE]); }
    v }
#[inline] pub fn sigma_top(mut r: Row, h: u16, top: u16) -> Row { if h == top { return r; }
    let f = |l: u16| if l == top { h } else if l == h { top } else { l }; for j in 1..=qubits(r[0]) { r[j] = f(r[j]); } if r[0] == 2 { r[2] = f(r[2]); } r }
pub fn table2() -> Option<Relabel> { if let Some(d) = tap::table_override(2) { return Some(parse_table(&d)); }
    let d = lzma::decode(include_bytes!("data/relabel2.lzma")).expect("second relabel table"); Some(parse_table(&d)) }
pub fn apply<S: Slot + Send>(out: &mut [S], n: usize, t: &Relabel) -> usize { apply_top(out, n, t, HIDE) }
pub fn apply_top<S: Slot + Send>(out: &mut [S], n: usize, t: &Relabel, top: u16) -> usize {
    let mut h = HASH0; for s in &out[..n] { h = hash_step(h, s.to_row()); }
    assert!(t.n == n as u64 && t.hash == h, "relabel table was planned on another stream (table n {} hash {:016x}, stream n {} hash {:016x}): rerun i1census", t.n, t.hash, n, h);
    let m = t.ent.len(); let hid = |k: usize| if k == 0 { t.h0 } else { t.ent[k - 1].1 };
    let mvs: Vec<Vec<Row>> = (0..m).map(|k| moves_top(hid(k), t.ent[k].1, t.ent[k].2, top)).collect();
    let total = n + mvs.iter().map(|v| v.len()).sum::<usize>(); assert!(out.len() >= total);
    // 1. rename every record in place with the frame of its stretch (all cores)
    par_chunks(&mut out[..n], &|c: &mut [S], b: usize| { let mut k = t.ent.partition_point(|e| e.0 <= b as u64); let mut hh = hid(k);
        for (o, x) in c.iter_mut().enumerate() { let i = (b + o) as u64; while k < m && t.ent[k].0 <= i { hh = t.ent[k].1; k += 1; } *x = S::from_row(sigma_top(x.to_row(), hh, top)); } });
    // 2. top down: move each stretch up by the moves before it, then write the moves of its entry just in front of it
    let mut off: Vec<usize> = Vec::with_capacity(m); let mut acc = 0usize; for v in &mvs { acc += v.len(); off.push(acc); }
    for k in (0..m).rev() { let start = t.ent[k].0 as usize; let end = if k + 1 < m { t.ent[k + 1].0 as usize } else { n }; assert!(start <= end && end <= n);
        if end > start && off[k] > 0 { out.copy_within(start..end, start + off[k]); }
        let base = start + off[k] - mvs[k].len(); for (q, r) in mvs[k].iter().enumerate() { out[base + q] = S::from_row(*r); } }
    if FULL_632 { let bad = std::sync::atomic::AtomicUsize::new(0);
        par_chunks(&mut out[..total], &|c: &mut [S], _b: usize| { let x = c.iter().filter(|s| names(&s.to_row(), top)).count(); bad.fetch_add(x, std::sync::atomic::Ordering::Relaxed); });
        assert!(bad.into_inner() == 0, "FULL_632: records name lane {} after the relabelling", top); }
    total
}
