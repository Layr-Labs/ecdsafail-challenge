//! hp1 local tools (never submitted): survey of this tree's walk regions (cut points by the op-pattern rules), the i1
//! relabelling table around them, the W4 lane patch, and the census build used by Check A.
use super::*;
use super::hybrid::{self, h, x, y, z};
use super::i1::{Relabel, HIDE};

fn seg_range(pk: &Pack, sh: &Shift, seg: usize) -> (u64, u64) {
    let (mut lo, mut hi) = (u64::MAX, 0u64);
    for p in pk.his.iter() { if p.seg != seg { continue; } let o = (p.out as i64 + sh.at(p.out)) as u64; lo = lo.min(o); hi = hi.max(o + (p.to - p.from)); }
    (lo, hi)
}

/// moves inserted by the relabelling before record p (entries at positions <= p)
pub fn moves_before(t: &Relabel, p: u64) -> u64 {
    let mut acc = 0u64; for e in t.ent.iter() { if e.0 > p { break; } acc += 2 * ((e.2 & 1) + ((e.2 >> 1) & 1)) as u64; } acc
}

/// the cut points of one walk segment by the rules (hybrid.rs module comment); returns (P_2, P_65) or (P'_65, P'_2)
fn cuts(out: &[Row], m: &[u16], lo: u64, hi: u64, fwd: bool, log: &mut String) -> (u64, u64) {
    let l = |id: usize| m[id];
    let a = [8, l(h(3)), l(h(4)), NONE]; let b = [8, l(z(0)), l(h(3)), NONE];
    let (p, q) = if fwd { (a, b) } else { (b, a) };
    let hits: Vec<u64> = (lo..hi - 1).filter(|&i| out[i as usize] == p && out[i as usize + 1] == q).collect();
    log.push_str(&format!("    pattern hits: {} (first {:?}, last {:?})\n", hits.len(), hits.first(), hits.last()));
    if fwd {
        assert!(hits.len() == 127, "forward hits {}", hits.len());
        let pk = |k: usize| hits[k - 2] + 2;
        log.push_str(&format!("    P_2 {}  P_64 {}  P_65 {}  P_80 {}  P_90 {}  (P_65 - P_2 = {})\n", pk(2), pk(64), pk(65), pk(80), pk(90), pk(65) - pk(2)));
        (pk(2), pk(65))
    } else {
        assert!(hits.len() == 127, "reverse hits {}", hits.len());
        // PUSH scopes longer than 1000 ops inside the segment range
        let mut st: Vec<u64> = Vec::new(); let mut long: Vec<(u64, u64)> = Vec::new();
        for i in lo..hi { match out[i as usize][0] { 15 => st.push(i), 16 => { if let Some(s) = st.pop() { if i - s > 1000 { long.push((s, i)); } } } _ => {} } }
        long.sort();
        log.push_str(&format!("    long PUSH scopes: {}\n", long.len()));
        let pk = |kk: usize| { let hit = hits[127 - kk]; let j = long.partition_point(|s| s.0 <= hit); long[j].1 + 1 };
        log.push_str(&format!("    P'_64 {}  P'_65 {}  P'_80 {}  P'_90 {}  P'_2 {}  (P'_2 - P'_65 = {})\n", pk(64), pk(65), pk(80), pk(90), pk(2), pk(2) - pk(65)));
        (pk(65), pk(2))
    }
}

/// hybtools survey: everything the port needs to know, printed (heavy: the full assembled list, ~19 GB)
pub fn survey() {
    let t0 = std::time::Instant::now();
    let tab = i1::table().expect("relabel table");
    let mut fl = [0usize; 4]; for e in tab.ent.iter() { fl[(e.2 & 3) as usize] += 1; }
    let to632 = tab.ent.iter().filter(|e| e.1 == HIDE).count();
    println!("RELABEL table: n {} hash {:016x} h0 {} entries {} (flags 0: {}, 1: {}, 2: {}, 3: {}); entries with target 632: {}", tab.n, tab.hash, tab.h0, tab.ent.len(), fl[0], fl[1], fl[2], fl[3], to632);
    let (pk, sh, out, n, _rt) = assemble::<Row>(false);
    let hh = hybrid::stream_hash(&out[..n]);
    println!("[{:?}] assembled list (splice off, before the relabelling): n {} hash {:016x}: table binding {}", t0.elapsed(), n, hh, if tab.n == n as u64 && tab.hash == hh { "OK (length and hash equal)" } else { "MISMATCH" });
    // segment ranges (output positions) and the W4 / lane facts
    let mut pk0 = Pack::parse(&lzma::decode(include_bytes!("data/pack.lzma")).expect("pack tables")); walkpack::apply(&mut pk0);
    for &seg in [2usize, 3, 12, 13, 14, 18, 19, 28, 29, 30].iter() {
        let (lo, hi) = seg_range(&pk, &sh, seg);
        let m = &pk.segs[seg].map; let m0 = &pk0.segs[seg].map;
        let changed = (0..646).filter(|&i| m[i] != m0[i]).collect::<Vec<_>>();
        println!("seg {seg}: his output range [{lo}, {hi}) ({} ops); id on lane 632: {}; lane of id 498: before W4 {} after {}; map entries changed by W4: {:?}",
            hi.saturating_sub(lo), pk.segs[seg].inv[632], m0[498] as i32, if m[498] == NONE { -1 } else { m[498] as i32 }, changed);
    }
    // cut points
    let mut cutv: Vec<(usize, bool, u64, u64)> = Vec::new();
    for &(seg, fwd) in [(2usize, true), (13, false), (18, true), (29, false)].iter() {
        let (lo, hi) = seg_range(&pk, &sh, seg); let mut log = String::new();
        let (s, e) = cuts(&out, &pk.segs[seg].map, lo, hi, fwd, &mut log);
        println!("WALK seg {seg} ({}): range [{s}, {e}) = {} ops\n{log}", if fwd { "forward" } else { "reverse" }, e - s);
        cutv.push((seg, fwd, s, e));
    }
    println!("REGIONS for hybrid.rs:");
    for &(seg, fwd, s, e) in cutv.iter() { println!("    Region {{ start: {s}, end: {e}, seg: {seg}, fwd: {fwd} }},"); }
    // fingerprints (the same as hybrid::check)
    for &(seg, fwd, s, e) in cutv.iter() {
        let m = &pk.segs[seg].map; let l = |id: usize| m[id]; let r = |p: u64| out[p as usize];
        let ok = if fwd { r(s - 2) == [8, l(h(3)), l(h(4)), NONE] && r(s - 1) == [8, l(z(0)), l(h(3)), NONE] && r(s) == [6, l(y(0)), NONE, NONE]
                && r(e) == [6, l(z(65)), NONE, NONE] && r(e + 1) == [13, l(z(0)), l(z(65)), l(x(0))] }
            else { r(s - 1) == [16, NONE, NONE, NONE] && r(s) == [8, l(x(192)), l(z(0)), NONE] && r(e - 1) == [16, NONE, NONE, NONE] && r(e) == [8, l(x(255)), l(z(0)), NONE] };
        println!("  fingerprints seg {seg}: {}", if ok { "OK" } else { "FAIL" });
    }
    // relabelling frames at and inside the cut ranges, and over the walk segments
    for &(seg, _fwd, s, e) in cutv.iter() {
        let (lo, hi) = seg_range(&pk, &sh, seg);
        let inside: Vec<&(u64, u16, u8)> = tab.ent.iter().filter(|en| en.0 > s && en.0 < e).collect();
        let at: Vec<&(u64, u16, u8)> = tab.ent.iter().filter(|en| en.0 == s || en.0 == e).collect();
        let inseg: Vec<&(u64, u16, u8)> = tab.ent.iter().filter(|en| en.0 >= lo && en.0 < hi).collect();
        println!("  frames seg {seg}: at segment start {} | at s {} | at e-1 {} | at e {} | segment end {}; entries strictly inside the range: {} {:?}; at s / e: {:?}; entries in the whole segment [{lo}, {hi}): {} first {:?} last {:?}",
            hybrid::frame_at(&tab, lo), hybrid::frame_at(&tab, s), hybrid::frame_at(&tab, e - 1), hybrid::frame_at(&tab, e), hybrid::frame_at(&tab, hi - 1),
            inside.len(), inside.iter().take(8).collect::<Vec<_>>(), at, inseg.len(), inseg.first(), inseg.last());
        // nearest entries around the range
        let kb = tab.ent.partition_point(|en| en.0 <= s); let ka = tab.ent.partition_point(|en| en.0 < e);
        println!("    nearest entry at/before s: {:?}; first at/after e: {:?}", if kb > 0 { Some(tab.ent[kb - 1]) } else { None }, tab.ent.get(ka));
    }
    // lanes named: his records in each range vs our generated rows (pre-relabel lanes)
    for (i, &(seg, fwd, s, e)) in cutv.iter().enumerate() {
        let mut his = vec![false; 633]; for p in s..e { let r = out[p as usize]; for j in 1..=qubits(r[0]) { his[r[j] as usize] = true; } }
        let mut ours = vec![false; 633]; let mut cnt = 0u64; let mut bits = std::collections::BTreeSet::new();
        hybrid::gen(fwd, &pk.segs[seg].map, hybrid::W0, hybrid::SCR, &mut |r| { cnt += 1; for j in 1..=qubits(r[0]) { ours[r[j] as usize] = true; }
            match r[0] { 15 => { bits.insert(r[1]); } 12 => { bits.insert(r[2]); } 4 => { bits.insert(r[1]); } 7 => if r[2] != NONE { bits.insert(r[2]); }, _ => {} } });
        let hs = hybrid::frame_at(&tab, s);
        let nh = his.iter().filter(|&&v| v).count(); let no = ours.iter().filter(|&&v| v).count();
        let only_ours: Vec<usize> = (0..633).filter(|&l| ours[l] && !his[l]).collect();
        let m = &pk.segs[seg].map; let inv = &pk.segs[seg].inv;
        let ylanes: Vec<usize> = (0..243).filter(|&k| m[y(k)] != NONE && ours[m[y(k)] as usize]).collect();
        println!("  region {i} (seg {seg}): his records name {nh} lanes, our {cnt} rows name {no} lanes (passenger ids Y{}..Y{} touched: {}); lanes only ours: {:?} (ids {:?}); our rows name 632 (logical): {}; name h_s = {}: {}; his records name h_s: {}; classical bits ours {:?}..{:?} ({} distinct)",
            ylanes.first().unwrap_or(&999), ylanes.last().unwrap_or(&999), ylanes.len(), only_ours, only_ours.iter().map(|&l| inv[l]).collect::<Vec<_>>(), ours[632], hs, ours[hs as usize], his[hs as usize], bits.iter().next(), bits.iter().last(), bits.len());
    }
    // W4 patch pieces vs the cut ranges
    let patch = include_str!("data/w4i1.patch");
    let mut froms: Vec<(u64, u16, u16)> = Vec::new();
    for line in patch.lines() { let f: Vec<&str> = line.split_whitespace().collect(); if f.len() == 4 && (f[0] == "sub" || f[0] == "resub") { froms.push((f[1].parse().unwrap(), f[2].parse().unwrap(), f[3].parse().unwrap())); } }
    for &(seg, _fwd, s, e) in cutv.iter() {
        let (mut inside, mut cross, mut before, mut after) = (0, 0, 0, 0); let mut near: Vec<String> = Vec::new();
        let mut last_before = 0u64; let mut first_after = u64::MAX;
        for &(fr, a, b) in froms.iter() { let k = match pk.his.iter().position(|p| p.from == fr) { Some(k) => k, None => continue }; let p = &pk.his[k]; if p.seg != seg { continue; }
            let o = (p.out as i64 + sh.at(p.out)) as u64; let oe = o + (p.to - p.from);
            if oe <= s { before += 1; last_before = last_before.max(oe); } else if o >= e { after += 1; first_after = first_after.min(o); }
            else if o >= s && oe <= e { inside += 1; } else { cross += 1; near.push(format!("[{o},{oe}) {a}->{b}")); } }
        println!("  W4 patch pieces in seg {seg}: before the range {before} (last ends at {last_before}, {} ops before s), inside {inside}, after {after} (first at {first_after}, {} ops after e), CROSSING a cut point {cross} {:?}",
            s.saturating_sub(last_before), first_after.saturating_sub(e), near);
    }
    // classical bits of the whole list
    let mut bu = vec![0u64; 65536];
    for r in out[..n].iter() { let bs: [u16; 2] = match r[0] { 3 | 4 | 5 => [r[1], r[2]], 6 | 7 => [r[2], NONE], 8 | 9 => [r[3], NONE], 12 => [r[2], NONE], 15 => [r[1], NONE], 18 => [r[2], NONE], _ => [NONE, NONE] };
        for b in bs { if b != NONE { bu[b as usize] += 1; } } }
    let used = bu.iter().filter(|&&v| v > 0).count(); let maxb = (0..65536).rev().find(|&b| bu[b] > 0);
    let hyb: u64 = (hybrid::W0..hybrid::W0 + 63).chain(std::iter::once(hybrid::SCR)).map(|b| bu[b as usize]).sum();
    println!("classical bits: {used} distinct used, max {:?}; uses of the hybrid bits {}..{} + {}: {hyb}; uses of 65400..65532: {}", maxb, hybrid::W0, hybrid::W0 + 62, hybrid::SCR, (65400..65533).map(|b| bu[b]).sum::<u64>());
    let maxl = out[..n].iter().map(|r| (1..=qubits(r[0])).map(|j| r[j]).max().unwrap_or(0)).max().unwrap_or(0);
    println!("highest lane named before the relabelling: {maxl}; [{:?}]", t0.elapsed());
}

/// Check A build: the un-optimised list exactly as build_slots_h(false, hyb) makes it (assemble, relabel, nonce rows),
/// plus the positions in it of the entry / re-entry points of the four regions (state before the record at that
/// position = before the relabelling moves inserted there, if any... see `moves_before`: entries AT p put their moves
/// before record p, so a mark at p means after those moves)
pub fn census_build(hyb: bool) -> (Vec<Row>, Vec<(usize, String)>, Vec<u16>) {
    let (_pk, _sh, mut out, n, rt) = assemble::<Row>(hyb);
    let lay = hybrid::layout();
    let mut pre: Vec<(u64, String)> = Vec::new();
    for (i, &(s, e, ns, nl)) in lay.iter().enumerate() {
        if hyb { pre.push((ns, format!("r{i}_in"))); pre.push((ns + nl, format!("r{i}_out"))); } else { pre.push((s, format!("r{i}_in"))); pre.push((e, format!("r{i}_out"))); } }
    let t = rt.as_ref().expect("relabel table");
    let frames: Vec<u16> = pre.iter().map(|(p, _)| hybrid::frame_at(t, *p)).collect();
    let marks: Vec<(usize, String)> = pre.iter().map(|(p, lab)| ((*p + moves_before(t, *p)) as usize, lab.clone())).collect();
    if hyb { println!("  {}", hybrid::LOG.lock().unwrap()); }
    let n = i1::apply(&mut out, n, t);
    println!("  relabelled list: {} rows (+{} move rows); FULL_632 assertion passed inside i1::apply", n, n as u64 - t.n);
    for i in 0..TAIL { out[n + i] = nonce_row(i, NONCE); }
    out.truncate(n + TAIL);
    (out, marks, frames)
}

// ---------------------------------------------------------------------------------------------------------------------
// c1 (q631 census agent, 2026-11-19; local research, never submitted; additive): the census list exactly as census_build
// makes it (= build_slots_h(false, hyb): assemble, splice when hyb, relabelling, nonce rows) plus, in ITS positions:
// every placed piece (his piece / item / scan / generated hybrid region), the segment ranges, the relabelling frames
// (position from which hidden lane c is in force) and the segment inverse maps (logical lane -> his id).
pub struct C1Build { pub rows: Vec<Row>, pub pieces: Vec<(u64, u64, u8, u32, u16)>, pub segs: Vec<(u64, u64)>, pub frames: Vec<(u64, u16)>, pub h0: u16, pub inv: Vec<Vec<u16>> }
pub fn c1_build(hyb: bool) -> C1Build {
    let (pk, sh, mut out, n, rt) = assemble::<Row>(hyb);
    let hl = i1::hook_lens(&pk);
    let at = |o: u64| (o as i64 + sh.at(o)) as u64;
    // pre-splice positions (the assembled list before the splice)
    let mut pcs: Vec<(u64, u64, u8, u32, u16)> = Vec::new();
    for (k, p) in pk.his.iter().enumerate() { let s = at(p.out); pcs.push((s, s + (p.to - p.from), 0, k as u32, p.seg as u16)); }
    for (k, it) in pk.items.iter().enumerate() { let s = at(it.out); let e = at(it.out + it.n); assert!(e - s == hl[k].unwrap_or(it.n), "c1: item {} length", k); pcs.push((s, e, 1, k as u32, pk.seg_of(it.out) as u16)); }
    for (k, sp) in pk.scans.iter().enumerate() { pcs.push((at(sp.out), at(sp.end), 2, k as u32, pk.seg_of(sp.out) as u16)); }
    let mut segs: Vec<(u64, u64)> = Vec::new(); let mut prev = 0u64;
    for s in pk.segs.iter() { segs.push((at(prev), at(s.end))); prev = s.end; }
    // splice: drop the cut ranges from every piece, add the generated regions (kind 3, index = region)
    if hyb {
        let lay = hybrid::layout();
        let mut np: Vec<(u64, u64, u8, u32, u16)> = Vec::new();
        for &(s, e, k, i, sg) in pcs.iter() {
            let mut parts = vec![(s, e)];
            for r in hybrid::REGIONS.iter() { let mut nx = Vec::new(); for &(a, b) in parts.iter() { if b <= r.start || a >= r.end { nx.push((a, b)); continue; } if a < r.start { nx.push((a, r.start)); } if b > r.end { nx.push((r.end, b)); } } parts = nx; }
            for (a, b) in parts { if b > a { np.push((hybrid::map_pos(a), hybrid::map_pos(b), k, i, sg)); } }
        }
        for (i, (r, l)) in hybrid::REGIONS.iter().zip(lay.iter()).enumerate() { np.push((l.2, l.2 + l.3, 3, i as u32, r.seg as u16)); }
        pcs = np;
        for s in segs.iter_mut() { *s = (hybrid::map_pos(s.0), hybrid::map_pos(s.1)); }
    }
    let t = rt.as_ref().expect("relabel table");
    let fin = |p: u64| p + moves_before(t, p);
    for p in pcs.iter_mut() { p.0 = fin(p.0); p.1 = fin(p.1); }
    for s in segs.iter_mut() { *s = (fin(s.0), fin(s.1)); }
    pcs.sort();
    let frames: Vec<(u64, u16)> = t.ent.iter().map(|e| (fin(e.0), e.1)).collect();
    let inv: Vec<Vec<u16>> = pk.segs.iter().map(|s| s.inv.clone()).collect();
    let h0 = t.h0;
    let n = i1::apply(&mut out, n, t);
    for i in 0..TAIL { out[n + i] = nonce_row(i, NONCE); }
    out.truncate(n + TAIL);
    C1Build { rows: out, pieces: pcs, segs, frames, h0, inv }
}

/// pre1 (2026-11-25, local research, never submitted): dump his column-1 records of walks 1 and 3 (unspliced assembled list, before the
/// relabelling) as u16 x4 little endian rows, plus the id <-> lane maps of segments 2 and 18.  Files in `dir`.
pub fn pre1_dump(dir: &str) {
    use std::io::Write;
    let (pk, sh, out, n, _rt) = assemble::<Row>(false);
    println!("assembled n {}", n);
    std::fs::create_dir_all(dir).unwrap();
    for &(seg, ri, tag) in [(2usize, 0usize, "w1"), (18, 2, "w3")].iter() {
        let (lo, _hi) = seg_range(&pk, &sh, seg); let end = hybrid::REGIONS[ri].start;
        let lo0 = if seg == 2 { 0 } else { lo };   // walk 1: dump the whole prefix [0, P_2) so a small sim can start from op 0
        println!("{tag}: dumping [{lo0}, {end})");
        println!("{tag}: seg {seg} his range lo {lo}; column 1 = [{lo}, {end}) = {} rows", end - lo);
        let mut f = std::io::BufWriter::new(std::fs::File::create(format!("{dir}/rows_{tag}.bin")).unwrap());
        for r in out[lo0 as usize..end as usize].iter() { for v in r.iter() { f.write_all(&v.to_le_bytes()).unwrap(); } }
        let mut g = std::fs::File::create(format!("{dir}/map_{tag}.txt")).unwrap();
        writeln!(g, "# start {lo} end {end}; id lane (id 0..645, lane NONE=65535), then lane id").unwrap();
        for i in 0..646 { writeln!(g, "id {} {}", i, pk.segs[seg].map[i]).unwrap(); }
        for l in 0..633 { writeln!(g, "lane {} {}", l, pk.segs[seg].inv[l] as i64).unwrap(); }
    }
}

/// pre3 (local research): the unspliced assembled list (his records, before any splice / relabelling) and the four segments' ranges
pub fn pre3_assemble() -> (Vec<Row>, usize, Vec<(usize, u64, u64)>) {
    let (pk, sh, out, n, _rt) = assemble::<Row>(false);
    let sr: Vec<(usize, u64, u64)> = [2usize, 13, 18, 29].iter().map(|&s| { let (lo, hi) = seg_range(&pk, &sh, s); (s, lo, hi) }).collect();
    (out, n, sr)
}
