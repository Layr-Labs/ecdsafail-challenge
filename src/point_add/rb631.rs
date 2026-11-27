//! q631 / rb (agent rb1, 2026-11-19; LOCAL RESEARCH, never part of a package): the two REVERSE walk brackets with a 15th
//! erased bit, id 497 (= Y241).
//!   bracket 2 = item 6 (W4 erase row of id 498, bit 11888) -> segments 11, 12, 13 (stage + walk 2 + U rebuild) -> scan I
//!               (scan 3) -> item 7 (W4 phase fix, bit 11888 at offset 0);
//!   bracket 4 = item 14 (bit 11890) -> segments 27, 28, 29 -> scan I' (scan 7) -> item 15 (bit 11890).
//! THE SWITCH: `ON` (false) or the runtime `FORCE` (local tools).  Off = nothing here is called; the build is unchanged.
//! On (needs the hybrid splice): `apply` edits the FINAL relabelled list (after i1::apply and after the q631 rewrites, before
//! rp1 and the peephole), so every piece placed by position before it (hybrid / cf631 regions, the relabelling table, the
//! q631 ITEM 4 / ITEM 12 ranges) is untouched:
//!   1. Hmr of id 497 into a fresh classical bit right after the W4 erase row of brackets 2 and 4;
//!   2. every record of [bracket entry, scan start) that names the lane of id 497 is renamed onto a host lane that no record
//!      of its cluster window names (table data/rb631_moves.txt, positions relative to the W4 erase row, window content
//!      hash asserted, as the relabelling table is bound);
//!   3. scans I / I' replaced by their 15-bit traces (si631::si_trace), expanded with the classical state the list's own
//!      14-bit expansion had (asserted: the list range equals the 14-bit expansion under its frames), renamed by the frame
//!      in force; the frame switch inside the scan (hidden lane 498 -> none, no move) re-placed at the first record that
//!      names logical lane 498, the rule the shipped table follows (asserted on the 14-bit expansion);
//!   4. conditioned Z on id 497 right after the W4 phase-fix row (after the scan).
use super::*;
use std::sync::atomic::{AtomicBool, Ordering};
use std::fmt::Write as _;

pub const ON: bool = super::FINAL631;
pub static FORCE: AtomicBool = AtomicBool::new(false);
pub fn active() -> bool { ON || FORCE.load(Ordering::Relaxed) }

/// the 15th erased id and its lane
pub const ID: u16 = 497;
/// per reverse bracket: (W4 bracket index into i1::W4_ERASE / W4_FIX, scan index, segments)
pub const BRACKETS: [(usize, usize, [usize; 2]); 2] = [(1, 3, [12, 13]), (3, 7, [28, 29])];

#[inline] fn nq(k: u16) -> usize { qubits(k) }
/// classical bits a row reads or writes
fn bits_of(r: &Row) -> [u16; 2] { match r[0] { 3 | 4 | 5 => [r[1], r[2]], 6 | 7 => [r[2], NONE], 8 | 9 => [r[3], NONE], 12 => [r[2], NONE], 15 => [r[1], NONE], 18 => [r[2], NONE], _ => [NONE, NONE] } }
#[inline] fn sig(l: u16, h: u16) -> u16 { if h == i1::HIDE { l } else if l == i1::HIDE { h } else if l == h { i1::HIDE } else { l } }

/// the pack exactly as assemble_c prepares it (no list)
pub fn pack() -> Pack {
    let mut pk = Pack::parse(&lzma::decode(include_bytes!("data/pack.lzma")).expect("pack tables"));
    walkpack::apply(&mut pk); unrollpack::check(&pk); i1::w4_apply(&mut pk); pk
}
/// the trace scan_rows expands for scan i (all three hooks, in its order)
pub fn list_trace(i: usize) -> Vec<u8> { bs631::trace_for(i, si631::trace_for(i, scq631::trace_for(i, scq631::shipped_trace(i)))) }
fn run_one(pk: &Pack, i: usize, trace: &[u8], cls: &mut scan::Classical, put: &mut dyn FnMut(Row)) {
    let sp = &pk.scans[i];
    let k0 = pk.wmr.partition_point(|x| x.0 < sp.out); let ranged = k0 < pk.wmr.len() && pk.wmr[k0].0 == sp.out;
    let ins = pk.ins_of(true, i); let fixed = ranged || !ins.is_empty();
    vm::TOP_BIT.with(|t| t.set(!fixed));
    if i == 0 { borrow_scan::run(trace, sp.bit0, cls, put, KG_ZERO[i]); }
    else if i == 4 && i1::BP_NATIVE { bp_scan::run(trace, sp.bit0, cls, put, -1, 214, true); }
    else if fixed { scan::run(trace, sp.bit0, cls, put, KG_ZERO[i]); }
    else { opt_scan::run(trace, sp.bit0, cls, put, KG_ZERO[i], true); }
    vm::TOP_BIT.with(|t| t.set(false));
}
/// classical layer state at the entry of scan i, as scan_rows has it (scans 0..i-1 with the list's traces)
pub fn cls_before(pk: &Pack, i: usize) -> scan::Classical {
    let mut cls = scan::Classical::new();
    for j in 0..i { let tr = list_trace(j); let mut sink = |_r: Row| {}; run_one(pk, j, &tr, &mut cls, &mut sink); }
    cls }
fn nexts(c: &scan::Classical) -> [usize; 3] { [c.cl[0].next, c.cl[1].next, c.cl[2].next] }
fn set_nexts(c: &mut scan::Classical, v: [usize; 3]) { for k in 0..3 { c.cl[k].next = v[k]; } }
/// (14-bit rows as the list has them, 15-bit rows), LOGICAL lanes, both from the classical state of the list at the scan's
/// entry; + the classical allocator positions (before, after 14, after 15)
pub fn scan_pair(pk: &Pack, i: usize) -> (Vec<Row>, Vec<Row>, [[usize; 3]; 3]) {
    let mut cls = cls_before(pk, i); let n0 = nexts(&cls);
    let r14 = si631::expand_with(pk, i, &list_trace(i), &mut cls); let n14 = nexts(&cls);
    set_nexts(&mut cls, n0);
    let r15 = si631::expand_with(pk, i, &si631::si_trace(i), &mut cls); let n15 = nexts(&cls);
    (r14, r15, [n0, n14, n15]) }

/// both scans in one pass of the classical layer: [(r14, r15, allocators) of scan 3, of scan 7]; the scans between them run with
/// the 14-bit state (the list's), and the allocator positions after the 15-bit expansion are asserted equal to the 14-bit ones
pub fn scan_pairs(pk: &Pack) -> [(Vec<Row>, Vec<Row>, [[usize; 3]; 3]); 2] {
    let mut cls = scan::Classical::new(); let mut res: Vec<(Vec<Row>, Vec<Row>, [[usize; 3]; 3])> = Vec::new();
    for j in 0..8 {
        if j == 3 || j == 7 {
            let n0 = nexts(&cls);
            let r14 = si631::expand_with(pk, j, &list_trace(j), &mut cls); let n14 = nexts(&cls);
            set_nexts(&mut cls, n0);
            let r15 = si631::expand_with(pk, j, &si631::si_trace(j), &mut cls); let n15 = nexts(&cls);
            set_nexts(&mut cls, n14);
            res.push((r14, r15, [n0, n14, n15]));
            if j == 7 { break; }
        } else { let tr = list_trace(j); let mut sink = |_r: Row| {}; run_one(pk, j, &tr, &mut cls, &mut sink); }
    }
    let b = res.pop().unwrap(); let a = res.pop().unwrap(); [a, b]
}

/// first use of each bit of `bits` in the row stream: 1 = a pure write (Hmr into it, or an unconditional store, outside any
/// PUSH scope), 2 = anything else (a read), 0 = not used
pub fn first_uses(rows: impl Iterator<Item = Row>, bits: &[u16]) -> Vec<u8> {
    let mut res = vec![0u8; bits.len()]; let mut left = bits.len();
    let idx: std::collections::HashMap<u16, usize> = bits.iter().enumerate().map(|(j, &b)| (b, j)).collect();
    let mut depth = 0i64;
    for r in rows { if left == 0 { break; }
        for x in bits_of(&r) { if x == NONE { continue; } if let Some(&j) = idx.get(&x) { if res[j] == 0 {
            let pure = depth == 0 && ((r[0] == 12 && r[2] == x) || ((r[0] == 4 || r[0] == 5) && r[1] == x && r[2] == NONE));
            res[j] = if pure { 1 } else { 2 }; left -= 1; } } }
        match r[0] { 15 => depth += 1, 16 => depth -= 1, _ => {} } }
    res }

/// the classical bits a row stream writes (xor / store targets, measurement results)
pub fn written(rows: impl Iterator<Item = Row>) -> std::collections::HashSet<u16> {
    let mut w = std::collections::HashSet::new();
    for r in rows { match r[0] { 3 | 4 | 5 => { w.insert(r[1]); } 12 => { if r[2] != NONE { w.insert(r[2]); } } _ => {} } } w }
/// per bit: is its LAST use in the stream an unconditional clear (BitStore0 outside any PUSH scope)?
pub fn last_clear(rows: impl Iterator<Item = Row>, bits: &[u16]) -> Vec<bool> {
    let idx: std::collections::HashMap<u16, usize> = bits.iter().enumerate().map(|(j, &b)| (b, j)).collect();
    let mut res = vec![false; bits.len()]; let mut depth = 0i64;
    for r in rows { for x in bits_of(&r) { if x == NONE { continue; } if let Some(&j) = idx.get(&x) { res[j] = depth == 0 && r[0] == 4 && r[1] == x && r[2] == NONE; } }
        match r[0] { 15 => depth += 1, 16 => depth -= 1, _ => {} } }
    res }

pub fn hash_rows(rows: &[Row]) -> u64 { let mut h = i1::HASH0; for r in rows { h = i1::hash_step(h, *r); } h }

// ------------------------------------------------------------------------------------------------------------- apply
/// classical bits of the two new Hmrs (bracket 2, bracket 4) and of their phase fixes: MEASURED unused anywhere in the list
/// (survey: 0 uses on the census list with cf and q on), next to W4's 11887..11890
pub const BITS: [u16; 2] = [11891, 11892];
/// hidden lane (relabelling frame) in force at the W4 erase row and at the W4 phase-fix row of each bracket, MEASURED (survey);
/// both callers assert their frames equal these, so that the lane of id 497 is physical lane 497 at both inserted rows
pub const H_AT: [[u16; 2]; 2] = [[250, 632], [248, 632]];
const MOVES: &str = include_str!("data/rb631_moves.txt");
/// one moved cluster: bracket (0 = bracket 2, 1 = bracket 4), window [E + r0, E + r1] (E = the W4 erase row's position in the
/// list before this module's rows), records naming lane 497 in it, hash of the window's rows (i1 hash), host lane
#[derive(Clone, Copy, Debug)]
pub struct Move { pub br: usize, pub r0: u64, pub r1: u64, pub cnt: u32, pub hash: u64, pub host: u16 }
pub fn moves() -> Vec<Move> {
    let mut v = Vec::new();
    for l in MOVES.lines() { let l = l.trim(); if l.is_empty() || l.starts_with('#') { continue; } let f: Vec<&str> = l.split_whitespace().collect();
        assert!(f[0] == "m" && f.len() == 7, "rb631 moves: bad line {l}");
        v.push(Move { br: f[1].parse().unwrap(), r0: f[2].parse().unwrap(), r1: f[3].parse().unwrap(), cnt: f[4].parse().unwrap(), hash: u64::from_str_radix(f[5], 16).unwrap(), host: f[6].parse().unwrap() }); }
    v }
/// where the edits went: old -> new positions
#[derive(Clone, Debug, Default)]
pub struct Info {
    /// per bracket, OLD list: W4 erase row, scan start, W4 fix row (= scan end), 14-bit / 15-bit lengths, frame switch inside the
    /// scan (relative: first record naming logical 498) for 14 / 15 bits
    pub e: [u64; 2], pub s: [u64; 2], pub f: [u64; 2], pub l14: [u64; 2], pub l15: [u64; 2], pub p14: [u64; 2], pub p15: [u64; 2],
    /// classical bits the 15-bit scan uses and the 14-bit one does not (the census checks they are 0 at the scan entry and exit)
    pub newbits: [Vec<u16>; 2],
    /// total growth, new list length
    pub g: u64, pub n: u64,
    /// moved windows in NEW positions: (bracket, start, end inclusive, host)
    pub moved: Vec<(usize, u64, u64, u16)>,
}
impl Info {
    /// shift of an OLD position p (p outside the interiors of the replaced scans; a scan start maps to the new scan start)
    pub fn map(&self, p: u64) -> u64 {
        let d2 = self.l15[0] - self.l14[0]; let d4 = self.l15[1] - self.l14[1];
        let mut q = p;
        if p > self.e[0] { q += 1; }
        if p > self.s[0] { assert!(p >= self.f[0], "rb631: position {p} inside scan I"); q += d2; }
        if p > self.f[0] { q += 1; }
        if p > self.e[1] { q += 1; }
        if p > self.s[1] { assert!(p >= self.f[1], "rb631: position {p} inside scan I'"); q += d4; }
        if p > self.f[1] { q += 1; }
        q }
    /// NEW positions: (inserted Hmr, scan start, scan end = W4 fix row, inserted Z) of bracket b
    pub fn new_marks(&self, b: usize) -> (u64, u64, u64, u64) { let e = self.map(self.e[b]) + 1; let s = self.map(self.s[b]); let f = self.map(self.f[b]); (e, s, f, f + 1) }
}

/// the edits on the FINAL relabelled list out[..n] (TAIL rows not included; out may be longer: capacity), given the frames at
/// the W4 erase / fix rows (`h_at`, asserted = H_AT).  Returns (new n, Info).
pub fn apply_core<S: Slot>(pk: &Pack, out: &mut Vec<S>, n: usize, h_at: [[u16; 2]; 2]) -> (usize, Info) {
    let t0 = ();
    assert!(h_at == H_AT, "rb631: frames at the W4 rows {:?} differ from the surveyed {:?}", h_at, H_AT);
    assert!(!si631::SI_SCAN_I && !si631::SI_SCAN_IP, "rb631 replaces scans I / I' itself: the si631 switches must stay off");
    for b in 0..2 { for h in h_at[b] { assert!(h != ID, "rb631: lane {ID} hidden at a W4 row"); } }
    // 1. anchors: the unique W4 rows of the two reverse brackets
    let mut info = Info::default();
    for (b, &(k, si, _)) in BRACKETS.iter().enumerate() {
        let (_, be) = i1::W4_ERASE[k]; let (_, bf) = i1::W4_FIX[k];
        let mut er: Vec<u64> = Vec::new(); let mut fx: Vec<u64> = Vec::new(); let mut other = 0u64;
        for (i, s) in out[..n].iter().enumerate() { let r = s.to_row(); let bs = bits_of(&r);
            if bs[0] == be || bs[1] == be || bs[0] == BITS[b] || bs[1] == BITS[b] { if r[0] == 12 && r[2] == be { er.push(i as u64); } else if r[0] == 7 && r[2] == bf { fx.push(i as u64); } else { other += 1; } } }
        assert!(be == bf && er.len() == 1 && fx.len() == 1 && other == 0, "rb631 bracket {b}: W4 rows {:?} {:?}, other uses of bits {be} / {} {other}", er, fx, BITS[b]);
        assert!(out[er[0] as usize].to_row() == [12, 498, be, NONE] && out[fx[0] as usize].to_row() == [7, 498, bf, NONE], "rb631: W4 rows");
        info.e[b] = er[0]; info.f[b] = fx[0]; let _ = si;
    }
    assert!(info.e[0] < info.f[0] && info.f[0] < info.e[1] && info.e[1] < info.f[1], "rb631: bracket order");
    // 2. the scans: the list range must be the 14-bit expansion (identity frames: it names neither logical 632 nor, before the
    //    switch, logical 498); the 15-bit rows are placed the same way
    let pairs = scan_pairs(pk);
    let mut r15s: Vec<Vec<Row>> = Vec::new();
    for b in 0..2 { let (r14, r15, nx) = &pairs[b];
        let l14 = r14.len() as u64; let s = info.f[b] - l14; info.s[b] = s; info.l14[b] = l14; info.l15[b] = r15.len() as u64;
        assert!(nx[1] == nx[2], "rb631: classical allocators differ after the 14-bit / 15-bit scan {}: {:?}", BRACKETS[b].1, nx);
        assert!(info.l15[b] >= l14, "rb631: 15-bit scan shorter");
        assert!(out[s as usize..info.f[b] as usize].iter().zip(r14.iter()).all(|(x, y)| x.to_row() == *y), "rb631: list range of scan {} is not its 14-bit expansion", BRACKETS[b].1);
        let fnm = |rr: &[Row], l: u16| rr.iter().position(|r| i1::names(r, l)).expect("rb631: lane never named") as u64;
        for rr in [r14, r15] { assert!(!rr.iter().any(|r| i1::names(r, i1::HIDE)), "rb631: a scan names logical lane 632"); assert!(rr.iter().all(|r| (1..=nq(r[0])).all(|j| r[j] < i1::HIDE)), "rb631: scan lane >= 632"); }
        info.p14[b] = fnm(r14, 498); info.p15[b] = fnm(r15, 498);
        // classical bits.  The scans draw classical vectors from the shared stack allocators (scan::Classical): a bit above the
        // allocator's top is zero (released bits are cleared) and a scan clears what it allocated.  Checked statically: every bit
        // the 15-bit rows use whose first use AFTER the scan in the list is a read must end the 15-bit scan with an
        // unconditional clear (and, if the 14-bit rows use it too, so must they: the reader then sees 0 in both lists).  Bits
        // new at 15 bits (not used by the 14-bit rows) are listed in Info; the census checks that they are 0 at the scan entry.
        { let b14: std::collections::HashSet<u16> = r14.iter().flat_map(|r| bits_of(r)).filter(|&x| x != NONE).collect();
          let mut all: Vec<u16> = r15.iter().flat_map(|r| bits_of(r)).filter(|&x| x != NONE).collect(); all.sort(); all.dedup();
          let after = first_uses(out[info.f[b] as usize..n].iter().map(|x| x.to_row()), &all);
          let l15 = last_clear(r15.iter().copied(), &all); let l14 = last_clear(r14.iter().copied(), &all);
          let w15 = written(r15.iter().copied()); let w14 = written(r14.iter().copied());
          let mut nread = 0usize;
          for (j, &x) in all.iter().enumerate() { if after[j] != 2 || !(w15.contains(&x) || w14.contains(&x)) { continue; } nread += 1;
              assert!((!w15.contains(&x) || l15[j]) && (!w14.contains(&x) || l14[j]) && (!b14.contains(&x) || w15.contains(&x) == w14.contains(&x)), "rb631: classical bit {x} written by scan {} and read after it, not cleared at its end (15-bit writes {} cleared {}, 14-bit writes {} cleared {})", BRACKETS[b].1, w15.contains(&x), l15[j], w14.contains(&x), l14[j]); }
          let nb: Vec<u16> = all.iter().copied().filter(|x| !b14.contains(x)).collect();
          let inside = first_uses(r15.iter().copied(), &nb);
          eprintln!("rb631: scan {}: classical bits used {} (written by the scan and read first after it: {}, all cleared at the scan end in both traces); new at 15 bits {:?}, first use inside {:?} (1 write, 2 read), written by the 15-bit rows {:?}", BRACKETS[b].1, all.len(), nread, nb, inside, nb.iter().map(|x| w15.contains(x)).collect::<Vec<_>>());
          info.newbits[b] = nb; }
        r15s.push(r15.clone());
        assert!(info.e[b] < s, "rb631: erase row after the scan start"); }
    drop(pairs);
    eprintln!("rb631: anchors {:?} {:?}, scans {:?} lengths 14 {:?} -> 15 {:?}, frame switch 14 {:?} -> 15 {:?} [{:?}]", info.e, info.f, info.s, info.l14, info.l15, info.p14, info.p15, 0u8);
    // 3. moves (in place, old positions)
    let mv = moves(); let mut nmoved = [0u32; 2];
    for m in mv.iter() { let b = m.br; let (w0, w1) = ((info.e[b] + m.r0) as usize, (info.e[b] + m.r1) as usize);
        assert!(w0 > info.e[b] as usize && w1 < info.s[b] as usize, "rb631: move window outside its bracket");
        assert!(m.host != ID && m.host != 498 && m.host < i1::HIDE, "rb631: host {}", m.host);
        let rows: Vec<Row> = out[w0..=w1].iter().map(|x| x.to_row()).collect();
        assert!(hash_rows(&rows) == m.hash, "rb631: window [{w0}, {w1}] of bracket {b} differs from the surveyed one (hash)");
        let c = rows.iter().filter(|r| i1::names(r, ID)).count() as u32; assert!(c == m.cnt, "rb631: window touches {c} != {}", m.cnt);
        assert!(!rows.iter().any(|r| i1::names(r, m.host)), "rb631: host {} named in window [{w0}, {w1}]", m.host);
        for (o, r) in rows.iter().enumerate() { if i1::names(r, ID) { let mut x = *r; for j in 1..=nq(x[0]) { if x[j] == ID { x[j] = m.host; } } out[w0 + o] = S::from_row(x); } }
        nmoved[b] += c; }
    for b in 0..2 { let bad = out[info.e[b] as usize + 1..info.s[b] as usize].iter().filter(|x| i1::names(&x.to_row(), ID)).count();
        assert!(bad == 0, "rb631: {bad} records of bracket {b} still name lane {ID} after the moves"); }
    // 4. growth, top-down block moves (all shifts >= 0), inserted rows
    let d = [info.l15[0] - info.l14[0], info.l15[1] - info.l14[1]];
    let g = 4 + d[0] + d[1]; let nn = n + g as usize; let need = nn + TAIL;
    if out.len() < need { out.reserve_exact(need - out.len()); out.resize(need, S::empty()); }
    let (e2, s2, f2, e4, s4, f4) = (info.e[0] as usize, info.s[0] as usize, info.f[0] as usize, info.e[1] as usize, info.s[1] as usize, info.f[1] as usize);
    let (d2, d4) = (d[0] as usize, d[1] as usize);
    // (old start, old end, shift), highest first
    let blocks = [(f4 + 1, n, 4 + d2 + d4), (f4, f4 + 1, 3 + d2 + d4), (e4 + 1, s4, 3 + d2), (f2 + 1, e4 + 1, 2 + d2), (f2, f2 + 1, 1 + d2), (e2 + 1, s2, 1)];
    for &(a, z, sh) in blocks.iter() { if z > a { out.copy_within(a..z, a + sh); } }
    let lane = |b: usize| -> u16 { let _ = b; ID };
    out[e2 + 1] = S::from_row([12, lane(0), BITS[0], NONE]);
    for (j, r) in r15s[0].iter().enumerate() { out[s2 + 1 + j] = S::from_row(*r); }
    out[f2 + 1 + d2 + 1] = S::from_row([7, lane(0), BITS[0], NONE]);
    out[e4 + 3 + d2] = S::from_row([12, lane(1), BITS[1], NONE]);
    for (j, r) in r15s[1].iter().enumerate() { out[s4 + 3 + d2 + j] = S::from_row(*r); }
    out[f4 + 3 + d2 + d4 + 1] = S::from_row([7, lane(1), BITS[1], NONE]);
    info.g = g; info.n = nn as u64;
    for m in mv.iter() { let b = m.br; info.moved.push((b, info.map(info.e[b] + m.r0), info.map(info.e[b] + m.r1), m.host)); }
    // post-checks on the new list: inserted rows where Info says, scans placed, lane ID unnamed over each bracket
    for b in 0..2 { let (ne, ns, nf, nz) = info.new_marks(b);
        assert!(out[ne as usize - 1].to_row()[2] == i1::W4_ERASE[BRACKETS[b].0].1 && out[ne as usize].to_row() == [12, ID, BITS[b], NONE], "rb631: new erase rows");
        assert!(out[nf as usize].to_row()[2] == i1::W4_FIX[BRACKETS[b].0].1 && out[nz as usize].to_row() == [7, ID, BITS[b], NONE], "rb631: new fix rows");
        assert!(out[ns as usize..nf as usize].iter().zip(r15s[b].iter()).all(|(x, y)| x.to_row() == *y) && nf - ns == info.l15[b], "rb631: new scan rows");
        let bad = out[ne as usize + 1..ns as usize].iter().filter(|x| i1::names(&x.to_row(), ID)).count(); assert!(bad == 0, "rb631: lane {ID} named in the new bracket {b}"); }
    assert!(!out[..nn].iter().any(|x| { let r = x.to_row(); (1..=nq(r[0])).any(|j| r[j] >= i1::HIDE) }) || !i1::FULL_632, "rb631: a record names lane >= 632");
    eprintln!("rb631: moved {:?} records ({} windows), list {} -> {} (+{}) [{:?}]", nmoved, mv.len(), n, nn, g, 0u8);
    (nn, info)
}

/// the builder hook (mod.rs build_slots_hcq, after the q631 rewrites): frames at the W4 rows from the relabelling table in the
/// pre-relabel coordinates of the hybrid / cf631-spliced list
pub fn apply<S: Slot>(pk: &Pack, sh: &Shift, rt: Option<&i1::Relabel>, hyb: bool, cf: bool, out: &mut Vec<S>, n: usize) -> usize {
    assert!(hyb, "rb631 needs the hybrid splice (its move table is surveyed on the hybrid list)");
    let t = rt.expect("rb631 needs the relabelling table");
    let at = |o: u64| -> u64 { let p = (o as i64 + sh.at(o)) as u64; let p = hybrid::map_pos(p); if cf { cf631::map_pos(p) } else { p } };
    let at = |o: u64| -> u64 { super::int4::map_pos(at(o)) };   // q631 / int4 hook: identity without its map
    let mut h_at = [[0u16; 2]; 2];
    for (b, &(k, _, _)) in BRACKETS.iter().enumerate() {
        let ie = i1::W4_ERASE[k].0; let ifx = i1::W4_FIX[k].0;
        let pe = at(pk.items[ie].out) + pk.items[ie].n;   // the W4 row appended at the end of the item (item length n + 1)
        let pf = at(pk.items[ifx].out);                     // the W4 row at offset 0
        h_at[b] = [hybrid::frame_at(t, pe), hybrid::frame_at(t, pf)]; }
    apply_core(pk, out, n, h_at).0
}

// ------------------------------------------------------------------------------------------------------------- survey
/// stage 1 survey on the census list (q631::c1_build_cq(cf, q) = build_slots_hcq(false, true, cf, q) + piece / segment / frame
/// tables in its positions).  Text to stdout; cluster table to <dir>/clusters_<cf><q>.txt.  Heavy (~31 GB).
pub fn survey(cf: bool, q: bool, dir: &str) {
    let t0 = ();
    let cb = q631::c1_build_cq(cf, q);
    let rows = &cb.rows; let n = rows.len() - TAIL;
    println!("[{:?}] census list cf {cf} q {q}: {} rows (+{TAIL} nonce), {} pieces, {} frames, h0 {}", 0u8, n, cb.pieces.len(), cb.frames.len(), cb.h0);
    let pk = pack();
    let frame_at = |i: u64| -> u16 { let k = cb.frames.partition_point(|f| f.0 <= i); if k == 0 { cb.h0 } else { cb.frames[k - 1].1 } };
    let seg_of = |i: u64| -> usize { cb.segs.partition_point(|s| s.1 <= i) };
    let id_of = |i: u64, l: u16| -> i32 { let s = seg_of(i).min(cb.inv.len() - 1); let lg = sig(l, frame_at(i)); let v = cb.inv[s][lg as usize]; if v == NONE { -1 } else { v as i32 } };
    // classical bits of the whole list
    let mut bu = vec![0u32; 65536];
    for r in rows[..n].iter() { for b in bits_of(r) { if b != NONE { bu[b as usize] += 1; } } }
    { let used = bu.iter().filter(|&&v| v > 0).count();
      print!("classical bits: {used} distinct used; uses of 11880..11910:"); for b in 11880..11910 { print!(" {}:{}", b, bu[b]); } println!();
      let free: Vec<usize> = (11000..13000).filter(|&b| bu[b] == 0).take(40).collect(); println!("  first unused bits in 11000..13000: {:?}", free);
      let free2: Vec<usize> = (60000..65533).filter(|&b| bu[b] == 0).take(10).collect(); println!("  first unused bits in 60000..65533: {:?}", free2); }
    let piece = |kind: u8, idx: u32| -> (u64, u64, u16) { let p = cb.pieces.iter().find(|p| p.2 == kind && p.3 == idx).expect("piece"); (p.0, p.1, p.4) };
    let mut ctab = String::new();
    for (bi, &(k, si, segs)) in BRACKETS.iter().enumerate() {
        let (ie, be) = i1::W4_ERASE[k]; let (ifx, bf) = i1::W4_FIX[k];
        println!("\n================ BRACKET {} (W4 index {k}: erase item {ie} bit {be}, scan {si}, fix item {ifx} bit {bf}, segments {:?})", if bi == 0 { 2 } else { 4 }, segs);
        let er: Vec<usize> = (0..n).filter(|&i| rows[i][0] == 12 && rows[i][2] == be).collect();
        let fx: Vec<usize> = (0..n).filter(|&i| rows[i][0] == 7 && rows[i][2] == bf).collect();
        println!("  rows Hmr -> bit {be}: {:?} {:?}; Z if bit {bf}: {:?} {:?}; all uses of bit {be}: {}", er, er.iter().map(|&i| rows[i]).collect::<Vec<_>>(), fx, fx.iter().map(|&i| rows[i]).collect::<Vec<_>>(), bu[be as usize]);
        let (is, iend, iseg) = piece(1, ie as u32); let (fs, fe, fseg) = piece(1, ifx as u32); let (ss, se, sseg) = piece(2, si as u32);
        println!("  item {ie}: [{is}, {iend}) seg {iseg} len {}; scan {si}: [{ss}, {se}) seg {sseg} len {}; item {ifx}: [{fs}, {fe}) seg {fseg} len {}", iend - is, se - ss, fe - fs);
        assert!(er.len() == 1 && er[0] as u64 == iend - 1 && fx.len() == 1 && fx[0] as u64 == fs && se == fs, "anchors");
        for i in is..iend { println!("    item {ie} +{}: {:?} frame {} id {:?}", i - is, rows[i as usize], frame_at(i), (1..=nq(rows[i as usize][0])).map(|j| id_of(i, rows[i as usize][j])).collect::<Vec<_>>()); }
        for i in fs..fe { println!("    item {ifx} +{}: {:?} frame {} id {:?}", i - fs, rows[i as usize], frame_at(i), (1..=nq(rows[i as usize][0])).map(|j| id_of(i, rows[i as usize][j])).collect::<Vec<_>>()); }
        let a = iend; // first record after the W4 erase row
        println!("  bracket [{a}, {ss}) = {} records; segments: {}", ss - a, (seg_of(a)..=seg_of(ss)).map(|s| format!("{s} [{}, {})", cb.segs[s].0, cb.segs[s].1)).collect::<Vec<_>>().join(", "));
        { let mut by: std::collections::BTreeMap<(u8, u16), (u64, u64, u64)> = std::collections::BTreeMap::new();
          for p in cb.pieces.iter() { if p.1 <= a || p.0 >= ss { continue; } let e = by.entry((p.2, p.4)).or_insert((0, u64::MAX, 0)); e.0 += p.1.min(ss) - p.0.max(a); e.1 = e.1.min(p.0); e.2 = e.2.max(p.1); }
          for (key, v) in by.iter() { println!("    pieces kind {} seg {}: {} records, [{}, {})", key.0, key.1, v.0, v.1, v.2); } }
        let fr: Vec<&(u64, u16)> = cb.frames.iter().filter(|f| f.0 + 2000 >= a && f.0 <= fe + 100).collect();
        println!("  frame at a-1 {} at a {}; frames in [a - 2000, fix end + 100]: {:?}", frame_at(a - 1), frame_at(a), fr);
        // lane of id 497 in the segments
        for s in seg_of(a - 1)..=seg_of(fe) { let l = pk.segs[s].map[ID as usize]; println!("    seg {s}: lane of id {ID} = {}; id on lane {ID} = {}; id on lane 498 = {}; id on lane 632 = {}", l as i32, pk.segs[s].inv[ID as usize] as i32, pk.segs[s].inv[498] as i32, pk.segs[s].inv[632] as i32); }
        // records naming physical lane ID in [a, ss)
        let tl = ID;
        let touch: Vec<u64> = (a..ss).filter(|&i| { let r = &rows[i as usize]; (1..=nq(r[0])).any(|j| r[j] == tl) }).collect();
        println!("  records naming lane {tl} in the bracket: {} (first {:?} last {:?}); in the scan [{ss}, {se}): {}", touch.len(), touch.first(), touch.last(), (ss..se).filter(|&i| { let r = &rows[i as usize]; (1..=nq(r[0])).any(|j| r[j] == tl) }).count());
        // per segment
        for s in seg_of(a)..=seg_of(ss - 1) { let c = touch.iter().filter(|&&i| seg_of(i) == s).count(); println!("    seg {s}: {c} records"); }
        // whole-bracket unnamed lanes
        let mut named_all = vec![0u64; 633]; for i in a..ss { let r = &rows[i as usize]; for j in 1..=nq(r[0]) { named_all[r[j] as usize] += 1; } }
        let un: Vec<String> = (0..633).filter(|&l| named_all[l] == 0).map(|l| format!("{l}(s{}:{},s{}:{})", segs[0], pk.segs[segs[0]].inv[l] as i32, segs[1], pk.segs[segs[1]].inv[l] as i32)).collect();
        println!("  lanes named by NO record of the bracket: {} {:?}", un.len(), un);
        // clusters (gap > 4096)
        let mut cl: Vec<(u64, u64, u64)> = Vec::new();
        for &i in touch.iter() { if let Some(c) = cl.last_mut() { if i - c.1 <= 4096 { c.1 = i; c.2 += 1; continue; } } cl.push((i, i, 1)); }
        println!("  clusters (gap > 4096): {}", cl.len());
        writeln!(ctab, "# bracket {} anchor (W4 erase row) {} a {a} scan [{ss}, {se})", if bi == 0 { 2 } else { 4 }, a - 1).unwrap();
        for (ci, &(c0, c1, cnt)) in cl.iter().enumerate() {
            let mut named = vec![false; 633]; let mut kinds = [0u32; 20]; let mut tk = [0u32; 20];
            for i in c0..=c1 { let r = &rows[i as usize]; kinds[r[0] as usize] += 1; for j in 1..=nq(r[0]) { named[r[j] as usize] = true; } if (1..=nq(r[0])).any(|j| r[j] == tl) { tk[r[0] as usize] += 1; } }
            let hs: std::collections::BTreeSet<u16> = (c0..=c1).map(|i| frame_at(i)).collect();
            let pcs: Vec<String> = cb.pieces.iter().filter(|p| p.1 > c0 && p.0 <= c1).map(|p| format!("{}:{}:s{}", p.2, p.3, p.4)).collect();
            let cand: Vec<u16> = (0..632u16).filter(|&l| !named[l as usize] && l != tl && l != 498 && !hs.contains(&l)).collect();
            let nall = cand.iter().filter(|&&l| named_all[l as usize] == 0).count();
            let ccand: Vec<String> = cand.iter().take(12).map(|&l| format!("{l}:{}", id_of(c0, l))).collect();
            let hh = hash_rows(&rows[c0 as usize..=c1 as usize]);
            println!("    c{ci:02} [{c0}, {c1}] rel [{}, {}] len {} touches {cnt} (X {} CX {} CCX {} Z {} CZ {} Hmr {}) window (X {} CX {} CCX {} Z {} CZ {} Hmr {} push {} pop {}) seg {} frames {:?} pieces {:?}; unnamed hosts {} (of them unnamed over the whole bracket {}) first {:?}",
                c0 - (a - 1), c1 - (a - 1), c1 - c0 + 1, tk[6], tk[8], tk[13], tk[7], tk[9], tk[12], kinds[6], kinds[8], kinds[13], kinds[7], kinds[9], kinds[12], kinds[15], kinds[16], seg_of(c0), hs, pcs, cand.len(), nall, ccand);
            writeln!(ctab, "c {} {ci} {} {} {cnt} {:016x} {}", if bi == 0 { 2 } else { 4 }, c0 - (a - 1), c1 - (a - 1), hh, cand.iter().map(|l| l.to_string()).collect::<Vec<_>>().join(",")).unwrap();
        }
        // hybrid regions in the bracket
        for p in cb.pieces.iter().filter(|p| p.2 == 3 && p.0 >= a && p.1 <= ss) { let c = (p.0..p.1).filter(|&i| { let r = &rows[i as usize]; (1..=nq(r[0])).any(|j| r[j] == tl) }).count(); println!("  hybrid region {} [{}, {}): records naming lane {tl}: {c}", p.3, p.0, p.1); }
        // scans: 14-bit check against the list, 15-bit facts
        let t1 = ();
        let (r14, r15, nx) = scan_pair(&pk, si);
        println!("  scan {si}: 14-bit expansion {} rows (list {}), 15-bit {} rows; classical allocators before {:?} after 14-bit {:?} after 15-bit {:?} [{:?}]", r14.len(), se - ss, r15.len(), nx[0], nx[1], nx[2], 0u8);
        assert!(r14.len() as u64 == se - ss, "scan length");
        let mut mism = 0u64; let mut first_mis = None;
        for (j, r) in r14.iter().enumerate() { let i = ss + j as u64; let h = frame_at(i); if i1::sigma(*r, h) != rows[i as usize] { mism += 1; if first_mis.is_none() { first_mis = Some((j, *r, rows[i as usize], h)); } } }
        println!("    list range vs sigma(14-bit expansion) under the census frames: {mism} mismatches, first {:?}", first_mis);
        let inside: Vec<(u64, u16)> = cb.frames.iter().filter(|f| f.0 > ss && f.0 < se).map(|f| (f.0 - ss, f.1)).collect();
        let first_named = |rr: &[Row], l: u16| rr.iter().position(|r| (1..=nq(r[0])).any(|j| r[j] == l));
        let count_named = |rr: &[Row], l: u16| rr.iter().filter(|r| (1..=nq(r[0])).any(|j| r[j] == l)).count();
        for (nm, rr) in [("14-bit", &r14), ("15-bit", &r15)] {
            let maxl = rr.iter().map(|r| (1..=nq(r[0])).map(|j| r[j]).max().unwrap_or(0)).max().unwrap_or(0);
            let mut bs: std::collections::BTreeSet<u16> = std::collections::BTreeSet::new(); let mut kk = [0u64; 20];
            for r in rr.iter() { kk[r[0] as usize] += 1; for b in bits_of(r) { if b != NONE { bs.insert(b); } } }
            println!("    {nm}: first naming logical 498 at {:?}, 497 at {:?}, 632 at {:?} (count {}); records naming 497 {} 498 {}; max lane {maxl}; kinds X {} CX {} CCX {} Z {} CZ {} Hmr {} push {} pop {} cl {} ; classical bits {} ({:?}..{:?})",
                first_named(&rr[..], 498), first_named(&rr[..], 497), first_named(&rr[..], 632), count_named(&rr[..], 632), count_named(&rr[..], 497), count_named(&rr[..], 498), kk[6], kk[8], kk[13], kk[7], kk[9], kk[12], kk[15], kk[16], kk[3] + kk[4] + kk[5], bs.len(), bs.iter().next(), bs.iter().last());
        }
        println!("    frames strictly inside the scan (rel, lane): {:?}", inside);
        { let b14: std::collections::HashSet<u16> = r14.iter().flat_map(|r| bits_of(r)).filter(|&b| b != NONE).collect();
          let b15: std::collections::HashSet<u16> = r15.iter().flat_map(|r| bits_of(r)).filter(|&b| b != NONE).collect();
          let mut newb: Vec<u16> = b15.difference(&b14).copied().collect(); newb.sort();
          // uses of the new bits outside the scan range
          let mut out_uses = 0u64; let nb: std::collections::HashSet<u16> = newb.iter().copied().collect();
          for i in (0..ss).chain(se..n as u64) { for b in bits_of(&rows[i as usize]) { if b != NONE && nb.contains(&b) { out_uses += 1; } } }
          println!("    classical bits named by the 15-bit expansion and not by the 14-bit one: {} ({:?}..{:?}); their uses elsewhere in the list: {out_uses}", newb.len(), newb.first(), newb.last()); }
    }
    std::fs::write(format!("{dir}/clusters_{}{}.txt", cf as u8, q as u8), ctab).unwrap();
    println!("[{:?}] survey done", 0u8);
}
