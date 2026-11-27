//! Hybrid walk on the 632 tree (hp1, 2026-11-18; local research, not submitted; port of hi1's q633h/hybrid.rs).
//! The early part of each of the four Euclid walk regions (his compiled records) is replaced by our capped front rows,
//! generated at build time by `capfront` (hr1's Rust port of the hs2 generator: V1, quotient cap B = 24, general rows
//! 1..63 + unit rows 1..63).
//!
//! WHERE: on the ASSEMBLED op list (his records, items with their hooks, scans placed) and BEFORE the i1 relabelling
//! (and before the peephole passes).  The four cut ranges are dropped and the generated rows written in their place;
//! everything after a range moves down (in place: each generated block is shorter than its range).  The copy schedule
//! of his records, the hooks and the scan shifts are all consumed during assembly, so none of them is disturbed.
//!
//! THE RELABELLING TABLE (i1.rs, data/relabel.lzma) is bound to the assembled stream it was planned on: its entries are
//! RECORD POSITIONS of that stream, and i1::apply asserts the stream's length and a hash of its content.  `splice`
//!   1. asserts that table against the unspliced stream (the same check as i1::apply, on the stream it was planned on),
//!   2. splices, and
//!   3. re-binds the table to the spliced stream: entries before a range are kept, entries after it move down by the
//!      length difference, entries strictly inside a range are dropped (the records they served are gone).  Our rows
//!      run in the frame in force at the range start (h_s); the builder asserts that no generated row names h_s (so
//!      lane 632 stays unnamed and h_s stays at its value).  If the frame at the end of the range differs (h_e != h_s,
//!      only possible when entries were dropped), one entry (e, h_e, move) is added: the 2 CX move of lane 632's data
//!      from h_s to h_e, which needs h_e zero at e -- the same premise as in their stream, since every lane at e equals
//!      the unspliced stream's state at e (Check A).  An entry AT e keeps its target and gets its move flag re-derived
//!      from its new predecessor.  Then length and hash of the spliced stream are written into the new table and
//!      i1::apply runs unchanged (rename, moves, the FULL_632 assertion over the whole stream, our rows included).
//!
//! Cut points (op positions of the assembled list with the splice off, i.e. before the relabelling; "position P" =
//! state before op P), re-derived on this tree by the op-pattern rules (hp1/hybtools.rs survey; hs1 / hw2 rules):
//!   forward  [P_2, P_65):   P_K right after the K-th pair "CX H3->H4; CX Z0->H3" of the forward walk
//!   reverse  [P'_65, P'_2): P'_K = 1 + the POP of the first PUSH scope longer than 1000 ops after the (127-K)-th pair
//!                            "CX Z0->H3; CX H3->H4" of the reverse walk
//! Inserted (hj1 section 4, both pairs alike):
//!   forward: R0, U1, G1, R1, ..., U63, G63 (round discipline: one bare HMR per general row into W_k), then X on Y1..Y63
//!   reverse: inverse of U1, G1, R1, ..., U63, G63, R63 (G_k: Z on the flag conditioned on W_k, then W_k cleared; own
//!            retires HMR -> SCR, PUSH SCR, replay, POP), then SCR cleared.
//! Generator wire -> his id: w < 256 -> X_w; 256 -> Z0; 257..384 -> Z_{w-256}; 385 -> H4; 386..389 -> H0..H3;
//! 390..632 -> Y_{w-390}; his id -> lane through the region's segment map.  In this tree id 498 (= Y242, generator wire
//! 632) is unmapped in the walk segments (W4 erase): the generator never touches it (asserted per row).
use super::capfront::{self, Config, Dir, Op, Params};
use super::i1::{self, Relabel, HIDE};
use super::{qubits, Pack, Row, Shift, Slot, NONE};

/// THE SWITCH.  false = their package unchanged (byte-identical op list); true = the four walk regions spliced.
pub const ON: bool = super::FINAL631;
/// fin631 package: hash of the pruned unspliced stream (placeholders = BitStore0(65499)); measured by the package build
pub const PRUNED_HASH: u64 = 0x8e798556b83940dc;

/// classical bits: forward witness record of general row k (k = 1..63) = W0 + (k - 1); SCR = the reverse's retire
/// scratch.  Both pairs use the same 64 bits (pair 1's reverse clears all of them before pair 2's forward starts).
/// They must be bits the package never uses (checked by the bit scan of hp1/hybcheck) and below the passes' reserved
/// 65533 / 65534.
pub const W0: u32 = 65401;
pub const SCR: u32 = 65499;
/// capfront numbers the reverse's own HMRs from here; every one of them is renamed to SCR (hj1's discipline)
const OWN0: u32 = 1 << 20;

pub struct Region { pub start: u64, pub end: u64, pub seg: usize, pub fwd: bool }
/// positions in the assembled list (splice off, before the relabelling) of THIS tree, MEASURED by hybtools::survey
/// with the rules above (asserted by the fingerprints in `check`)
/// (hp1/survey.log: 127 pattern hits per walk; lengths 103,314,384 / 119,446,950 = the 633 tree's; fingerprints OK; the
/// relabelling hides lane 632 on lane 498 over each whole range, with no table entry inside or at either end)
pub const REGIONS: [Region; 4] = [
    Region { start: 24_796_226, end: 128_110_610, seg: 2, fwd: true },
    Region { start: 1_049_003_890, end: 1_168_450_840, seg: 13, fwd: false },
    Region { start: 1_201_756_056, end: 1_305_070_440, seg: 18, fwd: true },
    Region { start: 2_219_795_826, end: 2_339_242_776, seg: 29, fwd: false },
];
/// generated rows per region (asserted): forward 58,918,590 rows + 63 adapter X; reverse 68,539,446 + the SCR clear
pub const FWD_LEN: u64 = 58_918_653;
pub const REV_LEN: u64 = 68_539_447;
pub fn gen_len(r: &Region) -> u64 { if r.fwd { FWD_LEN } else { REV_LEN } }

/// (old start, old end, new start, new length) of every region: the new op list is old[..s0] gen0 old[e0..s1] gen1 ...
pub fn layout() -> Vec<(u64, u64, u64, u64)> {
    let mut d = 0i64;
    REGIONS.iter().map(|r| { let ns = (r.start as i64 - d) as u64; d += (r.end - r.start) as i64 - gen_len(r) as i64; (r.start, r.end, ns, gen_len(r)) }).collect()
}
/// new position of an old position outside the cut ranges (a range end maps to the end of its generated block)
pub fn map_pos(p: u64) -> u64 {
    let mut d = 0i64;
    for r in REGIONS.iter() { if p >= r.end { d += (r.end - r.start) as i64 - gen_len(r) as i64; } else { assert!(p <= r.start, "position inside a cut range"); } }
    (p as i64 - d) as u64
}

/// rows631 switch (default OFF): env CAPFRONT_LOANSKIP=<X>[:<S>] (X = a generator wire, e.g. 358 = bank[101]; S defaults to 569 = Y179,
/// a lane no generated row names): wherever a dirty-loan list of the capped rows would contain X (all four regions) it contains S instead;
/// every other loan is unchanged, so X is never named; see q631/rows1/summary.py
pub fn loanskip() -> Option<(u32, u32)> {
    let v = match Err::<String, ()>(()) { Ok(v) => v, Err(_) => if super::FINAL631 { "358:569".to_string() } else { return None } }; let mut it = v.split(':');
    let x: u32 = it.next()?.parse().ok()?; let s: u32 = it.next().and_then(|t| t.parse().ok()).unwrap_or(569); Some((x, s))
}

const N: u16 = NONE;
// his ids: X 0..256, Y 256..512, Z 512..641, H 641..646
pub const fn x(i: usize) -> usize { i }
pub const fn y(i: usize) -> usize { 256 + i }
pub const fn z(i: usize) -> usize { 512 + i }
pub const fn h(i: usize) -> usize { 641 + i }
fn id_of(w: u32) -> usize {
    let w = w as usize;
    match w { 0..=255 => x(w), 256 => z(0), 257..=384 => z(w - 256), 385 => h(4), 386..=389 => h(w - 386), 390..=632 => y(w - 390), _ => panic!("generator wire {}", w) }
}
fn bit16(b: u32) -> u16 { assert!(b < 65533, "classical bit {} out of range", b); b as u16 }
/// lane value given to a generator wire whose id has no lane in the segment (id 498 here): never a valid lane
const UNMAPPED: u32 = 0xFFFF;

/// capfront op -> records (hj1/emit.cjs Rec)
struct Conv { buf: Vec<Row>, cur: Option<u16>, fwd: bool, scr: u32, own_max: u32 }
impl Conv {
    fn bit(&self, b: u32) -> u16 { if b >= OWN0 { assert!(!self.fwd && b < OWN0 + self.own_max, "own HMR bit"); bit16(self.scr) } else { bit16(b) } }
    fn gate(&mut self, r: Row, put: &mut dyn FnMut(Row)) { if self.cur.is_some() { self.buf.push(r) } else { put(r) } }
    fn op(&mut self, op: Op, put: &mut dyn FnMut(Row)) {
        let l = |q: u32| -> u16 { assert!(q != UNMAPPED, "generated row names a generator wire whose id has no lane (id 498)"); assert!(q < 633); q as u16 };
        match op {
            Op::X { t, .. } => self.gate([6, l(t), N, N], put),
            Op::Cx { c, t, .. } => self.gate([8, l(c), l(t), N], put),
            Op::Ccx { a, b, t, .. } => self.gate([13, l(a), l(b), l(t)], put),
            Op::Z { q, .. } => self.gate([7, l(q), N, N], put),
            Op::Hmr { q, bit } => { assert!(self.cur.is_none(), "HMR inside a conditional block"); let b = self.bit(bit); put([12, l(q), b, N]) }
            Op::CondBegin { bit } => { assert!(self.cur.is_none(), "nested conditional block"); self.cur = Some(self.bit(bit)); self.buf.clear(); }
            Op::CondEnd => {
                let b = self.cur.take().expect("CondEnd without CondBegin");
                if self.buf.len() == 1 && self.buf[0][0] == 7 { put([7, self.buf[0][1], b, N]); }
                else { put([15, b, N, N]); for &r in self.buf.iter() { put(r); } put([16, N, N, N]); }
                if b != bit16(self.scr) { put([4, b, N, N]); }
            }
        }
    }
}

/// the rows of one region, lanes through `seg_map` (his id -> lane), classical bits W_k = w0 + (k - 1) and scr; returns the count
pub fn gen(fwd: bool, seg_map: &[u16], w0: u32, scr: u32, put: &mut dyn FnMut(Row)) -> u64 {
    // every generator wire whose id has a lane gets it; an unmapped id (498 in the walk segments) gets UNMAPPED, which
    // Conv refuses to emit (so a row that touched it would stop the build)
    let map: Vec<u32> = (0..633u32).map(|w| { let l = seg_map[id_of(w)]; if l == NONE { UNMAPPED } else { assert!(l < 633, "lane {}", l); l as u32 } }).collect();
    let unm: Vec<u32> = (0..633u32).filter(|&w| map[w as usize] == UNMAPPED).collect();
    assert!(unm.iter().all(|&w| w == 632), "generator wires without a lane: {:?} (only wire 632 = id 498 may be unmapped)", unm);
    let mut cfg = Config::new(64, 24);
    cfg.excl = loanskip();
    let mut cnt = 0u64;
    assert!(scr < w0 || scr >= w0 + 63, "scratch bit inside the record range");
    let mut conv = Conv { buf: Vec::new(), cur: None, fwd, scr, own_max: 126 };
    {
        let mut put2 = |r: Row| { cnt += 1; put(r) };
        let prm = if fwd { Params { map: &map, cbit_base: w0, hist_base: 0, round: true, include_pre: false } }
                  else { Params { map: &map, cbit_base: OWN0, hist_base: w0, round: true, include_pre: false } };
        let st = capfront::front_join(&cfg, 63, if fwd { Dir::Fwd } else { Dir::Rev }, &prm, &mut |op| conv.op(op, &mut put2)).expect("capfront emission");
        assert!(conv.cur.is_none(), "open conditional block");
        assert!(st.hmr == if fwd { 63 } else { 126 }, "HMR count {}", st.hmr);
        let yl = |i: usize| -> u16 { let l = seg_map[y(i)]; assert!(l != NONE && l < 633); l };
        if fwd { for i in 1..=63 { put2([6, yl(i), N, N]); } }   // exit adapter: his P_65 passenger mask has Y0..Y63 set, P_2's only Y0
        else { put2([4, bit16(scr), N, N]); }
    }
    cnt
}

/// checks the cut points: the rows at both ends of each range (hj1 / hw2 fingerprints, through the segment map) and
/// that every op of the range is one of his records placed through that range's segment
fn check<S: Slot>(pk: &Pack, sh: &Shift, out: &[S]) {
    for (i, r) in REGIONS.iter().enumerate() {
        let m = &pk.segs[r.seg].map; let (s, e) = (r.start as usize, r.end as usize);
        assert!(s > 2 && e > s, "region {} positions not set", i);
        let row = |p: usize| out[p].to_row();
        let l = |id: usize| { let v = m[id]; assert!(v != NONE, "fingerprint id {} unmapped", id); v };
        if r.fwd {
            // ... CX H3->H4; CX Z0->H3 | X Y0 ... | X Z65; CCX(Z0, Z65 -> X0)
            assert_eq!(row(s - 2), [8, l(h(3)), l(h(4)), N], "region {} entry fingerprint", i);
            assert_eq!(row(s - 1), [8, l(z(0)), l(h(3)), N], "region {} entry fingerprint", i);
            assert_eq!(row(s), [6, l(y(0)), N, N], "region {} first dropped row", i);
            assert_eq!(row(e - 2), [8, l(h(3)), l(h(4)), N], "region {} exit fingerprint", i);
            assert_eq!(row(e - 1), [8, l(z(0)), l(h(3)), N], "region {} exit fingerprint", i);
            assert_eq!(row(e), [6, l(z(65)), N, N], "region {} first kept row", i);
            assert_eq!(row(e + 1), [13, l(z(0)), l(z(65)), l(x(0))], "region {} first kept rows", i);
        } else {
            // POP | CX X192->Z0 ... POP | CX X255->Z0
            assert_eq!(row(s - 1), [16, N, N, N], "region {} entry fingerprint", i);
            assert_eq!(row(s), [8, l(x(192)), l(z(0)), N], "region {} first dropped row", i);
            assert_eq!(row(e - 1), [16, N, N, N], "region {} last dropped row", i);
            assert_eq!(row(e), [8, l(x(255)), l(z(0)), N], "region {} first kept row", i);
        }
        // coverage: his pieces of segment r.seg tile [s, e)
        let mut cov = 0u64;
        for p in pk.his.iter() {
            let o = (p.out as i64 + sh.at(p.out)) as u64; let oe = o + (p.to - p.from);
            if oe <= r.start || o >= r.end { continue; }
            assert!(p.seg == r.seg, "region {}: his piece in segment {} (expected {})", i, p.seg, r.seg);
            cov += oe.min(r.end) - o.max(r.start);
        }
        assert!(cov == r.end - r.start, "region {}: his pieces cover {} of {} ops", i, cov, r.end - r.start);
    }
}

/// the i1 hash of out[..n] (i1::apply's binding check)
pub fn stream_hash<S: Slot>(out: &[S]) -> u64 { let mut h = i1::HASH0; for s in out { h = i1::hash_step(h, s.to_row()); } h }
/// hidden lane in force at record p of the table's stream
pub fn frame_at(t: &Relabel, p: u64) -> u16 { let k = t.ent.partition_point(|e| e.0 <= p); if k == 0 { t.h0 } else { t.ent[k - 1].1 } }

/// what the re-binding did, per region (for the report): (h_s, h_e, dropped entries, added entry, entry at e re-derived)
pub struct RebindNote { pub hs: u16, pub he: u16, pub dropped: usize, pub added: bool, pub at_end: bool }

/// re-bind the relabelling table `t` (planned on the unspliced stream) to the spliced stream: see the module comment.
/// `named(i, lane)` = whether generated region i names `lane` (pre-relabel lanes).
pub fn rebind(t: &Relabel, named: &dyn Fn(usize, u16) -> bool) -> (Vec<(u64, u16, u8)>, Vec<RebindNote>) {
    let lay = layout();
    let mut notes = Vec::new();
    let mut ent: Vec<(u64, u16, u8)> = Vec::with_capacity(t.ent.len() + 4);
    let mut k = 0usize; let m = t.ent.len();
    let mut d = 0i64;   // shift of positions after the regions passed so far
    for (i, r) in REGIONS.iter().enumerate() {
        // entries up to and including the range start: kept (shifted by the earlier regions)
        while k < m && t.ent[k].0 <= r.start { let e = t.ent[k]; ent.push(((e.0 as i64 - d) as u64, e.1, e.2)); k += 1; }
        let hs = frame_at(t, r.start); let he = frame_at(t, r.end - 1);
        assert!(hs != HIDE && he != HIDE, "region {}: lane 632 not hidden at the range (gap) h_s {} h_e {}", i, hs, he);
        assert!(!named(i, hs), "region {}: a generated row names the hidden lane {}", i, hs);
        // entries strictly inside: dropped (no gap moves may be among them)
        let mut dropped = 0usize;
        while k < m && t.ent[k].0 < r.end { assert!(t.ent[k].2 & 2 == 0, "region {}: gap entry inside the range", i); dropped += 1; k += 1; }
        d += (r.end - r.start) as i64 - lay[i].3 as i64;
        let ne = (r.end as i64 - d) as u64; assert!(ne == lay[i].2 + lay[i].3, "region {} new end", i);
        let at_end = k < m && t.ent[k].0 == r.end;
        let mut added = false;
        if at_end && dropped == 0 {
            // nothing dropped: the entry at e keeps its predecessor (h_s = h_e) and its flags; it only moves down
            let e = t.ent[k]; k += 1; ent.push((ne, e.1, e.2));
        } else if at_end {
            // the entry at e moves from its NEW predecessor (h_s) to its target: re-derive its move flag
            let e = t.ent[k]; k += 1;
            assert!(e.2 & 2 == 0, "region {}: gap entry at the range end", i);
            if e.1 != hs { let f = if hs != HIDE && e.1 != HIDE { 1u8 } else { 0u8 }; ent.push((ne, e.1, (e.2 & !1) | f)); }
        } else if he != hs {
            let f = if hs != HIDE && he != HIDE { 1u8 } else { 0u8 };
            ent.push((ne, he, f)); added = true;
        }
        notes.push(RebindNote { hs, he, dropped, added, at_end });
    }
    while k < m { let e = t.ent[k]; ent.push(((e.0 as i64 - d) as u64, e.1, e.2)); k += 1; }
    assert!(ent.windows(2).all(|w| w[0].0 <= w[1].0), "re-bound table out of order");
    (ent, notes)
}

/// what the last `splice` did to the relabelling table (read by the local tools; the builder prints nothing)
pub static LOG: std::sync::Mutex<String> = std::sync::Mutex::new(String::new());
/// splice the four regions into out[..n] in place and re-bind the relabelling table; returns the new length and table
pub fn splice<S: Slot>(pk: &Pack, sh: &Shift, out: &mut [S], n: usize, rt: Option<Relabel>) -> (usize, Option<Relabel>) {
    assert!(REGIONS.windows(2).all(|w| w[0].end < w[1].start) && (REGIONS[3].end as usize) < n, "region order");
    check(pk, sh, out);
    // 1. the table must be the one planned on THIS (unspliced) stream: i1::apply's own check, here before the splice
    // fin631 package: with the his pruning the unspliced stream differs inside the replaced ranges, so the check pins both the
    // shipped table (its hash) and the pruned stream (measured by the package build, 2026-11-26)
    if let Some(t) = &rt { let hh = stream_hash(&out[..n]);
        if super::his_prune() { assert!(t.n == n as u64 && t.hash == 0xd5b8721e98af1557 && hh == PRUNED_HASH, "hybrid: pruned stream check (table n {} hash {:016x}, stream n {} hash {:016x})", t.n, t.hash, n, hh); } else {
        assert!(t.n == n as u64 && t.hash == hh, "hybrid: relabel table was planned on another stream (table n {} hash {:016x}, stream n {} hash {:016x})", t.n, t.hash, n, hh); } }
    // 2. splice; record the lanes every generated region names
    let mut lanes: Vec<Vec<bool>> = vec![vec![false; 633]; REGIONS.len()];
    let (mut w, mut rd) = (0usize, 0usize);
    for (i, r) in REGIONS.iter().enumerate() {
        let (s, e) = (r.start as usize, r.end as usize);
        if w != rd { out.copy_within(rd..s, w); } w += s - rd;
        let start = w;
        let ln = &mut lanes[i];
        let cnt = gen(r.fwd, &pk.segs[r.seg].map, W0, SCR, &mut |row| { assert!(w < e, "generated rows overrun region {}", i);
            for j in 1..=qubits(row[0]) { ln[row[j] as usize] = true; } out[w] = S::from_row(row); w += 1; });
        assert!(cnt == gen_len(r) && (w - start) as u64 == cnt, "region {}: {} generated rows", i, cnt);
        assert!(start as u64 == layout()[i].2, "region {} new start", i);
        rd = e;
    }
    out.copy_within(rd..n, w); w += n - rd;
    // 3. re-bind the table
    let rt = rt.map(|t| { let (ent, notes) = rebind(&t, &|i, l| lanes[i][l as usize]);
        let nt = Relabel { n: w as u64, hash: stream_hash(&out[..w]), h0: t.h0, ent };
        *LOG.lock().unwrap() = format!("rebind: table {} entries -> {}; per region (h_s, h_e, dropped, added, entry at e): {:?}; new n {} hash {:016x}",
            t.ent.len(), nt.ent.len(), notes.iter().map(|x| (x.hs, x.he, x.dropped, x.added, x.at_end)).collect::<Vec<_>>(), nt.n, nt.hash);
        nt });
    (w, rt)
}

/// local tools: the segment maps (his id -> lane) of the four regions, as the builder uses them (after the W4 patch)
pub fn seg_maps() -> Vec<Vec<u16>> {
    let mut pk = Pack::parse(&super::lzma::decode(include_bytes!("data/pack.lzma")).expect("pack tables"));
    super::walkpack::apply(&mut pk); i1::w4_apply(&mut pk);
    REGIONS.iter().map(|r| pk.segs[r.seg].map.clone()).collect()
}

// ---------------------------------------------------------------------------------------------------------------------
// pre3 (2026-11-25, local research, never submitted; switch = int4 mask bit PRE3): his column 1 of the four walks replaced by
// our generator.  Forward block (walks 1 / 3, in place of [walk start, P_2)): pre-step + G0 (row 0's general step; its R0 is the
// first item of the old region 0 / 2 block).  Reverse block (walks 2 / 4, in place of [P'_2, segment end)): R0^-1, G0^-1,
// pre-step^-1.  Row 0's witness bit is WX; rows 1..63 keep W0 + (k - 1); the reverse's own HMRs (2) are numbered OWN0 + 126, 127
// and renamed to SCR as in `gen`.
pub const WX: u32 = 65400;
/// the rows of one pre3 block through `seg_map`; returns the count
/// pre5: gen_x for the column-1 range `idx` (walk 3's block starts at a seam where the entry is already clean: no Z20 carry cleaning)
pub fn gen_x_i(idx: usize, fwd: bool, seg_map: &[u16], wx: u32, scr: u32, put: &mut dyn FnMut(Row)) -> u64 {
    capfront::X_NOCLEAN.store(idx == 2, std::sync::atomic::Ordering::SeqCst);
    let n = gen_x(fwd, seg_map, wx, scr, put);
    capfront::X_NOCLEAN.store(false, std::sync::atomic::Ordering::SeqCst); n }
pub fn gen_x(fwd: bool, seg_map: &[u16], wx: u32, scr: u32, put: &mut dyn FnMut(Row)) -> u64 {
    let map: Vec<u32> = (0..633u32).map(|w| { let l = seg_map[id_of(w)]; if l == NONE { UNMAPPED } else { assert!(l < 633, "lane {}", l); l as u32 } }).collect();
    let unm: Vec<u32> = (0..633u32).filter(|&w| map[w as usize] == UNMAPPED).collect();
    assert!(unm.iter().all(|&w| w == 632), "generator wires without a lane: {:?}", unm);
    let mut cfg = Config::new(64, 24);
    cfg.excl = loanskip();   // int7 merge (main, 2026-11-25): the column-1 block uses the same loan substitution as the rows
    let mut cnt = 0u64;
    assert!(scr < wx || scr >= wx + 64, "scratch bit inside the record range");
    let mut conv = Conv { buf: Vec::new(), cur: None, fwd, scr, own_max: 128 };
    {
        let mut put2 = |r: Row| { cnt += 1; put(r) };
        if fwd {
            let prm = Params { map: &map, cbit_base: wx, hist_base: 0, round: true, include_pre: false };
            let st = capfront::front_x(&cfg, &prm, false, &mut |op| conv.op(op, &mut put2)).expect("capfront pre0 emission");
            assert!(conv.cur.is_none(), "open conditional block"); assert!(st.hmr == 1, "HMR count {}", st.hmr);
        } else {
            let prm = Params { map: &map, cbit_base: OWN0 + 126, hist_base: wx, round: true, include_pre: true };
            let st = capfront::front_x(&cfg, &prm, true, &mut |op| conv.op(op, &mut put2)).expect("capfront row0 reverse emission");
            assert!(conv.cur.is_none(), "open conditional block"); assert!(st.hmr == 1, "HMR count {}", st.hmr);
            put2([4, bit16(scr), N, N]);
        }
    }
    cnt
}

/// pre3: the four column-1 ranges in the UNSPLICED assembled list (his records), replaced by `gen_x` blocks when int4's PRE3 bit is set
/// (forward: [walk start, P_2) -> pre-step + G0; reverse: [P'_2, segment end) -> R0^-1, G0^-1, pre-step^-1).  Measured by pre1dump / hp1's survey.
pub const X_REGIONS: [Region; 4] = [
    Region { start: 23_371_288, end: 24_796_226, seg: 2, fwd: true },
    Region { start: 1_168_450_840, end: 1_170_020_378, seg: 13, fwd: false },
    Region { start: 1_200_355_965, end: 1_201_756_056, seg: 18, fwd: true },   // pre5: walk 3 starts at the SEAM rel 697,135 of his column 1 (his column 1 starts at 1_199_658_830)
    Region { start: 2_339_242_776, end: 2_340_813_939, seg: 29, fwd: false },
];

/// pre3: lengths of the four replaced ranges (his records)
pub const X_LENS: [u64; 4] = [1_424_938, 1_569_538, 1_400_091, 1_571_163];
/// pre3 fingerprints of the cut points; `rows` = the list from 3 records before the range to 3 records after it (physical pre-relabel lanes)
pub fn check_x<S: Slot>(idx: usize, m: &[u16], rows: &[S], len: u64) {
    assert!(len == X_LENS[idx], "pre3 range {}: length {} (expected {})", idx, len, X_LENS[idx]);
    assert!(rows.len() as u64 == len + 6);
    let _ = m;   // fingerprints: filled in from the pre3scan survey (see check_x_fp)
    check_x_fp(idx, m, rows);
}
fn check_x_fp<S: Slot>(idx: usize, m: &[u16], rows: &[S]) {
    let r = |i: usize| rows[i].to_row(); let nr = rows.len();
    let l = |id: usize| { let v = m[id]; assert!(v != NONE, "pre3 fingerprint id {} unmapped", id); v };
    let (first, last, after) = (3usize, nr - 4, nr - 3);   // first row of the range, last row of the range, first row after it
    if X_REGIONS[idx].fwd {
        // ... HMR lane 498 (W4 erase) | col 1 ... CX H3->H4; CX Z0->H3 | X Y0; X H1 (his next column)
        if idx == 2 {   // pre5: the seam inside walk 3's column 1: ... CX Y0->X13; CX Y0->X14; CX Y0->X15 | X X255 (his pre-step start) ...
            assert_eq!(r(first - 3), [8, l(y(0)), l(x(13)), N], "pre5 seam entry fingerprint"); assert_eq!(r(first - 2), [8, l(y(0)), l(x(14)), N], "pre5 seam entry fingerprint");
            assert_eq!(r(first - 1), [8, l(y(0)), l(x(15)), N], "pre5 seam entry fingerprint"); assert_eq!(r(first), [6, l(x(255)), N, N], "pre5 seam first row");
        } else {
        assert!(r(first - 1)[0] == 12 && r(first - 1)[1] == 498, "pre3 range {idx}: entry fingerprint (the W4 erase HMR of lane 498): {:?}", r(first - 1)); }
        assert_eq!(r(last - 1), [8, l(h(3)), l(h(4)), N], "pre3 range {idx}: exit fingerprint");
        assert_eq!(r(last), [8, l(z(0)), l(h(3)), N], "pre3 range {idx}: exit fingerprint");
        // after the range: his next column (X Y0; X H1) when the hybrid is off, or the first row of our hybrid region
        // (CX X255 -> Z0) when it is on (the old hybrid drops his X Y0 / X H1; main session 2026-11-25)
        let a = r(after);
        assert!(a == [6, l(y(0)), N, N] || a == [8, l(x(255)), l(z(0)), N], "pre3 range {idx}: first row after the range: {:?}", a);
    } else {
        // POP | CX X255->Z0; CX Z0->X255 ... (end of his reverse walk) | next piece
        assert_eq!(r(first - 1), [16, N, N, N], "pre3 range {idx}: entry fingerprint");
        assert_eq!(r(first), [8, l(x(255)), l(z(0)), N], "pre3 range {idx}: first row");
        assert_eq!(r(first + 1), [8, l(z(0)), l(x(255)), N], "pre3 range {idx}: second row");
        // MEASURED by pre3scan (physical pre-relabel lanes): last row of his reverse walk and the first row of the next piece
        let (lastrow, nextrow): (Row, Row) = if idx == 1 { ([13, 248, 523, 524], [3, 24601, 18084, N]) } else { ([13, 51, 518, 519], [6, 585, N, N]) };
        assert_eq!(r(last), lastrow, "pre3 range {idx}: last row"); assert_eq!(r(after), nextrow, "pre3 range {idx}: next piece's first row");
    }
}

/// test hook: rows of the entry-cleaning circuit alone
pub fn gen_clean(seg_map: &[u16], put: &mut dyn FnMut(Row)) {
    let map: Vec<u32> = (0..633u32).map(|w| { let l = seg_map[id_of(w)]; if l == NONE { UNMAPPED } else { l as u32 } }).collect();
    let cfg = Config::new(64, 24); let prm = Params { map: &map, cbit_base: 65400, hist_base: 0, round: true, include_pre: false };
    let mut conv = Conv { buf: Vec::new(), cur: None, fwd: true, scr: 65499, own_max: 128 };
    capfront::clean_only(&cfg, &prm, &mut |op| conv.op(op, put));
}
