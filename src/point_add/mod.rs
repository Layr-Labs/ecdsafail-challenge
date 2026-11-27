//! 638-qubit point addition: the walks, sign fixes, U rebuilds and point operations of the 646-qubit submission (af4f0042),
//! with its two field multiplications replaced by multiply / divide blocks and eight erase-and-rebuild scans that free lanes.
//! The op list is assembled out of order, straight into its final positions:
//!   * his records: the gate IR blocks our ranges need + his copy schedule, executed against the op list itself;
//!   * our multiply / divide blocks and small glue pieces: gate-record streams;
//!   * our scans: a trace of generator calls, expanded by `scan`.
//! Every record carries logical qubit ids (646 of them); each stretch of the output has one fixed id -> lane map (638 lanes).
use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId, NO_BIT};
mod cl;
mod gir;
mod lzma;
mod plan;
pub mod post_pass;
mod gadget_merge;
mod rns;
mod scan;mod borrow_scan;mod borrow_rns;mod opt_scan;mod opt_rns;
mod vm;
mod walkgen;
mod walkpack;
mod unroll;
mod unrollpack;
// (internal) ((internal)): pieces of the 632 assembly; switches in i1.rs
pub mod i1;
mod b5gen;
#[allow(dead_code, unused)] mod bp_scan;
pub mod w2rw;
mod w4patch;
mod m1gen;
mod m1tab;
mod c2capgen;
#[allow(dead_code)] mod r3walkgen;
#[allow(dead_code, unused)] pub mod w2;
#[allow(dead_code, unused)] pub mod c2;
#[allow(dead_code, unused)] pub mod c2e;
#[allow(dead_code, unused)] pub mod c3;
#[allow(dead_code, unused)] pub mod c3ctr;
#[allow(dead_code, unused)] pub mod c3pad;
// hp1 (local research, not submitted): hybrid walk (hybrid.rs, switch hybrid::ON; off = this tree unchanged) + local tools
#[allow(dead_code)] mod capfront;
pub mod hybrid;
#[allow(dead_code)] pub mod hybtools;
// q631 / sc (local research, not submitted): scan-level tools and the q631 traces of scans B / B' (scq631.rs; scan_rows calls scq631::trace_for = identity unless a switch there is on)
#[allow(dead_code)] pub mod scq631;
// q631 / si (local research, not submitted): scans I / I' at 15 bits (si631.rs; scan_rows calls si631::trace_for = identity unless SI_SCAN_I / SI_SCAN_IP there is on; both false)
#[allow(dead_code)] pub mod si631;
// q631 / i10 (local research, not submitted): ITEM 10 without the walk's held enable lane (i10.rs, switch i10::ON = false; nothing calls it while off)
#[allow(dead_code)] pub mod i10;
// q631 / i2 (local research, not submitted): ITEM 2 without its 632nd lane (i2.rs, switch i2::ON = false; nothing calls it while off)
#[allow(dead_code)] pub mod i2;
#[allow(dead_code)] pub mod i2b;   // q631 / i2b (local research, not submitted): ITEM 2 with a declared free lane at every record (i2b.rs, switch i2b::ON = false; nothing calls it)
// q631 / i4d (local research, not submitted): ITEM 4 in wire space for the walk tools (i4dwire.rs; nothing in the builder calls it)
#[allow(dead_code)] pub mod i4dwire;
// q631 / int1 (local research, not submitted): the three ITEM 4 rewrites applied after the relabelling (q631.rs; switch q631::ON = false)
#[allow(dead_code)] pub mod q631;
#[allow(dead_code)] pub mod i12;   // q631 / i12 (local research, not submitted): ITEM 12 tools + rewrite, switch i12::ON = false
// q631 / cf (local research, not submitted): the new 631-lane forward upper walk (delivered generator in research/, unmodified) spliced
// into walks 1 and 3 behind cf631::ON (false = this tree unchanged); cftools = local survey tools (nothing in the builder calls them)
#[allow(dead_code)] #[path = "research/upperwalk_forward631.rs"] pub mod upperwalk_forward631;
#[allow(dead_code)] pub mod cftools;
pub mod cf631;
#[allow(dead_code)] pub mod rp1;   // q631 / rp1 (local research, not submitted): second hidden lane, soft-mode relabelling (rp1.rs), switch rp1::ON = false
#[allow(dead_code)] pub mod sm;   // q631 / sm (local research, not submitted): park-seam rewrites of ITEM 4 / ITEM 12 (sm.rs), switches sm::sm4::ON / sm::sm12::ON = false
#[allow(dead_code)] pub mod bs631;   // q631 / bs (local research, not submitted): scans D, F, F' with a second free lane through the sweep (bs631.rs; scan_rows calls bs631::trace_for = identity unless BS_SCAN_D / BS_SCAN_F / BS_SCAN_FP there is on; all false)
#[allow(dead_code)] pub mod rb631;   // q631 / rb (local research, not submitted): the reverse brackets with a 15th erased bit (id 497), switch rb631::ON = false (runtime rb631::FORCE for tools); off = nothing calls it
#[allow(dead_code)] pub mod int4;   // q631 / int4 (local research, not submitted): the five pre-relabelling fixes in the chain + the shared position map, mask int4::ON = 0 (runtime int4::FORCE for tools); mask 0 = list unchanged
#[allow(dead_code)] pub mod fl;   // q631 / fl (local research, not submitted): the last no-free records (fl.rs: flwalk, ...), every switch OFF; nothing in the builder calls it
#[allow(dead_code)] pub mod fl2;   // q631 / fl2 (local research, not submitted): ITEM 4 phase B + unpark head (fl2.rs: fl2pb, fl2up), switches OFF; nothing in the builder calls it

pub type Row = [u16; 4];
const NONE: u16 = u16::MAX;
/// number of leading fields of a record that are qubits
#[inline] fn qubits(kind: u16) -> usize { match kind { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }
fn optional_bit(x: u16) -> BitId { if x == NONE { NO_BIT } else { BitId(x as u64) } }
pub fn row_to_op([kind, a, b, c]: Row) -> Op {
    use OperationType::*;
    let qa = QubitId(a as u64); let qb = QubitId(b as u64); let mut op = Op::empty();
    op.kind = match kind {
        1 => { op.r_target = RegisterId(a as u64); Register }
        2 => { op.r_target = RegisterId(a as u64); op.q_target = qb; AppendToRegister }
        18 => { op.r_target = RegisterId(a as u64); op.c_target = BitId(b as u64); AppendToRegister }
        3 | 4 | 5 => { op.c_target = BitId(a as u64); op.c_condition = optional_bit(b); if kind == 3 { BitInvert } else if kind == 4 { BitStore0 } else { BitStore1 } }
        6 | 7 => { op.q_target = qa; op.c_condition = optional_bit(b); if kind == 6 { X } else { Z } }
        8 | 9 => { op.q_control1 = qa; op.q_target = qb; op.c_condition = optional_bit(c); if kind == 8 { CX } else { CZ } }
        12 => { op.q_target = qa; op.c_target = optional_bit(b); Hmr }
        13 => { op.q_control2 = qa; op.q_control1 = qb; op.q_target = QubitId(c as u64); CCX }
        15 => { op.c_condition = BitId(a as u64); PushCondition }
        16 => PopCondition,
        _ => panic!("gate record kind {}", kind),
    };
    op
}
pub fn op_to_row(o: &Op) -> Row {
    use OperationType::*;
    let bit = |x: BitId| if x == NO_BIT { NONE } else { x.0 as u16 }; let mut r = [o.kind as u16, NONE, NONE, NONE];
    match o.kind {
        Register => r[1] = o.r_target.0 as u16,
        AppendToRegister => { r[1] = o.r_target.0 as u16; if o.c_target != NO_BIT { r[0] = 18; r[2] = bit(o.c_target); } else { r[2] = o.q_target.0 as u16; } }
        BitInvert | BitStore0 | BitStore1 => { r[1] = bit(o.c_target); r[2] = bit(o.c_condition); }
        X | Z => { r[1] = o.q_target.0 as u16; r[2] = bit(o.c_condition); }
        CX | CZ => { r[1] = o.q_control1.0 as u16; r[2] = o.q_target.0 as u16; r[3] = bit(o.c_condition); }
        CCX => { r[1] = o.q_control2.0 as u16; r[2] = o.q_control1.0 as u16; r[3] = o.q_target.0 as u16; }
        Hmr => { r[1] = o.q_target.0 as u16; r[2] = bit(o.c_target); }
        PushCondition => r[1] = bit(o.c_condition), PopCondition => (), _ => panic!("op kind"),
    }
    r
}
/// one cell of the output: the real build stores `Op`; tests store the 8-byte record
pub trait Slot: Copy { fn empty() -> Self; fn is_empty(&self) -> bool; fn from_row(r: Row) -> Self; fn to_row(&self) -> Row; }
impl Slot for Op { fn empty() -> Self { Op::empty() } fn is_empty(&self) -> bool { self.kind == OperationType::Neg } fn from_row(r: Row) -> Self { row_to_op(r) } fn to_row(&self) -> Row { op_to_row(self) } }
impl Slot for Row { fn empty() -> Self { [0; 4] } fn is_empty(&self) -> bool { self[0] == 0 } fn from_row(r: Row) -> Self { r } fn to_row(&self) -> Row { *self } }

// ---- tables (pack.lzma)
struct Seg { end: u64, map: Vec<u16>, inv: Vec<u16> }
struct HisPiece { from: u64, to: u64, out: u64, sub: Vec<(u16, u16)>, seg: usize }
struct Item { out: u64, n: u64, block0: usize, blocks: usize, wm: usize }
pub struct ScanPiece { pub out: u64, pub end: u64, pub bit0: u32 }
pub struct Pack { pub records: u64, segs: Vec<Seg>, his: Vec<HisPiece>, items: Vec<Item>, wire_maps: Vec<Vec<u16>>, pub scans: Vec<ScanPiece>, wmr: Vec<(u64, usize)>, ins: Vec<Ins> }
/// one inserted row of a placed piece (an item or a scan): emitted before the piece's record at `off` (record index in the piece's own record list
/// before region replacement) or, when `reg` > 0, before generated record `off` of walkpack region `reg - 1`; the row is in the piece's own id space
/// (wire space for items: before wire map and lane map); the pack's piece lengths include the inserted rows
pub struct Ins { scan: bool, piece: usize, reg: u32, off: u64, row: Row }
const RANGES: usize = u32::MAX as usize; // item.wm == RANGES: the wire map changes along the item (table wmr: first output position, wire map number + 1; 0 = identity)
struct Rd<'a> { d: &'a [u8], p: usize }
impl Rd<'_> { fn u16(&mut self) -> u16 { let v = u16::from_le_bytes(self.d[self.p..self.p + 2].try_into().unwrap()); self.p += 2; v }
    fn u32(&mut self) -> u32 { let v = u32::from_le_bytes(self.d[self.p..self.p + 4].try_into().unwrap()); self.p += 4; v }
    fn u64(&mut self) -> u64 { let v = u64::from_le_bytes(self.d[self.p..self.p + 8].try_into().unwrap()); self.p += 8; v } }
impl Pack {
    fn parse(d: &[u8]) -> Pack { assert!(&d[..8] == b"HYBPACK1", "pack tables"); let mut r = Rd { d, p: 8 };
        let records = r.u64(); let _total = r.u64(); let _literals = r.u64();
        let ns = r.u32() as usize; let mut segs = Vec::with_capacity(ns);
        for _ in 0..ns { let end = r.u64(); let map: Vec<u16> = (0..646).map(|_| r.u16()).collect(); let mut inv = vec![NONE; 633];
            for (id, &l) in map.iter().enumerate() { if l != NONE { assert!(inv[l as usize] == NONE, "lane map"); inv[l as usize] = id as u16; } } segs.push(Seg { end, map, inv }); }
        let seg_of = |o: u64| segs.partition_point(|s| s.end <= o);
        let nh = r.u32() as usize; let mut his = Vec::with_capacity(nh);
        for _ in 0..nh { let from = r.u64(); let to = r.u64(); let out = r.u64(); let k = r.u32() as usize; let sub = (0..k).map(|_| { let a = r.u16(); (a, r.u16()) }).collect();
            let seg = seg_of(out); assert!(seg < segs.len() && out + (to - from) <= segs[seg].end, "his piece crosses a segment"); his.push(HisPiece { from, to, out, sub, seg }); }
        let ni = r.u32() as usize; let items = (0..ni).map(|_| { let out = r.u64(); let n = r.u64(); let block0 = r.u32() as usize; let blocks = r.u32() as usize; Item { out, n, block0, blocks, wm: r.u32() as usize } }).collect();
        let nw = r.u32() as usize; let wire_maps = (0..nw).map(|_| (0..1024).map(|_| r.u16()).collect()).collect();
        let nsc = r.u32() as usize; let scans = (0..nsc).map(|_| { let out = r.u64(); let end = r.u64(); ScanPiece { out, end, bit0: r.u32() } }).collect();
        let nr = r.u32() as usize; let wmr = (0..nr).map(|_| { let p = r.u64(); (p, r.u32() as usize) }).collect();
        let ni2 = r.u32() as usize; let ins = (0..ni2).map(|_| { let k = r.u32(); let reg = r.u32(); let off = r.u64(); let row = [r.u16(), r.u16(), r.u16(), r.u16()]; Ins { scan: k >> 31 == 1, piece: (k & 0x7fff_ffff) as usize, reg, off, row } }).collect();
        assert!(r.p == d.len(), "pack tables length");
        Pack { records, segs, his, items, wire_maps, scans, wmr, ins } }
    /// the inserted rows of one piece, in stream order
    fn ins_of(&self, scan: bool, piece: usize) -> &[Ins] { let lo = self.ins.partition_point(|x| (x.scan, x.piece) < (scan, piece)); let hi = self.ins.partition_point(|x| (x.scan, x.piece) <= (scan, piece)); &self.ins[lo..hi] }
    /// the wire map in force at output position `o`; `ri` is the caller's cursor in the range table
    fn map_at(&self, ri: &mut usize, o: u64) -> Option<&Vec<u16>> { while *ri + 1 < self.wmr.len() && self.wmr[*ri + 1].0 <= o { *ri += 1; } if self.wmr[*ri].1 > 0 { Some(&self.wire_maps[self.wmr[*ri].1 - 1]) } else { None } }
    #[inline] fn seg_of(&self, o: u64) -> usize { self.segs.partition_point(|s| s.end <= o) }
    #[inline] fn piece_of(&self, i: u64) -> Option<usize> { let k = self.his.partition_point(|p| p.to <= i); if k < self.his.len() && self.his[k].from <= i { Some(k) } else { None } }
}
#[inline] fn map_lanes(mut row: Row, map: &[u16]) -> Row { for j in 1..=qubits(row[0]) { let l = map[row[j] as usize]; debug_assert!(l != NONE); row[j] = l; } if row[0] == 2 { row[2] = map[row[2] as usize]; } row }

// ---- his records: literal stream + copy schedule
struct Literals { g: gir::Girs, block: usize, start: u64, rows: Vec<Row> }
impl Literals { fn get(&mut self, li: u64) -> Row {
        while li >= self.start + self.rows.len() as u64 { let next = if self.rows.is_empty() && self.block == 0 && self.start == 0 { 0 } else { self.block + 1 };
            assert!(next < self.g.blocks.len(), "his literal stream ran out");
            if !(self.rows.is_empty() && next == 0) { self.start += self.rows.len() as u64; } self.start += self.g.blocks[next].gap; self.block = next; let g = &self.g; g.decode(next, &mut self.rows); }
        assert!(li >= self.start, "his literal record in a dropped block"); self.rows[(li - self.start) as usize] } }
fn his_stream<S: Slot>(pk: &Pack, out: &mut [S], sh: &Shift) {
    let hs: Vec<i64> = pk.his.iter().map(|p| sh.at(p.out)).collect();
    let plan = plan::Plan::parse(&lzma::decode(include_bytes!("data/plan.lzma")).expect("schedule"));
    let mut lits = Literals { g: gir::Girs::open(include_bytes!("data/his.girs")), block: 0, start: 0, rows: Vec::new() };
    let put = |out: &mut [S], k: usize, i: u64, mut row: Row| { let pc = &pk.his[k]; if !pc.sub.is_empty() { for j in 1..=qubits(row[0]) { if let Some(&(_, t)) = pc.sub.iter().find(|&&(f, _)| f == row[j]) { row[j] = t; } } }
        out[(hs[k] + (pc.out + (i - pc.from)) as i64) as usize] = S::from_row(map_lanes(row, &pk.segs[pc.seg].map)); };
    let get = |out: &[S], i: u64| -> Row { let k = pk.piece_of(i).expect("copy source outside the kept ranges"); let pc = &pk.his[k]; let mut row = out[(hs[k] + (pc.out + (i - pc.from)) as i64) as usize].to_row(); let inv = &pk.segs[pc.seg].inv;
        for j in 1..=qubits(row[0]) { row[j] = inv[row[j] as usize]; } if row[0] == 2 { row[2] = inv[row[2] as usize]; }
        if !pc.sub.is_empty() { for j in 1..=qubits(row[0]) { if let Some(&(f, _)) = pc.sub.iter().find(|&&(_, t)| t == row[j]) { row[j] = f; } } }
        row };
    // fin631 packaging (main session 2026-11-26): his records the final build never keeps are not written, so their literal
    // blocks can be dropped from data/his.girs: records inside the replaced ranges (prune_ranges, unspliced positions) that are
    // not, transitively, the source of a kept record's copy.  Switch: his_prune() (env HIS_PRUNE=1 or the packaged default).
    let need: Option<Vec<u64>> = if his_prune() {
        let rr = prune_ranges(); let in_rr = |o: u64| { let k = rr.partition_point(|r| r.1 <= o); k < rr.len() && rr[k].0 <= o };
        let total = plan.total as u64; let mut need = vec![0u64; (total as usize + 63) / 64];
        let set = |v: &mut Vec<u64>, i: u64| v[(i >> 6) as usize] |= 1u64 << (i & 63);
        for (k, pc) in pk.his.iter().enumerate() { for i in pc.from..pc.to { let o = (hs[k] + (pc.out + (i - pc.from)) as i64) as u64; if !in_rr(o) { set(&mut need, i); } } }
        let mut starts = Vec::with_capacity(plan.items.len()); let mut q = 0u64; for a in &plan.items { starts.push(q); q += a.size as u64; }
        for (ai, a) in plan.items.iter().enumerate().rev() { if a.mode == 0 { continue; } let p0 = starts[ai];
            for i in p0..p0 + a.size as u64 { if need[(i >> 6) as usize] >> (i & 63) & 1 == 1 { let src = if a.mode == 1 { a.src as u64 + (i - p0) } else { a.src as u64 - (i - p0) }; set(&mut need, src); } } }
        if let Ok(path) = std::env::var("HIS_PRUNE_DUMP") { use std::io::Write as _;
            // needed literal indices as intervals [a, b)
            let mut f = std::io::BufWriter::new(std::fs::File::create(&path).expect("HIS_PRUNE_DUMP")); let (mut lit, mut cur): (u64, Option<(u64, u64)>) = (0, None); let mut cnt = 0u64;
            for (ai, a) in plan.items.iter().enumerate() { if a.mode == 0 { let p0 = starts[ai];
                for i in p0..p0 + a.size as u64 { if need[(i >> 6) as usize] >> (i & 63) & 1 == 1 && pk.piece_of(i).is_some() { let li = lit + (i - p0); cnt += 1;
                    cur = match cur { Some((x, y)) if y == li => Some((x, li + 1)), Some((x, y)) => { writeln!(f, "{x} {y}").unwrap(); Some((li, li + 1)) }, None => Some((li, li + 1)) }; } }
                lit += a.size as u64; } }
            if let Some((x, y)) = cur { writeln!(f, "{x} {y}").unwrap(); } eprintln!("his prune: {cnt} needed literal records of {} (dump {path})", plan.literals); }
        Some(need) } else { None };
    let needed = |i: u64| need.as_ref().map_or(true, |v| v[(i >> 6) as usize] >> (i & 63) & 1 == 1);
    // a pruned record's slot gets a classical no-op (BitStore0 on the scratch bit 65499): every slot of the list stays readable
    let ph = |out: &mut [S], k: usize, i: u64| { let pc = &pk.his[k]; out[(hs[k] + (pc.out + (i - pc.from)) as i64) as usize] = S::from_row([4, 65499, NONE, NONE]); };
    let (mut pos, mut lit) = (0u64, 0u64);
    for a in &plan.items { let size = a.size as u64;
        // the kept pieces that meet [pos, pos + size)
        let mut k = pk.his.partition_point(|p| p.to <= pos);
        while k < pk.his.len() && pk.his[k].from < pos + size { let pc = &pk.his[k]; let lo = pc.from.max(pos); let hi = pc.to.min(pos + size);
            match a.mode {
                0 => for i in lo..hi { if !needed(i) { ph(out, k, i); continue; } let row = lits.get(lit + (i - pos)); put(out, k, i, row); },
                1 => { let m = &plan.maps[a.map]; for i in lo..hi { if !needed(i) { ph(out, k, i); continue; } let row = get(out, a.src as u64 + (i - pos)); put(out, k, i, m.apply(row)); } }
                _ => { let m = &plan.maps[a.map]; for i in lo..hi { if !needed(i) { ph(out, k, i); continue; } let row = get(out, a.src as u64 - (i - pos)); put(out, k, i, m.apply(row)); } }
            }
            k += 1; }
        if a.mode == 0 { lit += size; } pos += size; }
}

/// fin631 packaging: prune switch (env HIS_PRUNE=1 forces it; PRUNE_HIS = the packaged default)
pub const PRUNE_HIS: bool = FINAL631;
pub fn his_prune() -> bool { std::env::var("HIS_PRUNE").map(|v| v == "1").unwrap_or(PRUNE_HIS) }
/// the unspliced ranges whose his records the final build replaces (hybrid regions; cf631 regions mapped back through the
/// hybrid splice; the pre3 column-1 ranges the final build uses: walks 1 and 3), each shrunk by 16 records at both ends so the
/// splices' boundary fingerprints still see the original rows; sorted, disjoint
pub fn prune_ranges() -> Vec<(u64, u64)> {
    let mut v: Vec<(u64, u64)> = hybrid::REGIONS.iter().map(|r| (r.start, r.end)).collect();
    for c in cf631::REGIONS.iter() { // hybrid-spliced -> unspliced: undo the growth of the hybrid regions that end before it
        let mut d = 0i64; for r in hybrid::REGIONS.iter() { let new_end = (r.end as i64 + d + hybrid::gen_len(r) as i64 - (r.end - r.start) as i64) as u64; if new_end <= c.start { d += hybrid::gen_len(r) as i64 - (r.end - r.start) as i64; } }
        v.push(((c.start as i64 - d) as u64, (c.end as i64 - d) as u64)); }
    for j in [0usize, 2] { let x = &hybrid::X_REGIONS[j]; v.push((x.start, x.end)); }
    v.sort(); let mut out: Vec<(u64, u64)> = Vec::new();
    for (a, b) in v { assert!(out.last().map_or(true, |l| l.1 <= a), "prune ranges overlap"); if b > a + 32 { out.push((a + 16, b - 16)); } }
    out
}
// ---- our record items (multiply, divide, glue)
fn items<S: Slot>(pk: &Pack, out: &mut [S], sh: &Shift, hooked: &[Option<i1::Hooked>]) {
    let g = gir::Girs::open(include_bytes!("data/blocks.girs")); let mut rows: Vec<Row> = Vec::new();
    for (ii, it) in pk.items.iter().enumerate() {
        // i1 hook: a rewritten item (wire space, inserts placed) replaces the raw block (w2 mechanism; i1::emit_hooked)
        if let Some(h) = &hooked[ii] { let dsh = sh.at(it.out); let mut j = 0u64;
            i1::emit_hooked(pk, ii, h, &mut |_, row| { out[(dsh + (it.out + j) as i64) as usize] = S::from_row(row); j += 1; }); continue; }
        let mut o = it.out; let dsh = sh.at(it.out); let mut seg = pk.seg_of(o); let ranged = it.wm == RANGES; let wm0 = if it.wm > 0 && !ranged { Some(&pk.wire_maps[it.wm - 1]) } else { None };
        let mut ri = if ranged { pk.wmr.partition_point(|x| x.0 <= it.out) - 1 } else { 0 };
        // one output row: wire map (fixed or by range), then segment lane map
        let mut put = |r: Row| { let mut row = r; let wm = if ranged { pk.map_at(&mut ri, o) } else { wm0 };
            if let Some(w) = wm { for j in 1..=qubits(row[0]) { row[j] = w[row[j] as usize]; } }
            while o >= pk.segs[seg].end { seg += 1; } out[(dsh + o as i64) as usize] = S::from_row(map_lanes(row, &pk.segs[seg].map)); o += 1; };
        // inserts due before (reg, off)
        let ins = pk.ins_of(false, ii); let mut ip = 0usize;
        let mut due = |put: &mut dyn FnMut(Row), reg: u32, off: u64| { while ip < ins.len() && ins[ip].reg == reg && ins[ip].off == off { put(ins[ip].row); ip += 1; } };
        // walk regions (walkpack.rs): the records [start, end) of the raw item are replaced by the generated ones
        let mut regs = walkpack::regions(ii).peekable(); let mut idx = 0u64;
        if unrollpack::applies(ii) { // unrolled block (unroll.rs): decode the whole raw item, transform it; insert offsets (region 0) count the UNROLLED records
            assert!(regs.peek().is_none(), "item {} is both unrolled and walk-packed", ii);
            let mut raw: Vec<Row> = Vec::new(); for b in it.block0..it.block0 + it.blocks { g.decode(b, &mut rows); raw.extend_from_slice(&rows); }
            for r in unrollpack::transform(ii, raw) { due(&mut put, 0, idx); put(r); idx += 1; } }
        else { for b in it.block0..it.block0 + it.blocks { g.decode(b, &mut rows);
            for &r in rows.iter() {
                match regs.peek().copied() { Some((k, rg)) if idx >= rg.start => { if idx == rg.start { due(&mut put, 0, idx); let mut j = 0u64; walkpack::emit(rg, &mut |row| { due(&mut put, k as u32 + 1, j); put(row); j += 1; }); } if idx + 1 == rg.end { regs.next(); } } _ => { due(&mut put, 0, idx); put(r) } }
                idx += 1; } } }
        due(&mut put, 0, idx); assert!(ip == ins.len(), "item {} inserts not placed", ii);
        assert!(o == it.out + it.n, "item length"); }
}
// ---- our scans: trace -> records (in stream order: the classical layer's bit allocators carry over)
/// lane T (635): a scan with no insert rows and no range rows may change its length (grow or shrink) (scan::run's measurement-based levers); every later
/// placed piece moves by the growth of the scans before it.  A scan with inserts or ranges is expanded with the levers off and keeps its slot.
fn scan_rows(pk: &Pack) -> Vec<Vec<Row>> {
    let data: &[u8] = include_bytes!("data/scans.trc"); assert!(&data[..8] == b"SCANS1\0\0", "scan traces");
    let n = u32::from_le_bytes(data[8..12].try_into().unwrap()) as usize; assert!(n == pk.scans.len(), "scan count"); let mut at = 12 + 4 * n; let mut cls = scan::Classical::new();
    let mut all = Vec::with_capacity(n);
    for (i, sp) in pk.scans.iter().enumerate() { let len = u32::from_le_bytes(data[12 + 4 * i..16 + 4 * i].try_into().unwrap()) as usize; let trace = lzma::decode(&data[at..at + len]).expect("scan trace"); at += len; let trace = scq631::trace_for(i, trace);   // q631 / sc hook: identity unless a switch in scq631.rs is on
        let trace = si631::trace_for(i, trace);   // q631 / si hook (scans I, I' at 15 bits): identity unless a switch in si631.rs is on
        let trace = bs631::trace_for(i, trace);   // q631 / bs hook (scans D, F, F' with a second free lane): identity unless a switch in bs631.rs is on
        let seg = pk.seg_of(sp.out); assert!(sp.end <= pk.segs[seg].end, "scan crosses a segment"); let map = &pk.segs[seg].map; let (mut o, end) = (sp.out as usize, sp.end as usize);
        // a scan is ranged when the range table has a row at its first position (the rows apply to its ids)
        let k0 = pk.wmr.partition_point(|x| x.0 < sp.out); let ranged = k0 < pk.wmr.len() && pk.wmr[k0].0 == sp.out; let mut ri = k0;
        let ins = pk.ins_of(true, i); let mut ip = 0usize; let mut cnt = 0u64; let fixed = ranged || !ins.is_empty();
        let mut rows: Vec<Row> = Vec::with_capacity(end - o + if fixed { 0 } else { (end - o) / 16 });
        let mut emit = |row: Row| { let mut row = row; if ranged { if let Some(w) = pk.map_at(&mut ri, o as u64) { for j in 1..=qubits(row[0]) { row[j] = w[row[j] as usize]; } } }
            rows.push(map_lanes(row, map)); o += 1; };
        { let mut put = |row: Row| { while ip < ins.len() && ins[ip].off == cnt { emit(ins[ip].row); ip += 1; } emit(row); cnt += 1; };
            // dispatch of 8549bc4e: scan 0 by borrow_scan, a scan with inserts or ranges by the original scan.rs, every other scan by opt_scan (lane T levers on)
            vm::TOP_BIT.with(|t| t.set(!fixed));
            if i == 0 { assert!(!ranged && ins.is_empty()); borrow_scan::run(&trace, sp.bit0, &mut cls, &mut put, KG_ZERO[i]); }
            else if i == 4 && i1::BP_NATIVE { assert!(!fixed, "native B-prime requires an unranged scan without insertion rows"); bp_scan::run(&trace, sp.bit0, &mut cls, &mut put, -1, 214, true); }   // (internal) dispatch
            else if fixed { scan::run(&trace, sp.bit0, &mut cls, &mut put, KG_ZERO[i]); }
            else { opt_scan::run(&trace, sp.bit0, &mut cls, &mut put, KG_ZERO[i], true); }
            vm::TOP_BIT.with(|t| t.set(false)); }
        while ip < ins.len() && ins[ip].off == cnt { emit(ins[ip].row); ip += 1; }
        assert!(ip == ins.len(), "scan {} inserts not placed", i); assert!(!fixed || rows.len() == end - sp.out as usize, "scan {} length", i); 
        all.push(rows); }
    all
}
/// output shift of an original stream position: the growth of every scan that ends at or before it
pub struct Shift { ends: Vec<(u64, i64)> }
impl Shift { fn at(&self, o: u64) -> i64 { let k = self.ends.partition_point(|x| x.0 <= o); if k == 0 { 0 } else { self.ends[k - 1].1 } } }
/// per scan (order B D F I B' D' F' I'): local lane that is 0 at every hit-test MCX (the sweep adders' own clean carry-in lane c0), -1 = old borrowed-lane form.
/// Lever switch: all -1 = the emission of the tree without the lever (other lane's build-636y; Khattar-Gidney MCX in vm.rs)
const KG_ZERO: [i32; 8] = i1::KG_ZERO;   // i1: switch SCAN_B_KG_OFF; base633 value [249, 226, 235, -1, 214, 230, 230, -1];   // 633 traces (carry-in id of each trace from this tree's adder log, measured zero at every hit test on three panels): B CODEX e13 / w27, D 17 bits NB 40, F 18 NB 42 (ladder), B prime CODEX e13 / w27, D prime 18 NB 41 (ladder), F prime 17 NB 39 (all on 633 lanes; third 633)
/// Fiat-Shamir nonce: the op list ends with 96 X gates, in pairs on qubit 0 or qubit 1 (each pair is the identity); pair j
/// acts on qubit (NONCE >> j) & 1.  The nonce changes the evaluator's shot seed and nothing else.
const NONCE: u64 = 1;
pub const TAIL: usize = 96;
pub fn nonce_row(i: usize, nonce: u64) -> Row { [6, ((nonce >> (i / 2)) & 1) as u16, NONE, NONE] }
// ---- peephole pass over the assembled op list: an X / CX / CCX that meets an identical earlier one cancels with it, provided
// every op in between that shares a qubit with it commutes with it (two such gates commute when neither one's target is a
// control of the other), both carry the same classical condition (bit unchanged in between) and sit in the same condition
// scope.  Per qubit the last DEPTH surviving ops are remembered; measurements and phase gates are barriers on their qubits.
const DEPTH: usize = 128;
#[derive(Clone, Copy)]
struct Seen { idx: u32, sig: u64, cver: u32, scope: u32, target: bool, live: bool }
struct Ring { e: [Seen; DEPTH], head: usize, len: usize }
impl Ring {
    fn push(&mut self, s: Seen) { if self.len == DEPTH { self.head = (self.head + 1) % DEPTH; self.len -= 1; } self.e[(self.head + self.len) % DEPTH] = s; self.len += 1; }
    /// k = 0 is the most recent entry
    #[inline] fn at(&self, k: usize) -> &Seen { &self.e[(self.head + self.len - 1 - k) % DEPTH] }
    fn kill(&mut self, idx: u32) { for k in 0..self.len { let j = (self.head + self.len - 1 - k) % DEPTH; if self.e[j].live && self.e[j].idx == idx { self.e[j].live = false; return; } } }
}
/// cancels pairs inside out[..n], compacts, and returns the new length
fn peephole<S: Slot>(out: &mut [S], n: usize) -> usize {
    let none = Seen { idx: 0, sig: 0, cver: 0, scope: 0, target: false, live: false };
    let mut rings: Vec<Ring> = (0..640).map(|_| Ring { e: [none; DEPTH], head: 0, len: 0 }).collect();
    let mut ver = vec![0u32; 65536]; let (mut scope, mut next_scope) = (0u32, 1u32); let mut scopes: Vec<u32> = Vec::new();
    for i in 0..n { let [k, x, y, z] = out[i].to_row();
        match k {
            3 | 4 | 5 => ver[x as usize] = ver[x as usize].wrapping_add(1),
            15 => { scopes.push(scope); scope = next_scope; next_scope += 1; }
            16 => scope = scopes.pop().unwrap_or(0),
            12 | 7 | 9 => { if k == 12 && y != NONE { ver[y as usize] = ver[y as usize].wrapping_add(1); }
                let b = Seen { idx: i as u32, sig: u64::MAX, cver: 0, scope: 0, target: true, live: true }; rings[x as usize].push(b); if k == 9 { rings[y as usize].push(b); } }
            6 | 8 | 13 => { let (t, cs, cond): (u16, [u16; 2], u16) = match k { 13 => (z, [x, y], NONE), 8 => (y, [x, NONE], z), _ => (x, [NONE, NONE], y) };
                let sig = ((k as u64) << 48) | ((x as u64) << 32) | ((y as u64) << 16) | z as u64; let cver = if cond != NONE { ver[cond as usize] } else { 0 };
                // the twin on the target's ring, with only commuting (target-type) ops after it
                let mut twin: Option<u32> = None; { let r = &rings[t as usize]; for q in 0..r.len { let o = r.at(q); if !o.live { continue; } if o.sig == sig && o.cver == cver && o.scope == scope && o.target { twin = Some(o.idx); break; } if !o.target || o.sig == u64::MAX { break; } } }
                let mut ok = twin.is_some();
                if let Some(p) = twin { for &c in &cs { if c == NONE { continue; } let r = &rings[c as usize]; let mut found = false; for q in 0..r.len { let o = r.at(q); if !o.live { continue; } if o.idx == p { found = true; break; } if o.target { break; } } if !found { ok = false; break; } } }
                if ok { let p = twin.unwrap(); rings[t as usize].kill(p); for &c in &cs { if c != NONE { rings[c as usize].kill(p); } } out[p as usize] = S::empty(); out[i] = S::empty(); }
                else { rings[t as usize].push(Seen { idx: i as u32, sig, cver, scope, target: true, live: true }); for &c in &cs { if c != NONE { rings[c as usize].push(Seen { idx: i as u32, sig, cver, scope, target: false, live: true }); } } } }
            _ => {} } }
    let mut m = 0usize; for i in 0..n { if !out[i].is_empty() { if m != i { out[m] = out[i]; } m += 1; } }
    m
}
// ---- negative controls: X(q) G X(q), where G is the only op on q in between and q is a control of G, is G followed by G
// without that control (CCX(q, b, t) -> CX(b, t); CX(q, t) -> X(t)): one op less, same Toffoli count.  The second gate takes
// the slot of the closing X, so nothing between G and that X may touch G's other qubits (or change its classical condition).
#[derive(Clone, Copy)]
struct Neg { state: u8, xi: u32, gj: u32, scope: u32 }
const NEG_WINDOW: usize = 48;
fn neg_controls<S: Slot>(out: &mut [S], n: usize) -> usize {
    let mut q: Vec<Neg> = vec![Neg { state: 0, xi: 0, gj: 0, scope: 0 }; 640];
    let (mut scope, mut next_scope) = (0u32, 1u32); let mut scopes: Vec<u32> = Vec::new();
    for i in 0..n { if out[i].is_empty() { continue; } let [k, x, y, z] = out[i].to_row();
        match k {
            15 => { scopes.push(scope); scope = next_scope; next_scope += 1; }
            16 => scope = scopes.pop().unwrap_or(0),
            6 if y == NONE => { let e = q[x as usize];
                let mut done = false;
                if e.state == 2 && e.scope == scope && i - (e.gj as usize) <= NEG_WINDOW { let j = e.gj as usize; let [gk, ga, gb, gc] = out[j].to_row();
                    // the gate that replaces the closing X, and the qubits / bit it depends on
                    let (extra, o1, o2, cond): (Row, u16, u16, u16) = if gk == 13 { let other = if ga == x { gb } else { ga }; ([8, other, gc, NONE], other, gc, NONE) } else { ([6, gb, gc, NONE], gb, NONE, gc) };
                    let mut ok = true;
                    for m in j + 1..i { if out[m].is_empty() { continue; } let [mk, ma, mb, mc] = out[m].to_row();
                        let nq = qubits(mk); let r = [ma, mb, mc];
                        for t in 0..nq { if r[t] == o1 || r[t] == o2 { ok = false; } }
                        if mk == 15 || mk == 16 { ok = false; }
                        if cond != NONE && ((matches!(mk, 3 | 4 | 5) && ma == cond) || (mk == 12 && mb == cond)) { ok = false; }
                        if !ok { break; } }
                    if ok { out[e.xi as usize] = S::empty(); out[i] = S::from_row(extra); done = true;
                        q[x as usize].state = 0;
                        // the new op touches its own qubits
                        if extra[0] == 8 { q[extra[1] as usize].state = 0; q[extra[2] as usize].state = 0; }
                        else if extra[2] == NONE { q[extra[1] as usize] = Neg { state: 1, xi: i as u32, gj: 0, scope }; } else { q[extra[1] as usize].state = 0; } } }
                if !done { q[x as usize] = Neg { state: 1, xi: i as u32, gj: 0, scope }; } }
            13 | 8 => { let (cs, t): ([u16; 2], u16) = if k == 13 { ([x, y], z) } else { ([x, NONE], y) };
                for &c in &cs { if c == NONE { continue; } let e = &mut q[c as usize]; if e.state == 1 && e.scope == scope { e.state = 2; e.gj = i as u32; } else { e.state = 0; } }
                q[t as usize].state = 0; }
            6 | 7 | 12 => q[x as usize].state = 0,
            9 => { q[x as usize].state = 0; q[y as usize].state = 0; }
            _ => {} } }
    let mut m = 0usize; for i in 0..n { if !out[i].is_empty() { if m != i { out[m] = out[i]; } m += 1; } }
    m
}
pub fn build_slots<S: Slot + Send>(optimise: bool) -> Vec<S> { build_slots_h(optimise, hybrid::ON) }
/// hp1: `hyb` = splice the hybrid walk regions (hybrid.rs) into the assembled list before the relabelling
pub fn build_slots_h<S: Slot + Send>(optimise: bool, hyb: bool) -> Vec<S> { build_slots_hcq(optimise, hyb, hyb && (cf631::ON || q631::forced_cf()), q631::ON || q631::forced()) }
/// q631 / int1: `q` = apply the ITEM 4 rewrites (q631.rs) right after the relabelling (cf off)
pub fn build_slots_hq<S: Slot + Send>(optimise: bool, hyb: bool, q: bool) -> Vec<S> { build_slots_hcq(optimise, hyb, false, q) }
/// cf1: `cf` = also splice the new forward upper walk into walks 1 and 3 (cf631.rs; needs `hyb`); the ITEM 4 flag follows its switch
pub fn build_slots_hc<S: Slot + Send>(optimise: bool, hyb: bool, cf: bool) -> Vec<S> { build_slots_hcq(optimise, hyb, cf, q631::ON || q631::forced()) }
/// int2: THE chain, three independent flags: `hyb` = hybrid splice, `cf` = new forward splice (only with hyb), `q` = the ITEM 4 rewrites.
/// Order: assemble, hybrid splice, cf splice, relabelling (i1::apply), ITEM 4 rewrites.  hyb false / cf false / q false = the old paths.
pub fn build_slots_hcq<S: Slot + Send>(optimise: bool, hyb: bool, cf: bool, q: bool) -> Vec<S> {
    let (pk, sh, mut out, n, rt) = assemble_c::<S>(hyb, cf);
    // i1: per-stretch relabelling (lane 632 hidden where the planner found a free lane), moves inserted
    let n = if let Some(t) = &rt { i1::apply(&mut out, n, t) } else { n };
    let n = if q { let t = rt.as_ref().expect("q631 needs the relabelling table"); let (s, e) = q631::item4_range_c(&pk, &sh, t, hyb, cf); q631::apply_item4_c(&mut out, n, s, e, true, cf) } else { n };
    let n = if rb631::active() { rb631::apply(&pk, &sh, rt.as_ref(), hyb, cf, &mut out, n) } else { n };   // q631 / rb hook: 15th erased bit (id 497) in the reverse brackets; OFF = unchanged
    let n = if rp1::active() { rp1::apply_soft(&mut out, n) } else { n };   // q631 / rp1 hook: second hidden lane (soft mode); OFF = unchanged
    let m = if optimise { let m = peephole(&mut out, n); let m = neg_controls(&mut out, m); peephole(&mut out, m) } else { n };
    for i in 0..TAIL { out[m + i] = S::from_row(nonce_row(i, NONCE)); }
    out.truncate(m + TAIL);
    out
}
/// the tree's assembly (unchanged) up to the relabelling: (pack, shift, slots, length, relabelling table); hp1: + the
/// hybrid splice when `hyb` (it re-binds the table to the spliced stream, hybrid.rs)
fn assemble<S: Slot + Send>(hyb: bool) -> (Pack, Shift, Vec<S>, usize, Option<i1::Relabel>) { assemble_c(hyb, false) }
/// cf1: the same + the cf631 splice when `cf` (on the hybrid-spliced list; it re-binds the table again, cf631.rs)
fn assemble_c<S: Slot + Send>(hyb: bool, cf: bool) -> (Pack, Shift, Vec<S>, usize, Option<i1::Relabel>) {
    let mut pk = Pack::parse(&lzma::decode(include_bytes!("data/pack.lzma")).expect("pack tables"));
    walkpack::apply(&mut pk);
    unrollpack::check(&pk);
    i1::w4_apply(&mut pk);
    let srows = scan_rows(&pk);
    // i1 (memory, time; output identical): the hooked items have fixed lengths (i1::hook_lens, asserted when generated), so the
    // slot vector is allocated before any hook exists; the scan rows are placed and freed first; the hooks are generated on helper
    // threads while this thread writes the his stream; items() then copies them in and they are freed.
    let hlen = i1::hook_lens(&pk);
    let mut deltas: Vec<(u64, i64)> = pk.scans.iter().enumerate().map(|(i, sp)| (sp.end, srows[i].len() as i64 - (sp.end - sp.out) as i64)).collect();
    for (ii, h) in hlen.iter().enumerate() { if let Some(l) = h { let it = &pk.items[ii]; deltas.push((it.out + it.n, *l as i64 - it.n as i64)); } }
    deltas.sort_by_key(|x| x.0);
    let mut ends: Vec<(u64, i64)> = Vec::new(); let mut g = 0i64; for (pos, d) in deltas { g += d; ends.push((pos, g)); }
    let sh = Shift { ends };
    let rt = i1::table();
    let n = (pk.records as i64 + g) as usize; let mut out: Vec<S> = vec![S::empty(); n + i1::extra(&rt) + TAIL];
    for (sp, rows) in pk.scans.iter().zip(srows.into_iter()) { let o = (sp.out as i64 + sh.at(sp.out)) as usize;
        for (j, r) in rows.into_iter().enumerate() { out[o + j] = S::from_row(r); } }
    let ((), hooked) = i1::with_hooks(&pk, || his_stream(&pk, &mut out, &sh));
    i1::check_hook_lens(&hooked, &hlen);
    items(&pk, &mut out, &sh, &hooked); drop(hooked);
    let (n, rt) = if hyb { hybrid::splice(&pk, &sh, &mut out, n, rt) } else { (n, rt) };
    let (n, rt) = if cf { assert!(hyb, "cf631 needs the hybrid splice"); cf631::splice(&pk, &mut out, n, rt) } else { (n, rt) };
    let (n, rt) = int4::hook(&pk, &sh, &mut out, n, rt, hyb, cf);   // q631 / int4 hook: mask 0 = list and table unchanged (only the position map is cleared)
    (pk, sh, out, n, rt)
}
/// fin631 PACKAGE (main session 2026-11-26): every switch of the 631-qubit build at its final value when no env var overrides it
/// (local tools may still set the env vars).  The values are the ones the development round and the 180,480-shot holdout verified.
pub const FINAL631: bool = true;
pub const FINAL_RESETS: &str = "4:100224713:100224747:624:65510,12:98665221:98667276:112:65511,12:12267269:12267394:515:65512,12:84773006:84773009:515:65513,10:62234969:561783:620:65514,10:11227697:442500:619:65515,10:34365888:5909:629:65516,10:62232739:1070:630:65517,10:62233806:4760:629:65518";
pub const FINAL_SRESETS: &str = "1:133855502:16207:250:65519";
pub fn build() -> Vec<Op> { post_pass::build_final() }
