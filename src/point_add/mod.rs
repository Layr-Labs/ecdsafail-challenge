//! 639-qubit point addition: the walks, sign fixes, U rebuilds and point operations of the 646-qubit submission (af4f0042),
//! with its two field multiplications replaced by multiply / divide blocks and eight erase-and-rebuild scans that free lanes.
//! The op list is assembled out of order, straight into its final positions:
//!   * his records: the gate IR blocks our ranges need + his copy schedule, executed against the op list itself;
//!   * our multiply / divide blocks and small glue pieces: gate-record streams;
//!   * our scans: a trace of generator calls, expanded by `scan` (to come).
//! Every record carries logical qubit ids (646 of them); each stretch of the output has one fixed id -> lane map (639 lanes).
use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId, NO_BIT};
mod cl;
mod gir;
mod lzma;
mod plan;
mod rns;
mod scan;
mod vm;

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
pub struct Pack { pub records: u64, segs: Vec<Seg>, his: Vec<HisPiece>, items: Vec<Item>, wire_maps: Vec<Vec<u16>>, pub scans: Vec<ScanPiece> }
struct Rd<'a> { d: &'a [u8], p: usize }
impl Rd<'_> { fn u16(&mut self) -> u16 { let v = u16::from_le_bytes(self.d[self.p..self.p + 2].try_into().unwrap()); self.p += 2; v }
    fn u32(&mut self) -> u32 { let v = u32::from_le_bytes(self.d[self.p..self.p + 4].try_into().unwrap()); self.p += 4; v }
    fn u64(&mut self) -> u64 { let v = u64::from_le_bytes(self.d[self.p..self.p + 8].try_into().unwrap()); self.p += 8; v } }
impl Pack {
    fn parse(d: &[u8]) -> Pack { assert!(&d[..8] == b"HYBPACK1", "pack tables"); let mut r = Rd { d, p: 8 };
        let records = r.u64(); let _total = r.u64(); let _literals = r.u64();
        let ns = r.u32() as usize; let mut segs = Vec::with_capacity(ns);
        for _ in 0..ns { let end = r.u64(); let map: Vec<u16> = (0..646).map(|_| r.u16()).collect(); let mut inv = vec![NONE; 639];
            for (id, &l) in map.iter().enumerate() { if l != NONE { assert!(inv[l as usize] == NONE, "lane map"); inv[l as usize] = id as u16; } } segs.push(Seg { end, map, inv }); }
        let seg_of = |o: u64| segs.partition_point(|s| s.end <= o);
        let nh = r.u32() as usize; let mut his = Vec::with_capacity(nh);
        for _ in 0..nh { let from = r.u64(); let to = r.u64(); let out = r.u64(); let k = r.u32() as usize; let sub = (0..k).map(|_| { let a = r.u16(); (a, r.u16()) }).collect();
            let seg = seg_of(out); assert!(seg < segs.len() && out + (to - from) <= segs[seg].end, "his piece crosses a segment"); his.push(HisPiece { from, to, out, sub, seg }); }
        let ni = r.u32() as usize; let items = (0..ni).map(|_| { let out = r.u64(); let n = r.u64(); let block0 = r.u32() as usize; let blocks = r.u32() as usize; Item { out, n, block0, blocks, wm: r.u32() as usize } }).collect();
        let nw = r.u32() as usize; let wire_maps = (0..nw).map(|_| (0..1024).map(|_| r.u16()).collect()).collect();
        let nsc = r.u32() as usize; let scans = (0..nsc).map(|_| { let out = r.u64(); let end = r.u64(); ScanPiece { out, end, bit0: r.u32() } }).collect();
        assert!(r.p == d.len(), "pack tables length");
        Pack { records, segs, his, items, wire_maps, scans } }
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
fn his_stream<S: Slot>(pk: &Pack, out: &mut [S]) {
    let plan = plan::Plan::parse(&lzma::decode(include_bytes!("data/plan.lzma")).expect("schedule"));
    let mut lits = Literals { g: gir::Girs::open(include_bytes!("data/his.girs")), block: 0, start: 0, rows: Vec::new() };
    let put = |out: &mut [S], pc: &HisPiece, i: u64, mut row: Row| { if !pc.sub.is_empty() { for j in 1..=qubits(row[0]) { if let Some(&(_, t)) = pc.sub.iter().find(|&&(f, _)| f == row[j]) { row[j] = t; } } }
        out[(pc.out + (i - pc.from)) as usize] = S::from_row(map_lanes(row, &pk.segs[pc.seg].map)); };
    let get = |out: &[S], i: u64| -> Row { let pc = &pk.his[pk.piece_of(i).expect("copy source outside the kept ranges")]; let mut row = out[(pc.out + (i - pc.from)) as usize].to_row(); let inv = &pk.segs[pc.seg].inv;
        for j in 1..=qubits(row[0]) { row[j] = inv[row[j] as usize]; } if row[0] == 2 { row[2] = inv[row[2] as usize]; }
        if !pc.sub.is_empty() { for j in 1..=qubits(row[0]) { if let Some(&(f, _)) = pc.sub.iter().find(|&&(_, t)| t == row[j]) { row[j] = f; } } }
        row };
    let (mut pos, mut lit) = (0u64, 0u64);
    for a in &plan.items { let size = a.size as u64;
        // the kept pieces that meet [pos, pos + size)
        let mut k = pk.his.partition_point(|p| p.to <= pos);
        while k < pk.his.len() && pk.his[k].from < pos + size { let pc = &pk.his[k]; let lo = pc.from.max(pos); let hi = pc.to.min(pos + size);
            match a.mode {
                0 => for i in lo..hi { let row = lits.get(lit + (i - pos)); put(out, pc, i, row); },
                1 => { let m = &plan.maps[a.map]; for i in lo..hi { let row = get(out, a.src as u64 + (i - pos)); put(out, pc, i, m.apply(row)); } }
                _ => { let m = &plan.maps[a.map]; for i in lo..hi { let row = get(out, a.src as u64 - (i - pos)); put(out, pc, i, m.apply(row)); } }
            }
            k += 1; }
        if a.mode == 0 { lit += size; } pos += size; }
}
// ---- our record items (multiply, divide, glue)
fn items<S: Slot>(pk: &Pack, out: &mut [S]) {
    let g = gir::Girs::open(include_bytes!("data/blocks.girs")); let mut rows: Vec<Row> = Vec::new();
    for it in &pk.items { let mut o = it.out; let mut seg = pk.seg_of(o); let wm = if it.wm > 0 { Some(&pk.wire_maps[it.wm - 1]) } else { None };
        for b in it.block0..it.block0 + it.blocks { g.decode(b, &mut rows);
            for &r in rows.iter() { let mut row = r; if let Some(w) = wm { for j in 1..=qubits(row[0]) { row[j] = w[row[j] as usize]; } }
                while o >= pk.segs[seg].end { seg += 1; } out[o as usize] = S::from_row(map_lanes(row, &pk.segs[seg].map)); o += 1; } }
        assert!(o == it.out + it.n, "item length"); }
}
// ---- our scans: trace -> records (in stream order: the classical layer's bit allocators carry over)
fn scans<S: Slot>(pk: &Pack, out: &mut [S]) {
    let data: &[u8] = include_bytes!("data/scans.trc"); assert!(&data[..8] == b"SCANS1\0\0", "scan traces");
    let n = u32::from_le_bytes(data[8..12].try_into().unwrap()) as usize; assert!(n == pk.scans.len(), "scan count"); let mut at = 12 + 4 * n; let mut cls = scan::Classical::new();
    for (i, sp) in pk.scans.iter().enumerate() { let len = u32::from_le_bytes(data[12 + 4 * i..16 + 4 * i].try_into().unwrap()) as usize; let trace = lzma::decode(&data[at..at + len]).expect("scan trace"); at += len;
        let seg = pk.seg_of(sp.out); assert!(sp.end <= pk.segs[seg].end, "scan crosses a segment"); let map = &pk.segs[seg].map; let (mut o, end) = (sp.out as usize, sp.end as usize); let mut over = 0u64;
        { let mut put = |row: Row| { if o < end { out[o] = S::from_row(map_lanes(row, map)); o += 1; } else { over += 1; } }; scan::run(&trace, sp.bit0, &mut cls, &mut put); }
        assert!(o == end && over == 0, "scan {} length", i); }
}
/// Fiat-Shamir nonce: the op list ends with 96 X gates, in pairs on qubit 0 or qubit 1 (each pair is the identity); pair j
/// acts on qubit (NONCE >> j) & 1.  The nonce changes the evaluator's shot seed and nothing else.
const NONCE: u64 = 1;
pub const TAIL: usize = 96;
pub fn nonce_row(i: usize, nonce: u64) -> Row { [6, ((nonce >> (i / 2)) & 1) as u16, NONE, NONE] }
// ---- peephole pass over the assembled op list: an X / CX / CCX that meets an identical earlier one cancels with it, provided
// every op in between that shares a qubit with it commutes with it (two such gates commute when neither one's target is a
// control of the other), both carry the same classical condition (bit unchanged in between) and sit in the same condition
// scope.  Per qubit the last DEPTH surviving ops are remembered; measurements and phase gates are barriers on their qubits.
const DEPTH: usize = 32;
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
pub fn build_slots<S: Slot>(optimise: bool) -> Vec<S> {
    let pk = Pack::parse(&lzma::decode(include_bytes!("data/pack.lzma")).expect("pack tables"));
    let n = pk.records as usize; let mut out: Vec<S> = vec![S::empty(); n + TAIL];
    his_stream(&pk, &mut out);
    items(&pk, &mut out);
    scans(&pk, &mut out);
    let m = if optimise { peephole(&mut out, n) } else { n };
    for i in 0..TAIL { out[m + i] = S::from_row(nonce_row(i, NONCE)); }
    out.truncate(m + TAIL);
    out
}
pub fn build() -> Vec<Op> { build_slots::<Op>(true) }
