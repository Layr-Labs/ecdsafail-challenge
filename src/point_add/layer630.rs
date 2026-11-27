// Third physical layer for 630 slots (drop-in for composition::output; `segments`, `arity` and `varint` are
// the existing composition items). 631 logical lanes, 630 physical slots: the logical HOLE has no slot. It is
// zero when it becomes the hole (or, for a copy hole, equal to its source lane, or to its complement) and no
// record names it while it is the hole. A switch gives the hole the slot of lane `to` and makes `to` the hole:
// a pure relabel. A copy hole is cleared by CX(src,to) [+X] before the switch and restored the same way when it
// is next named; those rows are wrapped by popping and re-pushing every open condition guard. After the body,
// 3-CX swaps return the 512 output lanes to their declared slots, then the 96 nonce rows
// (post_pass::tail_rows, physical lanes 0/1) follow unchanged, so a new NONCE changes only the last 96 rows.
// Table (lzma): b"L630SW02", u64 source rows, u64 body rows, u32 n; n x (varint position delta, u16 lane,
// u16 copy source or 65535, u8 complement).
use super::Row;
use super::composition::{arity, varint};

pub const FINAL_COUNT: usize = 2_187_867_584;

const NONE16:u16=u16::MAX;
struct Event{pos:usize,to:u16,src:u16,kind:u8}
fn table()->(usize,usize,Vec<Event>){
    let d=super::lzma::decode(include_bytes!("layer630.lzma")).expect("layer table");
    assert_eq!(&d[..8],b"L630SW02");
    let rows=u64::from_le_bytes(d[8..16].try_into().unwrap()) as usize;
    let body=u64::from_le_bytes(d[16..24].try_into().unwrap()) as usize;
    let n=u32::from_le_bytes(d[24..28].try_into().unwrap()) as usize;
    let mut b=&d[28..];let mut pos=0usize;let mut v=Vec::with_capacity(n);
    for _ in 0..n{
        pos+=varint(&mut b);
        let to=u16::from_le_bytes([b[0],b[1]]);let src=u16::from_le_bytes([b[2],b[3]]);let kind=b[4];b=&b[5..];
        v.push(Event{pos,to,src,kind});
    }
    assert!(b.is_empty());(rows,body,v)
}
pub(super) struct Writer<F> {
    sink: F,
    table: Vec<Event>,
    event: usize,
    rows: usize,
    body: usize,
    pos: usize,
    phys: [u16; 631],
    hole: usize,
    source: u16,
    kind: u8,
    tail: Vec<Row>,
    guards: Vec<u16>,
}

impl<F: FnMut(Row)> Writer<F> {
    pub(super) fn new(sink: F) -> Self {
        let (rows, body, table) = table();
        let phys = std::array::from_fn(|i| if i == 630 { NONE16 } else { i as u16 });
        assert_eq!(rows - body, 96);
        Self { sink, table, event: 0, rows, body, pos: 0, phys, hole: 630,
               source: NONE16, kind: 0, tail: Vec::with_capacity(96), guards: Vec::new() }
    }

    pub(super) fn row(&mut self, mut r: Row) {
        if self.pos >= self.body {
            self.tail.push(r);
            self.pos += 1;
            return;
        }
        while let Some(e) = self.table.get(self.event).filter(|e| e.pos == self.pos) {
            let to = usize::from(e.to);
            assert!(to != self.hole && self.phys[to] != NONE16);
            let mut ins = Vec::new();
            let fix = |ins: &mut Vec<Row>, phys: &[u16; 631], lane: usize, s: u16, kind: u8| {
                ins.push([8, phys[s as usize], phys[lane], NONE16]);
                if kind == 1 { ins.push([6, phys[lane], NONE16, NONE16]); }
            };
            if e.src != NONE16 { fix(&mut ins, &self.phys, to, e.src, e.kind); }
            let (old, src, kind) = (self.hole, self.source, self.kind);
            self.phys.swap(self.hole, to);
            (self.hole, self.source, self.kind) = (to, e.src, e.kind);
            if src != NONE16 { fix(&mut ins, &self.phys, old, src, kind); }
            if !ins.is_empty() {
                for _ in &self.guards { (self.sink)([16, NONE16, NONE16, NONE16]); }
                for x in ins { (self.sink)(x); }
                for &g in &self.guards { (self.sink)([15, g, NONE16, NONE16]); }
            }
            self.event += 1;
        }
        match r[0] {
            15 => self.guards.push(r[1]),
            16 => { self.guards.pop().unwrap(); }
            2 => r[2] = self.phys[r[2] as usize],
            k => {
                for q in &mut r[1..1 + arity(k)] {
                    assert_ne!(*q as usize, self.hole);
                    *q = self.phys[*q as usize];
                }
            }
        }
        (self.sink)(r);
        self.pos += 1;
    }

    pub(super) fn finish(mut self) {
        assert_eq!(self.event, self.table.len());
        assert_eq!(self.pos, self.rows);
        assert!(self.hole >= 512 && self.source == NONE16 && self.guards.is_empty());
        let mut owner = [usize::MAX; 630];
        for (logical, &physical) in self.phys.iter().enumerate() {
            if physical != NONE16 { owner[physical as usize] = logical; }
        }
        for l in 0..512u16 {
            let a = self.phys[l as usize];
            if a == l { continue; }
            let m = owner[l as usize];
            (self.sink)([8, a, l, NONE16]);
            (self.sink)([8, l, a, NONE16]);
            (self.sink)([8, a, l, NONE16]);
            self.phys[m] = a;
            owner[a as usize] = m;
            self.phys[l as usize] = l;
            owner[l as usize] = l as usize;
        }
        for r in self.tail { (self.sink)(r); }
    }
}

pub fn output(src: impl Iterator<Item = Row>, sink: impl FnMut(Row)) {
    let mut writer = Writer::new(sink);
    for r in src { writer.row(r); }
    writer.finish();
}
