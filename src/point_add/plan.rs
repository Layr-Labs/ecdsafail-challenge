//! The 646-qubit submission's copy schedule ("GIRPLAN1"): literal chunks and copies of earlier output (forward or reversed)
//! under piecewise wire renamings.  Parsed here; executed by `super::his_stream` against the final op list.
#[derive(Clone, Copy)]
struct Piece { start: u16, base: u16, minus: bool }
pub struct Rename([Vec<Piece>; 3]);
fn namespace(kind: u16, j: usize) -> Option<usize> {
    match kind { 1 => (j == 0).then_some(2), 2 => [Some(2), Some(0), None][j], 18 => [Some(2), Some(1), None][j], 3..=5 => (j < 2).then_some(1), 6 | 7 | 12 => [Some(0), Some(1), None][j],
        8 | 9 => Some(if j < 2 { 0 } else { 1 }), 13 => Some(0), 15 => (j == 0).then_some(1), 16 => None, _ => panic!("gate kind {}", kind) }
}
impl Rename { pub fn apply(&self, mut row: [u16; 4]) -> [u16; 4] { let k = row[0];
        for j in 0..3 { let w = row[j + 1]; if w == u16::MAX { continue; }
            if let Some(ns) = namespace(k, j) { let runs = &self.0[ns]; if !runs.is_empty() { let p = runs[runs.partition_point(|p| p.start <= w) - 1]; row[j + 1] = if p.minus { p.base.wrapping_sub(w) } else { p.base.wrapping_add(w) }; } } }
        row } }
pub struct Action { pub size: usize, pub src: usize, pub map: usize, pub mode: u8 }
pub struct Plan { pub items: Vec<Action>, pub maps: Vec<Rename>, pub total: usize, pub literals: usize }
struct Rd<'a> { d: &'a [u8], p: usize }
impl Rd<'_> { fn byte(&mut self) -> u8 { let x = self.d[self.p]; self.p += 1; x }
    fn num(&mut self) -> usize { let mut x = 0u64; let mut sh = 0; loop { let b = self.byte(); x |= u64::from(b & 127) << sh; if b < 128 { return x as usize; } sh += 7; assert!(sh < 64, "schedule number"); } } }
impl Plan { pub fn parse(data: &[u8]) -> Plan {
        assert!(data.len() >= 24 && &data[..8] == b"GIRPLAN1", "schedule version");
        let total = u64::from_le_bytes(data[8..16].try_into().unwrap()) as usize; let literals = u64::from_le_bytes(data[16..24].try_into().unwrap()) as usize;
        let mut rd = Rd { d: data, p: 24 }; let nm = rd.num(); let mut maps = Vec::with_capacity(nm);
        for _ in 0..nm { let mut m = Rename([Vec::new(), Vec::new(), Vec::new()]);
            for bank in &mut m.0 { let nr = rd.num(); let mut start = 0usize;
                for i in 0..nr { if i != 0 { start += rd.num(); } let enc = rd.num(); assert!(start < 65535 && enc < 131072, "wire map"); let z = (enc >> 1) as u16; bank.push(Piece { start: start as u16, base: (z >> 1) ^ 0u16.wrapping_sub(z & 1), minus: enc & 1 != 0 }); } }
            maps.push(m); }
        let nc = rd.num(); let mut items = Vec::with_capacity(nc); let (mut pos, mut lit) = (0usize, 0usize);
        for _ in 0..nc { let mode = rd.byte(); let size = rd.num(); assert!(size != 0 && size <= total - pos, "schedule chunk");
            let (src, map) = match mode { 0 => { lit += size; (0, 0) } 1 | 2 => { let distance = rd.num(); let map = rd.num(); assert!(distance != 0 && distance <= pos && map < maps.len(), "history reference"); (pos - distance, map) } _ => panic!("schedule command") };
            items.push(Action { size, src, map, mode }); pos += size; }
        assert!(rd.p == data.len() && pos == total && lit == literals, "schedule totals");
        Plan { items, maps, total, literals } } }
