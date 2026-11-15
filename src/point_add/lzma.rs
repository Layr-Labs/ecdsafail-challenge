//! LZMA1 decoder (the ".lzma" container: 1 properties byte, 4 bytes dictionary size, 8 bytes size or -1, then the range-coded
//! stream; an end marker is honoured).  Written for this submission: the harness links zstd only, and the gate data needs a
//! stronger coder to fit the upload limit.  Follows the LZMA specification's reference decoder.
const K_NUM_STATES: usize = 12;
struct Rc<'a> { src: &'a [u8], pos: usize, range: u32, code: u32 }
impl<'a> Rc<'a> {
    #[inline] fn byte(&mut self) -> u32 { let b = self.src.get(self.pos).copied().unwrap_or(0); self.pos += 1; b as u32 }
    #[inline] fn norm(&mut self) { if self.range < (1 << 24) { self.range <<= 8; self.code = (self.code << 8) | self.byte(); } }
    #[inline] fn bit(&mut self, p: &mut u16) -> u32 { let bound = (self.range >> 11) * (*p as u32);
        if self.code < bound { self.range = bound; *p += (2048 - *p) >> 5; self.norm(); 0 } else { self.range -= bound; self.code -= bound; *p -= *p >> 5; self.norm(); 1 } }
    fn direct(&mut self, n: u32) -> u32 { let mut r = 0u32; for _ in 0..n { self.range >>= 1; self.code = self.code.wrapping_sub(self.range); let t = 0u32.wrapping_sub(self.code >> 31);
            self.code = self.code.wrapping_add(self.range & t); self.norm(); r = (r << 1).wrapping_add(t.wrapping_add(1)); } r }
    #[inline] fn tree(&mut self, probs: &mut [u16], bits: u32) -> u32 { let mut m = 1usize; for _ in 0..bits { m = (m << 1) + self.bit(&mut probs[m]) as usize; } m as u32 - (1 << bits) }
    #[inline] fn rtree(&mut self, probs: &mut [u16], off: usize, bits: u32) -> u32 { let (mut m, mut s) = (1usize, 0u32); for i in 0..bits { let b = self.bit(&mut probs[off + m]); m = (m << 1) + b as usize; s |= b << i; } s }
}
struct LenDec { choice: u16, choice2: u16, low: Vec<u16>, mid: Vec<u16>, high: Vec<u16> }
impl LenDec { fn new() -> Self { LenDec { choice: 1024, choice2: 1024, low: vec![1024; 16 << 3], mid: vec![1024; 16 << 3], high: vec![1024; 256] } }
    fn decode(&mut self, rc: &mut Rc, ps: usize) -> u32 { if rc.bit(&mut self.choice) == 0 { return rc.tree(&mut self.low[ps << 3..(ps + 1) << 3], 3); }
        if rc.bit(&mut self.choice2) == 0 { return 8 + rc.tree(&mut self.mid[ps << 3..(ps + 1) << 3], 3); } 16 + rc.tree(&mut self.high, 8) } }

pub fn decode(src: &[u8]) -> Result<Vec<u8>, &'static str> {
    if src.len() < 18 { return Err("lzma: short input"); }
    let d = src[0] as usize; if d >= 9 * 5 * 5 { return Err("lzma: bad properties"); }
    let (lc, lp, pb) = (d % 9, (d / 9) % 5, d / 45);
    let size = u64::from_le_bytes(src[5..13].try_into().unwrap()); let known = size != u64::MAX;
    let mut rc = Rc { src, pos: 13, range: 0xFFFF_FFFF, code: 0 };
    if rc.byte() != 0 { return Err("lzma: bad stream start"); } for _ in 0..4 { rc.code = (rc.code << 8) | rc.byte(); }
    let mut lit = vec![1024u16; 0x300 << (lc + lp)];
    let (mut is_match, mut is_rep, mut g0, mut g1, mut g2, mut rep0_long) = ([1024u16; K_NUM_STATES << 4], [1024u16; K_NUM_STATES], [1024u16; K_NUM_STATES], [1024u16; K_NUM_STATES], [1024u16; K_NUM_STATES], [1024u16; K_NUM_STATES << 4]);
    let (mut slot, mut posd, mut align) = (vec![1024u16; 4 << 6], vec![1024u16; 1 + 128 - 14], [1024u16; 16]);
    let (mut len_dec, mut rep_len) = (LenDec::new(), LenDec::new());
    let mut out: Vec<u8> = Vec::with_capacity(if known { size as usize } else { src.len() * 4 });
    let (mut rep0, mut rep1, mut rep2, mut rep3) = (0usize, 0usize, 0usize, 0usize); let mut state = 0usize;
    loop {
        if known && out.len() as u64 >= size { break; }
        let ps = out.len() & ((1 << pb) - 1);
        if rc.bit(&mut is_match[(state << 4) + ps]) == 0 {
            let prev = out.last().copied().unwrap_or(0) as usize;
            let ls = ((out.len() & ((1 << lp) - 1)) << lc) + (prev >> (8 - lc)); let probs = &mut lit[0x300 * ls..0x300 * (ls + 1)];
            let mut sym = 1usize;
            if state >= 7 { if rep0 >= out.len() { return Err("lzma: bad distance"); } let mut mb = out[out.len() - rep0 - 1] as usize;
                while sym < 0x100 { let mbit = (mb >> 7) & 1; mb <<= 1; let b = rc.bit(&mut probs[((1 + mbit) << 8) + sym]) as usize; sym = (sym << 1) | b; if mbit != b { break; } } }
            while sym < 0x100 { sym = (sym << 1) | rc.bit(&mut probs[sym]) as usize; }
            out.push(sym as u8); state = if state < 4 { 0 } else if state < 10 { state - 3 } else { state - 6 };
            continue;
        }
        let mut len: usize;
        if rc.bit(&mut is_rep[state]) != 0 {
            if out.is_empty() { return Err("lzma: repeat at start"); }
            if rc.bit(&mut g0[state]) == 0 {
                if rc.bit(&mut rep0_long[(state << 4) + ps]) == 0 { state = if state < 7 { 9 } else { 11 }; if rep0 >= out.len() { return Err("lzma: bad distance"); } let b = out[out.len() - rep0 - 1]; out.push(b); continue; }
            } else { let dist;
                if rc.bit(&mut g1[state]) == 0 { dist = rep1; } else { if rc.bit(&mut g2[state]) == 0 { dist = rep2; } else { dist = rep3; rep3 = rep2; } rep2 = rep1; }
                rep1 = rep0; rep0 = dist; }
            len = rep_len.decode(&mut rc, ps) as usize; state = if state < 7 { 8 } else { 11 };
        } else {
            rep3 = rep2; rep2 = rep1; rep1 = rep0;
            len = len_dec.decode(&mut rc, ps) as usize; state = if state < 7 { 7 } else { 10 };
            let ls = len.min(3); let ps2 = rc.tree(&mut slot[ls << 6..(ls + 1) << 6], 6);
            let dist: u32 = if ps2 < 4 { ps2 } else { let nb = (ps2 >> 1) - 1; let mut dd = (2 | (ps2 & 1)) << nb;
                if ps2 < 14 { dd = dd.wrapping_add(rc.rtree(&mut posd, (dd - ps2) as usize, nb)); } else { dd = dd.wrapping_add(rc.direct(nb - 4) << 4); dd = dd.wrapping_add(rc.rtree(&mut align, 0, 4)); } dd };
            if dist == 0xFFFF_FFFF { break; }                      // end marker
            rep0 = dist as usize;
        }
        len += 2; if rep0 >= out.len() { return Err("lzma: bad distance"); }
        let from = out.len() - rep0 - 1; if rep0 + 1 >= len { out.extend_from_within(from..from + len); } else { for i in 0..len { let b = out[from + i]; out.push(b); } }
    }
    if known && out.len() as u64 != size { return Err("lzma: size mismatch"); }
    Ok(out)
}
