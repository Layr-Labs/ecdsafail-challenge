//! Minimal safe-Rust LZMA1 ("alone" / .lzma) decoder. std only, no `unsafe`.
//!
//! Format facts relied on:
//!  * Header, 13 bytes: props byte `d = (pb*5 + lp)*9 + lc` (must be < 225), u32le dictionary size,
//!    u64le uncompressed size. An unknown size (all ones) is rejected; the size must be <= 512 MiB.
//!  * The range-coded stream follows: first byte 0, then a big-endian u32 `code`; `range` starts at 0xFFFFFFFF.
//!    Bits use 11-bit probabilities (init 1024, shift 5); `range` is renormalised below 2^24 by shifting in a byte.
//!  * Symbols: is_match[state][pos_state]; 0 -> literal (bit tree of 8 bits, context = lp low position bits and
//!    lc high bits of the previous byte; after a match the literal is "matched" against the byte at rep0).
//!    1 -> is_rep: 0 = new match (length, then distance via 6-bit slot tree, reverse-tree / direct bits / 4 align
//!    bits), 1 = repeat of rep0..rep3 or one-byte "short rep". Match length = decoded length + 2 (2..273).
//!  * Distances are stored minus one; 0xFFFFFFFF is the end-of-payload marker. Streams made by `xz --format=lzma`
//!    carry that marker even when the size is known (we patch the size into the header): it is accepted, but only
//!    directly after the last declared byte.
//!  * The output Vec is the dictionary: a back-reference needs distance <= bytes produced so far and <= the
//!    header dictionary size (at least 4096). A clean end means: exactly `size` bytes, `code == 0`, and every
//!    input byte consumed (no trailing bytes).
//!  * LZMA has no checksum: a corrupted stream can decode to wrong bytes without an error. Callers add their own.
use std::io::{Error, ErrorKind, Result};

const MAX_OUT: u64 = 512 << 20;
fn bad(m: &'static str) -> Error {
    Error::new(ErrorKind::InvalidData, m)
}

struct Rc<'a> {
    buf: &'a [u8],
    pos: usize,
    range: u32,
    code: u32,
}
impl Rc<'_> {
    #[inline(always)]
    fn norm(&mut self) {
        if self.range < 1 << 24 {
            self.range <<= 8;
            // past the end we feed zeros; `pos > buf.len()` is detected once per symbol
            self.code = self.code << 8 | self.buf.get(self.pos).copied().unwrap_or(0) as u32;
            self.pos += 1;
        }
    }
    #[inline(always)]
    fn bit(&mut self, p: &mut u16) -> usize {
        self.norm();
        let bound = (self.range >> 11) * *p as u32;
        if self.code < bound {
            self.range = bound;
            *p += (2048 - *p) >> 5;
            0
        } else {
            self.range -= bound;
            self.code -= bound;
            *p -= *p >> 5;
            1
        }
    }
    /// MSB-first bit tree of `n` bits over `p` (len >= 1 << n; index 0 unused).
    #[inline(always)]
    fn tree(&mut self, p: &mut [u16], n: u32) -> usize {
        let mut m = 1;
        for _ in 0..n {
            m = m << 1 | self.bit(&mut p[m]);
        }
        m - (1 << n)
    }
    fn rtree(&mut self, p: &mut [u16], n: u32) -> usize {
        let (mut m, mut r) = (1, 0);
        for i in 0..n {
            let b = self.bit(&mut p[m]);
            m = m << 1 | b;
            r |= b << i;
        }
        r
    }
    fn direct(&mut self, n: u32) -> usize {
        let mut r = 0;
        for _ in 0..n {
            self.norm();
            self.range >>= 1;
            let b = (self.code >= self.range) as u32;
            self.code -= self.range * b;
            r = r << 1 | b as usize;
        }
        r
    }
}

struct Len {
    choice: [u16; 2],
    low: [u16; 128],
    mid: [u16; 128],
    high: [u16; 256],
}
impl Len {
    fn new() -> Self {
        Len { choice: [1024; 2], low: [1024; 128], mid: [1024; 128], high: [1024; 256] }
    }
    fn get(&mut self, rc: &mut Rc, ps: usize) -> usize {
        if rc.bit(&mut self.choice[0]) == 0 {
            rc.tree(&mut self.low[ps * 8..ps * 8 + 8], 3)
        } else if rc.bit(&mut self.choice[1]) == 0 {
            8 + rc.tree(&mut self.mid[ps * 8..ps * 8 + 8], 3)
        } else {
            16 + rc.tree(&mut self.high, 8)
        }
    }
}

/// Decode a complete LZMA1 "alone" file held in memory.
pub fn decode(input: &[u8]) -> Result<Vec<u8>> {
    if input.len() < 13 + 5 {
        return Err(bad("lzma: input too short"));
    }
    let d = input[0] as usize;
    if d >= 225 {
        return Err(bad("lzma: bad properties byte"));
    }
    let (lc, lp, pb) = (d % 9, d / 9 % 5, d / 45);
    let dict = (u32::from_le_bytes(input[1..5].try_into().unwrap()) as usize).max(4096);
    let size = u64::from_le_bytes(input[5..13].try_into().unwrap());
    if size == u64::MAX {
        return Err(bad("lzma: unknown uncompressed size"));
    }
    if size > MAX_OUT {
        return Err(bad("lzma: uncompressed size too large"));
    }
    let size = size as usize;
    let buf = &input[13..];
    if buf[0] != 0 {
        return Err(bad("lzma: bad range coder start"));
    }
    let mut rc = Rc { buf, pos: 5, range: u32::MAX, code: u32::from_be_bytes(buf[1..5].try_into().unwrap()) };
    let mut lit = vec![1024u16; 0x300 << (lc + lp)];
    let mut is_match = [1024u16; 12 << 4];
    let mut is_rep0_long = [1024u16; 12 << 4];
    let (mut is_rep, mut g0, mut g1, mut g2) = ([1024u16; 12], [1024u16; 12], [1024u16; 12], [1024u16; 12]);
    let mut slot = [[1024u16; 64]; 4];
    let mut spec = [1024u16; 116];
    let mut align = [1024u16; 16];
    let (mut mlen, mut rlen) = (Len::new(), Len::new());
    let mut out: Vec<u8> = Vec::with_capacity(size);
    let (mut state, mut rep) = (0usize, [0usize; 4]);
    let (pbm, lpm) = ((1usize << pb) - 1, (1usize << lp) - 1);
    let mut marker = false;
    // one more symbol than `size` bytes is decoded only to accept the optional end marker
    loop {
        if out.len() == size && !marker {
            rc.norm();
            if rc.code == 0 && rc.pos == buf.len() {
                return Ok(out);
            }
            marker = true; // the only legal continuation is the end-of-payload marker
        }
        if rc.pos > buf.len() {
            return Err(bad("lzma: truncated input"));
        }
        let ps = out.len() & pbm;
        if rc.bit(&mut is_match[state << 4 | ps]) == 0 {
            if marker {
                return Err(bad("lzma: data after declared size"));
            }
            let prev = out.last().copied().unwrap_or(0) as usize;
            let ctx = ((out.len() & lpm) << lc) + (prev >> (8 - lc));
            let p = &mut lit[ctx * 0x300..ctx * 0x300 + 0x300];
            let mut s = 1usize;
            if state >= 7 {
                let mut mb = *out.get(out.len().wrapping_sub(rep[0] + 1)).ok_or_else(|| bad("lzma: bad match byte"))? as usize;
                let mut offs = 0x100;
                while s < 0x100 {
                    mb <<= 1;
                    let mbit = mb & offs;
                    let b = rc.bit(&mut p[offs + mbit + s]);
                    s = s << 1 | b;
                    offs &= if b == 0 { !mbit } else { mbit };
                }
            } else {
                while s < 0x100 {
                    s = s << 1 | rc.bit(&mut p[s]);
                }
            }
            out.push(s as u8);
            state = if state < 4 { 0 } else if state < 10 { state - 3 } else { state - 6 };
            continue;
        }
        let len;
        if rc.bit(&mut is_rep[state]) == 0 {
            rep = [0, rep[0], rep[1], rep[2]];
            len = mlen.get(&mut rc, ps);
            state = if state < 7 { 7 } else { 10 };
            let ls = len.min(3);
            let sl = rc.tree(&mut slot[ls], 6);
            rep[0] = if sl < 4 {
                sl
            } else {
                let nd = (sl >> 1) as u32 - 1;
                let base = (2 | sl & 1) << nd;
                if sl < 14 {
                    base + rc.rtree(&mut spec[base - sl..], nd)
                } else {
                    base + (rc.direct(nd - 4) << 4) + rc.rtree(&mut align, 4)
                }
            };
            if rep[0] == 0xFFFF_FFFF {
                if !marker {
                    return Err(bad("lzma: premature end marker"));
                }
                rc.norm();
                return if rc.code == 0 && rc.pos == buf.len() { Ok(out) } else { Err(bad("lzma: bad stream end")) };
            }
        } else {
            if marker {
                return Err(bad("lzma: data after declared size"));
            }
            if out.is_empty() {
                return Err(bad("lzma: repeat match with empty dictionary"));
            }
            if rc.bit(&mut g0[state]) == 0 {
                if rc.bit(&mut is_rep0_long[state << 4 | ps]) == 0 {
                    let b = *out.get(out.len().wrapping_sub(rep[0] + 1)).ok_or_else(|| bad("lzma: bad distance"))?;
                    out.push(b);
                    state = if state < 7 { 9 } else { 11 };
                    continue;
                }
            } else {
                let dist;
                if rc.bit(&mut g1[state]) == 0 {
                    dist = rep[1];
                } else {
                    if rc.bit(&mut g2[state]) == 0 {
                        dist = rep[2];
                    } else {
                        dist = rep[3];
                        rep[3] = rep[2];
                    }
                    rep[2] = rep[1];
                }
                rep[1] = rep[0];
                rep[0] = dist;
            }
            len = rlen.get(&mut rc, ps);
            state = if state < 7 { 8 } else { 11 };
        }
        if marker {
            return Err(bad("lzma: data after declared size"));
        }
        let (n, dist) = (len + 2, rep[0] + 1);
        if dist > out.len() || dist > dict {
            return Err(bad("lzma: distance beyond dictionary"));
        }
        if n > size - out.len() {
            return Err(bad("lzma: match exceeds declared size"));
        }
        let start = out.len() - dist;
        if dist >= n {
            out.extend_from_within(start..start + n);
        } else {
            for i in 0..n {
                let b = out[start + i];
                out.push(b);
            }
        }
    }
}
