// ---- GATEIR4: the 27 field streams of GATEIR3, held in LZMA1 "alone" streams (see lzma.rs) ----
// Layout after the 8-byte magic "GATEIR4\n" (all integers little endian):
//   27 x u32   length of field stream 0..26 (the same table, same order as GATEIR3:
//              hdr tok acnt rk dist.0-2 cnt.0-2 tr.0-2 rr.0-2 ra.0-2 rz.0-2 litk lit13 lit8 lit6 litm)
//   u64        FNV-1a (64 bit) of the 27 streams concatenated in that order (LZMA has no checksum)
//   u8         number of groups G (1..=27)
//   G x { u8 count, count x u8 stream index, u32 compressed length }   (every stream index exactly once;
//              the group's LZMA stream holds its member streams concatenated in the listed order)
//   G LZMA streams back to back, in group order, each a complete 13-byte-header file with the exact size.
use super::lzma;
use std::io;

const NSTREAMS: usize = 27;
const MAX_TOTAL: usize = 256 << 20;

fn bad(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}
struct Cur<'a>(&'a [u8]);
impl<'a> Cur<'a> {
    fn take(&mut self, n: usize) -> io::Result<&'a [u8]> {
        if n > self.0.len() {
            return Err(bad("short GATEIR4 container"));
        }
        let (a, b) = self.0.split_at(n);
        self.0 = b;
        Ok(a)
    }
    fn u8(&mut self) -> io::Result<usize> {
        Ok(self.take(1)?[0] as usize)
    }
    fn u32(&mut self) -> io::Result<usize> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()) as usize)
    }
}
pub fn fnv1a(streams: &[Vec<u8>]) -> u64 {
    let mut h = 0xcbf29ce484222325u64;
    for s in streams {
        for &b in s {
            h = (h ^ b as u64).wrapping_mul(0x100000001b3);
        }
    }
    h
}

/// `rest` = everything after the 8-byte magic. Returns the 27 field streams, integrity-checked.
pub fn read_streams_v4(rest: &[u8]) -> io::Result<Vec<Vec<u8>>> {
    let mut c = Cur(rest);
    let mut lens = [0usize; NSTREAMS];
    let mut sum = 0usize;
    for l in lens.iter_mut() {
        *l = c.u32()?;
        sum = sum.checked_add(*l).ok_or_else(|| bad("stream length overflow"))?;
    }
    if sum > MAX_TOTAL {
        return Err(bad("stream lengths too large"));
    }
    let want = u64::from_le_bytes(c.take(8)?.try_into().unwrap());
    let ng = c.u8()?;
    if ng == 0 || ng > NSTREAMS {
        return Err(bad("bad group count"));
    }
    let mut groups = Vec::with_capacity(ng);
    let mut seen = [false; NSTREAMS];
    for _ in 0..ng {
        let cnt = c.u8()?;
        let mut idx = Vec::with_capacity(cnt);
        for _ in 0..cnt {
            let i = c.u8()?;
            if i >= NSTREAMS || seen[i] {
                return Err(bad("bad stream index"));
            }
            seen[i] = true;
            idx.push(i);
        }
        groups.push((idx, c.u32()?));
    }
    if !seen.iter().all(|&s| s) {
        return Err(bad("missing stream index"));
    }
    let mut streams: Vec<Vec<u8>> = vec![Vec::new(); NSTREAMS];
    for (idx, clen) in groups {
        let raw = lzma::decode(c.take(clen)?)?;
        if raw.len() != idx.iter().map(|&i| lens[i]).sum::<usize>() {
            return Err(bad("group length mismatch"));
        }
        let mut at = 0;
        for i in idx {
            streams[i] = raw[at..at + lens[i]].to_vec();
            at += lens[i];
        }
    }
    if !c.0.is_empty() {
        return Err(bad("trailing bytes"));
    }
    if fnv1a(&streams) != want {
        return Err(bad("GATEIR4 integrity check failed"));
    }
    Ok(streams)
}
