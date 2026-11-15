//! Gate-record streams ("GIRS" container): the block format of the 646-qubit submission's gate IR (tokens: literal with
//! per-kind deltas, affine runs, translated copies inside a block), with the command bytes and the seven literal byte planes
//! stored as separate LZMA streams.  A record is [kind, a, b, c] (u16), kinds as in `super::row_to_op`.
use super::lzma;
const PERIODS: [usize; 32] = [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,20,24,28,32,40,48,56,64,80,96,112,128,160,192,224,256];
pub struct Block { pub n: usize, nb: usize, nl: usize, pub gap: u64, cmd_at: usize, lit_at: usize }
pub struct Girs { pub blocks: Vec<Block>, cmd: Vec<u8>, planes: Vec<Vec<u8>> }
fn varint(b: &[u8], at: &mut usize) -> usize { let mut r = 0usize; let mut sh = 0; loop { let x = b[*at]; *at += 1; r |= ((x & 127) as usize) << sh; if x < 128 { return r; } sh += 7; assert!(sh < 64, "varint"); } }
impl Girs {
    pub fn open(data: &[u8]) -> Girs {
        assert!(&data[..8] == b"GIRS1\n\0\0", "gate stream container");
        let nblocks = u32::from_le_bytes(data[8..12].try_into().unwrap()) as usize; let mut at = 48; let mut streams = Vec::with_capacity(9);
        for i in 0..9 { let len = u32::from_le_bytes(data[12 + 4 * i..16 + 4 * i].try_into().unwrap()) as usize; streams.push(lzma::decode(&data[at..at + len]).expect("gate stream")); at += len; }
        assert!(at == data.len(), "gate stream container length");
        let mut it = streams.into_iter(); let hdr = it.next().unwrap(); let cmd = it.next().unwrap(); let planes: Vec<Vec<u8>> = it.collect();
        let (mut p, mut cmd_at, mut lit_at) = (0usize, 0usize, 0usize); let mut blocks = Vec::with_capacity(nblocks);
        for _ in 0..nblocks { let n = varint(&hdr, &mut p); let nb = varint(&hdr, &mut p); let nl = varint(&hdr, &mut p); let gap = varint(&hdr, &mut p) as u64;
            blocks.push(Block { n, nb, nl, gap, cmd_at, lit_at }); cmd_at += nb; lit_at += nl; }
        assert!(p == hdr.len() && cmd_at == cmd.len() && planes.iter().all(|q| q.len() == lit_at), "gate stream sizes");
        Girs { blocks, cmd, planes }
    }
    /// records of block `b` into `out` (cleared first)
    pub fn decode(&self, b: usize, out: &mut Vec<[u16; 4]>) {
        let bl = &self.blocks[b]; let cmd = &self.cmd[bl.cmd_at..bl.cmd_at + bl.nb]; let n = bl.n; out.clear(); out.reserve(n);
        let mut last = [[0u16; 3]; 19]; let (mut at, mut lit) = (0usize, 0usize);
        while out.len() < n {
            let token = cmd[at] as usize; at += 1; let i = out.len();
            if token == 0 {
                assert!(lit < bl.nl, "missing literal"); let li = bl.lit_at + lit; let kind = self.planes[0][li] as usize; assert!(kind <= 18, "gate kind");
                let mut row = [kind as u16, 0, 0, 0];
                for j in 0..3 { let z = u16::from_le_bytes([self.planes[1 + 2 * j][li], self.planes[2 + 2 * j][li]]); let d = (z >> 1) ^ 0u16.wrapping_sub(z & 1);
                    last[kind][j] = last[kind][j].wrapping_add(d); row[j + 1] = last[kind][j]; }
                out.push(row); lit += 1;
            } else if (64..82).contains(&token) {
                let remapped = token >= 80; let reverse = if remapped { token == 81 } else { token & 8 != 0 };
                let distance = varint(cmd, &mut at) + 1; let count = varint(cmd, &mut at) + 4; assert!(distance <= i && count <= n - i, "copy");
                let source = i - distance; assert!(!reverse || count <= source + 1, "reversed copy");
                let mut d = [0u16; 3]; let mut pieces: Vec<(u16, u16)> = Vec::new();
                if remapped { let k = varint(cmd, &mut at); assert!(k != 0 && k <= 128, "wire mapping"); let mut start = 0usize;
                    for j in 0..k { if j != 0 { start += varint(cmd, &mut at); } let z = varint(cmd, &mut at); assert!(start < 65535 && z <= 65535, "wire mapping"); let x = z as u16; pieces.push((start as u16, (x >> 1) ^ 0u16.wrapping_sub(x & 1))); } }
                else { for j in 0..3 { if token & (1 << j) != 0 { let raw = varint(cmd, &mut at); assert!(raw <= 65535, "wire translation"); let z = raw as u16; d[j] = (z >> 1) ^ 0u16.wrapping_sub(z & 1); } } }
                for k in 0..count { let mut row = out[if reverse { source - k } else { source + k }];
                    for j in 0..3 { if row[j + 1] != 65535 { let off = if remapped { pieces[pieces.partition_point(|&(x, _)| x <= row[j + 1]) - 1].1 } else { d[j] }; row[j + 1] = row[j + 1].wrapping_add(off); } }
                    out.push(row); }
            } else {
                let p = PERIODS[token - 1]; let count = varint(cmd, &mut at) + 3; assert!(i >= 2 * p && count <= n - i, "affine run");
                for _ in 0..count { let i = out.len(); let x = out[i - p]; let y = out[i - 2 * p]; let mut row = [0u16; 4]; for j in 0..4 { row[j] = x[j].wrapping_mul(2).wrapping_sub(y[j]); } out.push(row); }
            }
        }
        assert!(at == cmd.len() && lit == bl.nl, "unused block data");
    }
}
