//! ITEM 4 (the first divide) of the 632-lane tree: the block is re-derived at build time from the item's original record block
//! by a compact edit script (data/item4_b5.bin).  The script is a token stream over two sources, the original block and the
//! output written so far:
//!   literal (per-kind operand deltas, byte planes as in gir.rs), affine run (period p: row = 2 * row[-p] - row[-2p]),
//!   copy from the output with a per-slot lane translation or with a lane substitution,
//!   copy from the original block (continuing behind the previous such copy, or at a signed offset from there) with an
//!   optional lane substitution (a short list of lane -> lane pairs; substitutions are numbered in order of first use).
//! Commands and the seven literal planes are separate LZMA streams.  The header pins the length and a hash of the input block
//! and of the output, so a different input block or a damaged script stops the build.
use super::*;
const PERIODS: [usize; 32] = [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,20,24,28,32,40,48,56,64,80,96,112,128,160,192,224,256];
#[inline] fn nq(kind: u16) -> usize { match kind { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }
#[inline] fn vi(b: &[u8], at: &mut usize) -> usize { let mut r = 0usize; let mut sh = 0; loop { let x = b[*at]; *at += 1; r |= ((x & 127) as usize) << sh; if x < 128 { return r; } sh += 7; } }
#[inline] fn zz(x: usize) -> i64 { ((x >> 1) as i64) ^ -((x & 1) as i64) }
pub fn rows_hash(rows: &[Row]) -> u64 { let mut h = 0x243F6A8885A308D3u64;
    for r in rows { let k = (r[0] as u64) | (r[1] as u64) << 16 | (r[2] as u64) << 32 | (r[3] as u64) << 48; let x = (h ^ k).wrapping_mul(0x9E3779B97F4A7C15); h = x ^ (x >> 29); } h }
/// substitution of a copy: 0 = none, 1 = a new one follows (count, then pairs: source lane as a delta, target as a signed offset), m >= 2 = number m - 2
fn mapspec(cmd: &[u8], at: &mut usize, maps: &mut Vec<Vec<(u16, u16)>>) -> usize {
    let m = vi(cmd, at); if m != 1 { return m; }
    let k = vi(cmd, at); let mut v = Vec::with_capacity(k); let mut f = 0usize;
    for _ in 0..k { f += vi(cmd, at); let t = (f as i64 + zz(vi(cmd, at))) as u16; v.push((f as u16, t)); }
    maps.push(v); maps.len() + 1
}
pub fn decode(raw: &[Row], d: &[u8]) -> Vec<Row> {
    assert!(&d[..8] == b"B5ITEM41", "item 4 script"); let u = |p: usize| u64::from_le_bytes(d[p..p + 8].try_into().unwrap());
    let (in_n, in_hash, out_n, out_hash) = (u(8) as usize, u(16), u(24) as usize, u(32));
    assert!(raw.len() == in_n && rows_hash(raw) == in_hash, "item 4: the script was made for another original block");
    let mut at = 40 + 32; let mut st: Vec<Vec<u8>> = Vec::with_capacity(8);
    for i in 0..8 { let len = u32::from_le_bytes(d[40 + 4 * i..44 + 4 * i].try_into().unwrap()) as usize; st.push(lzma::decode(&d[at..at + len]).expect("item 4 script stream")); at += len; }
    assert!(at == d.len(), "item 4 script length");
    let cmd = &st[0]; let mut out: Vec<Row> = Vec::with_capacity(out_n);
    let mut maps: Vec<Vec<(u16, u16)>> = Vec::new(); let mut tab: Vec<u16> = (0..=u16::MAX).collect();
    let mut last = [[0u16; 3]; 19]; let (mut c, mut lit, mut ie) = (0usize, 0usize, 0usize);
    while out.len() < out_n {
        let t = cmd[c] as usize; c += 1; let i = out.len();
        if t == 0 {
            let kind = st[1][lit] as usize; let mut row = [kind as u16, 0, 0, 0];
            for j in 0..3 { let z = u16::from_le_bytes([st[2 + 2 * j][lit], st[3 + 2 * j][lit]]); let dl = (z >> 1) ^ 0u16.wrapping_sub(z & 1); last[kind][j] = last[kind][j].wrapping_add(dl); row[j + 1] = last[kind][j]; }
            out.push(row); lit += 1;
        } else if t <= 32 {
            let p = PERIODS[t - 1]; let count = vi(cmd, &mut c) + 3; assert!(i >= 2 * p);
            for _ in 0..count { let i = out.len(); let (x, y) = (out[i - p], out[i - 2 * p]); let mut row = [0u16; 4]; for j in 0..4 { row[j] = x[j].wrapping_mul(2).wrapping_sub(y[j]); } out.push(row); }
        } else if (64..72).contains(&t) {
            let src = i - (vi(cmd, &mut c) + 1); let count = vi(cmd, &mut c) + 4; let mut dl = [0u16; 3];
            for j in 0..3 { if t & (1 << j) != 0 { dl[j] = zz(vi(cmd, &mut c)) as u16; } }
            for k in 0..count { let mut row = out[src + k]; for j in 1..=nq(row[0]) { row[j] = row[j].wrapping_add(dl[j - 1]); } out.push(row); }
        } else if t == 80 || (96..100).contains(&t) {
            let from_out = t == 80;
            let src = if from_out { i - (vi(cmd, &mut c) + 1) } else if t >= 98 { (ie as i64 + zz(vi(cmd, &mut c))) as usize } else { ie };
            let count = vi(cmd, &mut c) + if from_out { 4 } else { 1 };
            let m = if t == 96 || t == 98 { 0 } else { mapspec(cmd, &mut c, &mut maps) };
            if m >= 2 { for &(f, g) in &maps[m - 2] { tab[f as usize] = g; } }
            if from_out { for k in 0..count { let mut row = out[src + k]; for j in 1..=nq(row[0]) { row[j] = tab[row[j] as usize]; } out.push(row); } }
            else { assert!(src + count <= in_n); for k in 0..count { let mut row = raw[src + k]; for j in 1..=nq(row[0]) { row[j] = tab[row[j] as usize]; } out.push(row); } ie = src + count; }
            if m >= 2 { for &(f, _) in &maps[m - 2] { tab[f as usize] = f; } }
        } else { panic!("item 4 script token"); }
    }
    assert!(c == cmd.len() && lit == st[1].len() && out.len() == out_n && rows_hash(&out) == out_hash, "item 4: the script did not reproduce the block");
    out
}
/// the rewritten ITEM 4 (wire space of the item), from its original record block
pub fn generate(raw: &[Row]) -> Vec<Row> { decode(raw, include_bytes!("data/item4_b5.bin")) }
