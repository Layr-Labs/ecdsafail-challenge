//! q631 / i4d (local research, 2026-11-19; not submitted, not part of any package): ITEM 4 (item 4, segment 8, the first divide)
//! in WIRE space, for the walk-configuration recovery of agent i4d.  Nothing in the builder calls this module (it only reads the
//! pack tables), so the build is byte-identical with or without it.
//!   wire_rows4() -> raw item rows (wire space, insert rows placed), the tree's hooked rows (b5gen::generate(raw)), the
//!   provenance of every hooked row (decode of b5gen with a trace: literal / affine / copy from the output / copy from the raw
//!   block at index src with substitution m), and the wire -> physical lane map before the relabelling (item wire map, then
//!   the segment lane map).
use super::*;

pub struct Item4 { pub raw: Vec<Row>, pub b5: Vec<Row>, pub prov: Vec<u64>, pub map: Vec<u16>, pub subs: Vec<Vec<(u16, u16)>> }

/// provenance word: kind (0 literal, 1 affine run, 2 copy from the output, 3 copy from the raw block) | src << 8 | (map id + 1) << 48
pub const P_LIT: u64 = 0; pub const P_AFF: u64 = 1; pub const P_OUT: u64 = 2; pub const P_RAW: u64 = 3;

const PERIODS: [usize; 32] = [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,20,24,28,32,40,48,56,64,80,96,112,128,160,192,224,256];
#[inline] fn vi(b: &[u8], at: &mut usize) -> usize { let mut r = 0usize; let mut sh = 0; loop { let x = b[*at]; *at += 1; r |= ((x & 127) as usize) << sh; if x < 128 { return r; } sh += 7; } }
#[inline] fn zz(x: usize) -> i64 { ((x >> 1) as i64) ^ -((x & 1) as i64) }
fn mapspec(cmd: &[u8], at: &mut usize, maps: &mut Vec<Vec<(u16, u16)>>) -> usize {
    let m = vi(cmd, at); if m != 1 { return m; }
    let k = vi(cmd, at); let mut v = Vec::with_capacity(k); let mut f = 0usize;
    for _ in 0..k { f += vi(cmd, at); let t = (f as i64 + zz(vi(cmd, at))) as u16; v.push((f as u16, t)); }
    maps.push(v); maps.len() + 1
}
/// b5gen::decode with a provenance trace (same output; asserted by the script's own hash)
pub fn decode_prov(raw: &[Row], d: &[u8]) -> (Vec<Row>, Vec<u64>, Vec<Vec<(u16, u16)>>) {
    assert!(&d[..8] == b"B5ITEM41", "item 4 script"); let u = |p: usize| u64::from_le_bytes(d[p..p + 8].try_into().unwrap());
    let (in_n, in_hash, out_n, out_hash) = (u(8) as usize, u(16), u(24) as usize, u(32));
    assert!(raw.len() == in_n && b5gen::rows_hash(raw) == in_hash, "item 4: the script was made for another original block");
    let mut at = 40 + 32; let mut st: Vec<Vec<u8>> = Vec::with_capacity(8);
    for i in 0..8 { let len = u32::from_le_bytes(d[40 + 4 * i..44 + 4 * i].try_into().unwrap()) as usize; st.push(lzma::decode(&d[at..at + len]).expect("item 4 script stream")); at += len; }
    let cmd = &st[0]; let mut out: Vec<Row> = Vec::with_capacity(out_n); let mut prov: Vec<u64> = Vec::with_capacity(out_n);
    let mut maps: Vec<Vec<(u16, u16)>> = Vec::new(); let mut tab: Vec<u16> = (0..=u16::MAX).collect();
    let mut last = [[0u16; 3]; 19]; let (mut c, mut lit, mut ie) = (0usize, 0usize, 0usize);
    while out.len() < out_n {
        let t = cmd[c] as usize; c += 1; let i = out.len();
        if t == 0 {
            let kind = st[1][lit] as usize; let mut row = [kind as u16, 0, 0, 0];
            for j in 0..3 { let z = u16::from_le_bytes([st[2 + 2 * j][lit], st[3 + 2 * j][lit]]); let dl = (z >> 1) ^ 0u16.wrapping_sub(z & 1); last[kind][j] = last[kind][j].wrapping_add(dl); row[j + 1] = last[kind][j]; }
            out.push(row); prov.push(P_LIT | (lit as u64) << 8); lit += 1;
        } else if t <= 32 {
            let p = PERIODS[t - 1]; let count = vi(cmd, &mut c) + 3;
            for _ in 0..count { let i = out.len(); let (x, y) = (out[i - p], out[i - 2 * p]); let mut row = [0u16; 4]; for j in 0..4 { row[j] = x[j].wrapping_mul(2).wrapping_sub(y[j]); } out.push(row); prov.push(P_AFF | (p as u64) << 8); }
        } else if (64..72).contains(&t) {
            let src = i - (vi(cmd, &mut c) + 1); let count = vi(cmd, &mut c) + 4; let mut dl = [0u16; 3];
            for j in 0..3 { if t & (1 << j) != 0 { dl[j] = zz(vi(cmd, &mut c)) as u16; } }
            for k in 0..count { let mut row = out[src + k]; for j in 1..=qubits(row[0]) { row[j] = row[j].wrapping_add(dl[j - 1]); } out.push(row); prov.push(P_OUT | ((src + k) as u64) << 8); }
        } else if t == 80 || (96..100).contains(&t) {
            let from_out = t == 80;
            let src = if from_out { i - (vi(cmd, &mut c) + 1) } else if t >= 98 { (ie as i64 + zz(vi(cmd, &mut c))) as usize } else { ie };
            let count = vi(cmd, &mut c) + if from_out { 4 } else { 1 };
            let m = if t == 96 || t == 98 { 0 } else { mapspec(cmd, &mut c, &mut maps) };
            if m >= 2 { for &(f, g) in &maps[m - 2] { tab[f as usize] = g; } }
            let mtag = if m >= 2 { (m - 1) as u64 } else { 0 };
            if from_out { for k in 0..count { let mut row = out[src + k]; for j in 1..=qubits(row[0]) { row[j] = tab[row[j] as usize]; } out.push(row); prov.push(P_OUT | ((src + k) as u64) << 8 | mtag << 48); } }
            else { for k in 0..count { let mut row = raw[src + k]; for j in 1..=qubits(row[0]) { row[j] = tab[row[j] as usize]; } out.push(row); prov.push(P_RAW | ((src + k) as u64) << 8 | mtag << 48); } ie = src + count; }
            if m >= 2 { for &(f, _) in &maps[m - 2] { tab[f as usize] = f; } }
        } else { panic!("item 4 script token"); }
    }
    assert!(c == cmd.len() && lit == st[1].len() && out.len() == out_n && b5gen::rows_hash(&out) == out_hash, "item 4: the script did not reproduce the block");
    (out, prov, maps)
}

pub fn wire_rows4() -> Item4 {
    let mut pk = Pack::parse(&lzma::decode(include_bytes!("data/pack.lzma")).expect("pack tables"));
    walkpack::apply(&mut pk);
    unrollpack::check(&pk);
    i1::w4_apply(&mut pk);
    let g = gir::Girs::open(include_bytes!("data/blocks.girs"));
    let raw = w2rw::item_rows(&pk, &g, 4);
    let (b5, prov, subs) = decode_prov(&raw, include_bytes!("data/item4_b5.bin"));
    let it = &pk.items[4];
    let seg = pk.seg_of(it.out);
    assert!(seg == pk.seg_of(it.out + it.n - 1), "item 4 crosses a segment");
    let wm = if it.wm > 0 { Some(&pk.wire_maps[it.wm - 1]) } else { None };
    let map: Vec<u16> = (0..1024usize).map(|w| { let id = match wm { Some(m) => m[w], None => w as u16 };
        if id == NONE || id as usize >= 646 { NONE } else { pk.segs[seg].map[id as usize] } }).collect();
    Item4 { raw, b5, prov, map, subs }
}
