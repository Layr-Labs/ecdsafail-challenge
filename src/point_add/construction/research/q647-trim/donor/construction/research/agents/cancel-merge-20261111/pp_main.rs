// Offline companions for the 647 work (std only).
//   pp peep  IN OUT            one pass of RealAdii's exact peephole (their peephole.rs, unmodified), materialised
//   pp delta BASE FINAL OUT    edit script turning BASE into FINAL (copy / delete / insert records)
//   pp apply BASE DELTA OUT    apply an edit script (to verify it reproduces FINAL byte for byte)
// Traces are flat little-endian [u16;4] records.
mod peephole;
use std::io::{Read, Write};
type Row = [u16; 4];
fn load(p: &str) -> Vec<Row> {
    let mut f = std::fs::File::open(p).expect("open");
    let n = (f.metadata().unwrap().len() / 8) as usize;
    let mut v: Vec<Row> = vec![[0u16; 4]; n];
    let bytes = unsafe { std::slice::from_raw_parts_mut(v.as_mut_ptr() as *mut u8, n * 8) };
    f.read_exact(bytes).expect("read");
    v
}
fn save(p: &str, v: &[Row]) {
    let mut f = std::io::BufWriter::with_capacity(1 << 24, std::fs::File::create(p).expect("create"));
    let bytes = unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, v.len() * 8) };
    f.write_all(bytes).expect("write");
}
struct V(Vec<Row>, Vec<(usize, [Row; 3])>);
impl peephole::Rows for V {
    fn len(&self) -> usize { self.0.len() }
    fn get(&self, i: usize) -> Row { self.0[i] }
    fn set(&mut self, i: usize, r: Row) { self.0[i] = if r[0] == peephole::TOMB { [peephole::TOMB, 65535, 65535, 65535] } else { r }; }
    fn expand(&mut self, i: usize, b: [Row; 3]) {
        self.0[i] = [peephole::BLOCK, 65535, 65535, 65535];
        assert!(self.1.last().map_or(true, |l| l.0 < i));
        self.1.push((i, b));
    }
    fn block(&self, i: usize) -> [Row; 3] { let j = self.1.binary_search_by_key(&i, |e| e.0).expect("block"); self.1[j].1 }
}
fn leb(out: &mut Vec<u8>, mut x: usize) { loop { let b = (x & 127) as u8; x >>= 7; if x == 0 { out.push(b); break; } out.push(b | 128); } }
fn unleb(d: &[u8], p: &mut usize) -> usize { let (mut x, mut sh) = (0usize, 0u32); loop { let b = d[*p]; *p += 1; x |= ((b & 127) as usize) << sh; if b & 128 == 0 { break; } sh += 7; } x }
fn ccx(v: &[Row]) -> usize { v.iter().filter(|r| r[0] == 13).count() }
fn main() {
    let a: Vec<String> = std::env::args().collect();
    match a[1].as_str() {
        "peep" => {
            let rows = load(&a[2]);
            let (n0, c0) = (rows.len(), ccx(&rows));
            let mut v = V(rows, Vec::new());
            let st = peephole::pass(&mut v);
            eprintln!("pair {} merge {} gadget_t {} gadget_u {} copy {} ctrl_x {} ctrl_cx {} ctrl_xx {} removed_ccx {}", st.pair, st.merge, st.gadget_t, st.gadget_u, st.copy, st.ctrl_x, st.ctrl_cx, st.ctrl_xx, st.removed_ccx());
            let mut out: Vec<Row> = Vec::with_capacity(v.0.len());
            let mut bi = 0usize;
            for (i, r) in v.0.iter().enumerate() {
                if r[0] == peephole::TOMB { continue; }
                if r[0] == peephole::BLOCK { assert_eq!(v.1[bi].0, i); out.extend_from_slice(&v.1[bi].1); bi += 1; } else { out.push(*r); }
            }
            assert_eq!(bi, v.1.len());
            eprintln!("ops {} -> {}   static ccx {} -> {}", n0, out.len(), c0, ccx(&out));
            save(&a[3], &out);
        }
        "delta" => {
            // Alignment: skip equal rows; at a mismatch find the nearest anchor (K equal rows) with a hashed
            // window search, then take a minimal edit script (LCS) for the region in between.
            let (b, f) = (load(&a[2]), load(&a[3]));
            let (n, m) = (b.len(), f.len());
            const K: usize = 32;
            let key = |r: &Row| -> u64 { (r[0] as u64) | (r[1] as u64) << 16 | (r[2] as u64) << 32 | (r[3] as u64) << 48 };
            let wh = |v: &[Row], i: usize| -> u64 { let mut h = 0xcbf29ce484222325u64; for r in &v[i..i + K] { h = (h ^ key(r)).wrapping_mul(0x100000001b3).rotate_left(23); } h };
            enum Ev { Copy(usize), Del(usize), Ins(usize, usize) } // Ins(start in f, count)
            let mut ev: Vec<Ev> = Vec::new();
            let (mut i, mut j) = (0usize, 0usize);
            let (mut regions, mut crude, mut maxreg) = (0usize, 0usize, 0usize);
            loop {
                let mut c = 0usize;
                while i + c < n && j + c < m && b[i + c] == f[j + c] { c += 1; }
                if c > 0 { ev.push(Ev::Copy(c)); }
                i += c; j += c;
                if i == n && j == m { break; }
                // anchor search with growing windows
                let mut anchor: Option<(usize, usize)> = None;
                // cheap path: small shifts, checked directly
                'quick: for total in 1..=12usize {
                    for dj in 0..=total {
                        let di = total - dj;
                        if di != 0 && dj != 0 { continue; }   // only pure deletions or pure insertions here
                        if i + di + K > n || j + dj + K > m { continue; }
                        if b[i + di..i + di + K] == f[j + dj..j + dj + K] { anchor = Some((di, dj)); break 'quick; }
                    }
                }
                if anchor.is_none() {
                for &span in &[512usize, 8192, 131072, 2097152, 33554432] {
                    let (ie, je) = ((i + span).min(n), (j + span).min(m));
                    if ie < i + K || je < j + K { if ie == n && je == m { anchor = Some((n - i, m - j)); } if span >= 33554432 { anchor = Some((n - i, m - j)); } continue; }
                    let mut map: std::collections::HashMap<u64, usize> = std::collections::HashMap::with_capacity(je - j);
                    for y in (j..=je - K).rev() { map.insert(wh(&f, y), y); }
                    let mut best: Option<(usize, usize)> = None;
                    for x in i..=ie - K {
                        if let Some(&y) = map.get(&wh(&b, x)) { if b[x..x + K] == f[y..y + K] { best = Some((x - i, y - j)); break; } }
                    }
                    if best.is_some() { anchor = best; break; }
                    if ie == n && je == m { anchor = Some((n - i, m - j)); break; }
                }
                }
                let (di, dj) = anchor.expect("no anchor");
                regions += 1; maxreg = maxreg.max(di.max(dj));
                if di == 0 { ev.push(Ev::Ins(j, dj)); }
                else if dj == 0 { ev.push(Ev::Del(di)); }
                else if di.saturating_mul(dj) > 60_000_000 { crude += 1; ev.push(Ev::Del(di)); ev.push(Ev::Ins(j, dj)); }
                else {
                    // LCS table (suffix form) on the region
                    let (w, h) = (dj + 1, di + 1);
                    let mut t = vec![0u16; w * h];
                    for x in (0..di).rev() { for y in (0..dj).rev() {
                        t[x * w + y] = if b[i + x] == f[j + y] { t[(x + 1) * w + y + 1] + 1 } else { t[(x + 1) * w + y].max(t[x * w + y + 1]) };
                    } }
                    let (mut x, mut y) = (0usize, 0usize);
                    while x < di || y < dj {
                        if x < di && y < dj && b[i + x] == f[j + y] && t[x * w + y] == t[(x + 1) * w + y + 1] + 1 { ev.push(Ev::Copy(1)); x += 1; y += 1; }
                        else if x < di && (y == dj || t[(x + 1) * w + y] >= t[x * w + y + 1]) { ev.push(Ev::Del(1)); x += 1; }
                        else { ev.push(Ev::Ins(j + y, 1)); y += 1; }
                    }
                }
                i += di; j += dj;
            }
            // encode: records (copy, delete, insert rows)
            let mut out: Vec<u8> = Vec::new();
            let (mut cc, mut cd) = (0usize, 0usize); let mut ci: Vec<Row> = Vec::new();
            let (mut sites, mut dels, mut inss) = (0usize, 0usize, 0usize);
            let mut flush = |out: &mut Vec<u8>, cc: &mut usize, cd: &mut usize, ci: &mut Vec<Row>| {
                leb(out, *cc); leb(out, *cd); leb(out, ci.len());
                for r in ci.iter() { for x in r { out.extend_from_slice(&x.to_le_bytes()); } }
                *cc = 0; *cd = 0; ci.clear();
            };
            for e in &ev {
                match *e {
                    Ev::Copy(k) => { if cd > 0 || !ci.is_empty() { sites += 1; flush(&mut out, &mut cc, &mut cd, &mut ci); } cc += k; }
                    Ev::Del(k) => { cd += k; dels += k; }
                    Ev::Ins(s, k) => { ci.extend_from_slice(&f[s..s + k]); inss += k; }
                }
            }
            flush(&mut out, &mut cc, &mut cd, &mut ci);
            eprintln!("regions {} (largest {}, crude {}) edit records {} deleted rows {} inserted rows {} raw bytes {}", regions, maxreg, crude, sites, dels, inss, out.len());
            std::fs::write(&a[4], &out).expect("write");
        }
        "apply" => {
            let b = load(&a[2]);
            let d = std::fs::read(&a[3]).expect("delta");
            let mut out: Vec<Row> = Vec::with_capacity(b.len());
            let (mut p, mut r) = (0usize, 0usize);
            while p < d.len() {
                let c = unleb(&d, &mut p); let del = unleb(&d, &mut p); let ins = unleb(&d, &mut p);
                out.extend_from_slice(&b[r..r + c]); r += c + del;
                for _ in 0..ins { let mut row = [0u16; 4]; for x in row.iter_mut() { *x = u16::from_le_bytes([d[p], d[p + 1]]); p += 2; } out.push(row); }
            }
            assert_eq!(r, b.len());
            eprintln!("applied: {} -> {} ops", b.len(), out.len());
            save(&a[4], &out);
        }
        _ => panic!("usage"),
    }
}
