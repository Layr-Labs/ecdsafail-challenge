// Value-numbering pass. Every qubit carries a 128-bit hash of the boolean function it holds:
//   input qubits and classical condition bits are random atoms, XOR is XOR of hashes, AND is a mixed hash.
// Equal hashes mean equal functions (up to a 2^-128 style collision), so the pass can prove, gate by gate:
//   A  a control is constantly 0 (or the two controls are complementary)      -> the Toffoli never fires: delete
//   B  the two controls are equal, or one control is constantly 1             -> CX
//   C  the target already holds exactly a AND b, so the gate returns it to 0  -> measure-reset + conditional CZ
//   D  another qubit currently holds a AND b                                  -> CX from that qubit
use crate::common::*;
use std::collections::HashMap;

#[inline(always)] fn sm(z: u64) -> u64 {
    let mut z = z.wrapping_add(0x9E3779B97F4A7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
    z ^ (z >> 31)
}
#[inline(always)] fn mix(x: u128, y: u128) -> u128 {
    let (x0, x1, y0, y1) = (x as u64, (x >> 64) as u64, y as u64, (y >> 64) as u64);
    let a = sm(sm(sm(sm(x0) ^ x1) ^ y0) ^ y1);
    let b = sm(sm(sm(sm(y1 ^ 0x6A09E667F3BCC908) ^ y0) ^ x1) ^ x0 ^ 0xBB67AE8584CAA73B);
    ((a as u128) << 64) | b as u128
}
const ONE: u128 = 0x243F6A8885A308D313198A2E03707344;
#[inline(always)] fn prod(x: u128, y: u128) -> u128 {
    if x == 0 || y == 0 || x ^ y == ONE { return 0; }
    if x == y || y == ONE { return x; }
    if x == ONE { return y; }
    if x < y { mix(x, y) } else { mix(y, x) }
}
struct Frame { c: u128, serial: u32, list: Vec<(u16, u128, bool)> }

pub fn run(t: &[u64]) -> Vec<u64> {
    let lay = layout(t);
    let newbit = lay.nb; assert!(newbit < 65535);
    let mut h = vec![0u128; 65536];
    let mut ctr = 0u64;
    let mut fresh = || { ctr += 1; ((sm(ctr) as u128) << 64) | sm(ctr ^ 0x3C6EF372FE94F82B) as u128 };
    let mut cls = vec![true; 65536]; // qubit provably holds a function of classical bits only
    for &r in t { if kind(r) == K_APPQ { h[fb(r)] = fresh(); cls[fb(r)] = false; } }
    let (mut e1, mut e2, mut e0) = (0u64, 0u64, 0u64);
    let mut bver = vec![0u32; 65536];
    let catom = |bit: usize, bver: &Vec<u32>| mix(((bit as u128) << 32) | bver[bit] as u128, 0x510E527FADE682D19B05688C2B3E6C1F);
    let mut frames: Vec<Frame> = Vec::new();
    let mut stamp = vec![0u32; 65536]; let mut stamp2 = vec![0u32; 65536]; let mut serial = 0u32;
    let mut map: HashMap<u64, u16, std::hash::BuildHasherDefault<crate::opt::MixH>> = Default::default();
    let mut out: Vec<u64> = Vec::with_capacity(t.len() + (t.len() >> 6));
    let (mut na, mut nb, mut nc, mut nd, mut kept) = (0u64, 0u64, 0u64, 0u64, 0u64);
    let (mut nc_blk, mut nd_blk) = (0u64, 0u64);
    let nq = lay.nq; let mut hist = vec![0u64; 700]; let mut nzero = 0usize; let mut opi = 0u64;
    macro_rules! touch { ($q:expr) => { if let Some(f) = frames.last_mut() { let q = $q; if stamp[q] != f.serial { stamp[q] = f.serial; f.list.push((q as u16, h[q], cls[q])); } } } }
    for &r in t {
        let (k, a, b, c) = (kind(r), fa(r), fb(r), fc(r));
        opi += 1;
        if opi & 0xfff == 0 { nzero = h[..nq].iter().filter(|&&v| v == 0).count(); }
        if k == K_CCX { hist[nzero] += 1; }
        match k {
            K_CCX => {
                if a == c || b == c { touch!(c); cls[c] = false; h[c] = fresh(); out.push(r); kept += 1; continue; }
                if a == b { touch!(c); cls[c] = cls[c] && cls[a]; h[c] ^= h[a]; out.push(r); kept += 1; continue; }
                let (x, y) = (h[a], h[b]); let p = prod(x, y);
                if p == 0 { na += 1; continue; }
                if cls[a] && cls[b] { if cls[c] { e0 += 1; } else { e2 += 1; } } else if cls[a] || cls[b] { e1 += 1; }
                let cc = cls[a] && cls[b] && cls[c];
                if x == y || y == ONE { nb += 1; touch!(c); cls[c] = cc; h[c] ^= p; out.push(rec(K_CX, a, c, NONE)); continue; }
                if x == ONE { nb += 1; touch!(c); cls[c] = cc; h[c] ^= p; out.push(rec(K_CX, b, c, NONE)); continue; }
                if h[c] == p {
                    nc += 1; if !frames.is_empty() { nc_blk += 1; }
                    touch!(c); h[c] = 0; cls[c] = true;
                    out.push(rec(K_HMR, c, newbit, NONE)); out.push(rec(K_CZ, a, b, newbit));
                    continue;
                }
                if let Some(&w) = map.get(&(p as u64)) {
                    let w = w as usize;
                    if h[w] == p && w != c && w != a && w != b {
                        nd += 1; if !frames.is_empty() { nd_blk += 1; }
                        touch!(c); cls[c] = cc; h[c] ^= p; out.push(rec(K_CX, w, c, NONE)); continue;
                    }
                }
                touch!(c); cls[c] = cc; h[c] ^= p; map.insert(h[c] as u64, c as u16);
                out.push(r); kept += 1;
            }
            K_CX => {
                if a == b { touch!(b); cls[b] = false; h[b] = fresh(); }
                else { touch!(b); cls[b] = cls[b] && cls[a]; let v = if c == NONE { h[a] } else { prod(catom(c, &bver), h[a]) }; h[b] ^= v; }
                out.push(r);
            }
            K_X => { touch!(a); h[a] ^= if b == NONE { ONE } else { catom(b, &bver) }; out.push(r); }
            K_HMR => { touch!(a); h[a] = 0; cls[a] = true; if b != NONE { bver[b] += 1; } out.push(r); }
            K_BINV | K_BST0 | K_BST1 => { bver[a] += 1; out.push(r); }
            K_PUSH => { serial += 1; frames.push(Frame { c: catom(a, &bver), serial, list: Vec::new() }); out.push(r); }
            K_POP => {
                if let Some(f) = frames.pop() {
                    serial += 1;
                    for &(q, pre, pc) in &f.list {
                        let q = q as usize;
                        if stamp2[q] == serial { continue; }
                        stamp2[q] = serial;
                        let post = h[q];
                        cls[q] = cls[q] && pc;
                        if post != pre {
                            h[q] = pre ^ prod(f.c, pre ^ post);
                            if let Some(p) = frames.last_mut() { p.list.push((q as u16, pre, pc)); }
                        }
                        stamp[q] = 0;
                    }
                }
                out.push(r);
            }
            _ => out.push(r),
        }
    }
    eprintln!("gvn: A never-fires {}  B to-CX {}  C measure-uncompute {} (in blocks {})  D reuse {} (in blocks {})  Toffolis kept {}  map {}",
        na, nb, nc, nc_blk, nd, nd_blk, kept, map.len());
    eprintln!("gvn: Toffolis with classical-valued wires: one control {}  both controls {}  all three {}", e1, e2, e0);
    let tot: u64 = hist.iter().sum(); let mut acc = 0u64; let mut line = String::new();
    for (z, &v) in hist.iter().enumerate() { let before = acc; acc += v; for pct in [1u64, 5, 10, 25, 50, 75, 90, 99] { if before * 100 < tot * pct && acc * 100 >= tot * pct { line += &format!(" p{}={}", pct, z); } } }
    eprintln!("gvn: provably-zero qubits at Toffoli time (of {} qubits), percentiles over Toffolis:{}", nq, line);
    let mut b = String::new(); for z in (0..700).step_by(10) { let v: u64 = hist[z..(z + 10).min(700)].iter().sum(); if v > 0 { b += &format!(" {}-{}:{:.1}%", z, z + 9, v as f64 * 100.0 / tot as f64); } }
    eprintln!("gvn: histogram{}", b);
    eprintln!("gvn: ops in {} out {} new bit {}", t.len(), out.len(), newbit);
    out
}

// Measured-target rule:  CCX(a,b,t) ... Hmr(t -> m)   ==   Hmr(t -> m), CZ(a,b) if m
// valid when the Toffoli can be moved forward to the measurement: between the two, t is only used as a target,
// a and b are not modified, and both sit in the same condition-block instance.
pub fn measured_targets(t: &[u64]) -> Vec<u64> {
    let n = t.len();
    let mut ver = vec![0u32; 65536];
    let mut pend: Vec<Vec<(u32, u32, u32, u32)>> = (0..65536).map(|_| Vec::new()).collect();
    let mut del = crate::opt::mask_new(n);
    let mut ins: Vec<(u32, u64)> = Vec::new();
    let mut ctx = 0u32; let mut next_ctx = 1u32; let mut cstack: Vec<u32> = Vec::new();
    let mut cnt = 0u64;
    for i in 0..n {
        let r = t[i]; let (k, a, b, c) = (kind(r), fa(r), fb(r), fc(r));
        match k {
            K_CCX => {
                if a == b || a == c || b == c { for q in [a, b, c] { pend[q].clear(); ver[q] += 1; } continue; }
                pend[a].clear(); pend[b].clear();
                pend[c].push((i as u32, ver[a], ver[b], ctx)); ver[c] += 1;
            }
            K_CX => { if a == b { pend[a].clear(); ver[a] += 1; } else { pend[a].clear(); ver[b] += 1; } }
            K_X => { ver[a] += 1; }
            K_CZ => { pend[a].clear(); pend[b].clear(); }
            K_Z => { pend[a].clear(); }
            K_HMR => {
                if b != NONE {
                    for &(gi, va, vb, cx) in &pend[a] {
                        let g = t[gi as usize]; let (ga, gb) = (fa(g), fb(g));
                        if cx == ctx && ver[ga] == va && ver[gb] == vb {
                            crate::opt::mset(&mut del, gi as usize); ins.push((i as u32, rec(K_CZ, ga, gb, b))); cnt += 1;
                        }
                    }
                }
                pend[a].clear(); ver[a] += 1;
            }
            K_PUSH => { cstack.push(ctx); ctx = next_ctx; next_ctx += 1; }
            K_POP => { ctx = cstack.pop().unwrap_or(0); }
            _ => {}
        }
    }
    eprintln!("measured-target rule: {} Toffolis become measurement + CZ", cnt);
    let mut out = Vec::with_capacity(n); let mut p = 0;
    for i in 0..n {
        if !crate::opt::mget(&del, i) { out.push(t[i]); }
        while p < ins.len() && ins[p].0 as usize == i { out.push(ins[p].1); p += 1; }
    }
    out
}
