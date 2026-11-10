// Deletion-mask passes. A mask is a bitset over op indices (bit set = op deleted).
use crate::common::*;
use std::time::Instant;

pub fn mask_new(n: usize) -> Vec<u64> { vec![0u64; n.div_ceil(64)] }
#[inline] pub fn mget(m: &[u64], i: usize) -> bool { (m[i >> 6] >> (i & 63)) & 1 != 0 }
#[inline] pub fn mset(m: &mut [u64], i: usize) { m[i >> 6] |= 1 << (i & 63); }
pub fn mask_load(path: &str, n: usize) -> Vec<u64> {
    let b = std::fs::read(path).expect("mask"); assert_eq!(b.len(), n.div_ceil(64) * 8);
    b.chunks_exact(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect()
}
pub fn mask_save(path: &str, m: &[u64]) { let b: Vec<u8> = m.iter().flat_map(|x| x.to_le_bytes()).collect(); save_bytes(path, &b); }

struct Run { typ: u8, live: u32, ents: Vec<(u64, u32, u32)> } // (record, context id, op index)
fn envu(k: &str, d: usize) -> usize { std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d) }

/// Exact pass: cancels pairs of identical self-inverse gates (CCX, CX, X without classical condition, same
/// condition-block instance) when every gate between them on their wires commutes with them
/// (control wires only used as controls, target wire only used as target, no measurement).
pub fn cancel(t: &[u64], mask: &mut [u64]) -> (u64, u64) {
    let t0 = Instant::now();
    let cap = envu("QOPT_CAP", 48); let depth = envu("QOPT_DEPTH", 24);
    let nq = 1 << 16;
    let mut st: Vec<Vec<Run>> = (0..nq).map(|_| Vec::new()).collect();
    let mut ctx: u32 = 0; let mut next_ctx: u32 = 1; let mut cstack: Vec<u32> = Vec::new();
    let (mut pairs_ccx, mut pairs_other) = (0u64, 0u64);
    for i in 0..t.len() {
        if mget(mask, i) { continue; }
        let r = t[i]; let k = kind(r);
        let (a, b, c) = (fa(r), fb(r), fc(r));
        // wires: (qubit, type) with type 0 = control-like (Z basis), 1 = target-like (X basis)
        let mut w: [(usize, u8); 3] = [(0, 0); 3]; let nw; let cond;
        match k {
            K_CCX => { w = [(a, 0), (b, 0), (c, 1)]; nw = 3; cond = false; }
            K_CX => { w[0] = (a, 0); w[1] = (b, 1); nw = 2; cond = c != NONE; }
            K_CZ => { w[0] = (a, 0); w[1] = (b, 0); nw = 2; cond = true; } // never cancelled, only typed
            K_X => { w[0] = (a, 1); nw = 1; cond = b != NONE; }
            K_Z => { w[0] = (a, 0); nw = 1; cond = true; }
            K_HMR => { st[a].clear(); continue; }
            K_PUSH => { cstack.push(ctx); ctx = next_ctx; next_ctx += 1; continue; }
            K_POP => { ctx = cstack.pop().unwrap_or(0); continue; }
            _ => continue,
        }
        if nw == 3 && (a == b || a == c || b == c) { for x in 0..3 { st[w[x].0].clear(); } continue; }
        if nw == 2 && w[0].0 == w[1].0 { st[w[0].0].clear(); continue; }
        if !cond {
            // look for a partner present in the top run of every wire
            let mut pos: Option<u32> = None; let mut ok = true;
            for x in 0..nw {
                let (q, ty) = w[x];
                match st[q].last() {
                    Some(run) if run.typ == ty => {
                        match run.ents.iter().rev().find(|e| e.0 == r && e.1 == ctx) {
                            Some(e) => { if let Some(p) = pos { if p != e.2 { ok = false; } } else { pos = Some(e.2); } }
                            None => ok = false,
                        }
                    }
                    _ => ok = false,
                }
                if !ok { break; }
            }
            if ok {
                let p = pos.unwrap();
                for x in 0..nw {
                    let s = &mut st[w[x].0];
                    let run = s.last_mut().unwrap();
                    let j = run.ents.iter().rposition(|e| e.2 == p).unwrap();
                    run.ents.remove(j); run.live -= 1;
                    while let Some(top) = s.last() { if top.live == 0 { s.pop(); } else { break; } }
                }
                mset(mask, p as usize); mset(mask, i);
                if k == K_CCX { pairs_ccx += 1; } else { pairs_other += 1; }
                continue;
            }
        }
        for x in 0..nw {
            let (q, ty) = w[x];
            let s = &mut st[q];
            if s.last().map(|r| r.typ != ty).unwrap_or(true) {
                if s.len() >= depth { s.remove(0); }
                s.push(Run { typ: ty, live: 0, ents: Vec::new() });
            }
            let run = s.last_mut().unwrap();
            run.live += 1;
            if !cond { if run.ents.len() >= cap { run.ents.remove(0); } run.ents.push((r, ctx, i as u32)); }
        }
    }
    eprintln!("cancel: {} CCX pairs, {} other pairs in {:.1}s", pairs_ccx, pairs_other, t0.elapsed().as_secs_f64());
    (pairs_ccx, pairs_other)
}

/// Statistical root selection: Toffolis that were executed but never fired in the profile, and that sit at least
/// `w` ops away (both directions) from any Toffoli that fired only rarely (first fire at shot >= `late`).
pub fn roots(t: &[u64], flags: &[u8], first: &[u32], late: u32, w: usize, mask: &mut [u64]) -> u64 {
    let n = t.len();
    // distance to the previous / next rare-seen CCX, in ops
    let mut dist = vec![u32::MAX; flags.len()];
    let mut j = 0usize; let mut last: Option<usize> = None;
    for i in 0..n { if kind(t[i]) == K_CCX {
        if first[j] != u32::MAX && first[j] >= late { last = Some(i); }
        if let Some(l) = last { dist[j] = (i - l).min(u32::MAX as usize - 1) as u32; }
        j += 1;
    } }
    let mut last: Option<usize> = None;
    for i in (0..n).rev() { if kind(t[i]) == K_CCX {
        j -= 1;
        if first[j] != u32::MAX && first[j] >= late { last = Some(i); }
        if let Some(l) = last { dist[j] = dist[j].min((l - i).min(u32::MAX as usize - 1) as u32); }
    } }
    let th = [0usize, 1000, 5000, 20000, 50000, 100000, 200000, 400000, 800000, 1600000, 5000000];
    let mut hist = vec![0u64; th.len()];
    let mut del = 0u64; let mut j = 0usize;
    for i in 0..n { if kind(t[i]) == K_CCX {
        let f = flags[j];
        if f & 1 != 0 && f & 4 == 0 {
            let d = dist[j] as usize;
            for (x, &v) in th.iter().enumerate() { if d >= v { hist[x] += 1; } }
            if d >= w { mset(mask, i); del += 1; }
        }
        j += 1;
    } }
    for (x, &v) in th.iter().enumerate() { eprintln!("never-fired Toffolis at distance >= {:8} ops from a rarely-fired one: {}", v, hist[x]); }
    eprintln!("roots: deleted {} Toffolis (late >= {}, w = {})", del, late, w);
    del
}

pub fn apply(t: &[u64], mask: &[u64]) -> Vec<u64> {
    let mut o = Vec::with_capacity(t.len());
    for i in 0..t.len() { if !mget(mask, i) { o.push(t[i]); } }
    o
}

/// Run-length form of the mask: varints of alternating (kept run, deleted run) lengths, starting with kept.
pub fn encode(mask: &[u64], n: usize) -> Vec<u8> {
    let mut out = Vec::new(); let mut cur = false; let mut len = 0u64;
    let mut put = |mut v: u64, out: &mut Vec<u8>| { loop { let b = (v & 127) as u8; v >>= 7; if v == 0 { out.push(b); break; } out.push(b | 128); } };
    for i in 0..n { let d = mget(mask, i); if d == cur { len += 1; } else { put(len, &mut out); cur = d; len = 1; } }
    put(len, &mut out);
    out
}
