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

// ---- cancel2: same rule as `cancel`, but with no window limits ----
// Every wire keeps its full stack of runs (run counter, type, live count). A global hash map takes
// (record, condition-block instance) to the most recent surviving identical gate; older ones are chained through
// `prev`. Only the most recent one can sit in the top run of all its wires (an older twin lies in the same or a
// deeper run on every wire), so one lookup decides. A measurement on a wire kills its runs (`floor`).
#[derive(Default, Clone, Copy)]
pub struct MixH(u64);
impl std::hash::Hasher for MixH {
    fn finish(&self) -> u64 { let mut x = self.0; x ^= x >> 30; x = x.wrapping_mul(0xbf58476d1ce4e5b9); x ^= x >> 27; x = x.wrapping_mul(0x94d049bb133111eb); x ^ (x >> 31) }
    fn write(&mut self, b: &[u8]) { for &x in b { self.write_u64(x as u64); } }
    fn write_u64(&mut self, x: u64) { self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x517cc1b727220a95); }
    fn write_u32(&mut self, x: u32) { self.write_u64(x as u64); }
}
struct Run2 { c: u32, live: u32, typ: u8 }

pub fn cancel2(t: &[u64], mask: &mut [u64]) -> (u64, u64) {
    let t0 = Instant::now();
    let n = t.len(); assert!(n < u32::MAX as usize);
    let nq = 1 << 16;
    let mut st: Vec<Vec<Run2>> = (0..nq).map(|_| Vec::new()).collect();
    let mut next_c: Vec<u32> = vec![0; nq];
    let mut floor: Vec<u32> = vec![0; nq];
    let mut prev: Vec<u32> = vec![u32::MAX; n];
    let mut rids: Vec<[u32; 3]> = vec![[0; 3]; n];
    let mut map: std::collections::HashMap<(u64, u32), u32, std::hash::BuildHasherDefault<MixH>> = Default::default();
    let mut ctx: u32 = 0; let mut next_ctx: u32 = 1; let mut cstack: Vec<u32> = Vec::new();
    let (mut pairs_ccx, mut pairs_other, mut max_keys) = (0u64, 0u64, 0usize);
    for i in 0..n {
        if mget(mask, i) { continue; }
        let r = t[i]; let k = kind(r);
        let (a, b, c) = (fa(r), fb(r), fc(r));
        let mut w: [(usize, u8); 3] = [(0, 0); 3]; let nw; let cond;
        match k {
            K_CCX => { w = [(a, 0), (b, 0), (c, 1)]; nw = 3; cond = false; }
            K_CX => { w[0] = (a, 0); w[1] = (b, 1); nw = 2; cond = c != NONE; }
            K_CZ => { w[0] = (a, 0); w[1] = (b, 0); nw = 2; cond = true; }
            K_X => { w[0] = (a, 1); nw = 1; cond = b != NONE; }
            K_Z => { w[0] = (a, 0); nw = 1; cond = true; }
            K_HMR => { st[a].clear(); floor[a] = next_c[a]; continue; }
            K_PUSH => { cstack.push(ctx); ctx = next_ctx; next_ctx += 1; continue; }
            K_POP => { ctx = cstack.pop().unwrap_or(0); continue; }
            _ => continue,
        }
        let rep = (nw == 3 && (a == b || a == c || b == c)) || (nw == 2 && w[0].0 == w[1].0);
        if rep { for x in 0..nw { let q = w[x].0; st[q].clear(); floor[q] = next_c[q]; } continue; }
        if !cond {
            let key = (r, ctx);
            let mut hit: Option<u32> = None;
            if let Some(&p) = map.get(&key) {
                let pr = rids[p as usize];
                let (mut dead, mut top) = (false, true);
                for x in 0..nw {
                    let q = w[x].0;
                    if pr[x] < floor[q] { dead = true; break; }
                    match st[q].last() { Some(run) if run.c == pr[x] => {} _ => top = false }
                }
                if dead { map.remove(&key); } else if top { hit = Some(p); }
            }
            if let Some(p) = hit {
                let pp = prev[p as usize];
                if pp == u32::MAX { map.remove(&key); } else { map.insert(key, pp); }
                for x in 0..nw {
                    let s = &mut st[w[x].0];
                    s.last_mut().unwrap().live -= 1;
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
            if s.last().map(|r| r.typ != ty).unwrap_or(true) { s.push(Run2 { c: next_c[q], live: 0, typ: ty }); next_c[q] += 1; }
            let run = s.last_mut().unwrap();
            run.live += 1;
            if !cond { rids[i][x] = run.c; }
        }
        if !cond {
            prev[i] = map.insert((r, ctx), i as u32).unwrap_or(u32::MAX);
            if i & 0xfffff == 0 && map.len() > max_keys { max_keys = map.len(); }
        }
    }
    let runs_left: usize = st.iter().map(|s| s.len()).sum();
    eprintln!("cancel2: {} CCX pairs, {} other pairs in {:.1}s (map keys peak ~{}, runs left {})", pairs_ccx, pairs_other, t0.elapsed().as_secs_f64(), max_keys, runs_left);
    (pairs_ccx, pairs_other)
}

// ---- cancel3: cancel2 plus exact merging of Toffoli pairs that share wires ----
// M2 (same controls, different targets):  CCX(a,b,t1) ... CCX(a,b,t)  ->  CX(t->t1) CCX(a,b,t) CX(t->t1)
// M1 (same target, one shared control):   CCX(x,b1,t) ... CCX(x,c,t)  ->  CX(b1->c) CCX(x,c,t) CX(b1->c)
// The earlier gate must be movable forward to the later one (it sits in the top run of all its own wires), it is
// deleted, and the later gate is wrapped in two free CX gates. One Toffoli saved per merge.
// CCX records are matched with their controls sorted, so CCX(a,b,t) and CCX(b,a,t) count as twins.
// Output: mask (deleted ops) and patches (op index, p, q) meaning "wrap this op with CX(p->q) on both sides".
pub struct Patch { pub idx: u32, pub p: u16, pub q: u16 }
type Map64 = std::collections::HashMap<u64, u32, std::hash::BuildHasherDefault<MixH>>;

pub fn cancel3(t: &[u64], mask: &mut [u64], merge: bool) -> Vec<Patch> {
    let t0 = Instant::now();
    let n = t.len(); assert!(n < u32::MAX as usize);
    let nq = 1 << 16;
    let mut st: Vec<Vec<Run2>> = (0..nq).map(|_| Vec::new()).collect();
    let mut next_c: Vec<u32> = vec![0; nq];
    let mut floor: Vec<u32> = vec![0; nq];
    let mut prev: Vec<u32> = vec![u32::MAX; n];
    let mut rids: Vec<[u32; 3]> = vec![[0; 3]; n];
    let mut map: std::collections::HashMap<(u64, u32), u32, std::hash::BuildHasherDefault<MixH>> = Default::default();
    let mut m_ctl: Map64 = Default::default(); // (ctx, lo, hi)  -> latest CCX with these controls
    let mut m_xt: Map64 = Default::default();  // (ctx, x, t)    -> latest CCX with control x and target t
    let mut wrapped = mask_new(n);
    let mut patches: Vec<Patch> = Vec::new();
    let mut ctx: u32 = 0; let mut next_ctx: u32 = 1; let mut cstack: Vec<u32> = Vec::new();
    let (mut pairs_ccx, mut pairs_other, mut n_m1, mut n_m2) = (0u64, 0u64, 0u64, 0u64);
    // QOPT_SIB=1: a condition context is identified by (parent context, bit, version of the bit), so two blocks on
    // the same unchanged bit share one context, and a gate with its own condition bit lives in that bit's context.
    let sib = std::env::var("QOPT_SIB").ok().as_deref() == Some("1");
    let mut bver: Vec<u32> = vec![0; 1 << 16];
    let mut intern: std::collections::HashMap<(u32, u32, u32), u32, std::hash::BuildHasherDefault<MixH>> = Default::default();
    let mut pairs_cond = 0u64;
    // push one gate use on a wire; returns the run serial
    #[inline(always)] fn push(st: &mut [Vec<Run2>], next_c: &mut [u32], q: usize, ty: u8) -> u32 {
        let s = &mut st[q];
        if s.last().map(|r| r.typ != ty).unwrap_or(true) { s.push(Run2 { c: next_c[q], live: 0, typ: ty }); next_c[q] += 1; }
        let run = s.last_mut().unwrap(); run.live += 1; run.c
    }
    #[inline(always)] fn unpush(st: &mut [Vec<Run2>], q: usize) {
        let s = &mut st[q];
        s.last_mut().unwrap().live -= 1;
        while let Some(top) = s.last() { if top.live == 0 { s.pop(); } else { break; } }
    }
    for i in 0..n {
        if mget(mask, i) { continue; }
        let r0 = t[i]; let k = kind(r0);
        let (a, b, c) = (fa(r0), fb(r0), fc(r0));
        let mut w: [(usize, u8); 3] = [(0, 0); 3]; let nw; let mut cond; let mut r = r0; let mut cbit = NONE;
        match k {
            K_CCX => { let (lo, hi) = if a <= b { (a, b) } else { (b, a) }; w = [(lo, 0), (hi, 0), (c, 1)]; nw = 3; cond = false; r = rec(K_CCX, lo, hi, c); }
            K_CX => { w[0] = (a, 0); w[1] = (b, 1); nw = 2; cond = c != NONE; cbit = c; if sib { r = rec(K_CX, a, b, NONE); } }
            K_CZ => { let (lo, hi) = if a <= b { (a, b) } else { (b, a) }; w[0] = (lo, 0); w[1] = (hi, 0); nw = 2; cond = true; cbit = c; if sib { r = rec(K_CZ, lo, hi, NONE); } }
            K_X => { w[0] = (a, 1); nw = 1; cond = b != NONE; cbit = b; if sib { r = rec(K_X, a, NONE, NONE); } }
            K_Z => { w[0] = (a, 0); nw = 1; cond = true; cbit = b; if sib { r = rec(K_Z, a, NONE, NONE); } }
            K_HMR => { st[a].clear(); floor[a] = next_c[a]; if b != NONE { bver[b] += 1; } continue; }
            K_BINV | K_BST0 | K_BST1 => { bver[a] += 1; continue; }
            K_PUSH => {
                cstack.push(ctx);
                if sib { let nx = next_ctx; ctx = *intern.entry((ctx, a as u32, bver[a])).or_insert_with(|| nx); if ctx == nx { next_ctx += 1; } }
                else { ctx = next_ctx; next_ctx += 1; }
                continue;
            }
            K_POP => { ctx = cstack.pop().unwrap_or(0); continue; }
            _ => continue,
        }
        let rep = (nw == 3 && (a == b || a == c || b == c)) || (nw == 2 && w[0].0 == w[1].0);
        if rep { for x in 0..nw { let q = w[x].0; st[q].clear(); floor[q] = next_c[q]; } continue; }
        // context of this gate: the block context, refined by the gate's own condition bit
        let mut gctx = ctx;
        if sib {
            if cbit != NONE { let nx = next_ctx; gctx = *intern.entry((ctx, cbit as u32, bver[cbit])).or_insert_with(|| nx); if gctx == nx { next_ctx += 1; } }
            cond = false;
        }
        if !cond {
            let key = (r, gctx);
            let mut hit: Option<u32> = None;
            // twins deleted by a merge are still chained: skip them first
            while let Some(&p) = map.get(&key) {
                if mget(mask, p as usize) {
                    let pp = prev[p as usize];
                    if pp == u32::MAX { map.remove(&key); } else { map.insert(key, pp); }
                    continue;
                }
                let pr = rids[p as usize];
                let (mut dead, mut top) = (false, true);
                for x in 0..nw {
                    let q = w[x].0;
                    if pr[x] < floor[q] { dead = true; break; }
                    match st[q].last() { Some(run) if run.c == pr[x] => {} _ => top = false }
                }
                if dead { map.remove(&key); } else if top { hit = Some(p); }
                break;
            }
            if let Some(p) = hit {
                let pp = prev[p as usize];
                if pp == u32::MAX { map.remove(&key); } else { map.insert(key, pp); }
                for x in 0..nw { unpush(&mut st, w[x].0); }
                mset(mask, p as usize); mset(mask, i);
                if k == K_CCX { pairs_ccx += 1; } else { pairs_other += 1; if cbit != NONE { pairs_cond += 1; } }
                continue;
            }
        }
        if merge && k == K_CCX {
            let (lo, hi, tg) = (w[0].0, w[1].0, w[2].0);
            let kc = ((ctx as u64) << 32) | ((lo as u64) << 16) | hi as u64;
            let kx = [((ctx as u64) << 32) | ((lo as u64) << 16) | tg as u64, ((ctx as u64) << 32) | ((hi as u64) << 16) | tg as u64];
            // candidate must be alive, unwrapped, and on top of all three of its own wires
            let usable = |p: u32, st: &Vec<Vec<Run2>>, mask: &[u64], wrapped: &[u64]| -> Option<(usize, usize, usize)> {
                let pi = p as usize;
                if mget(mask, pi) || mget(wrapped, pi) { return None; }
                let pr0 = t[pi]; let (pa, pb, pt) = (fa(pr0), fb(pr0), fc(pr0));
                let (plo, phi) = if pa <= pb { (pa, pb) } else { (pb, pa) };
                let pr = rids[pi];
                for (x, q) in [plo, phi, pt].into_iter().enumerate() {
                    if pr[x] < floor[q] { return None; }
                    match st[q].last() { Some(run) if run.c == pr[x] => {} _ => return None }
                }
                Some((plo, phi, pt))
            };
            let mut found: Option<(u32, usize, usize, usize, usize, usize)> = None; // (p, plo, phi, pt, cx_from, cx_to)
            if let Some(&p) = m_ctl.get(&kc) {
                if let Some((plo, phi, pt)) = usable(p, &st, mask, &wrapped) {
                    if pt != tg && pt != lo && pt != hi { found = Some((p, plo, phi, pt, tg, pt)); n_m2 += 1; }
                }
            }
            if found.is_none() {
                for (j, x) in [lo, hi].into_iter().enumerate() {
                    if let Some(&p) = m_xt.get(&kx[j]) {
                        if let Some((plo, phi, pt)) = usable(p, &st, mask, &wrapped) {
                            let b1 = if plo == x { phi } else { plo };
                            let cc = if j == 0 { hi } else { lo };
                            if b1 != cc && b1 != tg && b1 != x { found = Some((p, plo, phi, pt, b1, cc)); n_m1 += 1; break; }
                        }
                    }
                }
            }
            if let Some((p, plo, phi, pt, from, to)) = found {
                // delete the earlier gate
                mset(mask, p as usize);
                unpush(&mut st, plo); unpush(&mut st, phi); unpush(&mut st, pt);
                // emit CX(from->to) G CX(from->to); all three are pinned (never cancelled or merged again)
                push(&mut st, &mut next_c, from, 0); push(&mut st, &mut next_c, to, 1);
                push(&mut st, &mut next_c, lo, 0); push(&mut st, &mut next_c, hi, 0); push(&mut st, &mut next_c, tg, 1);
                push(&mut st, &mut next_c, from, 0); push(&mut st, &mut next_c, to, 1);
                mset(&mut wrapped, i);
                patches.push(Patch { idx: i as u32, p: from as u16, q: to as u16 });
                continue;
            }
            for x in 0..3 { rids[i][x] = push(&mut st, &mut next_c, w[x].0, w[x].1); }
            prev[i] = map.insert((r, ctx), i as u32).unwrap_or(u32::MAX);
            m_ctl.insert(kc, i as u32); m_xt.insert(kx[0], i as u32); m_xt.insert(kx[1], i as u32);
            continue;
        }
        for x in 0..nw { let c = push(&mut st, &mut next_c, w[x].0, w[x].1); if !cond { rids[i][x] = c; } }
        if !cond { prev[i] = map.insert((r, gctx), i as u32).unwrap_or(u32::MAX); }
    }
    eprintln!("cancel3: contexts {} (shared mode {}), pairs of classically conditioned gates {}", next_ctx, sib, pairs_cond);
    eprintln!("cancel3: {} CCX pairs, {} other pairs, merges M1 {} M2 {} in {:.1}s", pairs_ccx, pairs_other, n_m1, n_m2, t0.elapsed().as_secs_f64());
    patches
}

/// Apply mask and patches: the transformed trace.
pub fn apply2(t: &[u64], mask: &[u64], patches: &[Patch]) -> Vec<u64> {
    let mut out = Vec::with_capacity(t.len()); let mut pi = 0;
    for i in 0..t.len() {
        let pat = if pi < patches.len() && patches[pi].idx as usize == i { pi += 1; Some(&patches[pi - 1]) } else { None };
        if mget(mask, i) { assert!(pat.is_none()); continue; }
        if let Some(p) = pat { let cx = rec(K_CX, p.p as usize, p.q as usize, NONE); out.push(cx); out.push(t[i]); out.push(cx); } else { out.push(t[i]); }
    }
    assert_eq!(pi, patches.len());
    out
}

/// Patch list encoding: per patch LEB128(delta of the op's index among KEPT ops), then p and q as u16 LE.
pub fn encode_patches(mask: &[u64], n: usize, patches: &[Patch]) -> Vec<u8> {
    let mut out = Vec::new(); let (mut kept, mut last, mut pi) = (0u64, 0u64, 0usize);
    for i in 0..n {
        if mget(mask, i) { continue; }
        if pi < patches.len() && patches[pi].idx as usize == i {
            let mut d = kept - last; last = kept;
            loop { let b = (d & 127) as u8; d >>= 7; if d == 0 { out.push(b); break; } out.push(b | 128); }
            out.extend_from_slice(&patches[pi].p.to_le_bytes()); out.extend_from_slice(&patches[pi].q.to_le_bytes());
            pi += 1;
        }
        kept += 1;
    }
    assert_eq!(pi, patches.len());
    out
}
