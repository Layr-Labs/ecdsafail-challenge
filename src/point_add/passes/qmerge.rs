//! almond-lab's exact cancellation + Toffoli merging ("qopt mode 23"), per chunk of 8-byte rows.
//!
//! Port of `cancel2` + `cancel3(merge = true)` of almond-lab's qopt tool (public in our earlier rows under
//! `research/agents/peephole-cancel-20261110/`), unchanged in its rules, applied to one chunk at a time:
//!
//! * cancellation: two identical self-inverse gates (CCX, CX, X), neither with a classical condition of its own, in the
//!   same condition-block instance, are both deleted when on each of their wires every surviving gate between them uses
//!   the wire the same way (control-like on controls, target-like on the target) and no measurement of the wire lies
//!   between (a gate that repeats a wire resets the wire).
//! * merging, same conditions, the earlier gate movable forward to the later one on all its own wires:
//!   `CCX(a,b,t1) .. CCX(a,b,t)  ->  CX(t->t1) CCX(a,b,t) CX(t->t1)` and
//!   `CCX(x,b1,t) .. CCX(x,c,t)  ->  CX(b1->c) CCX(x,c,t) CX(b1->c)`; merged gates are pinned.
//!
//! The chunk is first padded so that every condition scope it opens or closes is balanced (lead pushes on a reserved
//! bit, trailing pops), exactly as the tree's `pad`, so no gate is ever paired across a scope boundary.
//! Only the record kinds listed in `known` may occur; anything else aborts the build.
#![allow(dead_code)]
pub type Row = [u16; 4];
const NONE: usize = 65535;
const K_BINV: u16 = 3; const K_BST0: u16 = 4; const K_BST1: u16 = 5;
const K_X: u16 = 6; const K_Z: u16 = 7; const K_CX: u16 = 8; const K_CZ: u16 = 9;
const K_HMR: u16 = 12; const K_CCX: u16 = 13; const K_PUSH: u16 = 15; const K_POP: u16 = 16;
fn known(k: u16) -> bool { matches!(k, 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 12 | 13 | 15 | 16 | 18) }

#[inline(always)] fn kind(r: u64) -> u16 { r as u16 }
#[inline(always)] fn fa(r: u64) -> usize { ((r >> 16) & 0xffff) as usize }
#[inline(always)] fn fb(r: u64) -> usize { ((r >> 32) & 0xffff) as usize }
#[inline(always)] fn fc(r: u64) -> usize { (r >> 48) as usize }
#[inline(always)] fn rec(k: u16, a: usize, b: usize, c: usize) -> u64 { (k as u64) | ((a as u64) << 16) | ((b as u64) << 32) | ((c as u64) << 48) }
#[inline(always)] fn to64(r: &Row) -> u64 { rec(r[0], r[1] as usize, r[2] as usize, r[3] as usize) }
#[inline(always)] fn to_row(x: u64) -> Row { [kind(x), fa(x) as u16, fb(x) as u16, fc(x) as u16] }

#[inline] fn mget(m: &[u64], i: usize) -> bool { (m[i >> 6] >> (i & 63)) & 1 != 0 }
#[inline] fn mset(m: &mut [u64], i: usize) { m[i >> 6] |= 1 << (i & 63); }
fn mask_new(n: usize) -> Vec<u64> { vec![0u64; n.div_ceil(64)] }

#[derive(Default, Clone, Copy)]
struct MixH(u64);
impl std::hash::Hasher for MixH {
    fn finish(&self) -> u64 { let mut x = self.0; x ^= x >> 30; x = x.wrapping_mul(0xbf58476d1ce4e5b9); x ^= x >> 27; x = x.wrapping_mul(0x94d049bb133111eb); x ^ (x >> 31) }
    fn write(&mut self, b: &[u8]) { for &x in b { self.write_u64(x as u64); } }
    fn write_u64(&mut self, x: u64) { self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x517cc1b727220a95); }
    fn write_u32(&mut self, x: u32) { self.write_u64(x as u64); }
}
type H = std::hash::BuildHasherDefault<MixH>;
struct Run2 { c: u32, live: u32, typ: u8 }
struct Patch { idx: u32, p: u16, q: u16 }

/// cancellation without window limits (qopt `cancel2`)
fn cancel2(t: &[u64], mask: &mut [u64], nq: usize) -> (u64, u64) {
    let n = t.len(); assert!(n < u32::MAX as usize);
    let mut st: Vec<Vec<Run2>> = (0..nq).map(|_| Vec::new()).collect();
    let mut next_c: Vec<u32> = vec![0; nq];
    let mut floor: Vec<u32> = vec![0; nq];
    let mut prev: Vec<u32> = vec![u32::MAX; n];
    let mut rids: Vec<[u32; 3]> = vec![[0; 3]; n];
    let mut map: std::collections::HashMap<(u64, u32), u32, H> = Default::default();
    let mut ctx: u32 = 0; let mut next_ctx: u32 = 1; let mut cstack: Vec<u32> = Vec::new();
    let (mut pairs_ccx, mut pairs_other) = (0u64, 0u64);
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
            K_POP => { ctx = cstack.pop().expect("unbalanced pop in padded chunk"); continue; }
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
        if !cond { prev[i] = map.insert((r, ctx), i as u32).unwrap_or(u32::MAX); }
    }
    (pairs_ccx, pairs_other)
}

/// cancellation plus merging (qopt `cancel3`, merge = true, QOPT_SIB off); returns patches and the merge counts
fn cancel3(t: &[u64], mask: &mut [u64], nq: usize) -> (Vec<Patch>, u64, u64) {
    let n = t.len(); assert!(n < u32::MAX as usize);
    let mut st: Vec<Vec<Run2>> = (0..nq).map(|_| Vec::new()).collect();
    let mut next_c: Vec<u32> = vec![0; nq];
    let mut floor: Vec<u32> = vec![0; nq];
    let mut prev: Vec<u32> = vec![u32::MAX; n];
    let mut rids: Vec<[u32; 3]> = vec![[0; 3]; n];
    let mut map: std::collections::HashMap<(u64, u32), u32, H> = Default::default();
    let mut m_ctl: std::collections::HashMap<u64, u32, H> = Default::default();
    let mut m_xt: std::collections::HashMap<u64, u32, H> = Default::default();
    let mut wrapped = mask_new(n);
    let mut patches: Vec<Patch> = Vec::new();
    let mut ctx: u32 = 0; let mut next_ctx: u32 = 1; let mut cstack: Vec<u32> = Vec::new();
    let (mut n_m1, mut n_m2) = (0u64, 0u64);
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
        let mut w: [(usize, u8); 3] = [(0, 0); 3]; let nw; let cond; let mut r = r0;
        match k {
            K_CCX => { let (lo, hi) = if a <= b { (a, b) } else { (b, a) }; w = [(lo, 0), (hi, 0), (c, 1)]; nw = 3; cond = false; r = rec(K_CCX, lo, hi, c); }
            K_CX => { w[0] = (a, 0); w[1] = (b, 1); nw = 2; cond = c != NONE; }
            K_CZ => { let (lo, hi) = if a <= b { (a, b) } else { (b, a) }; w[0] = (lo, 0); w[1] = (hi, 0); nw = 2; cond = true; }
            K_X => { w[0] = (a, 1); nw = 1; cond = b != NONE; }
            K_Z => { w[0] = (a, 0); nw = 1; cond = true; }
            K_HMR => { st[a].clear(); floor[a] = next_c[a]; continue; }
            K_BINV | K_BST0 | K_BST1 => { continue; }
            K_PUSH => { cstack.push(ctx); ctx = next_ctx; next_ctx += 1; continue; }
            K_POP => { ctx = cstack.pop().expect("unbalanced pop in padded chunk"); continue; }
            _ => continue,
        }
        let rep = (nw == 3 && (a == b || a == c || b == c)) || (nw == 2 && w[0].0 == w[1].0);
        if rep { for x in 0..nw { let q = w[x].0; st[q].clear(); floor[q] = next_c[q]; } continue; }
        if !cond {
            let key = (r, ctx);
            let mut hit: Option<u32> = None;
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
                continue;
            }
        }
        if k == K_CCX {
            let (lo, hi, tg) = (w[0].0, w[1].0, w[2].0);
            let kc = ((ctx as u64) << 32) | ((lo as u64) << 16) | hi as u64;
            let kx = [((ctx as u64) << 32) | ((lo as u64) << 16) | tg as u64, ((ctx as u64) << 32) | ((hi as u64) << 16) | tg as u64];
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
            let mut found: Option<(u32, usize, usize, usize, usize, usize)> = None;
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
                mset(mask, p as usize);
                unpush(&mut st, plo); unpush(&mut st, phi); unpush(&mut st, pt);
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
        if !cond { prev[i] = map.insert((r, ctx), i as u32).unwrap_or(u32::MAX); }
    }
    (patches, n_m1, n_m2)
}

/// Counts of one chunk: (CCX pairs cancelled by the first sweep, other pairs cancelled by it, merges M1, merges M2,
/// CCX records removed in total).
pub type Counts = (u64, u64, u64, u64, u64);

/// Mode 23 on one chunk of rows whose condition scopes are already balanced (padded by the caller).
pub fn mode23(rows: Vec<Row>) -> (Vec<Row>, Counts) {
    let t: Vec<u64> = rows.iter().map(|r| { assert!(known(r[0]), "qmerge: unknown record kind {}", r[0]); to64(r) }).collect();
    drop(rows);
    let n = t.len();
    let nq = 1usize << 16;
    let mut mask = mask_new(n);
    let (p_ccx, p_other) = cancel2(&t, &mut mask, nq);
    let (patches, m1, m2) = cancel3(&t, &mut mask, nq);
    let mut out: Vec<Row> = Vec::with_capacity(n + 2 * patches.len());
    let mut pi = 0;
    for i in 0..n {
        let pat = if pi < patches.len() && patches[pi].idx as usize == i { pi += 1; Some(&patches[pi - 1]) } else { None };
        if mget(&mask, i) { assert!(pat.is_none()); continue; }
        if let Some(p) = pat { let cx: Row = [K_CX, p.p, p.q, NONE as u16]; out.push(cx); out.push(to_row(t[i])); out.push(cx); }
        else { out.push(to_row(t[i])); }
    }
    assert_eq!(pi, patches.len());
    let ccx = |v: &mut dyn Iterator<Item = u16>| v.filter(|&k| k == K_CCX).count() as u64;
    let removed = ccx(&mut t.iter().map(|&x| kind(x))) - ccx(&mut out.iter().map(|r| r[0]));
    (out, (p_ccx, p_other, m1, m2, removed))
}
