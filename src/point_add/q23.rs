// Exact pair cancellation and Toffoli merging over one chunk of 8-byte rows (almond-lab's `qopt` mode 23, ported to run
// inside the build per chunk; the logic is the offline tool's `cancel2` followed by `cancel3(merge = true)`).
// Rows are [kind, a, b, c]: 6 X(a) if b, 7 Z(a) if b, 8 CX(a -> b) if c, 9 CZ(a, b) if c, 12 HMR(a -> bit b), 13 CCX(a, b -> c),
// 15 push condition a, 16 pop; 1 / 2 / 18 register records, 3 / 4 / 5 classical bit records (no qubit).
//
// cancel2: two identical unconditioned self-inverse gates (X, CX, CCX; controls of a CCX sorted) in the same condition-block
// instance cancel when every gate between them on their wires commutes with them: on each wire the two gates sit in the same
// "run" of uses of one type (control-type uses: CCX / CX controls, CZ, Z; target-type uses: CCX / CX target, X), and no
// measurement (HMR) on any of their wires lies between them.
// cancel3: cancel2 again, plus merging of a Toffoli with an earlier movable one (on top of all its wires' runs):
//   M2 (same controls, different targets):  CCX(a,b,t1) ... CCX(a,b,t)  ->  CX(t->t1) CCX(a,b,t) CX(t->t1)
//   M1 (same target, one shared control):   CCX(x,b1,t) ... CCX(x,c,t)  ->  CX(b1->c) CCX(x,c,t) CX(b1->c)
// The earlier gate is deleted and the later one wrapped in two CX gates: one Toffoli saved per merge. Every rewrite is a
// permutation identity on basis states (no phase). Any record kind outside the list above stops the build (assert).
use super::Row;

const NONE: usize = 65535;
const K_X: u16 = 6; const K_Z: u16 = 7; const K_CX: u16 = 8; const K_CZ: u16 = 9; const K_HMR: u16 = 12; const K_CCX: u16 = 13;
const K_PUSH: u16 = 15; const K_POP: u16 = 16;

#[inline(always)] fn kind(r: u64) -> u16 { r as u16 }
#[inline(always)] fn fa(r: u64) -> usize { ((r >> 16) & 0xffff) as usize }
#[inline(always)] fn fb(r: u64) -> usize { ((r >> 32) & 0xffff) as usize }
#[inline(always)] fn fc(r: u64) -> usize { (r >> 48) as usize }
#[inline(always)] fn rec(k: u16, a: usize, b: usize, c: usize) -> u64 { (k as u64) | ((a as u64) << 16) | ((b as u64) << 32) | ((c as u64) << 48) }
#[inline(always)] fn to_u64(r: Row) -> u64 { (r[0] as u64) | ((r[1] as u64) << 16) | ((r[2] as u64) << 32) | ((r[3] as u64) << 48) }
#[inline(always)] fn to_row(x: u64) -> Row { [x as u16, (x >> 16) as u16, (x >> 32) as u16, (x >> 48) as u16] }
#[inline] fn mget(m: &[u64], i: usize) -> bool { (m[i >> 6] >> (i & 63)) & 1 != 0 }
#[inline] fn mset(m: &mut [u64], i: usize) { m[i >> 6] |= 1 << (i & 63); }

#[derive(Default, Clone, Copy)]
struct MixH(u64);
impl std::hash::Hasher for MixH {
    fn finish(&self) -> u64 { let mut x = self.0; x ^= x >> 30; x = x.wrapping_mul(0xbf58476d1ce4e5b9); x ^= x >> 27; x = x.wrapping_mul(0x94d049bb133111eb); x ^ (x >> 31) }
    fn write(&mut self, b: &[u8]) { for &x in b { self.write_u64(x as u64); } }
    fn write_u64(&mut self, x: u64) { self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x517cc1b727220a95); }
    fn write_u32(&mut self, x: u32) { self.write_u64(x as u64); }
}
type BH = std::hash::BuildHasherDefault<MixH>;
struct Run2 { c: u32, live: u32, typ: u8 }

fn check_kinds(t: &[u64]) { for &r in t { let k = kind(r); assert!(matches!(k, 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 12 | 13 | 15 | 16 | 18), "q23: record kind {}", k); } }

fn cancel2(t: &[u64], mask: &mut [u64]) -> u64 {
    let n = t.len(); assert!(n < u32::MAX as usize);
    let nq = 1 << 16;
    let mut st: Vec<Vec<Run2>> = (0..nq).map(|_| Vec::new()).collect();
    let mut next_c: Vec<u32> = vec![0; nq];
    let mut floor: Vec<u32> = vec![0; nq];
    let mut prev: Vec<u32> = vec![u32::MAX; n];
    let mut rids: Vec<[u32; 3]> = vec![[0; 3]; n];
    let mut map: std::collections::HashMap<(u64, u32), u32, BH> = Default::default();
    let mut ctx: u32 = 0; let mut next_ctx: u32 = 1; let mut cstack: Vec<u32> = Vec::new();
    let mut pairs = 0u64;
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
            K_POP => { ctx = cstack.pop().expect("q23: pop without push"); continue; }
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
                pairs += 1;
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
    pairs
}

struct Patch { idx: u32, p: u16, q: u16 }

fn cancel3(t: &[u64], mask: &mut [u64]) -> (Vec<Patch>, u64) {
    let n = t.len(); assert!(n < u32::MAX as usize);
    let nq = 1 << 16;
    let mut st: Vec<Vec<Run2>> = (0..nq).map(|_| Vec::new()).collect();
    let mut next_c: Vec<u32> = vec![0; nq];
    let mut floor: Vec<u32> = vec![0; nq];
    let mut prev: Vec<u32> = vec![u32::MAX; n];
    let mut rids: Vec<[u32; 3]> = vec![[0; 3]; n];
    let mut map: std::collections::HashMap<(u64, u32), u32, BH> = Default::default();
    let mut m_ctl: std::collections::HashMap<u64, u32, BH> = Default::default();
    let mut m_xt: std::collections::HashMap<u64, u32, BH> = Default::default();
    let mut wrapped = vec![0u64; n.div_ceil(64)];
    let mut patches: Vec<Patch> = Vec::new();
    let mut ctx: u32 = 0; let mut next_ctx: u32 = 1; let mut cstack: Vec<u32> = Vec::new();
    let mut pairs = 0u64;
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
            K_PUSH => { cstack.push(ctx); ctx = next_ctx; next_ctx += 1; continue; }
            K_POP => { ctx = cstack.pop().expect("q23: pop without push"); continue; }
            _ => continue,
        }
        let rep = (nw == 3 && (a == b || a == c || b == c)) || (nw == 2 && w[0].0 == w[1].0);
        if rep { for x in 0..nw { let q = w[x].0; st[q].clear(); floor[q] = next_c[q]; } continue; }
        if !cond {
            let key = (r, ctx);
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
                pairs += 1;
                continue;
            }
        }
        if k == K_CCX {
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
                    if pt != tg && pt != lo && pt != hi { found = Some((p, plo, phi, pt, tg, pt)); }
                }
            }
            if found.is_none() {
                for (j, x) in [lo, hi].into_iter().enumerate() {
                    if let Some(&p) = m_xt.get(&kx[j]) {
                        if let Some((plo, phi, pt)) = usable(p, &st, mask, &wrapped) {
                            let b1 = if plo == x { phi } else { plo };
                            let cc = if j == 0 { hi } else { lo };
                            if b1 != cc && b1 != tg && b1 != x { found = Some((p, plo, phi, pt, b1, cc)); break; }
                        }
                    }
                }
            }
            if let Some((p, plo, phi, pt, from, to)) = found {
                mset(mask, p as usize);
                unpush(&mut st, plo); unpush(&mut st, phi); unpush(&mut st, pt);
                // CX(from->to) G CX(from->to); all three are pinned (never cancelled or merged again)
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
    (patches, pairs)
}

/// One chunk (condition scopes balanced by the caller's padding): returns the rewritten rows and
/// (cancel2 pairs, cancel3 pairs, merges, Toffolis removed).
pub fn q23(rows: Vec<Row>) -> (Vec<Row>, [u64; 4]) {
    let t: Vec<u64> = rows.into_iter().map(to_u64).collect();
    check_kinds(&t);
    let n = t.len();
    let mut mask = vec![0u64; n.div_ceil(64)];
    let p2 = cancel2(&t, &mut mask);
    let (patches, p3) = cancel3(&t, &mut mask);
    let mut out: Vec<Row> = Vec::with_capacity(n + 2 * patches.len());
    let (mut pi, mut ccx_in, mut ccx_out) = (0usize, 0u64, 0u64);
    for i in 0..n {
        if kind(t[i]) == K_CCX { ccx_in += 1; }
        let pat = if pi < patches.len() && patches[pi].idx as usize == i { pi += 1; Some(&patches[pi - 1]) } else { None };
        if mget(&mask, i) { assert!(pat.is_none()); continue; }
        if kind(t[i]) == K_CCX { ccx_out += 1; }
        if let Some(p) = pat { let cx = to_row(rec(K_CX, p.p as usize, p.q as usize, NONE)); out.push(cx); out.push(to_row(t[i])); out.push(cx); }
        else { out.push(to_row(t[i])); }
    }
    assert_eq!(pi, patches.len());
    (out, [p2, p3, patches.len() as u64, ccx_in - ccx_out])
}
