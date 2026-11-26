//! Exact stream pass "abstriicher", VERSION 2 (port of abstriicher4.rs; differs from abstriicher_port.rs by: no Swap rule S15, no CCZ rule S14, and a guard), worker batzechlemmer of lane CLAUDE-Q644, files
//! q644/bw637/batzechlemmer/abstriicher4.rs; posted 2026-11-14T12:02Z; copied with that lane's permission).
//! Takes the gate records of one chunk and returns the chunk after these exact identities, iterated to a fixed point:
//!   (1) cancel: identical self-inverse records (X, CX, CCX, Z, CZ, same condition bit and scope) h ... g with only
//!       commuting records between them;
//!   (2) sandwich: U w U with U an unconditional X(a), CX(a,b) or CCX(a,b,t) and ONE non-commuting record w between:
//!         CX(a,b) CX(b,y;c) CX(a,b) = CX(b,y;c) CX(a,y;c)     CX(a,b) CX(x,a;c) CX(a,b) = CX(x,a;c) CX(x,b;c)
//!         CX(a,b) X(a;c) CX(a,b) = X(a;c) X(b;c)               CX(a,b) Z(b;c) CX(a,b) = Z(b;c) Z(a;c)
//!         CX(a,b) CZ(b,y;c) CX(a,b) = CZ(b,y;c) CZ(a,y;c)      X(a) CX(a,y;c) X(a) = CX(a,y;c) X(y;c)
//!         X(a) CCX(a,y,t) X(a) = CCX(a,y,t) CX(y,t)            X(a) CZ(a,y;c) X(a) = CZ(a,y;c) Z(y;c)
//!         CCX(a,b,t) w CCX(a,b,t) for w = CX / X / Z on a, b or t: one Toffoli less (the CZ form, CCZ kind 14, is NOT applied)
//!       these save one record (and one Toffoli for the CCX forms);
//! The pass NEVER creates a Swap (kind 10) or a CCZ (kind 14): the output kinds are those of the input.  GUARD: a chunk that holds a record
//! of kind 10, 11 or 14, of any kind outside {1-9, 12, 13, 15, 16, 18}, or a qubit id >= 1024 is returned UNCHANGED (counted, see `guarded_chunks`).
//! Phase, classical bits and every lane are unchanged.  Settings: mode 1 (cancellation and sandwiches), 40 rounds, stop when a round removes fewer than STOPBELOW records.
//! The function is a pure function of the input records: no file, environment, hash order or thread dependence.
//! One call handles a chunk that may start or end inside open condition scopes (a pop on an empty stack opens a new frame).
use super::Row;
use std::sync::atomic::{AtomicUsize, Ordering};

static GUARDED: AtomicUsize = AtomicUsize::new(0);
/// number of chunks returned unchanged by the guard so far (a count only; it influences nothing)
pub fn guarded_chunks() -> usize { GUARDED.load(Ordering::Relaxed) }

/// true when the pass may touch this chunk: only kinds 1-9, 12, 13, 15, 16, 18 and qubit operands below NQ
fn admissible(rows: &[Row]) -> bool {
    rows.iter().all(|r| match r[0] {
        1 | 2 | 3 | 4 | 5 | 15 | 16 | 18 => true,
        6 | 7 | 12 => (r[1] as usize) < NQ,
        8 | 9 => (r[1] as usize) < NQ && (r[2] as usize) < NQ,
        13 => (r[1] as usize) < NQ && (r[2] as usize) < NQ && (r[3] as usize) < NQ,
        _ => false,
    })
}

const NQ: usize = 1024;
const NB: usize = 65536;
/// rounds and per-round stop threshold (records removed) of the lane's run
pub const ROUNDS: usize = 40;
pub const STOPBELOW: i64 = 20000;

#[inline] fn norm(r: &Row) -> Row {
    if r[0] == 13 && r[1] > r[2] { [13, r[2], r[1], r[3]] }
    else if (r[0] == 9 || r[0] == 10) && r[1] > r[2] { [r[0], r[2], r[1], r[3]] }
    else if r[0] == 14 { let mut t = [r[1], r[2], r[3]]; t.sort(); [14, t[0], t[1], t[2]] }
    else { *r }
}
/// (qubit, role) of the qubit operands: role 1 = target of a self-inverse gate, 0 = control / phase-type, 2 = measurement, 3 = swap
#[inline] fn roles(r: &Row, out: &mut [(u16, u8); 3]) -> usize {
    match r[0] {
        6 => { out[0] = (r[1], 1); 1 }
        8 => { out[0] = (r[2], 1); out[1] = (r[1], 0); 2 }
        13 => { out[0] = (r[3], 1); out[1] = (r[1], 0); out[2] = (r[2], 0); 3 }
        7 => { out[0] = (r[1], 0); 1 }
        9 => { out[0] = (r[1], 0); out[1] = (r[2], 0); 2 }
        10 => { out[0] = (r[1], 3); out[1] = (r[2], 3); 2 }
        14 => { out[0] = (r[1], 0); out[1] = (r[2], 0); out[2] = (r[3], 0); 3 }
        12 => { out[0] = (r[1], 2); 1 }
        _ => 0,
    }
}
#[inline] fn condbit(r: &Row) -> u16 { match r[0] { 6 | 7 => r[2], 8 => r[3], 9 => r[3], 10 => r[3], _ => 65535 } }
fn role_on(h: &Row, q: u16) -> u8 {
    let mut rk = [(0u16, 0u8); 3]; let n = roles(h, &mut rk); let mut role = 9u8;
    for t in 0..n { if rk[t].0 == q { role = rk[t].1; } }
    role
}
/// conjugate w by U (U an unconditional X, CX or CCX); returns the extra record to put after w (w itself stays)
fn conj(u: &Row, w: &Row) -> Option<Row> {
    if u[0] == 8 {
        let (a, b) = (u[1], u[2]); if u[3] != 65535 { return None; }
        match w[0] {
            8 => { let (x, y, c) = (w[1], w[2], w[3]);
                if x == b && y != a && y != b { Some([8, a, y, c]) } else if y == a && x != b && x != a { Some([8, x, b, c]) } else { None } }
            6 => { if w[1] == a { Some([6, b, w[2], 0]) } else { None } }
            7 => { if w[1] == b { Some([7, a, w[2], 0]) } else { None } }
            9 => { let (x, y, c) = (w[1], w[2], w[3]);
                if x == b || y == b { let o = if x == b { y } else { x }; if o == a { Some([7, a, c, 0]) } else { Some([9, a.min(o), a.max(o), c]) } } else { None } }
            _ => None,
        }
    } else if u[0] == 6 {
        if u[2] != 65535 { return None; } let q = u[1];
        match w[0] {
            8 => { if w[1] == q && w[2] != q { Some([6, w[2], w[3], 0]) } else { None } }
            13 => { if w[1] == q { Some([8, w[2], w[3], 65535]) } else if w[2] == q { Some([8, w[1], w[3], 65535]) } else { None } }
            9 => { if w[1] == q { Some([7, w[2], w[3], 0]) } else if w[2] == q { Some([7, w[1], w[3], 0]) } else { None } }
            _ => None,
        }
    } else if u[0] == 13 {
        let (a, b, t) = (u[1], u[2], u[3]);
        match w[0] {
            8 => { let (x, y, c) = (w[1], w[2], w[3]); if c != 65535 { return None; }
                if x == t && y != a && y != b && y != t { Some([13, a, b, y]) }
                else if y == a && x != b && x != t && x != a { Some([13, x, b, t]) }
                else if y == b && x != a && x != t && x != b { Some([13, a, x, t]) } else { None } }
            6 => { if w[1] == a { Some([8, b, t, w[2]]) } else if w[1] == b { Some([8, a, t, w[2]]) } else { None } }
            7 => { if w[1] == t { Some([9, a.min(b), a.max(b), w[2]]) } else { None } }
            9 => { let (x, y, c) = (w[1], w[2], w[3]); if c != 65535 { return None; }
                let o = if x == t { y } else if y == t { x } else { return None };
                let _ = (o, a, b); None }
            _ => None,
        }
    } else { None }
}

/// The pass with mode 1 (no Swap rule), ROUNDS rounds, STOPBELOW.
pub fn abst(rows: Vec<Row>) -> Vec<Row> { abst_with(rows, 1, ROUNDS, STOPBELOW) }

/// `mode`: bit 0 = sandwiches; mode 0 = plain cancellation.  Bit 1 (Swap creation) was REMOVED in this version: mode is taken as mode & 1.
pub fn abst_with(rows: Vec<Row>, mode: u32, rounds: usize, thr: i64) -> Vec<Row> {
    let sand = (mode & 1) != 0;
    if !admissible(&rows) { GUARDED.fetch_add(1, Ordering::Relaxed); return rows; }
    let mut v0: Vec<Row> = rows;
    for _round in 0..rounds {
        let n = v0.len();
        let mut v: Vec<Row> = vec![[0; 4]; 2 * n];
        for i in 0..n { v[2 * i] = v0[i]; }
        drop(std::mem::take(&mut v0));
        let mut alive = vec![false; 2 * n]; for i in 0..n { alive[2 * i] = true; }
        let mut frame = vec![0u32; 2 * n];
        let mut lists: Vec<Vec<u32>> = vec![Vec::new(); NQ];
        let mut lastw = vec![0i64; NB];
        let mut stack: Vec<u32> = vec![0]; let mut nextf = 1u32; let mut removed = 0i64;
        let mut rg = [(0u16, 0u8); 3];
        for gi in 0..n {
            let p2 = 2 * gi; let g = norm(&v[p2]); let k = g[0];
            match k {
                15 => { frame[p2] = *stack.last().unwrap(); stack.push(nextf); nextf += 1; continue; }
                16 => { if stack.len() > 1 { stack.pop(); } else { stack[0] = nextf; nextf += 1; } frame[p2] = *stack.last().unwrap(); continue; }
                3 | 4 | 5 => { lastw[g[1] as usize] = p2 as i64 + 1; continue; }
                12 => { lastw[g[2] as usize] = p2 as i64 + 1; frame[p2] = *stack.last().unwrap();
                    let nr = roles(&g, &mut rg); for j in 0..nr { lists[rg[j].0 as usize].push(p2 as u32); } continue; }
                1 | 2 | 18 => { continue; }
                _ => {}
            }
            frame[p2] = *stack.last().unwrap(); let fr = frame[p2];
            let nr = roles(&g, &mut rg); let cb = condbit(&g); let mut done = false;
            let p = rg[0].0 as usize; let mut idx = lists[p].len(); let mut steps = 0;
            let mut blockers: Vec<u32> = Vec::new(); let mut hpos: i64 = -1;
            while idx > 0 && steps < 8192 {
                idx -= 1; let kk = lists[p][idx] as usize; if !alive[kk] { continue; } steps += 1; let h = norm(&v[kk]);
                if h == g && frame[kk] == fr { hpos = kk as i64; break; }
                let role = role_on(&h, rg[0].0);
                if role == 2 || role != rg[0].1 { if !sand || blockers.len() >= 1 || role == 2 { break; } blockers.push(kk as u32); }
            }
            if hpos >= 0 {
                let kk = hpos as usize; let mut ok = true;
                if cb != 65535 && lastw[cb as usize] > kk as i64 + 1 { ok = false; }
                if ok {
                    for j in 1..nr {
                        let q = rg[j].0 as usize; let mut i2 = lists[q].len(); let mut st2 = 0;
                        while i2 > 0 {
                            i2 -= 1; let k2 = lists[q][i2] as usize; if k2 <= kk { break; } if !alive[k2] { continue; }
                            st2 += 1; if st2 > 8192 { ok = false; break; }
                            let h2 = norm(&v[k2]); let role = role_on(&h2, rg[j].0);
                            if role == 2 { ok = false; break; }
                            if role != rg[j].1 {
                                if !sand { ok = false; break; }
                                if !blockers.contains(&(k2 as u32)) { if blockers.len() >= 1 { ok = false; break; } blockers.push(k2 as u32); }
                            }
                        }
                        if !ok { break; }
                    }
                }
                if ok && blockers.is_empty() {
                    alive[kk] = false; alive[p2] = false; removed += 2; done = true;
                } else if ok && blockers.len() == 1 && (mode & 1) != 0 && (k == 6 || k == 8 || k == 13) {
                    let w = blockers[0] as usize;
                    if w % 2 == 0 && !alive[w + 1] && (g[0] == 6 && g[2] == 65535 || g[0] == 8 && g[3] == 65535 || g[0] == 13) {
                        if let Some(x) = conj(&g, &norm(&v[w])) {
                            alive[kk] = false; alive[p2] = false; v[w + 1] = x; alive[w + 1] = true; frame[w + 1] = frame[w]; removed += 1;
                            let mut rx = [(0u16, 0u8); 3]; let nx = roles(&x, &mut rx);
                            for j in 0..nx { let l = &mut lists[rx[j].0 as usize]; let pos = l.partition_point(|&e| (e as usize) < w + 1); l.insert(pos, (w + 1) as u32); }
                            done = true;
                        }
                    }
                }
            }
            if !done { for j in 0..nr { lists[rg[j].0 as usize].push(p2 as u32); } }
        }
        let mut w = Vec::new(); for i in 0..2 * n { if alive[i] { w.push(v[i]); } } v0 = w;
        if removed < thr { break; }
    }
    v0.shrink_to_fit();
    v0
}
