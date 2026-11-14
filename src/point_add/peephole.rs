// Exact stream-level peephole over decoded gate records ([u32; 4] rows, unbounded classical bit IDs).
pub const TOMB: u32 = 17;
pub const BLOCK: u32 = 20;
pub const CLASS_PAIR: u32 = 1;
pub const CLASS_MERGE: u32 = 2;
pub const CLASS_GADGET_T: u32 = 3;
pub const CLASS_GADGET_U: u32 = 4;
pub const CLASS_COPY: u32 = 5;
pub const CLASS_CTRLW: u32 = 6;
pub const NONE: u32 = u32::MAX;
const NQ: usize = 1024;

pub trait Rows {
    fn len(&self) -> usize;
    fn get(&self, i: usize) -> [u32; 4];
    fn set(&mut self, i: usize, r: [u32; 4]);
    fn expand(&mut self, i: usize, block: [[u32; 4]; 3]);
    fn block(&self, i: usize) -> [[u32; 4]; 3];
}

#[derive(Default, Clone, Copy, Debug)]
pub struct Stats {
    pub pair: u64,
    pub merge: u64,
    pub gadget_t: u64,
    pub gadget_u: u64,
    pub copy: u64,
    pub ctrl_x: u64,
    pub ctrl_cx: u64,
    pub ctrl_xx: u64,
}
impl Stats {
    pub fn removed_ccx(&self) -> u64 {
        self.pair + self.merge + self.gadget_t + self.gadget_u + self.copy + self.ctrl_cx + 2 * self.ctrl_x + 2 * self.ctrl_xx
    }
}

#[inline]
fn tomb(class: u32) -> [u32; 4] {
    [TOMB, class, NONE, NONE]
}

struct Ring {
    ring: usize,
    idx: Vec<u32>,
    cnt: Vec<u64>,
}
impl Ring {
    fn new(ring: usize) -> Self {
        Ring { ring, idx: vec![0; NQ * ring], cnt: vec![0; NQ] }
    }
    #[inline]
    fn push(&mut self, q: usize, i: usize) {
        let r = self.ring;
        let c = self.cnt[q];
        self.idx[q * r + (c as usize % r)] = i as u32;
        self.cnt[q] = c + 1;
    }
    fn live_since<R: Rows>(&self, q: usize, p: usize, rows: &R) -> Option<([usize; 2], usize)> {
        let r = self.ring;
        let c = self.cnt[q] as usize;
        let m = c.min(r);
        let mut out = [0usize; 2];
        let mut k = 0usize;
        for j in 0..m {
            let e = self.idx[q * r + ((c - 1 - j) % r)] as usize;
            if e <= p {
                return Some((out, k));
            }
            if rows.get(e)[0] != TOMB {
                if k == 2 {
                    return None;
                }
                out[k] = e;
                k += 1;
            }
        }
        if c <= r { Some((out, k)) } else { None }
    }
    fn clear_since<R: Rows>(&self, q: usize, p: usize, rows: &R) -> bool {
        let r = self.ring;
        let c = self.cnt[q] as usize;
        let m = c.min(r);
        for j in 0..m {
            let e = self.idx[q * r + ((c - 1 - j) % r)] as usize;
            if e <= p {
                return true;
            }
            if rows.get(e)[0] != TOMB {
                return false;
            }
        }
        c <= r
    }
}

#[inline]
fn same_ccx(r: [u32; 4], x: usize, y: usize, t: usize) -> bool {
    r[0] == 13 && r[3] as usize == t && ((r[1] as usize == x && r[2] as usize == y) || (r[1] as usize == y && r[2] as usize == x))
}

#[derive(Clone, Copy)]
struct Gad {
    pos: [usize; 4],
    t: [u32; 4],
    u: [u32; 4],
    tfirst: bool,
}
impl Gad {
    fn layout(&self, tfirst: bool) -> [[u32; 4]; 4] {
        let (t, u) = (self.t, self.u);
        if tfirst { [t, u, t, u] } else { [u, t, u, t] }
    }
    fn intact<R: Rows>(&self, rows: &R) -> bool {
        let native = self.layout(self.tfirst);
        (0..4).all(|k| rows.get(self.pos[k]) == native[k])
    }
}

fn detect_gadget<R: Rows>(rows: &R, i: usize) -> Option<Gad> {
    let n = rows.len();
    let mut pos = [i, 0, 0, 0];
    let mut rr = [rows.get(i), [0; 4], [0; 4], [0; 4]];
    let mut j = i + 1;
    for k in 1..4 {
        while j < n && rows.get(j)[0] == TOMB {
            j += 1;
        }
        if j >= n {
            return None;
        }
        let r = rows.get(j);
        if r[0] != 13 {
            return None;
        }
        pos[k] = j;
        rr[k] = r;
        j += 1;
    }
    if rr[0] != rr[2] || rr[1] != rr[3] {
        return None;
    }
    for (tfirst, t, u) in [(true, rr[0], rr[1]), (false, rr[1], rr[0])] {
        let (c1, c2, d) = (t[1], t[2], t[3]);
        let ut = u[3];
        if (u[1] == d || u[2] == d) && ut != c1 && ut != c2 && ut != d {
            return Some(Gad { pos, t, u, tfirst });
        }
    }
    None
}

#[derive(Clone, Copy)]
struct Pend {
    idx: u32,
    ctx: u32,
}

#[inline]
fn key3(x: usize, y: usize, t: usize) -> u32 {
    let (x, y) = if x < y { (x, y) } else { (y, x) };
    ((x as u32) << 20) | ((y as u32) << 10) | t as u32
}

pub fn pass_cfg<R: Rows>(rows: &mut R, ring_cap: usize, tgt_hist: usize) -> Stats {
    let n = rows.len();
    assert!(n < u32::MAX as usize);
    let mut max_bit = 0usize;
    for i in 0..n {
        let r = rows.get(i);
        let b = match r[0] {
            3 | 4 | 5 | 15 => r[1],
            12 => r[2],
            _ => NONE,
        };
        if b != NONE && b as usize >= max_bit {
            max_bit = b as usize + 1;
        }
    }
    let mut st = Stats::default();
    let mut wl = Ring::new(ring_cap);
    let mut rl = Ring::new(ring_cap);
    let mut bep = vec![0u32; max_bit.max(1)];
    let mut ctx: u32 = 0;
    let mut last_ctx_change = 0usize;
    let mut stack: Vec<u32> = vec![];
    let mut intern: std::collections::HashMap<(u32, u32, u32), u32> = std::collections::HashMap::new();
    let mut pending: std::collections::HashMap<u32, Pend> = std::collections::HashMap::with_capacity(1 << 16);
    let mut bytgt: Vec<Vec<(u32, u32, u32, u32)>> = vec![vec![(u32::MAX, 0, 0, 0); tgt_hist]; NQ];
    let mut gad_t: std::collections::HashMap<u64, Gad> = std::collections::HashMap::new();
    let mut gad_u: std::collections::HashMap<u64, Gad> = std::collections::HashMap::new();
    let gkey = |r: [u32; 4], ctx: u32| -> u64 {
        let (x, y) = (r[1].min(r[2]) as u64, r[1].max(r[2]) as u64);
        (x << 52) | (y << 42) | ((r[3] as u64) << 32) | ctx as u64
    };
    for i in 0..n {
        let r = rows.get(i);
        let k = r[0];
        match k {
            TOMB | 0 | 1 | 2 | 18 => {}
            BLOCK => {
                for br in rows.block(i) {
                    match br[0] {
                        6 => wl.push(br[1] as usize, i),
                        8 => { rl.push(br[1] as usize, i); wl.push(br[2] as usize, i); }
                        13 => { rl.push(br[1] as usize, i); rl.push(br[2] as usize, i); wl.push(br[3] as usize, i); }
                        _ => panic!("peephole: unexpected block row"),
                    }
                }
            }
            15 => {
                last_ctx_change = i;
                let b = r[1] as usize;
                let nid = intern.len() as u32 + 1;
                let c = *intern.entry((ctx, r[1], bep[b])).or_insert(nid);
                stack.push(ctx);
                ctx = c;
            }
            16 => {
                last_ctx_change = i;
                ctx = stack.pop().expect("peephole: unbalanced pop");
            }
            3 | 4 | 5 => bep[r[1] as usize] += 1,
            6 => wl.push(r[1] as usize, i),
            7 => rl.push(r[1] as usize, i),
            8 => {
                wl.push(r[2] as usize, i);
                rl.push(r[1] as usize, i);
            }
            9 => {
                rl.push(r[1] as usize, i);
                rl.push(r[2] as usize, i);
            }
            10 => {
                let (a, b) = (r[1] as usize, r[2] as usize);
                wl.push(a, i); wl.push(b, i); rl.push(a, i); rl.push(b, i);
            }
            11 => {
                let q = r[1] as usize;
                wl.push(q, i);
                rl.push(q, i);
            }
            12 => {
                let (q, b) = (r[1] as usize, r[2]);
                if b != NONE {
                    bep[b as usize] += 1;
                }
                wl.push(q, i);
                rl.push(q, i);
            }
            14 => {
                rl.push(r[1] as usize, i);
                rl.push(r[2] as usize, i);
                rl.push(r[3] as usize, i);
            }
            19 => {
                rl.push(r[1] as usize, i);
                rl.push(r[2] as usize, i);
                wl.push(r[3] as usize, i);
                rl.push(r[3] as usize, i);
            }
            13 => {
                let (a, b, t) = (r[1] as usize, r[2] as usize, r[3] as usize);
                assert!(a < NQ && b < NQ && t < NQ, "peephole: qubit index outside key packing");
                let key = key3(a, b, t);
                if let Some(p) = pending.get(&key).copied() {
                    let pi = p.idx as usize;
                    if p.ctx == ctx
                        && same_ccx(rows.get(pi), a, b, t)
                        && wl.clear_since(a, pi, rows)
                        && wl.clear_since(b, pi, rows)
                        && rl.clear_since(t, pi, rows)
                    {
                        pending.remove(&key);
                        rows.set(pi, tomb(CLASS_PAIR));
                        rows.set(i, tomb(CLASS_PAIR));
                        st.pair += 2;
                        continue;
                    }
                }
                if let Some(p) = pending.get(&key).copied() {
                    let pi = p.idx as usize;
                    if p.ctx == ctx && last_ctx_change < pi && same_ccx(rows.get(pi), a, b, t) && rl.clear_since(t, pi, rows) {
                        let la = wl.live_since(a, pi, rows);
                        let lb = wl.live_since(b, pi, rows);
                        let all_x = |l: Option<([usize; 2], usize)>, q: usize| -> Option<usize> {
                            let (x, c) = l?;
                            for z in 0..c {
                                let g = rows.get(x[z]);
                                if !(g[0] == 6 && g[1] as usize == q && g[2] == NONE) { return None; }
                            }
                            Some(c)
                        };
                        if let (Some(ca), Some(cb)) = (all_x(la, a), all_x(lb, b)) {
                            if ca + cb >= 2 {
                                let (pa, pb) = (ca % 2 == 1, cb % 2 == 1);
                                pending.remove(&key);
                                rows.set(pi, tomb(CLASS_CTRLW));
                                let (au, bu, tu) = (a as u32, b as u32, t as u32);
                                match (pa, pb) {
                                    (false, false) => rows.set(i, tomb(CLASS_CTRLW)),
                                    (true, false) => { rows.set(i, [8, bu, tu, NONE]); wl.push(t, i); rl.push(b, i); }
                                    (false, true) => { rows.set(i, [8, au, tu, NONE]); wl.push(t, i); rl.push(a, i); }
                                    (true, true) => {
                                        rows.expand(i, [[6, tu, NONE, NONE], [8, au, tu, NONE], [8, bu, tu, NONE]]);
                                        wl.push(t, i); rl.push(a, i); rl.push(b, i);
                                    }
                                }
                                st.ctrl_xx += 1;
                                continue;
                            }
                        }
                        let pick = match (la, lb) {
                            (Some((x, 1)), Some((_, 0))) => Some((a, b, x[0])),
                            (Some((_, 0)), Some((x, 1))) => Some((b, a, x[0])),
                            _ => None,
                        };
                        if let Some((w, o, j)) = pick {
                            let g = rows.get(j);
                            if g[0] == 6 && g[1] as usize == w && g[2] == NONE {
                                pending.remove(&key);
                                rows.set(pi, tomb(CLASS_CTRLW));
                                rows.set(i, [8, o as u32, t as u32, NONE]);
                                st.ctrl_x += 1;
                                wl.push(t, i);
                                rl.push(o, i);
                                continue;
                            }
                            if g[0] == 8 && g[2] as usize == w && g[3] == NONE {
                                let x = g[1] as usize;
                                if x != o && x != t && wl.clear_since(x, j, rows) {
                                    pending.remove(&key);
                                    rows.set(pi, tomb(CLASS_CTRLW));
                                    rows.set(i, [13, x as u32, o as u32, t as u32]);
                                    st.ctrl_cx += 1;
                                    let nk = key3(x, o, t);
                                    pending.insert(nk, Pend { idx: i as u32, ctx });
                                    wl.push(t, i);
                                    rl.push(x, i);
                                    rl.push(o, i);
                                    continue;
                                }
                            }
                        }
                    }
                }
                let mut t = t;
                let mut key = key;
                if let Some(p) = pending.get(&key).copied() {
                    let pi = p.idx as usize;
                    if p.ctx == ctx
                        && last_ctx_change < pi
                        && same_ccx(rows.get(pi), a, b, t)
                        && wl.clear_since(a, pi, rows)
                        && wl.clear_since(b, pi, rows)
                    {
                        if let Some((ls, 1)) = rl.live_since(t, pi, rows) {
                            let j = ls[0];
                            let cx = rows.get(j);
                            let y = cx[2] as usize;
                            if cx[0] == 8 && cx[1] as usize == t && cx[3] == NONE && y != a && y != b && y != t
                                && rl.clear_since(y, j, rows)
                            {
                                pending.remove(&key);
                                rows.set(pi, tomb(CLASS_COPY));
                                rows.set(i, [13, a as u32, b as u32, y as u32]);
                                st.copy += 1;
                                t = y;
                                key = key3(a, b, t);
                            }
                        }
                    }
                }
                if let Some(g) = detect_gadget(rows, i) {
                    let (tr, ur) = (g.t, g.u);
                    let (c1, c2, d) = (tr[1] as usize, tr[2] as usize, tr[3] as usize);
                    let (e1, e2, tu) = (ur[1] as usize, ur[2] as usize, ur[3] as usize);
                    let (tk, uk) = (gkey(tr, ctx), gkey(ur, ctx));
                    let mut paired = false;
                    if let Some(p) = gad_t.get(&tk).copied() {
                        let pl = p.pos[3];
                        if pl < i && p.intact(rows) && wl.clear_since(c1, pl, rows) && wl.clear_since(c2, pl, rows) && rl.clear_since(d, pl, rows) {
                            let a2 = p.layout(false);
                            for q in 0..4 { rows.set(p.pos[q], a2[q]); }
                            rows.set(pl, tomb(CLASS_GADGET_T));
                            let b2 = g.layout(true);
                            for q in 0..4 { rows.set(g.pos[q], b2[q]); }
                            rows.set(g.pos[0], tomb(CLASS_GADGET_T));
                            gad_t.remove(&tk);
                            st.gadget_t += 2;
                            paired = true;
                        }
                    }
                    if !paired {
                        if let Some(p) = gad_u.get(&uk).copied() {
                            let pl = p.pos[3];
                            if pl < i && p.intact(rows) && wl.clear_since(e1, pl, rows) && wl.clear_since(e2, pl, rows) && rl.clear_since(tu, pl, rows) {
                                let a2 = p.layout(true);
                                for q in 0..4 { rows.set(p.pos[q], a2[q]); }
                                rows.set(pl, tomb(CLASS_GADGET_U));
                                let b2 = g.layout(false);
                                for q in 0..4 { rows.set(g.pos[q], b2[q]); }
                                rows.set(g.pos[0], tomb(CLASS_GADGET_U));
                                gad_u.remove(&uk);
                                st.gadget_u += 2;
                                paired = true;
                            }
                        }
                    }
                    if paired {
                        continue;
                    }
                    gad_t.insert(tk, g);
                    gad_u.insert(uk, g);
                }
                let mut merged_with: Option<usize> = None;
                for e in bytgt[t].iter_mut() {
                    let (pi, ea, eb, ec) = *e;
                    if pi == u32::MAX || ec != ctx {
                        continue;
                    }
                    let pi = pi as usize;
                    let (ea, eb) = (ea as usize, eb as usize);
                    if !same_ccx(rows.get(pi), ea, eb, t) {
                        *e = (u32::MAX, 0, 0, 0);
                        continue;
                    }
                    let (s_, bo) = if ea == a || ea == b {
                        (ea, eb)
                    } else if eb == a || eb == b {
                        (eb, ea)
                    } else {
                        continue;
                    };
                    if bo == a || bo == b {
                        continue;
                    }
                    let c = if s_ == a { b } else { a };
                    if wl.clear_since(s_, pi, rows) && wl.clear_since(bo, pi, rows) && rl.clear_since(t, pi, rows) {
                        rows.set(pi, tomb(CLASS_MERGE));
                        let (su, bu, cu, tu) = (s_ as u32, bo as u32, c as u32, t as u32);
                        rows.expand(i, [[8, cu, bu, NONE], [13, su, bu, tu], [8, cu, bu, NONE]]);
                        st.merge += 1;
                        *e = (u32::MAX, 0, 0, 0);
                        merged_with = Some(bo);
                        break;
                    }
                }
                if let Some(bo) = merged_with {
                    wl.push(t, i);
                    rl.push(a, i);
                    rl.push(b, i);
                    rl.push(bo, i);
                    continue;
                }
                {
                    let slots = &mut bytgt[t];
                    slots.rotate_right(1);
                    slots[0] = (i as u32, a as u32, b as u32, ctx);
                }
                pending.insert(key, Pend { idx: i as u32, ctx });
                wl.push(t, i);
                rl.push(a, i);
                rl.push(b, i);
            }
            _ => panic!("peephole: unexpected kind {k}"),
        }
    }
    assert!(stack.is_empty(), "peephole: unbalanced condition stack");
    st
}
