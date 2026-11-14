// Exact stream-level peephole over the decoded gate records.
//
// Rows use the packaged record layout of mod.rs: [kind, a, b, c] with
//   3/4/5 bit ops (a bit, b own condition), 6/7 X/Z (a qubit, b own condition),
//   8/9 CX/CZ (a control, b target, c own condition), 12 HMR (a qubit, b bit),
//   13 CCX (a control, b control, c target), 15 push condition (a bit), 16 pop,
//   1/2/18 register declarations, 17 = removed row (tombstone, a = rewrite class).
//
// Every rewrite is an identity of the circuit on every basis state (no use of the initial state,
// of input values or of any sampling), decided from the gate list alone:
//   pair:   two identical CCX under the same condition context such that every live op between them
//           commutes with that CCX: no X-type write or reset on either control, and no control read,
//           Z-type op or reset on the target. CCX*CCX = I, so both are removed.
//   merge:  CCX(s,b,t) followed by CCX(s,c,t) (b != c) under the same context, the first commuting
//           forward to the second as for a pair. CCX(s,b,t)CCX(s,c,t) = t ^= s&(b^c)
//           = CX(c,b) CCX(s,b,t) CX(c,b), placed at the second; the first is removed. The block reads
//           s, b, c and writes only t (b is restored), which is how later commutation checks treat it.
//   copy:   CCX(a,b,t) W1 CX(t,y) W2 CCX(a,b,t), W1 and W2 commuting with CCX(a,b,t), y not in {a,b,t}:
//           conjugating CX(t,y) by CCX(a,b,t) gives CX(t,y) CCX(a,b,y). The first CCX is removed and the
//           second becomes CCX(a,b,y), which also commutes back over W2 (no op in W2 reads, Z-types or
//           resets y; none writes a or b). One Toffoli saved.
//   ctrlw:  CCX(a,b,t) W1 G W2 CCX(a,b,t), W1 and W2 commuting with CCX(a,b,t), where G is the only op
//           between them that writes a control (a, say) and runs in the same context:
//             G = X(a):    t ^= ab ^ (1^a)b = b, so the pair becomes X(a) and CX(b,t) (two Toffoli saved);
//             G = CX(x,a), x not in {b,t}: t ^= ab ^ (a^x)b = xb, so the pair becomes CX(x,a) and
//                          CCX(x,b,t) (one saved); W2 must also leave x unwritten.
//           The first CCX is removed and the second replaced in place (it commutes back over W2).
//           With two or more writers that are all unconditioned X gates, the second CCX sees a^p, b^q
//           (p, q the flip parities) and the pair contributes ab ^ (a^p)(b^q): nothing, CX(b,t), CX(a,t)
//           or X(t) CX(a,t) CX(b,t) at the second position. Two Toffoli saved.
//   gadget: a dirty-borrow gadget T U T U with T = CCX(c1,c2,d), U = CCX(d,x,t), t not in {c1,c2,d}
//           computes t ^= c1&c2&x and leaves d unchanged for every value of d, and so does U T U T.
//           When two such gadgets share T and context and the ops between them commute with T, the
//           first is written U T U T and the second T U T U; the two adjacent T cancel (pair rule).
//           Symmetrically, when they share U, the first is written T U T U and the second U T U T so
//           the two U cancel.
// Condition contexts are compared exactly: a context is an interned id of (parent context, pushed bit,
// number of writes to that bit before the push). sim.rs fixes a condition at push time, so two ops with
// the same id run on exactly the same shots.
// Blockers are kept per qubit in short rings of op indices. A removed op no longer blocks, so nested
// compute/uncompute ladders collapse from the inside out within one pass. If a ring has overflowed past
// the earlier op of a candidate the candidate is rejected.

pub const TOMB: u16 = 17;
/// Row kind reported by `Rows::get` for a row replaced by a three-op block via `Rows::expand`.
pub const BLOCK: u16 = 20;
pub const CLASS_PAIR: u16 = 1;
pub const CLASS_MERGE: u16 = 2;
pub const CLASS_GADGET_T: u16 = 3;
pub const CLASS_GADGET_U: u16 = 4;
pub const CLASS_COPY: u16 = 5;
pub const CLASS_CTRLW: u16 = 6;
const NONE: u16 = u16::MAX;
const BS: usize = 65536;
const NQ: usize = 1024;
const RING: usize = 64;

pub trait Rows {
    fn len(&self) -> usize;
    fn get(&self, i: usize) -> [u16; 4];
    fn set(&mut self, i: usize, r: [u16; 4]);
    /// Replace row i by the three rows of `block` (in order). Afterwards get(i)[0] == BLOCK.
    fn expand(&mut self, i: usize, block: [[u16; 4]; 3]);
    /// The block stored at row i by `expand`.
    fn block(&self, i: usize) -> [[u16; 4]; 3];
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
    pub chain_cand: u64,
    pub gadget_seen: u64,
    pub unpaired_none: u64,
    pub unpaired_changed: u64,
    pub unpaired_overlap: u64,
    pub unpaired_blocked: u64,
    /// diagnostics: failed identical pairs by live blocker counts [wa+wb capped 3][rt capped 3]
    pub fail_hist: [[u64; 4]; 4],
    /// diagnostics: single blocker kind (row kind, own condition present) for w=0,rt=1 and w=1,rt=0
    pub single_rt: [[u64; 2]; 24],
    pub single_w: [[u64; 2]; 24],
    /// diagnostics: (2 control writers, 0 target readers) cell, writer kind pairs: [k1][k2] for kinds X=0, CX=1, other=2
    pub double_w: [[u64; 3]; 3],
    /// diagnostics: (earlier gadget last row, current gadget first row) for a few blocked cases
    pub blocked_sample: [(u32, u32); 6],
}
impl Stats {
    pub fn removed_ccx(&self) -> u64 {
        self.pair + self.merge + self.gadget_t + self.gadget_u + self.copy + self.ctrl_cx + 2 * self.ctrl_x + 2 * self.ctrl_xx
    }
}

#[inline]
fn tomb(class: u16) -> [u16; 4] {
    [TOMB, class, NONE, NONE]
}

/// Per-qubit ring of blocker op indices.
struct Ring {
    idx: Vec<u32>, // NQ * RING
    cnt: Vec<u64>, // pushes per qubit
}
impl Ring {
    fn new() -> Self {
        Ring { idx: vec![0; NQ * RING], cnt: vec![0; NQ] }
    }
    #[inline]
    fn push(&mut self, q: usize, i: usize) {
        let c = self.cnt[q];
        self.idx[q * RING + (c as usize % RING)] = i as u32;
        self.cnt[q] = c + 1;
    }
    /// The live blockers on q with index > p, if there are at most two and the ring covers them.
    fn live_since<R: Rows>(&self, q: usize, p: usize, rows: &R) -> Option<([usize; 2], usize)> {
        let c = self.cnt[q] as usize;
        let m = c.min(RING);
        let mut out = [0usize; 2];
        let mut k = 0usize;
        for j in 0..m {
            let e = self.idx[q * RING + ((c - 1 - j) % RING)] as usize;
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
        if c <= RING { Some((out, k)) } else { None }
    }
    /// True if no live blocker on q has index > p.
    fn clear_since<R: Rows>(&self, q: usize, p: usize, rows: &R) -> bool {
        let c = self.cnt[q] as usize;
        let m = c.min(RING);
        for j in 0..m {
            let e = self.idx[q * RING + ((c - 1 - j) % RING)] as usize;
            if e <= p {
                return true;
            }
            if rows.get(e)[0] != TOMB {
                return false;
            }
        }
        c <= RING
    }
}

#[inline]
fn same_ccx(r: [u16; 4], x: usize, y: usize, t: usize) -> bool {
    r[0] == 13 && r[3] as usize == t && ((r[1] as usize == x && r[2] as usize == y) || (r[1] as usize == y && r[2] as usize == x))
}

#[derive(Clone, Copy)]
struct Gad {
    pos: [usize; 4],
    t: [u16; 4],
    u: [u16; 4],
    tfirst: bool,
}
impl Gad {
    fn layout(&self, tfirst: bool) -> [[u16; 4]; 4] {
        let (t, u) = (self.t, self.u);
        if tfirst { [t, u, t, u] } else { [u, t, u, t] }
    }
    fn intact<R: Rows>(&self, rows: &R) -> bool {
        let native = self.layout(self.tfirst);
        (0..4).all(|k| rows.get(self.pos[k]) == native[k])
    }
}

/// A dirty gadget T U T U or U T U T in the next four live rows from i (all CCX, so all in one context).
/// Both copies of T (and of U) must be the identical row, so the layouts reproduce them exactly.
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
    // T first: rr[0] = T (target d), rr[1] = U controlled by d; else U first.
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

/// One forward pass. Returns the rewrites applied in this pass.
pub fn pass<R: Rows>(rows: &mut R) -> Stats {
    let n = rows.len();
    assert!(n < u32::MAX as usize);
    let mut st = Stats::default();
    let mut wl = Ring::new(); // X-type writes and resets, per qubit (block a pending CCX controlled by it)
    let mut rl = Ring::new(); // control reads, Z-type ops and resets, per qubit (block a pending CCX targeting it)
    let mut bep = vec![0u32; BS]; // writes per classical bit
    let mut ctx: u32 = 0;
    let mut last_ctx_change = 0usize; // index of the latest push or pop
    let mut stack: Vec<u32> = vec![];
    let mut intern: std::collections::HashMap<(u32, u16, u32), u32> = std::collections::HashMap::new();
    let mut pending: std::collections::HashMap<u32, Pend> = std::collections::HashMap::with_capacity(1 << 16);
    // last few CCX per target, for same-target shared-control merges
    let mut bytgt: Vec<[(u32, u16, u16, u32); 4]> = vec![[(u32::MAX, 0, 0, 0); 4]; NQ];
    // last unpaired dirty gadget per (T or U controls, target, context)
    let mut gad_t: std::collections::HashMap<u64, Gad> = std::collections::HashMap::new();
    let mut gad_u: std::collections::HashMap<u64, Gad> = std::collections::HashMap::new();
    // statistics: last merge block per target (index, s, b, c)
    let mut lastblk: Vec<(u32, u16, u16, u16)> = vec![(u32::MAX, 0, 0, 0); NQ];
    let gkey = |r: [u16; 4], ctx: u32| -> u64 {
        let (x, y) = (r[1].min(r[2]) as u64, r[1].max(r[2]) as u64);
        (x << 52) | (y << 42) | ((r[3] as u64) << 32) | ctx as u64
    };
    for i in 0..n {
        let r = rows.get(i);
        let k = r[0];
        match k {
            TOMB | 1 | 2 | 18 => {}
            BLOCK => {
                // A block from an earlier pass, recorded op by op (conservative: as if unblocked).
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
                let c = *intern.entry((ctx, b as u16, bep[b])).or_insert(nid);
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
            12 => {
                let (q, b) = (r[1] as usize, r[2] as usize);
                bep[b] += 1;
                wl.push(q, i);
                rl.push(q, i);
            }
            13 => {
                let (a, b, t) = (r[1] as usize, r[2] as usize, r[3] as usize);
                assert!(a < NQ && b < NQ && t < NQ, "peephole: qubit index outside key packing");
                let key = key3(a, b, t);
                // pair
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
                // ctrlw: the only live op between the two CCX that writes a control is one X or CX on it
                if let Some(p) = pending.get(&key).copied() {
                    let pi = p.idx as usize;
                    if p.ctx == ctx && last_ctx_change < pi && same_ccx(rows.get(pi), a, b, t) && rl.clear_since(t, pi, rows) {
                        let la = wl.live_since(a, pi, rows);
                        let lb = wl.live_since(b, pi, rows);
                        // every live writer of a and b is an unconditioned X: t gets ab ^ (a^p)(b^q) with the
                        // flip parities p, q, i.e. nothing, CX(b,t), CX(a,t), or X(t) CX(a,t) CX(b,t)
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
                                let (a16, b16, t16) = (a as u16, b as u16, t as u16);
                                match (pa, pb) {
                                    (false, false) => rows.set(i, tomb(CLASS_CTRLW)),
                                    (true, false) => { rows.set(i, [8, b16, t16, NONE]); wl.push(t, i); rl.push(b, i); }
                                    (false, true) => { rows.set(i, [8, a16, t16, NONE]); wl.push(t, i); rl.push(a, i); }
                                    (true, true) => {
                                        rows.expand(i, [[6, t16, NONE, NONE], [8, a16, t16, NONE], [8, b16, t16, NONE]]);
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
                                rows.set(i, [8, o as u16, t as u16, NONE]);
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
                                    rows.set(i, [13, x as u16, o as u16, t as u16]);
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
                // diagnostics for identical pairs that no rule handled so far
                if let Some(p) = pending.get(&key).copied() {
                    let pi = p.idx as usize;
                    if p.ctx == ctx && same_ccx(rows.get(pi), a, b, t) {
                        let cnt = |o: Option<([usize; 2], usize)>| o.map_or(3, |x| x.1);
                        let w = (cnt(wl.live_since(a, pi, rows)) + cnt(wl.live_since(b, pi, rows))).min(3);
                        let rt = cnt(rl.live_since(t, pi, rows)).min(3);
                        st.fail_hist[w][rt] += 1;
                        let kind_of = |o: Option<([usize; 2], usize)>| -> Option<(usize, usize)> {
                            let (x, c) = o?;
                            if c != 1 { return None; }
                            let r = rows.get(x[0]);
                            let cond = match r[0] { 3..=7 => r[2] != NONE, 8 | 9 => r[3] != NONE, _ => false } as usize;
                            Some(((r[0] as usize).min(23), cond))
                        };
                        if w == 0 && rt == 1 {
                            if let Some((k2, c2)) = kind_of(rl.live_since(t, pi, rows)) { st.single_rt[k2][c2] += 1; }
                        }
                        if w == 2 && rt == 0 {
                            let mut ks: Vec<usize> = vec![];
                            for q in [a, b] {
                                if let Some((x, c)) = wl.live_since(q, pi, rows) {
                                    for z in 0..c {
                                        let r = rows.get(x[z]);
                                        ks.push(match (r[0], r[0] == 6 && r[2] == NONE || r[0] == 8 && r[3] == NONE) { (6, true) => 0, (8, true) => 1, _ => 2 });
                                    }
                                }
                            }
                            if ks.len() == 2 { st.double_w[ks[0].min(ks[1])][ks[0].max(ks[1])] += 1; }
                        }
                        if w == 1 && rt == 0 {
                            let o = if wl.live_since(a, pi, rows).map_or(false, |x| x.1 == 1) { wl.live_since(a, pi, rows) } else { wl.live_since(b, pi, rows) };
                            if let Some((k2, c2)) = kind_of(o) { st.single_w[k2][c2] += 1; }
                        }
                    }
                }
                // copy: the only live op between the two CCX that reads t is one CX(t,y)
                let mut t = t;
                let mut key = key;
                if let Some(p) = pending.get(&key).copied() {
                    let pi = p.idx as usize;
                    // the CX must run under the same condition as the CCX: no push or pop in the window
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
                                rows.set(i, [13, a as u16, b as u16, y as u16]);
                                st.copy += 1;
                                t = y;
                                key = key3(a, b, t);
                            }
                        }
                    }
                }
                // gadget alternation
                if let Some(g) = detect_gadget(rows, i) {
                    st.gadget_seen += 1;
                    let (tr, ur) = (g.t, g.u);
                    let (c1, c2, d) = (tr[1] as usize, tr[2] as usize, tr[3] as usize);
                    let (e1, e2, tu) = (ur[1] as usize, ur[2] as usize, ur[3] as usize);
                    let (tk, uk) = (gkey(tr, ctx), gkey(ur, ctx));
                    let mut paired = false;
                    let mut why = 0u8; // 0 no stored partner, 1 changed, 2 overlap, 3 blocked
                    if let Some(p) = gad_t.get(&tk).copied() {
                        let pl = p.pos[3];
                        if pl >= i {
                            why = 2;
                        } else if !p.intact(rows) {
                            why = 1;
                        } else if wl.clear_since(c1, pl, rows) && wl.clear_since(c2, pl, rows) && rl.clear_since(d, pl, rows) {
                            // first gadget U T U T, its trailing T meets the second's leading T
                            let a2 = p.layout(false);
                            for q in 0..4 {
                                rows.set(p.pos[q], a2[q]);
                            }
                            rows.set(pl, tomb(CLASS_GADGET_T));
                            let b2 = g.layout(true);
                            for q in 0..4 {
                                rows.set(g.pos[q], b2[q]);
                            }
                            rows.set(g.pos[0], tomb(CLASS_GADGET_T));
                            gad_t.remove(&tk);
                            st.gadget_t += 2;
                            paired = true;
                        } else {
                            why = 3;
                            let k = (st.unpaired_blocked as usize) / 150_000;
                            if k < 6 && st.blocked_sample[k].1 == 0 { st.blocked_sample[k] = (pl as u32, i as u32); }
                        }
                    }
                    if !paired {
                        if let Some(p) = gad_u.get(&uk).copied() {
                            let pl = p.pos[3];
                            if pl < i
                                && p.intact(rows)
                                && wl.clear_since(e1, pl, rows)
                                && wl.clear_since(e2, pl, rows)
                                && rl.clear_since(tu, pl, rows)
                            {
                                // first gadget T U T U, its trailing U meets the second's leading U
                                let a2 = p.layout(true);
                                for q in 0..4 {
                                    rows.set(p.pos[q], a2[q]);
                                }
                                rows.set(pl, tomb(CLASS_GADGET_U));
                                let b2 = g.layout(false);
                                for q in 0..4 {
                                    rows.set(g.pos[q], b2[q]);
                                }
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
                    match why {
                        0 => st.unpaired_none += 1,
                        1 => st.unpaired_changed += 1,
                        2 => st.unpaired_overlap += 1,
                        _ => st.unpaired_blocked += 1,
                    }
                    gad_t.insert(tk, g);
                    gad_u.insert(uk, g);
                }
                // statistics: would extend an earlier merge block on the same target sharing s
                {
                    let (bi, bs, bb, bc) = lastblk[t];
                    if bi != u32::MAX && rows.get(bi as usize)[0] == BLOCK {
                        let (bs, bb, bc) = (bs as usize, bb as usize, bc as usize);
                        if (a == bs || b == bs) && wl.clear_since(bs, bi as usize, rows) && wl.clear_since(bb, bi as usize, rows)
                            && wl.clear_since(bc, bi as usize, rows) && rl.clear_since(t, bi as usize, rows) {
                            st.chain_cand += 1;
                        }
                    }
                }
                // merge: a live, commuting earlier CCX on the same target sharing exactly one control
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
                        let (s16, b16, c16, t16) = (s_ as u16, bo as u16, c as u16, t as u16);
                        rows.expand(i, [[8, c16, b16, NONE], [13, s16, b16, t16], [8, c16, b16, NONE]]);
                        st.merge += 1;
                        *e = (u32::MAX, 0, 0, 0);
                        merged_with = Some(bo);
                        lastblk[t] = (i as u32, s16, b16, c16);
                        break;
                    }
                }
                if let Some(bo) = merged_with {
                    // the block reads a, b (= s and c) and bo, and writes t
                    wl.push(t, i);
                    rl.push(a, i);
                    rl.push(b, i);
                    rl.push(bo, i);
                    continue;
                }
                {
                    let slots = &mut bytgt[t];
                    slots.rotate_right(1);
                    slots[0] = (i as u32, a as u16, b as u16, ctx);
                }
                pending.insert(key, Pend { idx: i as u32, ctx });
                wl.push(t, i);
                rl.push(a, i);
                rl.push(b, i);
            }
            10 => {
                // AKP: SWAP(a, b) (any condition): writes and reads both wires; blocks every pending pair on either.
                let (a, b) = (r[1] as usize, r[2] as usize);
                wl.push(a, i); wl.push(b, i); rl.push(a, i); rl.push(b, i);
            }
            _ => panic!("peephole: unexpected kind {k}"),
        }
    }
    assert!(stack.is_empty(), "peephole: unbalanced condition stack");
    st
}

/// Repeat passes until nothing changes (bounded).
pub fn run<R: Rows>(rows: &mut R, max_passes: usize) -> Vec<Stats> {
    let mut all = vec![];
    for _ in 0..max_passes {
        let s = pass(rows);
        let done = s.removed_ccx() == 0;
        all.push(s);
        if done {
            break;
        }
    }
    all
}
