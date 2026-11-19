//! D791: determinant word (drop in the X basis, regenerate from the determinant relation A*tB + B*tA = p).
//!
//! Design: swarm astra lanes L4 (determinant_check.py) and L9 (check.py, placement.csv); this is the native port of the
//! "wire_plan" kernel with digit-serial clipped operands. Everything here is X / CX / CCX, so the whole decoder is a
//! recording that is played forward, read out, and played in reverse.
//!
//! Frame (greedyfrog_model.rs): ring value bit k at lane W-L+k; cofactor bit i at lane CW-1-L-i, so lane 0 is the cofactor
//! frame's top. With r = h + k + 5 prefix digits (h leading B digits incl. the normalised one, k missing digits, g = 5 guard):
//!   x = top r lanes of X (A prefix), t = top r lanes of Y (B prefix, hole = k digits at lanes W-h-k .. W-h)
//!   y = lanes 0..r of X read MSB first, clipped to the cofactor frame (lanes < W-LA)
//!   v = lanes 0..r of Y read MSB first, clipped to the frame (lanes < W-LB)
//! and the missing word J = [x*y + v*(t_known + (j-1/2) 2^g) < K] summed over j (k = 1: one test).
use super::arith::and_mixed_on;
use super::builder::{B, G};
use crate::circuit::QubitId;

#[derive(Clone, Copy, Debug)]
pub struct Dw {
    pub h: usize,
    pub k: usize,
    /// L9's shallow post-I9 kernel (h = 1, k = 1): r = 5, accumulator 9 bits with 3 dirty, threshold 488 (shallow_cert.py)
    pub shallow: bool,
    /// L9's 4-clean variant (h = 1, k = 1): r = 6, accumulator 11 bits with 7 dirty, K = 2^11 (684 CCX instead of 452, two clean wires fewer)
    pub narrow: bool,
}
impl Dw {
    pub fn new(h: usize, k: usize) -> Dw { Dw { h, k, shallow: false, narrow: false } }
    pub fn shallow() -> Dw { Dw { h: 1, k: 1, shallow: true, narrow: false } }
    pub fn narrow() -> Dw { Dw { h: 1, k: 1, shallow: false, narrow: true } }
    /// the small post-I9 kernels (certified for the F5 / stall frames only)
    pub fn small(&self) -> bool { self.shallow || self.narrow }
    pub fn r(&self) -> usize { if self.shallow { 5 } else if self.narrow { 6 } else { self.h + self.k + 5 } }
    pub fn g(&self) -> usize { self.r() - self.h - self.k }
    pub fn width(&self) -> usize { if self.shallow { 9 } else if self.narrow { 11 } else { 2 * self.r() - self.h + 1 } }
    pub fn dirty(&self) -> usize { if self.shallow { 3 } else if self.narrow { 7 } else { 2 * self.r() - self.h - self.k - 3 } }
    /// the threshold constant K (the accumulator starts at -K)
    pub fn kconst(&self) -> usize { if self.shallow { 488 } else { 1usize << (2 * self.r() - 1) } }
    pub fn clean(&self) -> usize { self.width() - self.dirty() }
    /// dirty wires the kernel needs: accumulator low part + padding + scratch for the length predicates
    pub fn dirty_need(&self) -> usize { self.dirty() + self.width() + SCR }
}
/// scratch lanes for the multi-controlled flag ANDs (n literals need n-2)
pub const SCR: usize = 10;

pub struct Ctx<'a> {
    /// ring width W
    pub w: usize,
    pub dw: Dw,
    pub x: &'a [QubitId],
    pub y: &'a [QubitId],
    /// plain length registers, LSB first (9 bits in the tree)
    pub la: &'a [QubitId],
    pub lb: &'a [QubitId],
    /// inclusive windows of LA and LB at the decode instant (parent envelope)
    pub la_win: (usize, usize),
    pub lb_win: (usize, usize),
    /// the k output wires (J bit m = dst[m]); XORed into
    pub dst: &'a [QubitId],
    /// dw.clean() zero wires for the accumulator top, then one zero wire for the digit flag
    pub clean: &'a [QubitId],
    /// borrowed wires in any state (restored): dw.dirty_need() of them, disjoint from everything else
    pub dirty: &'a [QubitId],
    /// k >= 2 only: a wire that is 1 on every shot (Y top)
    pub one: Option<QubitId>,
    /// negative controls for the gate tests only
    pub brk: u32,
    /// the top lane of Y is the known leading 1 of B (LB >= 1 on the window): use the t-controlled form when no v digit is clipped
    pub top_one: bool,
}

enum Dig {
    Skip,
    Direct(QubitId),
    Cubes(QubitId, Vec<Vec<(QubitId, bool)>>),
}

fn bit_len(v: usize) -> usize { (usize::BITS - v.leading_zeros()) as usize }

/// disjoint prefix cubes over the low `size` bits of the length register that cover exactly the window values where `yes`
fn prefix_cover(lo: usize, hi: usize, yes: &dyn Fn(usize) -> bool) -> Vec<(usize, usize)> {
    let size = bit_len(hi - lo);
    let answers: Vec<(usize, bool)> = (lo..=hi).map(|i| (i & ((1usize << size) - 1), yes(i))).collect();
    fn descend(answers: &[(usize, bool)], size: usize, v: usize, n: usize) -> Vec<(usize, usize)> {
        let vals: Vec<bool> = answers.iter().filter(|(i, _)| (i >> (size - n)) == v).map(|&(_, b)| b).collect();
        if !vals.iter().any(|&b| b) { return vec![]; }
        if vals.iter().all(|&b| b) { return vec![(v, n)]; }
        let mut r = descend(answers, size, 2 * v, n + 1);
        r.extend(descend(answers, size, 2 * v + 1, n + 1));
        r
    }
    descend(&answers, size, 0, 0)
}

fn clip_dig(raw: QubitId, lane: usize, w: usize, len: &[QubitId], win: (usize, usize)) -> Dig {
    // digit valid iff lane < W - Len  <=>  Len <= W - 1 - lane
    let lim = w as i64 - 1 - lane as i64;
    if lim >= win.1 as i64 { return Dig::Direct(raw); }
    if lim < win.0 as i64 { return Dig::Skip; }
    let size = bit_len(win.1 - win.0);
    let cov = prefix_cover(win.0, win.1, &|l| (l as i64) <= lim);
    let cubes = cov.into_iter().map(|(v, n)| (0..n).map(|t| (len[size - 1 - t], (v >> (n - 1 - t)) & 1 == 1)).collect()).collect();
    Dig::Cubes(raw, cubes)
}

/// the ancilla-free ripple adder of L4 (determinant_check.py `adder`): t += s (or only when ctrl), s restored
fn adder(t: &[QubitId], s: &[QubitId], ctrl: Option<QubitId>) -> Vec<G> {
    let n = t.len();
    let mut o: Vec<G> = vec![];
    if n == 0 { return o; }
    for i in 1..n { o.push(G::Cx(s[i], t[i])); }
    for i in (1..n.saturating_sub(1)).rev() { o.push(G::Cx(s[i], s[i + 1])); }
    for i in 0..n - 1 { o.push(G::Ccx(s[i], t[i], s[i + 1])); }
    let wr = |o: &mut Vec<G>, a: QubitId, b: QubitId| match ctrl { None => o.push(G::Cx(a, b)), Some(c) => o.push(G::Ccx(c, a, b)) };
    for i in (1..n).rev() {
        wr(&mut o, s[i], t[i]);
        o.push(G::Ccx(s[i - 1], t[i - 1], s[i]));
    }
    for i in 1..n.saturating_sub(1) { o.push(G::Cx(s[i], s[i + 1])); }
    wr(&mut o, s[0], t[0]);
    for i in 1..n { o.push(G::Cx(s[i], t[i])); }
    o
}
fn rev(o: &[G]) -> Vec<G> { o.iter().rev().cloned().collect() }

/// acc[at..] += reg (zero-extended through the dirty padding, whose contribution is subtracted again), under ctrl
fn add_short(acc: &[QubitId], pad: &[QubitId], reg: &[QubitId], at: usize, ctrl: Option<QubitId>) -> Vec<G> {
    let t = &acc[at.min(acc.len())..];
    if t.is_empty() { return vec![]; }
    let s = &reg[..reg.len().min(t.len())];
    let ext = &pad[..t.len() - s.len()];
    let mut src = s.to_vec();
    src.extend_from_slice(ext);
    let mut o = adder(t, &src, ctrl);
    if !ext.is_empty() { o.extend(rev(&adder(&t[s.len()..], ext, ctrl))); }
    o
}

/// frames where A or B can be shorter than the r prefix lanes (or A = 0, B = 1): the clipped form with the LB = 1 seam
pub fn short_mode(dw: &Dw, la_win: (usize, usize), lb_win: (usize, usize)) -> bool { dw.small() && (la_win.0 < dw.r() || lb_win.0 < dw.r()) }

/// cubes (q, pos) over the low bits of `len` for `pred` over the window
fn pred_cubes(len: &[QubitId], win: (usize, usize), pred: &dyn Fn(usize) -> bool) -> Vec<Vec<(QubitId, bool)>> {
    let size = bit_len(win.1 - win.0);
    if size == 0 { return if pred(win.0) { vec![vec![]] } else { vec![] }; }
    prefix_cover(win.0, win.1, pred).into_iter().map(|(v, n)| (0..n).map(|t| (len[size - 1 - t], (v >> (n - 1 - t)) & 1 == 1)).collect()).collect()
}
fn pred_dig(raw: QubitId, len: &[QubitId], win: (usize, usize), pred: &dyn Fn(usize) -> bool) -> Dig {
    if (win.0..=win.1).all(|l| pred(l)) { Dig::Direct(raw) }
    else if !(win.0..=win.1).any(|l| pred(l)) { Dig::Skip }
    else { Dig::Cubes(raw, pred_cubes(len, win, pred)) }
}
/// out ^= OR of the cubes (disjoint); self-inverse
fn flag_apply(b: &mut B, cubes: &[Vec<(QubitId, bool)>], out: QubitId, scr: &[QubitId]) {
    for cube in cubes {
        if cube.is_empty() { b.x(out); continue; }
        let lits: Vec<(QubitId, bool)> = cube.iter().map(|&(q, pos)| (q, !pos)).collect();
        and_mixed_on(b, &lits, out, &[], scr);
    }
}
fn with_ctl_fn(b: &mut B, out: &mut Vec<G>, d: &Dig, flag: QubitId, scr: &[QubitId], body: &mut dyn FnMut(Option<QubitId>) -> Vec<G>) {
    match d {
        Dig::Skip => {}
        Dig::Direct(q) => out.extend(body(Some(*q))),
        Dig::Cubes(raw, cubes) => {
            let comp = rec(b, |b| {
                for cube in cubes {
                    let mut lits: Vec<(QubitId, bool)> = vec![(*raw, false)];
                    lits.extend(cube.iter().map(|&(q, pos)| (q, !pos)));
                    and_mixed_on(b, &lits, flag, &[], scr);
                }
            });
            out.extend(comp.iter().cloned());
            out.extend(body(Some(flag)));
            out.extend(comp.iter().cloned());
        }
    }
}
/// binary selection tree of Fredkins: after it leaves[0] holds leaves[index]; the reverse order restores
fn tree_ops(sel: &[QubitId], leaves: &[QubitId]) -> Vec<(QubitId, QubitId, QubitId)> {
    let n = leaves.len();
    let mut o = vec![];
    for (s, &sq) in sel.iter().enumerate() {
        let stride = 1usize << s;
        let mut base = 0;
        while base + stride < n { o.push((sq, leaves[base], leaves[base + stride])); base += 2 * stride; }
    }
    o
}
fn tree_play(b: &mut B, ops: &[(QubitId, QubitId, QubitId)], inverse: bool) {
    if inverse { for &(c, x, y) in ops.iter().rev() { b.cswap(c, x, y); } } else { for &(c, x, y) in ops { b.cswap(c, x, y); } }
}

/// the shallow decoder on frames where A or B may be shorter than r (down to A = 0 / B = 1): the short operand's digits are the
/// controls (clipped by its length window), the long cofactor prefix is the added register; the oracle is gated by [LB >= 2] and
/// the LB = 1 word (a cofactor bit: tA0 = 1 ^ A0 C0) is selected by Fredkin trees over the lane of A0 / C0
fn decode_short(b: &mut B, c: &Ctx) {
    let dw = c.dw;
    let (r, g, k, w) = (dw.r(), dw.g(), dw.k, c.w);
    assert!(k == 1 && c.dst.len() == 1 && c.clean.len() > dw.clean() && c.dirty.len() >= dw.dirty_need());
    assert!(c.la_win.1 + r <= w && c.lb_win.1 + r <= w && c.lb_win.0 >= 1, "short decode window");
    let acc: Vec<QubitId> = c.dirty[..dw.dirty()].iter().chain(c.clean[..dw.clean()].iter()).cloned().collect();
    let pad: &[QubitId] = &c.dirty[dw.dirty()..dw.dirty() + dw.width()];
    let scr: &[QubitId] = &c.dirty[dw.dirty() + dw.width()..dw.dirty() + dw.width() + SCR];
    let flag = c.clean[dw.clean()];
    let dst = c.dst[0];
    let mut setup: Vec<G> = vec![];
    let negk = (1usize << dw.width()).wrapping_sub(dw.kconst()) & ((1usize << dw.width()) - 1);
    for i in dw.dirty()..dw.width() { if (negk >> i) & 1 == 1 { setup.push(G::X(acc[i])); } }
    // x * y: the digits of x (the top lanes of X, clipped by LA) control adds of the cofactor prefix y (the low lanes of X)
    let yreg: Vec<QubitId> = (0..r).map(|i| c.x[r - 1 - i]).collect();
    for j in 0..r {
        let d = if c.brk == 5 { Dig::Direct(c.x[w - r + j]) } else { pred_dig(c.x[w - r + j], c.la, c.la_win, &|la| la + j >= r) };
        with_ctl_fn(b, &mut setup, &d, flag, scr, &mut |ctl| add_short(&acc, pad, &yreg, j, ctl));
    }
    // v * t: the known digits of t (clipped by LB) control adds of v; the leading one and the half unit are plain adds
    let vs: Vec<QubitId> = (0..r).map(|i| c.y[r - 1 - i]).collect();
    for i in (0..r - 1).filter(|&i| i < g || i >= g + k) {
        let d = pred_dig(c.y[w - r + i], c.lb, c.lb_win, &|lb| lb + i >= r);
        with_ctl_fn(b, &mut setup, &d, flag, scr, &mut |ctl| add_short(&acc, pad, &vs, i, ctl));
    }
    setup.extend(add_short(&acc, pad, &vs, r - 1, None));
    setup.extend(add_short(&acc, pad, &vs, g - 1, None));
    b.play(&setup, false);
    let top = acc[acc.len() - 1];
    if c.lb_win.0 < 2 && c.brk != 7 {
        let f2 = pred_cubes(c.lb, c.lb_win, &|lb| lb >= 2);
        flag_apply(b, &f2, flag, scr);
        b.ccx(top, flag, dst);
        flag_apply(b, &f2, flag, scr);
    } else {
        b.cx(top, dst);
    }
    b.play(&setup, true);
    if c.lb_win.0 <= 1 && c.brk != 6 {
        // B = 1: the word is tA0 = 1 ^ A0 C0 (p = A tB + tA, p odd), A0 = X[W - LA], C0 = X[W - 1 - LA] (A0 = 0 when A = 0)
        let f1 = pred_cubes(c.lb, c.lb_win, &|lb| lb == 1);
        flag_apply(b, &f1, flag, scr);
        b.cx(flag, dst);
        let (t1, t2, zl) = (c.clean[0], c.clean[1], c.clean[2]);
        let (lo, hi) = c.la_win;
        let size = bit_len(hi - lo);
        let n = 1usize << size;
        let sel: Vec<QubitId> = c.la[..size].to_vec();
        let mut dummy = c.dirty.iter().cloned();
        let mut la_leaves: Vec<QubitId> = vec![];
        let mut lc_leaves: Vec<QubitId> = vec![];
        for rho in 0..n {
            match (lo..=hi).find(|a| a & (n - 1) == rho) {
                Some(a) => { la_leaves.push(if a == 0 { zl } else { c.x[w - a] }); lc_leaves.push(c.x[w - 1 - a]); }
                None => { la_leaves.push(dummy.next().unwrap()); lc_leaves.push(dummy.next().unwrap()); }
            }
        }
        let ta = tree_ops(&sel, &la_leaves);
        let tc = tree_ops(&sel, &lc_leaves);
        tree_play(b, &ta, false);
        b.cx(la_leaves[0], t1);
        tree_play(b, &ta, true);
        tree_play(b, &tc, false);
        b.ccx(t1, lc_leaves[0], t2);
        b.ccx(flag, t2, dst);
        b.ccx(t1, lc_leaves[0], t2);
        tree_play(b, &tc, true);
        tree_play(b, &ta, false);
        b.cx(la_leaves[0], t1);
        tree_play(b, &ta, true);
        flag_apply(b, &f1, flag, scr);
    }
}

/// does the decoder need its digit-flag wire (some digit is clipped by a length window)?
pub fn needs_flag(dw: &Dw, w: usize, la_win: (usize, usize), lb_win: (usize, usize)) -> bool {
    let r = dw.r();
    if short_mode(dw, la_win, lb_win) { return true; }
    (0..r).any(|i| {
        let lane = r - 1 - i;
        let lim = w as i64 - 1 - lane as i64;
        (lim < la_win.1 as i64 && lim >= la_win.0 as i64) || (lim < lb_win.1 as i64 && lim >= lb_win.0 as i64)
    })
}

/// record what `f` emits
fn rec(b: &mut B, f: impl FnOnce(&mut B)) -> Vec<G> {
    b.begin();
    f(b);
    b.end()
}

/// dst ^= J (the missing word). Every borrowed wire is restored, the clean wires return to zero, ring/length wires are only read.
pub fn decode_xor(b: &mut B, c: &Ctx) {
    let dw = c.dw;
    if dw.small() && c.brk != 8 && short_mode(&dw, c.la_win, c.lb_win) { return decode_short(b, c); }
    let (r, g, k, w) = (dw.r(), dw.g(), dw.k, c.w);
    assert!(c.dst.len() == k && c.clean.len() >= dw.clean() && c.dirty.len() >= dw.dirty_need());
    let acc: Vec<QubitId> = c.dirty[..dw.dirty()].iter().chain(c.clean[..dw.clean()].iter()).cloned().collect();
    assert_eq!(acc.len(), dw.width());
    let pad: &[QubitId] = &c.dirty[dw.dirty()..dw.dirty() + dw.width()];
    let scr: &[QubitId] = &c.dirty[dw.dirty() + dw.width()..dw.dirty() + dw.width() + SCR];
    let flag = c.clean.get(dw.clean()).copied().unwrap_or(c.clean[0]);
    // operands: x source (LSB first), t segments of (t + 2^(g-1)), per-digit controls
    let xs: Vec<QubitId> = (0..r).map(|j| c.x[w - r + j]).collect();
    let tl = |i: usize| c.y[w - r + i];
    // t'' = known + 2^(g-1): bits 0..g-1 with bit g-1 inverted (segment A), bit g = old bit g-1 (segment B), bits g+k.. (segment C)
    let seg_a: Vec<QubitId> = (0..g).map(tl).collect();
    let seg_b: Vec<QubitId> = vec![tl(g - 1)];
    let seg_c: Vec<QubitId> = (g + k..r).map(tl).collect();
    let ydig: Vec<Dig> = (0..r).map(|i| clip_dig(c.x[r - 1 - i], r - 1 - i, w, c.la, c.la_win)).collect();
    let vdig: Vec<Dig> = (0..r).map(|i| clip_dig(c.y[r - 1 - i], r - 1 - i, w, c.lb, c.lb_win)).collect();
    let mut setup: Vec<G> = vec![];
    // offset: K = 2^(2r-1); -K mod 2^width has no bits below 2r-1, so on the clean top part only
    let negk = (1usize << dw.width()).wrapping_sub(dw.kconst()) & ((1usize << dw.width()) - 1);
    for i in dw.dirty()..dw.width() {
        if (negk >> i) & 1 == 1 { setup.push(G::X(acc[i])); }
    }
    assert!(negk & ((1usize << dw.dirty()) - 1) == 0 || dw.shallow || dw.narrow, "K has bits in the dirty part");
    // controlled-by-digit adds, digit flag computed into the clean flag wire and erased straight after
    let mut with_ctl = |b: &mut B, setup: &mut Vec<G>, d: &Dig, body: &mut dyn FnMut(Option<QubitId>) -> Vec<G>| {
        match d {
            Dig::Skip => {}
            Dig::Direct(q) => setup.extend(body(Some(*q))),
            Dig::Cubes(raw, cubes) => {
                let comp = rec(b, |b| {
                    for cube in cubes {
                        let mut lits: Vec<(QubitId, bool)> = vec![(*raw, false)];
                        lits.extend(cube.iter().map(|&(q, pos)| (q, !pos)));
                        and_mixed_on(b, &lits, flag, &[], scr);
                    }
                });
                setup.extend(comp.iter().cloned());
                setup.extend(body(Some(flag)));
                setup.extend(comp.iter().cloned());
            }
        }
    };
    for i in 0..r {
        with_ctl(b, &mut setup, &ydig[i], &mut |ctl| add_short(&acc, pad, &xs, i, ctl));
    }
    let v_direct = vdig.iter().all(|d| matches!(d, Dig::Direct(_))) && c.brk != 3;
    if v_direct && c.top_one {
        // L9's wire plan: the known t digits control adds of the v register; half unit and the leading one are plain adds
        let vs: Vec<QubitId> = (0..r).map(|i| c.y[r - 1 - i]).collect();
        for i in (0..r - 1).filter(|&i| (i < g || i >= g + k) && !(c.brk == 1 && i == g - 1)) {
            setup.extend(add_short(&acc, pad, &vs, i, Some(tl(i))));
        }
        setup.extend(add_short(&acc, pad, &vs, r - 1, None));
        if c.brk != 4 { setup.extend(add_short(&acc, pad, &vs, g - 1, None)); }
    } else {
    for i in 0..r {
        let (sa, sb, sc) = (&seg_a, &seg_b, &seg_c);
        let (acc_r, pad_r) = (&acc, pad);
        let brk = c.brk;
        with_ctl(b, &mut setup, &vdig[i], &mut |ctl| {
            let mut o = vec![G::X(sa[g - 1])];
            o.extend(add_short(acc_r, pad_r, sa, i, ctl));
            o.push(G::X(sa[g - 1]));
            if brk != 1 { o.extend(add_short(acc_r, pad_r, sb, i + g, ctl)); }
            o.extend(add_short(acc_r, pad_r, sc, i + g + k, ctl));
            o
        });
    }
    }
    // advance by v * 2^g between the thresholds: (j-1/2) -> (j+1/2)
    let mut advance: Vec<G> = vec![];
    if k >= 2 {
        let one = [c.one.expect("k >= 2 needs the known-one wire")];
        for i in 0..r {
            with_ctl(b, &mut advance, &vdig[i], &mut |ctl| add_short(&acc, pad, &one, i + g, ctl));
        }
    }
    b.play(&setup, false);
    let sign = |b: &mut B, j: usize| {
        for (m, &q) in c.dst.iter().enumerate() {
            if ((j ^ (j - 1)) >> m) & 1 == 1 { b.cx(acc[acc.len() - 1], q); }
        }
    };
    sign(b, 1);
    for j in 2..(1usize << k) {
        b.play(&advance, false);
        sign(b, j);
    }
    for _ in 2..(1usize << k) { b.play(&advance, true); }
    b.play(&setup, true);
}

/// D791 lending: cubes (over the low `size` bits of the plain length register, `size` = bit length of the window span) whose
/// OR is bit `j` of the length on every value of the window (j >= size); the window values outside the span are don't-cares.
/// Disjoint cubes: bit j ^= XOR of the cube ANDs. Empty cover: the bit is 0 on the whole window; [(empty cube)]: it is 1.
pub fn bit_cubes(len: &[QubitId], win: (usize, usize), j: usize) -> Option<Vec<Vec<(QubitId, bool)>>> {
    let size = bit_len(win.1 - win.0);
    if j < size { return None; }
    if size == 0 { return Some(if (win.0 >> j) & 1 == 1 { vec![vec![]] } else { vec![] }); }
    let cov = prefix_cover(win.0, win.1, &|i| (i >> j) & 1 == 1);
    Some(cov.into_iter().map(|(v, n)| (0..n).map(|t| (len[size - 1 - t], (v >> (n - 1 - t)) & 1 == 1)).collect()).collect())
}
/// CCX count of one application of `lend_toggle`
pub fn cubes_cost(cubes: &[Vec<(QubitId, bool)>]) -> usize {
    cubes.iter().map(|c| { let n = c.len(); if n < 2 { 0 } else if n == 2 { 1 } else { 4 * n - 8 } }).sum()
}
/// tgt ^= (OR of the cubes); self-inverse (a second call restores tgt)
pub fn lend_toggle(b: &mut B, tgt: QubitId, cubes: &[Vec<(QubitId, bool)>], scr: &[QubitId]) {
    for cube in cubes {
        if cube.is_empty() { b.x(tgt); continue; }
        let lits: Vec<(QubitId, bool)> = cube.iter().map(|&(q, pos)| (q, !pos)).collect();
        and_mixed_on(b, &lits, tgt, &[], scr);
    }
}

/// X-basis measurement of the word's wires; outcomes kept. Frees nothing (the caller frees the lanes in its allocator).
pub fn drop_word(b: &mut B, word: &[QubitId]) -> Vec<crate::circuit::BitId> {
    let bits = b.fresh_bits(word.len());
    for (q, &m) in word.iter().zip(bits.iter()) { b.hmr_to(*q, m); }
    bits
}

/// decode onto the (zero) word wires, then one outcome-controlled Z per digit
pub fn restore_word(b: &mut B, c: &Ctx, bits: &[crate::circuit::BitId]) {
    decode_xor(b, c);
    if c.brk != 2 { for (q, &m) in c.dst.iter().zip(bits.iter()) { b.z_if(*q, m); } }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};

    #[derive(Clone, Copy)]
    struct St { a: u64, b: u64, u: u64, v: u64, la: usize, lb: usize }

    fn bl(x: u64) -> usize { (64 - x.leading_zeros()) as usize }
    /// L4 walk(p, b, cap): states at F5 / stall
    fn walk(p: u64, b0: u64, cap: usize, out: &mut Vec<St>) {
        let (mut a, mut b, mut u, mut v, mut la, mut lb) = (p, b0, 0u64, 1u64, bl(p), bl(b0));
        while la > 0 {
            if bl(a) == la {
                let mut shift = la - lb;
                let d = ((b << shift) > a) as usize;
                shift -= d;
                a -= b << shift;
                la -= d;
                u += v << shift;
                out.push(St { a, b, u, v, la, lb });
            } else {
                out.push(St { a, b, u, v, la, lb });
            }
            la -= cap.min(la - bl(a));
            if la == bl(a) && 0 < a && a < b {
                std::mem::swap(&mut a, &mut b);
                std::mem::swap(&mut u, &mut v);
                std::mem::swap(&mut la, &mut lb);
            }
        }
        // the finished frame: A = 0, B = 1 (cofactor of B: p)
        out.push(St { a, b, u, v, la, lb });
    }
    /// ring lanes (index = lane) of the raw orientation: X = (A, tB), Y = (B, tA)
    fn pack(val: u64, len: usize, cof: u64, w: usize) -> Vec<u8> {
        let mut r = vec![0u8; w];
        for k in 0..len { r[w - len + k] = ((val >> k) & 1) as u8; }
        for i in 0..(w - len) { r[w - 1 - len - i] = ((cof >> i) & 1) as u8; }
        r
    }
    fn prefix(val: u64, span: usize, r: usize) -> u128 { ((val as u128) << r) >> span }

    struct Case { x: Vec<u8>, y: Vec<u8>, la: usize, lb: usize, word: u64 }

    fn each_case(p: u64, dw: Dw, mode: u8, f: &mut dyn FnMut(Case)) {
        let (h, k) = (dw.h, dw.k);
        let w = bl(p) + 1;
        let r = dw.r();
        for b0 in 1..=(p + 1) / 2 - 1 {
            for cap in [2usize, 7] {
                let mut sts = vec![];
                walk(p, b0, cap, &mut sts);
                for s in sts {
                    if mode < 2 && (s.la < r || s.lb < r) { continue; }
                    if mode == 2 && s.lb < 1 { continue; }
                    if mode >= 1 && (s.la > w - r || s.lb > w - r) { continue; }
                    // the quarter-bound promise of the pivot (small primes do not satisfy it on every frame)
                    let vv = prefix(s.u, w - s.lb, r);
                    if vv < 1u128 << (r - 2) { continue; }
                    let x = pack(s.a, s.la, s.v, w);
                    let mut y = pack(s.b, s.lb, s.u, w);
                    // the finished frame carries a counter in the low lanes of Y (not the cofactor digits): junk there
                    if s.la == 0 { for l in 0..r { y[l] ^= (((s.v >> l) & 1) as u8) ^ ((l & 1) as u8); } }
                    let mut word = 0u64;
                    for m in 0..k { word |= (y[w - h - k + m] as u64) << m; }
                    f(Case { x, y, la: s.la, lb: s.lb, word });
                }
            }
        }
    }

    struct Rig {
        b: B,
        x: Vec<QubitId>,
        y: Vec<QubitId>,
        la: Vec<QubitId>,
        lb: Vec<QubitId>,
        dst: Vec<QubitId>,
        clean: Vec<QubitId>,
        dirty: Vec<QubitId>,
    }
    fn rig(w: usize, dw: Dw) -> Rig {
        let mut b = B::new();
        let x = b.alloc_n(w);
        let y = b.alloc_n(w);
        let la = b.alloc_n(9);
        let lb = b.alloc_n(9);
        let dst: Vec<QubitId> = (0..dw.k).map(|m| y[w - dw.h - dw.k + m]).collect();
        let clean = b.alloc_n(dw.clean() + 1);
        let dirty = b.alloc_n(dw.dirty_need());
        Rig { b, x, y, la, lb, dst, clean, dirty }
    }

    /// run all cases (64 shots a batch); mode 0: value (decode onto the zero word wires), mode 1: drop + restore with phase
    fn run(p: u64, dw: Dw, brk: u32, mode: u32) -> (usize, usize, usize) { run2(p, dw, brk, mode, 0) }
    fn run2(p: u64, dw: Dw, brk: u32, mode: u32, direct: u8) -> (usize, usize, usize) {
        let (h, k) = (dw.h, dw.k);
        let w = bl(p) + 1;
        let (mut la_lo, mut la_hi, mut lb_lo, mut lb_hi, mut ncase) = (usize::MAX, 0, usize::MAX, 0, 0usize);
        each_case(p, dw, direct, &mut |c| { la_lo = la_lo.min(c.la); la_hi = la_hi.max(c.la); lb_lo = lb_lo.min(c.lb); lb_hi = lb_hi.max(c.lb); ncase += 1; });
        assert!(ncase > 0);
        let mut rg = rig(w, dw);
        let one = rg.y[w - 1];
        let ctx = Ctx { w, dw, x: &rg.x, y: &rg.y, la: &rg.la, lb: &rg.lb, la_win: (la_lo, la_hi), lb_win: (lb_lo, lb_hi), dst: &rg.dst, clean: &rg.clean,
                        dirty: &rg.dirty, one: Some(one), brk, top_one: true };
        let bits = if mode == 1 { drop_word(&mut rg.b, &rg.dst.clone()) } else { vec![] };
        if mode == 1 { restore_word(&mut rg.b, &ctx, &bits); } else { decode_xor(&mut rg.b, &ctx); }
        let nb = rg.b.fresh_bits(1)[0].0 as usize + 1;
        let (mut bad_val, mut bad_rest, mut bad_phase) = (0usize, 0usize, 0usize);
        let mut rs: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut nx = || { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; rs };
        let mut chunk: Vec<Case> = vec![];
        let mut proc = |chunk: &Vec<Case>, rg: &mut Rig| {
            let mut h2 = sha3::Shake256::default();
            h2.update(b"d791-detword");
            let mut xof = h2.finalize_xof();
            let mut sim = Simulator::new(rg.b.width() as usize, nb, &mut xof);
            for &q in &rg.dirty { sim.qubits[q.0 as usize] = nx(); }
            let d0: Vec<u64> = rg.dirty.iter().map(|q| sim.qubits[q.0 as usize]).collect();
            for (sh, c) in chunk.iter().enumerate() {
                for l in 0..w {
                    if c.x[l] == 1 { sim.qubits[rg.x[l].0 as usize] |= 1 << sh; }
                    if c.y[l] == 1 { sim.qubits[rg.y[l].0 as usize] |= 1 << sh; }
                }
                for i in 0..9 {
                    if c.la >> i & 1 == 1 { sim.qubits[rg.la[i].0 as usize] |= 1 << sh; }
                    if c.lb >> i & 1 == 1 { sim.qubits[rg.lb[i].0 as usize] |= 1 << sh; }
                }
                if mode == 1 {
                    for m in 0..k { if c.word >> m & 1 == 1 { sim.qubits[rg.dst[m].0 as usize] |= 1 << sh; } }
                } else {
                    for m in 0..k { sim.qubits[rg.dst[m].0 as usize] &= !(1 << sh); }
                    // dst starts as zero; the true word is expected on it
                }
            }
            let snap = sim.qubits.clone();
            sim.apply_iter(rg.b.ops.iter());
            let used = if chunk.len() == 64 { !0u64 } else { (1u64 << chunk.len()) - 1 };
            for (sh, c) in chunk.iter().enumerate() {
                let mut got = 0u64;
                for m in 0..k { got |= ((sim.qubits[rg.dst[m].0 as usize] >> sh) & 1) << m; }
                if got != c.word { bad_val += 1; }
            }
            // everything but the word wires and the (unused-here) rest must be unchanged
            for q in 0..snap.len() {
                if rg.dst.iter().any(|d| d.0 as usize == q) { continue; }
                if (sim.qubits[q] ^ snap[q]) & used != 0 { bad_rest += 1; }
            }
            for (i, &q) in rg.dirty.iter().enumerate() { if sim.qubits[q.0 as usize] != d0[i] { bad_rest += 1000; } }
            if mode == 1 { bad_phase += (sim.phase & used).count_ones() as usize; }
        };
        each_case(p, dw, direct, &mut |c| { chunk.push(c); if chunk.len() == 64 { proc(&chunk, &mut rg); chunk.clear(); } });
        if !chunk.is_empty() { proc(&chunk, &mut rg); }
        eprintln!("detword shallow {} h {h} k {k} p {p} brk {brk} mode {mode}:", dw.shallow); eprintln!("detword h {h} k {k} p {p} brk {brk} mode {mode}: {} cases, ccx {}, bad value {bad_val}, bad rest {bad_rest}, bad phase {bad_phase}", ncase, rg.b.tof);
        (bad_val, bad_rest, bad_phase)
    }

    fn full(p: u64, dw: Dw) {
        for &direct in &[0u8, 1u8] {
            let (v, r, ph) = run2(p, dw, 0, 0, direct);
            assert_eq!((v, r), (0, 0));
            let (v, r, ph2) = run2(p, dw, 0, 1, direct);
            assert_eq!((v, r, ph, ph2), (0, 0, 0, 0));
            let (v1, _, _) = run2(p, dw, 1, 0, direct);
            assert!(v1 > 0, "negative control brk=1 did not break the value (direct {direct})");
            let (_, _, ph3) = run2(p, dw, 2, 1, direct);
            assert!(ph3 > 0, "negative control brk=2 (no Z) did not break the phase (direct {direct})");
        }
        // direct frames: the t-controlled form against the digit-serial form, and the half-unit mutant
        let (v, r, _) = run2(p, dw, 3, 0, 1);
        assert_eq!((v, r), (0, 0));
        let (v4, _, _) = run2(p, dw, 4, 0, 1);
        assert!(v4 > 0, "negative control brk=4 (no half unit) did not break the value");
    }

    #[test]
    fn detword_kernel_exhaustive() {
        for &(p, h, k) in &[(131071u64, 1usize, 1usize), (524287, 3, 1)] { full(p, Dw::new(h, k)); }
    }

    #[test]
    fn detword_shallow_exhaustive() {
        for &p in &[131071u64, 524287] { full(p, Dw::shallow()); }
    }

    /// short frames: A and B down to A = 0 / B = 1 (mode 2), against the dropped word, with the wrong variants
    #[test]
    fn detword_narrow_exhaustive() {
        for &p in &[131071u64, 524287] { full(p, Dw::narrow()); }
    }

    #[test]
    fn detword_short_exhaustive() {
        for &p in &[131071u64, 524287] { for dw in [Dw::shallow(), Dw::narrow()] {
            let (v, r, ph) = run2(p, dw, 0, 0, 2);
            assert_eq!((v, r), (0, 0));
            let (v, r, ph2) = run2(p, dw, 0, 1, 2);
            assert_eq!((v, r, ph, ph2), (0, 0, 0, 0));
            for brk in [5u32, 6, 7] {
                let (v, _, _) = run2(p, dw, brk, 0, 2);
                assert!(v > 0, "short: negative control brk={brk} did not break the value");
            }
            let (_, _, ph3) = run2(p, dw, 2, 1, 2);
            assert!(ph3 > 0, "short: negative control brk=2 (no Z) did not break the phase");
        } }
    }
}
