//! Masked leading-one deposit (research code).
//!
//! [`lod_deposit`]: cells `x[i]` by significance; the region is the cells below a data-dependent cut
//! `E` read through a [`Thr`]. With `r = 1 + max{i < E : x[i] = 1}` (`r = 0` when none):
//! ```text
//!   out ^= gate * f(r)        (self-inverse; x, the threshold register and gate restored)
//! ```
//! Support: `r >= rlo` (cells below `rlo` are never scanned) and `E` inside the threshold window.
//!
//! Mechanism: a prefix chain rooted at the cut, scanned downward,
//! `p_i = (p_{i+1} XOR [E == i+1]) AND NOT x[i]` (so `p_i = [r <= i < E]`), with the telescoping deposit
//! `out ^= f(E)` at the leaf `E` and `out ^= f(i) ^ f(i+1)` under every `p_i` (CNOTs only). The chain
//! is cleared upward by measurement with Clifford phase repairs (the one-hot engine walks back up).
//! Room: with `room = Some(R)` at most `R` chain wires are live. The chain is cut into clean chunks
//! (`adder::chunk_plan`): each non-final chunk keeps its lowest wire as the next chunk's root and clears
//! the rest; the kept wires are released at the end by measurement, the phase repair replaying the
//! chunk's chain under the measured bit (expected half a chunk of Toffoli each).
//! Toffoli: 1 per chain cell + replays + ~1.3 per engine step (down, up per chunk, and replays).
use super::engine::Engine;
use super::mc::Thr;
use crate::circuit::{BitId, QubitId as Q};
use crate::point_add::builder::Builder;

fn deposit(c: &mut Builder, ctl: Option<Q>, out: &[Q], val: usize) {
    for (j, &q) in out.iter().enumerate() {
        if (val >> j) & 1 == 1 {
            match ctl {
                Some(w) => c.cx(w, q),
                None => c.x(q),
            }
        }
    }
}

struct Lod<'a> {
    x: &'a [Q],
    eng: Engine,
    leaves: Vec<(usize, usize)>,
}

impl Lod<'_> {
    fn leaf_at(&self, k: usize) -> Option<usize> {
        self.leaves.iter().find(|&&(kk, _)| kk == k).map(|&(_, v)| v)
    }
    /// Position the engine at the seed of cell `i` (cut `i+1`); returns the leaf (Some(None) = constant 1).
    fn seed(&mut self, c: &mut Builder, i: usize) -> Option<Option<Q>> {
        let v = self.leaf_at(i + 1)?;
        self.eng.goto(c, v);
        Some(self.eng.leaf())
    }
    /// `p_i` into a fresh wire (None when identically 0).
    fn compute(&mut self, c: &mut Builder, i: usize, prev: Option<Q>, seed: Option<Option<Q>>) -> Option<Q> {
        let xi = self.x[i];
        match (seed, prev) {
            (None, None) => None,
            (Some(s), Some(pv)) => {
                let s = s.expect("lod: constant leaf with a chain above");
                c.cx(s, pv);
                c.x(xi);
                let p = c.alloc_qubit();
                c.ccx(pv, xi, p);
                c.x(xi);
                c.cx(s, pv);
                Some(p)
            }
            (Some(s), None) => {
                let p = c.alloc_qubit();
                match s {
                    Some(s) => {
                        c.x(xi);
                        c.ccx(s, xi, p);
                        c.x(xi);
                    }
                    None => {
                        c.cx(xi, p);
                        c.x(p);
                    }
                }
                Some(p)
            }
            (None, Some(pv)) => {
                let p = c.alloc_qubit();
                c.x(xi);
                c.ccx(pv, xi, p);
                c.x(xi);
                Some(p)
            }
        }
    }
    /// Phase `(-1)^{p_i}` (from its definition) under the measured bit `m`.
    fn phase(&mut self, c: &mut Builder, i: usize, prev: Option<Q>, seed: Option<Option<Q>>, m: BitId) {
        let xi = self.x[i];
        match (seed, prev) {
            (None, None) => {}
            (Some(s), Some(pv)) => {
                let s = s.unwrap();
                c.cx(s, pv);
                c.x(xi);
                c.cz_if(pv, xi, m);
                c.x(xi);
                c.cx(s, pv);
            }
            (Some(s), None) => {
                c.x(xi);
                match s {
                    Some(s) => c.cz_if(s, xi, m),
                    None => c.cz_if(xi, xi, m),
                }
                c.x(xi);
            }
            (None, Some(pv)) => {
                c.x(xi);
                c.cz_if(pv, xi, m);
                c.x(xi);
            }
        }
    }
    /// Measurement uncompute of `p_i` (prev = `p_{i+1}`, alive).
    fn clear(&mut self, c: &mut Builder, i: usize, p: Q, prev: Option<Q>) {
        let seed = self.seed(c, i);
        let m = c.alloc_bit();
        c.hmr(p, m);
        self.phase(c, i, prev, seed, m);
        c.free_bit(m);
        c.release_clean(p);
    }
}

/// Two-seed boundary conversion on one register `[val | gap | cof]` (cells by significance).
///
/// The gap indicator `p_i = [b <= i < E]` (`b` = value-field top cut, `E` = cofactor-field cut, the
/// cofactor's top bit sits at `E` or `E = cells`) satisfies two recursions on a canonical register:
/// top-seeded `p_i = (p_{i+1} XOR [E == i+1]) AND NOT x_i` and bottom-seeded
/// `p_i = (p_{i-1} XOR [b == i]) AND NOT x_i`. One chain therefore converts between the two boundary
/// registers: built from one register's leaves, it telescopes `f_other` of the other cut into the other
/// register, and the second pass erases the first register (telescoping from the other end) while
/// clearing the chain with the other recursion.
/// * `top_to_bot`: `bot ^= f_bot(b)` (bot = 0 on entry), then `top ^= f_top(E)` (-> 0).
/// * `!top_to_bot`: `top ^= f_top(E)` (top = 0 on entry), then `bot ^= f_bot(b)` (-> 0).
/// Toffoli: one per chain cell (`[b_lo, E_hi)`) + one engine pass per register. Wires: the whole chain
/// + one engine (no chunking: callers use it when the room allows).
#[allow(clippy::too_many_arguments)]
pub fn convert(c: &mut Builder, x: &[Q], top: &Thr, bot: &Thr, top_to_bot: bool, f_top: &dyn Fn(usize) -> usize,
               f_bot: &dyn Fn(usize) -> usize) -> usize {
    convert_gated(c, x, top, bot, top_to_bot, f_top, f_bot, None)
}

/// [`convert`] under a gate wire: with `gate = 0` both registers are left unchanged (every seed is
/// gated, so the chain stays zero and nothing is deposited).
#[allow(clippy::too_many_arguments)]
pub fn convert_gated(c: &mut Builder, x: &[Q], top: &Thr, bot: &Thr, top_to_bot: bool, f_top: &dyn Fn(usize) -> usize,
                     f_bot: &dyn Fn(usize) -> usize, gate: Option<Q>) -> usize {
    let mut tl: Vec<(usize, usize)> = top.pairs.iter().map(|&(v, k)| (k, v)).collect();
    let mut bl: Vec<(usize, usize)> = bot.pairs.iter().map(|&(v, k)| (k, v)).collect();
    tl.sort();
    bl.sort();
    let ehi = tl.last().unwrap().0;
    let blo = bl.first().unwrap().0;
    assert!(ehi <= x.len());
    let at = |l: &Vec<(usize, usize)>, k: usize| l.iter().find(|&&(kk, _)| kk == k).map(|&(_, v)| v);
    let cells: Vec<usize> = (blo..ehi).collect();
    let base = blo;
    let mut p: Vec<Option<Q>> = vec![None; cells.len()];
    let idx = |i: usize| i - base;
    let get = |p: &Vec<Option<Q>>, i: isize| -> Option<Q> {
        if i < base as isize || i >= ehi as isize { None } else { p[i as usize - base] }
    };
    // generic chain cell: p = (nb XOR seed) AND NOT x  (nb = neighbour chain wire)
    let and_cell = |c: &mut Builder, xi: Q, nb: Option<Q>, seed: Option<Option<Q>>| -> Option<Q> {
        match (seed, nb) {
            (None, None) => None,
            (Some(s), Some(pv)) => {
                let s = s.expect("convert: constant leaf");
                c.cx(s, pv);
                c.x(xi);
                let q = c.alloc_qubit();
                c.ccx(pv, xi, q);
                c.x(xi);
                c.cx(s, pv);
                Some(q)
            }
            (Some(s), None) => {
                let q = c.alloc_qubit();
                c.x(xi);
                match s {
                    Some(s) => c.ccx(s, xi, q),
                    None => {
                        c.x(xi);
                        c.cx(xi, q);
                        c.x(q);
                        c.x(xi);
                    }
                }
                c.x(xi);
                Some(q)
            }
            (None, Some(pv)) => {
                let q = c.alloc_qubit();
                c.x(xi);
                c.ccx(pv, xi, q);
                c.x(xi);
                Some(q)
            }
        }
    };
    let phase_cell = |c: &mut Builder, xi: Q, nb: Option<Q>, seed: Option<Option<Q>>, m: BitId| match (seed, nb) {
        (None, None) => {}
        (Some(s), Some(pv)) => {
            let s = s.unwrap();
            c.cx(s, pv);
            c.x(xi);
            c.cz_if(pv, xi, m);
            c.x(xi);
            c.cx(s, pv);
        }
        (Some(s), None) => {
            c.x(xi);
            match s {
                Some(s) => c.cz_if(s, xi, m),
                None => c.cz_if(xi, xi, m),
            }
            c.x(xi);
        }
        (None, Some(pv)) => {
            c.x(xi);
            c.cz_if(pv, xi, m);
            c.x(xi);
        }
    };
    let (src, dst, f_dst, f_src) = if top_to_bot { (top, bot, f_bot, f_top) } else { (bot, top, f_top, f_bot) };
    // pass 1: build the chain from `src`'s leaves, telescope f_dst into dst
    let (slo, shi) = src.vwin();
    let mut e = Engine::new(c, src.reg, gate, slo, shi);
    let order: Vec<usize> = if top_to_bot { cells.iter().rev().copied().collect() } else { cells.clone() };
    for &i in &order {
        // seed for cell i: top -> cut i+1 ; bottom -> cut i
        let (sl, cut) = if top_to_bot { (&tl, i + 1) } else { (&bl, i) };
        let seed = at(sl, cut).map(|v| {
            e.goto(c, v);
            let l = e.leaf();
            deposit(c, l, dst.reg, f_dst(cut));
            l
        });
        let nb = if top_to_bot { get(&p, i as isize + 1) } else { get(&p, i as isize - 1) };
        let q = and_cell(c, x[i], nb, seed);
        if let Some(q) = q {
            deposit(c, Some(q), dst.reg, f_dst(i) ^ f_dst(i + 1));
        }
        p[idx(i)] = q;
    }
    // leaves outside the chain range: deposit only
    let sl = if top_to_bot { &tl } else { &bl };
    for &(k, v) in sl.iter() {
        let inside = if top_to_bot { k > blo && k <= ehi } else { k >= blo && k < ehi };
        if !inside {
            e.goto(c, v);
            let l = e.leaf();
            deposit(c, l, dst.reg, f_dst(k));
        }
    }
    e.finish(c);
    // pass 2: dst's leaves; telescope f_src into src (erasing it) and clear the chain with the other
    // recursion, in the same direction as pass 1
    let (dlo, dhi) = dst.vwin();
    let mut e = Engine::new(c, dst.reg, gate, dlo, dhi);
    for &i in &order {
        let (dl, cut) = if top_to_bot { (&bl, i) } else { (&tl, i + 1) };
        let seed = at(dl, cut).map(|v| {
            e.goto(c, v);
            let l = e.leaf();
            deposit(c, l, src.reg, f_src(cut));
            l
        });
        let Some(q) = p[idx(i)] else { continue };
        deposit(c, Some(q), src.reg, f_src(i) ^ f_src(i + 1));
        let nb = if top_to_bot { get(&p, i as isize - 1) } else { get(&p, i as isize + 1) };
        let m = c.alloc_bit();
        c.hmr(q, m);
        phase_cell(c, x[i], nb, seed, m);
        c.free_bit(m);
        c.release_clean(q);
        p[idx(i)] = None;
    }
    let dl = if top_to_bot { &bl } else { &tl };
    for &(k, v) in dl.iter() {
        let inside = if top_to_bot { k >= blo && k < ehi } else { k > blo && k <= ehi };
        if !inside {
            e.goto(c, v);
            let l = e.leaf();
            deposit(c, l, src.reg, f_src(k));
        }
    }
    e.finish(c);
    cells.len()
}

/// Room for the chain: unbounded, a cap on all live wires, or a direct chain-wire budget.
#[derive(Clone, Copy, Debug)]
pub enum Room {
    Unbounded,
    Cap(usize),
    Chain(usize),
}

/// `out ^= gate * f(r)` (module doc). Returns the number of chain cells.
#[allow(clippy::too_many_arguments)]
pub fn lod_deposit(c: &mut Builder, x: &[Q], top: &Thr, rlo: usize, out: &[Q], f: &dyn Fn(usize) -> usize,
                   gate: Option<Q>, room: Room) -> usize {
    let mut leaves: Vec<(usize, usize)> = top.pairs.iter().map(|&(v, k)| (k, v)).collect();
    leaves.sort();
    let emax = leaves.last().unwrap().0;
    assert!(emax <= x.len(), "lod_deposit: cut {emax} beyond {} cells", x.len());
    for w in leaves.windows(2) {
        assert!(w[0].0 != w[1].0, "lod_deposit: two register values map to cut {}", w[0].0);
    }
    let (vlo, vhi) = top.vwin();
    let eng = Engine::new(c, top.reg, gate, vlo, vhi);
    // chain room: the cap minus what is live now, the engine, and one wire for the fold ladder
    let room = match room {
        Room::Unbounded => None,
        Room::Cap(k) => Some(k.saturating_sub(c.active_qubits() as usize + eng.wires() + 2).max(2)),
        Room::Chain(r) => Some(r),
    };
    let mut st = Lod { x, eng, leaves };
    // chain cells, top first
    let cells: Vec<usize> = (rlo..emax).rev().collect();
    let nc = cells.len();
    let plan: Vec<usize> = match room {
        None => vec![nc],
        Some(r) if r >= nc => vec![nc],
        // the smallest feasible budget at or above the requested one (the cap is exceeded when the room
        // cannot hold even the minimal chunk schedule; the caller's peak report shows it)
        Some(r) => (r.max(2)..=nc).find_map(|rr| super::super::skycof::adder::chunk_plan(nc, rr)).unwrap(),
    };
    let mut p: Vec<Option<Q>> = vec![None; nc];
    let prev_of = |p: &Vec<Option<Q>>, j: usize| if j == 0 { None } else { p[j - 1] };
    let mut bounds: Vec<(usize, usize)> = Vec::new(); // (chunk start index, boundary index)
    let mut start = 0usize;
    for (ci, &size) in plan.iter().enumerate() {
        if size == 0 {
            continue;
        }
        let end = start + size; // cells[start..end]
        for j in start..end {
            let i = cells[j];
            let seed = st.seed(c, i);
            if let Some(l) = seed {
                deposit(c, l, out, f(i + 1));
            }
            let q = st.compute(c, i, prev_of(&p, j), seed);
            if let Some(q) = q {
                deposit(c, Some(q), out, f(i) ^ f(i + 1));
            }
            p[j] = q;
        }
        let last = ci + 1 == plan.len();
        let keep_to = if last { end } else { end - 1 };
        for j in (start..keep_to).rev() {
            if let Some(q) = p[j] {
                let pv = prev_of(&p, j);
                st.clear(c, cells[j], q, pv);
                p[j] = None;
            }
        }
        if !last {
            bounds.push((start, end - 1));
        }
        start = end;
    }
    assert_eq!(start, nc);
    // leaves at or below the scan floor: deposit only
    let low: Vec<(usize, usize)> = st.leaves.iter().rev().filter(|&&(k, _)| k <= rlo).copied().collect();
    for (k, v) in low {
        st.eng.goto(c, v);
        let l = st.eng.leaf();
        deposit(c, l, out, f(k));
    }
    // release the kept boundaries, last chunk's first
    while let Some((s0, bj)) = bounds.pop() {
        let Some(bq) = p[bj] else { continue };
        let home = st.leaf_at(cells[s0] + 1).or_else(|| st.leaf_at(cells[bj] + 1));
        if let Some(h) = home {
            st.eng.goto(c, h);
        }
        let m = c.alloc_bit();
        c.hmr(bq, m);
        c.push_condition(m);
        for j in s0..bj {
            let i = cells[j];
            let seed = st.seed(c, i);
            p[j] = st.compute(c, i, prev_of(&p, j), seed);
        }
        let seed = st.seed(c, cells[bj]);
        st.phase(c, cells[bj], prev_of(&p, bj), seed, m);
        for j in (s0..bj).rev() {
            if let Some(q) = p[j] {
                let pv = prev_of(&p, j);
                st.clear(c, cells[j], q, pv);
                p[j] = None;
            }
        }
        if let Some(h) = home {
            st.eng.goto(c, h);
        }
        c.pop_condition();
        c.free_bit(m);
        c.release_clean(bq);
        p[bj] = None;
    }
    st.eng.finish(c);
    nc
}
