//! Masked single-carry-wire Cuccaro arithmetic on shared ring registers (research code).
//!
//! Cells `i = 0..n` pair a target wire `t[i]` with an operand wire `o[i]` (any wires; cell 0 = LSB).
//! A cell is ACTIVE when `L <= i < E`, where `E` (upper threshold) and `L` (lower threshold) are
//! data-dependent cell indices read from small boundary registers through [`Thr`] (value -> cell map).
//!
//! [`mc_add`] (`sub = false`) / subtract (`sub = true`), with `g` = optional control:
//! ```text
//!   t[L..E) := t[L..E) +- g * o[L..E)   (mod 2^(E-L));   every other wire unchanged
//! ```
//! Inactive cells pass the carry unchanged and never touch their target or operand wire, so foreign
//! bits of the other field (above `E`) and of the operand (below `L`) are safe. Cells below `L`
//! see a zero carry (nothing active below them), so they are the identity.
//!
//! Gates (single carry wire `c`, Cuccaro MAJ / UMA with the running carry in `c`):
//! ```text
//!   plain MAJ   cx(c,o) cx(c,t) ccx(t,o,c)                                   1 T
//!   plain UMA   ccx(t,o,c) cx(c,t) [cx(o,t) | ccx(g,o,t)] cx(c,o)            1 T | 2 T (controlled)
//!   masked MAJ  ccx(f,c,o) x=ccx(f,o) cx(c,t) ccx(t,x,c) mbu(x)             3 T
//!   masked UMA  x=ccx(f,o) ccx(t,x,c) cx(c,t) cx(x,t) mbu(x) ccx(f,c,o)      3 T
//! ```
//! `f` is ONE thermometer wire `g AND [L <= i < E]`, toggled at the threshold leaves of one-hot
//! [`Engine`] sweeps (ascending in the MAJ pass, descending in the UMA pass; the engines are gated
//! by `g`, so the masked cells need no further control). Plain cells are the cells that every
//! register value in the support leaves active; they carry the control in their sum gate.
//! Wires: `c`, `f`, `x` + the live engines (one per threshold whose zone is being swept).
//!
//! [`cmp_capture`]: the borrow cascade of `a` vs `b` (MAJ pass, captures, reverse MAJ pass) with
//! `out ^= leaf_k AND [a mod 2^k < b mod 2^k]` at the one-hot leaf of a threshold `k` (or at a fixed
//! `k = n`). Self-inverse; bits above the capture never influence it. 2 T per cell + 1 T per leaf.
use super::engine::Engine;
use crate::circuit::QubitId as Q;
use crate::point_add::builder::Builder;

/// A data-dependent cell threshold: register `reg` and its support as `(value, cell)` pairs (the
/// one-hot engine walks the value window `[min value, max value]`; only the listed values fire).
pub struct Thr<'a> {
    pub reg: &'a [Q],
    pub pairs: Vec<(usize, usize)>,
}

impl Thr<'_> {
    pub fn range(&self) -> (usize, usize) {
        let a = self.pairs.iter().map(|p| p.1).min().unwrap();
        let b = self.pairs.iter().map(|p| p.1).max().unwrap();
        (a, b)
    }
    pub fn vwin(&self) -> (usize, usize) {
        let a = self.pairs.iter().map(|p| p.0).min().unwrap();
        let b = self.pairs.iter().map(|p| p.0).max().unwrap();
        (a, b)
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Cls {
    Skip,
    Plain,
    Masked,
}

fn toggle(c: &mut Builder, leaf: Option<Q>, f: Q) {
    match leaf {
        Some(l) => c.cx(l, f),
        None => c.x(f),
    }
}

fn mbu_x(c: &mut Builder, x: Q, f: Q, o: Q) {
    let m = c.alloc_bit();
    c.hmr(x, m);
    c.cz_if(f, o, m);
    c.free_bit(m);
    c.release_clean(x);
}

/// Cost summary of the last [`mc_add`] (plain / masked cell counts, leaves) for reports.
#[derive(Clone, Copy, Debug, Default)]
pub struct McShape {
    pub plain: usize,
    pub masked: usize,
    pub leaves: usize,
}

/// Masked add / subtract over the cells (module doc). Returns the cell shape.
///
/// With both thresholds the active flag is normally ONE wire toggled by both engines (`[L <= i] XOR
/// [E <= i]`, valid when `L <= E` on the support). `and_form = true` keeps two flag wires and uses
/// `y = fE AND fL` per masked cell (+1 Toffoli per masked cell per pass), which is exact for every
/// `L, E` (an empty region when `L > E`).
#[allow(clippy::too_many_arguments)]
pub fn mc_add(c: &mut Builder, t: &[Q], o: &[Q], g: Option<Q>, sub: bool, upper: Option<&Thr>, lower: Option<&Thr>)
              -> McShape {
    mc_add_ex(c, t, o, g, sub, upper, lower, false)
}

#[allow(clippy::too_many_arguments)]
pub fn mc_add_ex(c: &mut Builder, t: &[Q], o: &[Q], g: Option<Q>, sub: bool, upper: Option<&Thr>, lower: Option<&Thr>,
                 and_form: bool) -> McShape {
    let n = t.len();
    assert_eq!(o.len(), n, "mc_add: target/operand cell counts");
    let and_form = and_form && upper.is_some() && lower.is_some();
    let (emin, emax) = upper.map(|u| u.range()).unwrap_or((usize::MAX, usize::MAX));
    let (lmin, lmax) = lower.map(|l| l.range()).unwrap_or((0, 0));
    let cls: Vec<Cls> = (0..n)
        .map(|i| {
            if i >= emax || i < lmin {
                Cls::Skip
            } else if i >= emin || i < lmax {
                Cls::Masked
            } else {
                Cls::Plain
            }
        })
        .collect();
    // toggles per cell: (threshold index, value)
    let mut tog: Vec<Vec<(usize, usize)>> = vec![Vec::new(); n + 1];
    let thrs: [Option<&Thr>; 2] = [upper, lower];
    for (ti, th) in thrs.iter().enumerate() {
        let Some(th) = th else { continue };
        // upper: a cut at emax needs no toggle (every cell from there on is skipped); lower: the cut at
        // lmax still toggles, because masked cells of the upper zone may lie above it
        let (zlo, zhi) = if ti == 0 { (emin, emax) } else { (lmin, lmax + 1) };
        let mut vs: Vec<(usize, usize)> = th.pairs.iter().map(|&(v, k)| (k, v)).filter(|&(k, _)| k >= zlo && k < zhi && k < n).collect();
        vs.sort();
        for (k, v) in vs {
            tog[k].push((ti, v));
        }
    }
    let any_masked = cls.iter().any(|&k| k == Cls::Masked);
    if !any_masked {
        // a single-value lower zone puts a toggle at its cut but leaves no masked cell: no flag needed
        tog.iter_mut().for_each(|x| x.clear());
    }
    let leaves: usize = tog.iter().map(|x| x.len()).sum();
    let shape = McShape {
        plain: cls.iter().filter(|&&k| k == Cls::Plain).count(),
        masked: cls.iter().filter(|&&k| k == Cls::Masked).count(),
        leaves,
    };
    if shape.plain + shape.masked == 0 {
        return shape;
    }
    if sub {
        for i in 0..n {
            if cls[i] != Cls::Skip {
                c.x(t[i]);
            }
        }
    }
    // flag wires: tflag[ti] is the wire threshold ti toggles; `on[ti]` = initialised to the gate
    let (tflag, on): ([Option<Q>; 2], [bool; 2]) = if !any_masked {
        ([None, None], [false, false])
    } else if and_form {
        let fe = c.alloc_qubit();
        let fl = c.alloc_qubit();
        ([Some(fe), Some(fl)], [true, false])
    } else {
        let f = c.alloc_qubit();
        ([Some(f), Some(f)], [lower.is_none(), false])
    };
    let init = |c: &mut Builder| {
        if tflag[0].is_some() && on[0] {
            match g {
                Some(g) => c.cx(g, tflag[0].unwrap()),
                None => c.x(tflag[0].unwrap()),
            }
        }
    };
    init(c);
    let cw = c.alloc_qubit();
    // the masked cell's flag: f itself, or y = fE AND fL (and form)
    let flag_on = |c: &mut Builder| -> Q {
        if and_form {
            let y = c.alloc_qubit();
            c.ccx(tflag[0].unwrap(), tflag[1].unwrap(), y);
            y
        } else {
            tflag[0].unwrap()
        }
    };
    let flag_off = |c: &mut Builder, y: Q| {
        if and_form {
            let m = c.alloc_bit();
            c.hmr(y, m);
            c.cz_if(tflag[0].unwrap(), tflag[1].unwrap(), m);
            c.free_bit(m);
            c.release_clean(y);
        }
    };
    // per-threshold first / last toggle cell
    let span = |ti: usize| -> Option<(usize, usize)> {
        let ks: Vec<usize> = (0..=n).filter(|&k| tog[k].iter().any(|&(x, _)| x == ti)).collect();
        Some((*ks.first()?, *ks.last()?))
    };
    let spans = [span(0), span(1)];
    let regs: [Option<(&[Q], usize, usize)>; 2] =
        [upper.map(|u| (u.reg, u.vwin().0, u.vwin().1)), lower.map(|l| (l.reg, l.vwin().0, l.vwin().1))];
    // MAJ pass
    let mut eng: [Option<Engine>; 2] = [None, None];
    for i in 0..n {
        for &(ti, v) in &tog[i] {
            if eng[ti].is_none() {
                let (r, lo, hi) = regs[ti].unwrap();
                eng[ti] = Some(Engine::new(c, r, g, lo, hi));
            }
            let e = eng[ti].as_mut().unwrap();
            e.goto(c, v);
            toggle(c, e.leaf(), tflag[ti].unwrap());
        }
        for ti in 0..2 {
            if spans[ti].is_some_and(|(_, last)| last == i) {
                eng[ti].take().unwrap().finish(c);
            }
        }
        let (ti_, oi) = (t[i], o[i]);
        match cls[i] {
            Cls::Skip => {}
            Cls::Plain => {
                c.cx(cw, oi);
                c.cx(cw, ti_);
                c.ccx(ti_, oi, cw);
            }
            Cls::Masked => {
                let f = flag_on(c);
                c.ccx(f, cw, oi);
                let x = c.alloc_qubit();
                c.ccx(f, oi, x);
                c.cx(cw, ti_);
                c.ccx(ti_, x, cw);
                mbu_x(c, x, f, oi);
                flag_off(c, f);
            }
        }
    }
    // UMA pass
    for i in (0..n).rev() {
        let (ti_, oi) = (t[i], o[i]);
        match cls[i] {
            Cls::Skip => {}
            Cls::Plain => {
                c.ccx(ti_, oi, cw);
                c.cx(cw, ti_);
                match g {
                    Some(g) => c.ccx(g, oi, ti_),
                    None => c.cx(oi, ti_),
                }
                c.cx(cw, oi);
            }
            Cls::Masked => {
                let f = flag_on(c);
                let x = c.alloc_qubit();
                c.ccx(f, oi, x);
                c.ccx(ti_, x, cw);
                c.cx(cw, ti_);
                c.cx(x, ti_);
                mbu_x(c, x, f, oi);
                c.ccx(f, cw, oi);
                flag_off(c, f);
            }
        }
        for &(ti, v) in tog[i].iter().rev() {
            if eng[ti].is_none() {
                let (r, lo, hi) = regs[ti].unwrap();
                eng[ti] = Some(Engine::new(c, r, g, lo, hi));
            }
            let e = eng[ti].as_mut().unwrap();
            e.goto(c, v);
            toggle(c, e.leaf(), tflag[ti].unwrap());
        }
        for ti in 0..2 {
            if spans[ti].is_some_and(|(first, _)| first == i) {
                eng[ti].take().unwrap().finish(c);
            }
        }
    }
    c.release_clean(cw);
    init(c);
    if let Some(f) = tflag[0] {
        c.release_clean(f);
    }
    if and_form {
        if let Some(f1) = tflag[1] {
            c.release_clean(f1);
        }
    }
    if sub {
        for i in 0..n {
            if cls[i] != Cls::Skip {
                c.x(t[i]);
            }
        }
    }
    shape
}

/// Phase `(-1)^[a < b]` (full cut `k = n`), emitted under the measured condition `cond`: the
/// measurement uncompute of a [`cmp_capture`] output. Expected Toffoli `n` (2n under the condition).
pub fn cmp_phase(c: &mut Builder, a: &[Q], b: &[Q], cond: crate::circuit::BitId) {
    let n = a.len();
    c.push_condition(cond);
    for &q in a {
        c.x(q);
    }
    let cw = c.alloc_qubit();
    for i in 0..n {
        c.cx(cw, b[i]);
        c.cx(cw, a[i]);
        c.ccx(a[i], b[i], cw);
    }
    c.cz(cw, cw);
    for i in (0..n).rev() {
        c.ccx(a[i], b[i], cw);
        c.cx(cw, a[i]);
        c.cx(cw, b[i]);
    }
    c.release_clean(cw);
    for &q in a {
        c.x(q);
    }
    c.pop_condition();
}

/// Capture compare (module doc). `a`, `b`: cells (LSB first). Captures `out ^= gate AND [k == thr]
/// AND [a mod 2^k < b mod 2^k]` for the threshold's cuts `k` (cell index; `k = n` allowed), and with
/// `thr = None` the fixed cut `k = n` (`out ^= gate AND [a < b]`; gate `None` = 1).
pub fn cmp_capture(c: &mut Builder, a: &[Q], b: &[Q], out: Q, thr: Option<&Thr>, gate: Option<Q>) {
    cmp_capture_impl(c, a, b, Some(out), thr, gate)
}

/// Phase `(-1)^{captured bit}` of [`cmp_capture`] (same `a`, `b`, `thr`, `gate`), emitted under the measured
/// condition `cond`: the measurement uncompute of a capture-compare output (expected Toffoli half the
/// compare's).
pub fn cmp_capture_phase(c: &mut Builder, a: &[Q], b: &[Q], thr: Option<&Thr>, gate: Option<Q>, cond: crate::circuit::BitId) {
    c.push_condition(cond);
    cmp_capture_impl(c, a, b, None, thr, gate);
    c.pop_condition();
}

fn cmp_capture_impl(c: &mut Builder, a: &[Q], b: &[Q], out: Option<Q>, thr: Option<&Thr>, gate: Option<Q>) {
    let n = a.len();
    assert_eq!(b.len(), n);
    let mut cuts: Vec<(usize, usize)> = match thr {
        Some(th) => th.pairs.iter().map(|&(v, k)| (k, v)).collect(),
        None => vec![(n, 0)],
    };
    cuts.sort();
    assert!(cuts.iter().all(|&(k, _)| k <= n), "cmp_capture: cut beyond the window");
    let kmax = cuts.last().map_or(0, |x| x.0);
    let cells = kmax.min(n);
    for &q in &a[..cells] {
        c.x(q);
    }
    let cw = c.alloc_qubit();
    let mut eng: Option<Engine> = None;
    let mut ci = 0;
    // out = Some: out ^= leaf AND cw ; out = None: phase (-1)^(leaf AND cw)
    let hit = |c: &mut Builder, l: Option<Q>, cw: Q| match (out, l) {
        (Some(o), Some(l)) => c.ccx(l, cw, o),
        (Some(o), None) => c.cx(cw, o),
        (None, Some(l)) => c.cz(l, cw),
        (None, None) => c.z_if(cw, crate::circuit::NO_BIT),
    };
    let capture = |c: &mut Builder, eng: &mut Option<Engine>, v: usize, cw: Q| match thr {
        Some(th) => {
            if eng.is_none() {
                *eng = Some(Engine::new(c, th.reg, gate, th.vwin().0, th.vwin().1));
            }
            let e = eng.as_mut().unwrap();
            e.goto(c, v);
            let l = e.leaf();
            hit(c, l, cw)
        }
        None => hit(c, gate, cw),
    };
    for i in 0..=cells {
        while ci < cuts.len() && cuts[ci].0 == i {
            capture(c, &mut eng, cuts[ci].1, cw);
            ci += 1;
        }
        if ci == cuts.len() {
            if let Some(e) = eng.take() {
                e.finish(c);
            }
        }
        if i < cells {
            c.cx(cw, b[i]);
            c.cx(cw, a[i]);
            c.ccx(a[i], b[i], cw);
        }
    }
    if let Some(e) = eng.take() {
        e.finish(c);
    }
    for i in (0..cells).rev() {
        c.ccx(a[i], b[i], cw);
        c.cx(cw, a[i]);
        c.cx(cw, b[i]);
    }
    c.release_clean(cw);
    for &q in &a[..cells] {
        c.x(q);
    }
}
