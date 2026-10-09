//! Masked letter decoder of the SKY-COF ring walk (k = 0, windowed), and the history push / pop.
//!
//! Post-state of a tick (unparked): `A = [u | s]`, `B = [v | r]`, `KA = bits(s)`, `VB = bits(v)`. Letters:
//! C iff `s[1] = 1`; otherwise A when `2r < s` is certain, else ambiguous (A or B; `typ = [A]` is pushed).
//!
//! # The decision (exact masked window compare)
//! Window cells: `x_i = B_cof[lo + i]`, `y_i = A_cof[lo + 1 + i]` for `i < ncell`, `kmax = KA_hi - 1`,
//! `lo = max(1, kmax - w)`, `ncell = kmax - lo`. With the capture compare
//! `lt = [x mod 2^k < y mod 2^k]`, `k = clamp(KA - 1 - lo, 0, ncell)` (captured at the `KA` leaf) and
//! `RB' = bits(r) + 1` (leading-one deposit below the cut `N - VB`):
//! `ge = NOT [RB' < KA + lt]`, i.e.
//! * `RB' < KA`: `r < 2^(KA-2) <= s/2`: certain A;
//! * `RB' > KA`: `r >= 2^(KA-1) > s/2`: ambiguous;
//! * `RB' = KA`: `bits(r) = KA - 1 <= N - VB`, so every cell below the capture holds `r` (no `v` bits) and
//!   `lt` is the exact windowed `[r >> lo < s >> (lo+1)]` (`s` lives entirely below `KA`).
//!
//! `D = en & !s[1]`, `amb = D & ge`. The comparison runs on `RB' - o` (a `w`-wire deposit) against
//! `KA - o` (`KA` offset in place), `o`, `w` per-tick constants of the zones.
//!
//! Wires held across the push: `lt`, `ltc = [RB' < KA + lt]`, `amb`; `RB' - o` lives only inside the
//! compare. Uncompute: `amb` by measurement (Clifford repair), `ltc` by measurement with the compare's
//! phase under the outcome, `lt` likewise (capture-compare phase).
use super::engine::{and_clear, and_into, Lit};
use super::lod::{lod_deposit, Room};
use super::mc::{cmp_capture, cmp_capture_phase, Thr};
use super::ring::{Ring, Rng};
use crate::circuit::QubitId as Q;
use crate::point_add::builder::Builder;
use crate::point_add::skycof::decoder::{shift_in, shift_out, Hreg};
use crate::point_add::skycof_mm as mm;

/// Decoder windows of one tick (post-state supports of `KA`, `VB`, `bits(r)`), window width `w`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DecZ {
    pub ka: Rng,
    pub vb: Rng,
    pub rb: Rng,
    pub w: usize,
    /// one step of lookback through a C letter (see [`push`])
    pub k1: bool,
}

impl DecZ {
    pub fn kmax(&self) -> usize {
        self.ka.hi.saturating_sub(1)
    }
    pub fn lo(&self) -> usize {
        self.kmax().saturating_sub(self.w).max(1)
    }
    pub fn ncell(&self) -> usize {
        self.kmax().saturating_sub(self.lo())
    }
    /// Capture cut for `KA = b`.
    pub fn cut(&self, b: usize) -> usize {
        (b as isize - 1 - self.lo() as isize).clamp(0, self.ncell() as isize) as usize
    }
    /// Second (k = 1) capture cut for `KA = b` (`s/4` lives below index `KA - 2`).
    pub fn cut2(&self, b: usize) -> usize {
        (b as isize - 2 - self.lo() as isize).clamp(0, self.ncell() as isize) as usize
    }
    /// Offset `o` and width `w` of the `RB' - o` vs `KA - o` comparison.
    pub fn off_w(&self) -> (usize, usize) {
        let o = (self.rb.lo + 1).min(self.ka.lo);
        let top = (self.rb.hi + 1).max(self.ka.hi) - o;
        (o, ((usize::BITS - top.leading_zeros()) as usize).max(1))
    }
}

fn cells(r: &Ring, z: &DecZ) -> (Vec<Q>, Vec<Q>) {
    let (lo, nc) = (z.lo(), z.ncell());
    let bc = r.bcof();
    let ac = r.acof();
    ((0..nc).map(|i| bc[lo + i]).collect(), (0..nc).map(|i| ac[lo + 1 + i]).collect())
}

/// Capture threshold on `KA - o` (KA is offset in place for the whole decoder call).
fn thr_ka<'a>(r: &'a Ring, z: &DecZ) -> Thr<'a> {
    let (o, w) = z.off_w();
    let mask = (1usize << w) - 1;
    Thr { reg: &r.ka[..w], pairs: z.ka.vals().map(|b| ((b - o) & mask, z.cut(b))).collect() }
}

fn ac(name: &'static str, a: usize, b: usize) {
    super::rwalk::ACCT.with(|x| {
        if let Some(v) = x.borrow_mut().as_mut() {
            v.push((name, a, b));
        }
    });
}

/// `out ^= [a < b + cin]` (borrow chain of `a - b - cin` over `a.len()` cells, `b` read on the same cells;
/// `out = None`: the phase `(-1)^[a < b + cin]` instead). Self-inverse; 2 Toffoli per cell.
fn cmp_cin(c: &mut Builder, a: &[Q], b: &[Q], cin: Q, out: Option<Q>) {
    let n = a.len();
    for &q in a {
        c.x(q);
    }
    let cw = c.alloc_qubit();
    c.cx(cin, cw);
    for i in 0..n {
        c.cx(cw, b[i]);
        c.cx(cw, a[i]);
        c.ccx(a[i], b[i], cw);
    }
    match out {
        Some(o) => c.cx(cw, o),
        None => c.z_if(cw, crate::circuit::NO_BIT),
    }
    for i in (0..n).rev() {
        c.ccx(a[i], b[i], cw);
        c.cx(cw, a[i]);
        c.cx(cw, b[i]);
    }
    c.cx(cin, cw);
    c.release_clean(cw);
    for &q in a {
        c.x(q);
    }
}

/// `y += k` (mod 2^len), constant `k`.
fn add_k(c: &mut Builder, y: &[Q], k: usize, room: usize) {
    if k % (1usize << y.len()) == 0 {
        return;
    }
    let ad = mm::const_ad(k as u128, y.len(), None);
    mm::add_gen(c, y, &ad, mm::Fin::Sum, None, room);
}

fn sub_k(c: &mut Builder, y: &[Q], k: usize, room: usize) {
    c.x_all(y);
    add_k(c, y, k, room);
    c.x_all(y);
}

fn room_of(c: &Builder, r: &Ring) -> usize {
    r.cap.map_or(64, |k| k.saturating_sub(c.active_qubits() as usize).max(2))
}

/// `RB' - o` deposited on `rb` (self-inverse) with `KA -= o` before / `KA += o` after (`pre`, `post`).
fn rb_dep(c: &mut Builder, r: &Ring, z: &DecZ, rb: &[Q]) {
    let (o, w) = z.off_w();
    let th = Thr { reg: &r.vb, pairs: z.vb.vals().map(|v| (v, r.n - v)).collect() };
    let room = r.cap.map_or(Room::Unbounded, Room::Cap);
    let mask = (1usize << w) - 1;
    let f = move |b: usize| (b + 1).wrapping_sub(o) & mask;
    let a0 = c.op_count();
    lod_deposit(c, &r.bcof(), &th, z.rb.lo, rb, &f, None, room);
    ac("d_rb", a0, c.op_count());
}

/// `ltc ^= [RB' < KA + lt]` (`ltc = None`: its phase); `rb` holds `RB' - o` and `KA` is offset by `-o`.
fn ltc_cmp(c: &mut Builder, r: &Ring, z: &DecZ, rb: &[Q], lt: Q, ltc: Option<Q>) {
    let (_, w) = z.off_w();
    cmp_cin(c, rb, &r.ka[..w], lt, ltc);
}

fn ka_off(c: &mut Builder, r: &Ring, z: &DecZ, sub: bool) {
    let (o, _) = z.off_w();
    let rm = room_of(c, r);
    if sub {
        sub_k(c, &r.ka, o, rm);
    } else {
        add_k(c, &r.ka, o, rm);
    }
}

/// `lt ^= capture` (`lt = None`: phase under the caller's condition is not supported here).
fn capture(c: &mut Builder, r: &Ring, z: &DecZ, lt: Q) {
    let (xc, yc) = cells(r, z);
    let th = thr_ka(r, z);
    let o0 = c.op_count();
    cmp_capture(c, &xc, &yc, lt, Some(&th), None);
    ac("d_capture", o0, c.op_count());
}

fn thr_ka2<'a>(r: &'a Ring, z: &DecZ) -> Thr<'a> {
    let (o, w) = z.off_w();
    let mask = (1usize << w) - 1;
    Thr { reg: &r.ka[..w], pairs: z.ka.vals().map(|b| ((b - o) & mask, z.cut2(b))).collect() }
}

/// In-place `t += o` over the cells (uncontrolled Cuccaro, one carry wire) with `out ^= leaf_k AND carry into
/// cell k` at the threshold's cuts (captured in the MAJ pass, before cell k). With `t` complemented before and
/// after, the same routine is `t -= o` and captures the borrow `[t mod 2^k < o mod 2^k]`.
fn add_cap(c: &mut Builder, t: &[Q], o: &[Q], th: &Thr, out: Q) {
    let n = t.len();
    let mut cuts: Vec<(usize, usize)> = th.pairs.iter().map(|&(v, k)| (k, v)).collect();
    cuts.sort();
    let cw = c.alloc_qubit();
    let mut eng: Option<super::engine::Engine> = None;
    let mut ci = 0;
    for i in 0..=n {
        while ci < cuts.len() && cuts[ci].0 == i {
            if eng.is_none() {
                eng = Some(super::engine::Engine::new(c, th.reg, None, th.vwin().0, th.vwin().1));
            }
            let e = eng.as_mut().unwrap();
            e.goto(c, cuts[ci].1);
            match e.leaf() {
                Some(l) => c.ccx(l, cw, out),
                None => c.cx(cw, out),
            }
            ci += 1;
        }
        if ci == cuts.len() {
            if let Some(e) = eng.take() {
                e.finish(c);
            }
        }
        if i < n {
            c.cx(cw, o[i]);
            c.cx(cw, t[i]);
            c.ccx(t[i], o[i], cw);
        }
    }
    if let Some(e) = eng.take() {
        e.finish(c);
    }
    for i in (0..n).rev() {
        c.ccx(t[i], o[i], cw);
        c.cx(cw, t[i]);
        c.cx(o[i], t[i]);
        c.cx(cw, o[i]);
    }
    c.release_clean(cw);
}

/// Capture compare `a` vs `b` at the second cuts with, at the same leaf, `dbit ^= leaf AND a[k]` (the cell at
/// the cut, read before the chain touches it). `phase = Some((m1, m2))`: the phases of both outputs under the
/// measured bits instead (the chain itself unconditional).
fn cap2_dbit(c: &mut Builder, a: &[Q], b: &[Q], th: &Thr, outs: Option<(Q, Q)>,
             phase: Option<(crate::circuit::BitId, crate::circuit::BitId)>) {
    // the chain runs over b's cells (up to the largest cut); a may be one cell longer (the cell read at that cut)
    let n = b.len();
    let a_full = a;
    let a = &a_full[..n];
    let mut cuts: Vec<(usize, usize)> = th.pairs.iter().map(|&(v, k)| (k, v)).collect();
    cuts.sort();
    for &q in a {
        c.x(q);
    }
    let cw = c.alloc_qubit();
    let mut eng: Option<super::engine::Engine> = None;
    let mut ci = 0;
    for i in 0..=n {
        while ci < cuts.len() && cuts[ci].0 == i {
            if eng.is_none() {
                eng = Some(super::engine::Engine::new(c, th.reg, None, th.vwin().0, th.vwin().1));
            }
            let e = eng.as_mut().unwrap();
            e.goto(c, cuts[ci].1);
            let l = e.leaf().expect("cap2: constant leaf");
            match (outs, phase) {
                (Some((cap, db)), None) => {
                    c.ccx(l, cw, cap);
                    if i < n {
                        // a[i] is complemented here: dbit ^= leaf AND NOT(~a[i])
                        c.x(a[i]);
                        c.ccx(l, a[i], db);
                        c.x(a[i]);
                    } else if i < a_full.len() {
                        c.ccx(l, a_full[i], db);
                    }
                }
                (None, Some((m1, m2))) => {
                    c.push_condition(m1);
                    c.cz(l, cw);
                    c.pop_condition();
                    if i < n {
                        c.push_condition(m2);
                        c.x(a[i]);
                        c.cz(l, a[i]);
                        c.x(a[i]);
                        c.pop_condition();
                    } else if i < a_full.len() {
                        c.push_condition(m2);
                        c.cz(l, a_full[i]);
                        c.pop_condition();
                    }
                }
                _ => unreachable!(),
            }
            ci += 1;
        }
        if ci == cuts.len() {
            if let Some(e) = eng.take() {
                e.finish(c);
            }
        }
        if i < n {
            c.cx(cw, b[i]);
            c.cx(cw, a[i]);
            c.ccx(a[i], b[i], cw);
        }
    }
    if let Some(e) = eng.take() {
        e.finish(c);
    }
    for i in (0..n).rev() {
        c.ccx(a[i], b[i], cw);
        c.cx(cw, a[i]);
        c.cx(cw, b[i]);
    }
    c.release_clean(cw);
    for &q in a {
        c.x(q);
    }
}

/// Phase `(-1)^{dbit}`, `dbit = OR over KA values of leaf AND a[cut2]` (an engine sweep, no chain).
fn dbit_phase(c: &mut Builder, a: &[Q], th: &Thr) {
    let mut cuts: Vec<(usize, usize)> = th.pairs.iter().map(|&(v, k)| (k, v)).collect();
    cuts.sort();
    let mut eng = super::engine::Engine::new(c, th.reg, None, th.vwin().0, th.vwin().1);
    for &(k, v) in &cuts {
        if k < a.len() {
            eng.goto(c, v);
            let l = eng.leaf().expect("dbit: constant leaf");
            c.cz(l, a[k]);
        }
    }
    eng.finish(c);
}

/// [`cmp_capture`]'s phase on the cells without pushing a condition (the caller holds one).
fn cmp_capture_phase_nocond(c: &mut Builder, a: &[Q], b: &[Q], th: &Thr) {
    super::mc::cmp_capture_phase_here(c, a, b, Some(th), None);
}

/// Cells of the second capture: `s/4` cells (`A_cof[lo + 2 + i]`) up to the largest second cut, and the `D'`
/// cells one longer (the cell at the cut is read for `dbit`).
fn cap2_cells(r: &Ring, z: &DecZ, xc: &[Q]) -> (Vec<Q>, Vec<Q>) {
    let lo = z.lo();
    let n2 = z.cut2(z.ka.hi);
    let ac = r.acof();
    let y2: Vec<Q> = (0..n2).map(|i| ac[lo + 2 + i]).collect();
    let xa: Vec<Q> = xc[..(n2 + 1).min(xc.len())].to_vec();
    (y2, xa)
}

/// k = 1 state held across the push: `rhi` (holding `[KA < RB'] XOR lt`), `g = [RB' < KA + 2]`, `cap2`,
/// `dbit` and `kill = s[2] AND g AND NOT rhi AND NOT dbit AND cap2`.
struct K1 {
    rhi: Q,
    g: Q,
    cap2: Q,
    dbit: Q,
    kill: super::engine::FAnd,
}

struct Open {
    lt: Q,
    ltc: Q,
    amb: Q,
    rb: Vec<Q>,
    lits: Vec<Lit>,
    k1: Option<K1>,
}

fn open(c: &mut Builder, r: &Ring, z: &DecZ, en: Option<Q>) -> Open {
    let s1 = r.a[r.n - 2];
    let (_, w) = z.off_w();
    ka_off(c, r, z, true);
    // RB' - o first (nothing else held), then the capture with RB' held, then the compare; RB' stays held
    // (narrow where the history is wide) so the compare's measured uncompute needs no second deposit
    let rb = c.alloc_qubits(w);
    rb_dep(c, r, z, &rb);
    super::rwalk::trace(c, "d.lod1", 0);
    let lt = c.alloc_qubit();
    let (xc, yc) = cells(r, z);
    if z.k1 {
        // x -= y in place (x = D'), lt = the borrow at the KA cut
        let th = thr_ka(r, z);
        let o0 = c.op_count();
        c.x_all(&xc);
        add_cap(c, &xc, &yc, &th, lt);
        c.x_all(&xc);
        ac("d_capture", o0, c.op_count());
    } else {
        capture(c, r, z, lt);
    }
    super::rwalk::trace(c, "d.capture", 0);
    let ltc = c.alloc_qubit();
    ltc_cmp(c, r, z, &rb, lt, Some(ltc));
    let mut k1 = None;
    if z.k1 {
        let o0 = c.op_count();
        let kw: Vec<Q> = r.ka[..w].to_vec();
        // cap2 = [D' mod 2^K2 < (s/4) mod 2^K2], dbit = D'[K2]
        let (y2, xa) = cap2_cells(r, z, &xc);
        let cap2 = c.alloc_qubit();
        let dbit = c.alloc_qubit();
        {
            let th2 = thr_ka2(r, z);
            cap2_dbit(c, &xa, &y2, &th2, Some((cap2, dbit)), None);
        }
        // rhi = [KA < RB'] (both offset), then rhi ^= lt
        let rhi = c.alloc_qubit();
        let zq = c.alloc_qubit();
        cmp_cin(c, &kw, &rb, zq, Some(rhi));
        c.release_clean(zq);
        c.cx(lt, rhi);
        // g = [RB' < KA + 2]: KA + 1, carry-in 1
        let g = c.alloc_qubit();
        let rm = room_of(c, r);
        add_k(c, &kw, 1, rm);
        let one = c.alloc_qubit();
        c.x(one);
        cmp_cin(c, &rb, &kw, one, Some(g));
        c.x(one);
        c.release_clean(one);
        let rm = room_of(c, r);
        sub_k(c, &kw, 1, rm);
        let s2 = r.a[r.n - 3];
        let lits = vec![
            Lit { q: s2, pol: true },
            Lit { q: g, pol: true },
            Lit { q: rhi, pol: false },
            Lit { q: dbit, pol: false },
            Lit { q: cap2, pol: true },
        ];
        let kill = super::engine::frozen_and(c, &lits, 3);
        ac("d_k1", o0, c.op_count());
        super::rwalk::trace(c, "d.k1", 0);
        k1 = Some(K1 { rhi, g, cap2, dbit, kill });
    }
    let mut lits = vec![Lit { q: s1, pol: false }, Lit { q: ltc, pol: false }];
    if let Some(k) = &k1 {
        lits.push(Lit { q: k.kill.z, pol: false });
    }
    if let Some(e) = en {
        lits.insert(0, Lit { q: e, pol: true });
    }
    let amb = and_into(c, &lits).unwrap();
    Open { lt, ltc, amb, rb, lits, k1 }
}

fn close(c: &mut Builder, r: &Ring, z: &DecZ, o: Open) {
    and_clear(c, &o.lits, Some(o.amb));
    let (_, w) = z.off_w();
    let (xc, yc) = cells(r, z);
    if let Some(k) = o.k1 {
        let o0 = c.op_count();
        k.kill.clear(c);
        let kw: Vec<Q> = r.ka[..w].to_vec();
        // g
        {
            let m = c.alloc_bit();
            c.hmr(k.g, m);
            c.release_clean(k.g);
            c.push_condition(m);
            let rm = room_of(c, r);
            add_k(c, &kw, 1, rm);
            let one = c.alloc_qubit();
            c.x(one);
            cmp_cin(c, &o.rb, &kw, one, None);
            c.x(one);
            c.release_clean(one);
            let rm = room_of(c, r);
            sub_k(c, &kw, 1, rm);
            c.pop_condition();
            c.free_bit(m);
        }
        // rhi (holds [KA < RB'] XOR lt)
        c.cx(o.lt, k.rhi);
        {
            let m = c.alloc_bit();
            c.hmr(k.rhi, m);
            c.release_clean(k.rhi);
            c.push_condition(m);
            let zq = c.alloc_qubit();
            cmp_cin(c, &kw, &o.rb, zq, None);
            c.release_clean(zq);
            c.pop_condition();
            c.free_bit(m);
        }
        // cap2 and dbit by measurement: cap2's phase from its chain under its bit, dbit's from a bare engine
        // sweep (leaf AND the cell at the cut) under its bit
        {
            let (y2, xa) = cap2_cells(r, z, &xc);
            let th2 = thr_ka2(r, z);
            let m2 = c.alloc_bit();
            c.hmr(k.dbit, m2);
            c.release_clean(k.dbit);
            c.push_condition(m2);
            dbit_phase(c, &xa, &th2);
            c.pop_condition();
            c.free_bit(m2);
            let m1 = c.alloc_bit();
            c.hmr(k.cap2, m1);
            c.release_clean(k.cap2);
            c.push_condition(m1);
            let xa2 = &xa[..y2.len()];
            cmp_capture_phase_nocond(c, xa2, &y2, &th2);
            c.pop_condition();
            c.free_bit(m1);
        }
        ac("d_k1", o0, c.op_count());
    }
    {
        let m = c.alloc_bit();
        c.hmr(o.ltc, m);
        c.release_clean(o.ltc);
        c.push_condition(m);
        ltc_cmp(c, r, z, &o.rb, o.lt, None);
        c.pop_condition();
        c.free_bit(m);
    }
    let o1 = c.op_count();
    if z.k1 {
        // x += y restores r; the carry at the KA cut equals lt and clears it
        let th = thr_ka(r, z);
        add_cap(c, &xc, &yc, &th, o.lt);
        c.release_clean(o.lt);
        ac("d_capture", o1, c.op_count());
        rb_dep(c, r, z, &o.rb);
        for &q in &o.rb {
            c.release_clean(q);
        }
    } else {
        rb_dep(c, r, z, &o.rb);
        for &q in &o.rb {
            c.release_clean(q);
        }
        let o1 = c.op_count();
        let th = thr_ka(r, z);
        let m = c.alloc_bit();
        c.hmr(o.lt, m);
        cmp_capture_phase(c, &xc, &yc, Some(&th), None, m);
        c.free_bit(m);
        c.release_clean(o.lt);
        ac("d_capture", o1, c.op_count());
    }
    super::rwalk::trace(c, "d.lod2", 0);
    ka_off(c, r, z, false);
}

/// `typ ^= D` with `D = en AND NOT s[1]` (`en` None: `D = NOT s[1]`).
fn typ_d(c: &mut Builder, r: &Ring, en: Option<Q>, typ: Q) {
    let s1 = r.a[r.n - 2];
    c.x(s1);
    match en {
        Some(e) => c.ccx(e, s1, typ),
        None => c.cx(s1, typ),
    }
    c.x(s1);
}

/// Forward: erase `typ` (= [A] on an unparked post-state, 0 on a parked one / a C tick) against the post-state,
/// pushing it into `h` on an ambiguous tick. `en` = NOT parked (None: parking impossible at this tick).
pub fn push(c: &mut Builder, r: &Ring, z: &DecZ, en: Option<Q>, typ: Q, h: &Hreg) {
    let o = open(c, r, z, en);
    let a = c.op_count();
    shift_in(c, o.amb, typ, &h.wires);
    ac("push", a, c.op_count());
    typ_d(c, r, en, typ);
    c.cx(o.amb, typ);
    close(c, r, z, o);
}

/// Reverse of [`push`]: recreate `typ` (0 on entry) and pop `h`.
pub fn pop(c: &mut Builder, r: &Ring, z: &DecZ, en: Option<Q>, typ: Q, h: &Hreg) {
    let o = open(c, r, z, en);
    c.cx(o.amb, typ);
    typ_d(c, r, en, typ);
    shift_out(c, o.amb, typ, &h.wires);
    close(c, r, z, o);
}

/// Classical model of the circuit decision (for probes and selftests): `(D, amb)` from the post-state.
/// `acof`, `bcof`: cofactor-order bit vectors of A, B (index j = cofactor bit j); `ka`, `vb` the registers.
pub fn model(acof: &[bool], bcof: &[bool], ka: usize, vb: usize, n: usize, z: &DecZ, en: bool) -> (bool, bool) {
    let d = en && !acof[1];
    let (lo, nc) = (z.lo(), z.ncell());
    let lt = if ka >= z.ka.lo && ka <= z.ka.hi {
        let k = z.cut(ka);
        let mut ltv = false; // borrow of x - y over k cells
        for i in 0..k.min(nc) {
            let (x, y) = (bcof[lo + i], acof[lo + 1 + i]);
            ltv = (!x & y) | (!(x ^ y) & ltv);
        }
        ltv
    } else {
        false
    };
    // RB' = 1 + leading one of B_cof below the cut n - vb (scan floor z.rb.lo), only for cuts in the zone
    let rbp = if vb >= z.vb.lo && vb <= z.vb.hi {
        let cut = n - vb;
        let mut lead = 0usize;
        for j in (z.rb.lo..cut).rev() {
            if bcof[j] {
                lead = j + 1;
                break;
            }
        }
        let lead = if lead == 0 { z.rb.lo.min(cut) } else { lead };
        lead + 1
    } else {
        0
    };
    // the circuit compares RB' - o and KA - o on w bits
    let (o, w) = z.off_w();
    let mask = (1usize << w) - 1;
    let (a, b) = (rbp.wrapping_sub(o) & mask, ka.wrapping_sub(o) & 511 & mask);
    let ltc = a < b + lt as usize;
    let mut amb = d && !ltc;
    if z.k1 && ka >= z.ka.lo && ka <= z.ka.hi {
        // D' = (x - y) mod 2^nc, cap2 = [D' mod 2^K2 < y2 mod 2^K2], dbit = D'[K2]
        let val = |bits: &[bool], off: usize| -> u128 {
            let mut v = 0u128;
            for i in 0..nc.min(127) {
                if off + i < bits.len() && bits[off + i] {
                    v |= 1u128 << i;
                }
            }
            v
        };
        assert!(nc <= 126, "dec model: window too wide for the k1 model");
        let m_nc = (1u128 << nc) - 1;
        let x = val(bcof, lo);
        let y = val(acof, lo + 1);
        let y2 = val(acof, lo + 2);
        let dp = x.wrapping_sub(y) & m_nc;
        let k2 = z.cut2(ka);
        let m2 = (1u128 << k2) - 1;
        let cap2 = (dp & m2) < (y2 & m2);
        let dbit = k2 < nc && (dp >> k2) & 1 == 1;
        let rhi = b < a; // [KA < RB'] on the offset values
        let g = a < b + 2; // [RB' < KA + 2]
        let kill = acof[2] && g && (rhi == lt) && !dbit && cap2;
        amb = amb && !kill;
    }
    (d, amb)
}
