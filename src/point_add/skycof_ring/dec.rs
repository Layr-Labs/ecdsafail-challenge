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

struct Open {
    lt: Q,
    ltc: Q,
    amb: Q,
    rb: Vec<Q>,
    lits: Vec<Lit>,
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
    capture(c, r, z, lt);
    super::rwalk::trace(c, "d.capture", 0);
    let ltc = c.alloc_qubit();
    ltc_cmp(c, r, z, &rb, lt, Some(ltc));
    let mut lits = vec![Lit { q: s1, pol: false }, Lit { q: ltc, pol: false }];
    if let Some(e) = en {
        lits.insert(0, Lit { q: e, pol: true });
    }
    let amb = and_into(c, &lits).unwrap();
    Open { lt, ltc, amb, rb, lits }
}

fn close(c: &mut Builder, r: &Ring, z: &DecZ, o: Open) {
    and_clear(c, &o.lits, Some(o.amb));
    {
        let m = c.alloc_bit();
        c.hmr(o.ltc, m);
        c.release_clean(o.ltc);
        c.push_condition(m);
        ltc_cmp(c, r, z, &o.rb, o.lt, None);
        c.pop_condition();
        c.free_bit(m);
    }
    rb_dep(c, r, z, &o.rb);
    for &q in &o.rb {
        c.release_clean(q);
    }
    super::rwalk::trace(c, "d.lod2", 0);
    let o1 = c.op_count();
    {
        let (xc, yc) = cells(r, z);
        let th = thr_ka(r, z);
        let m = c.alloc_bit();
        c.hmr(o.lt, m);
        cmp_capture_phase(c, &xc, &yc, Some(&th), None, m);
        c.free_bit(m);
        c.release_clean(o.lt);
    }
    ac("d_capture", o1, c.op_count());
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
    (d, d && !ltc)
}
