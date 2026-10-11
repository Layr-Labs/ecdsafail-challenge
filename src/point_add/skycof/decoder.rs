//! SKY-COF letter decoder and history accumulator.
//!
//! # The walk this serves
//!
//! Kaliski-frame cofactors `(s, r)` with `u*s + v*r = p`, `s` even and `r` odd on every
//! post-state, start `(0, 1)`. Letters: A `(s, r) <- (2s, r)`, B `(2s, r + s)`,
//! C `(2r, r + s)`; parked ticks (`u = 0`) only double `s` mod p.
//!
//! On the post-state of tick `t >= 1`:
//! * C iff `bit1(s) = 1` (exact);
//! * not C and `2r < s`  =>  A (after B, `2r' = 2r + 2s >= s'`);
//! * not C and `2r >= s`: A or B -- the ambiguous tick; one bit (`typ = [letter == A]`)
//!   is pushed into `Hreg`.
//!
//! # The windowed compare (conservative, exact on the field)
//!
//! `e` = public field width of the cofactor registers (values `< 2^e`), `w` = window bits,
//! `lo = max(1, e - w)`, `n = e - lo`. With `x = r[lo..e]` (n bits) and `y = s[lo+1..e]`
//! (n - 1 bits), `ge = [x >= y]`. `ge = 0` proves `2r < s` (certain A); `ge = 1` is "maybe
//! B" (ambiguous). For `e - w >= 1` this is the deciders' `k = 0, w` test
//! (`st <= 2*rt + 1` with `st = s >> b`, `rt = r >> b`, `b = e - w`) exactly; for `e <= w`
//! it equals the exact `2r >= s` because `r` is odd (bit 0 of the compare is decided).
//!
//! The compare is a carry chain of `x + ~y + 1` over n bits. Two constant wires of the
//! post-state are used instead of fresh ones: `r[0] = 1` (r odd) is the carry-in, and
//! `s[0] = 0` (s even, any non-parked post-state), inverted, is the top bit of `~y` (y is
//! zero-padded). The low `j` bits use Gidney carries on fresh wires (1 CCX per bit, erased
//! by measurement for free); the remaining `n - j` bits are an in-place Cuccaro MAJ chain
//! (1 CCX per bit forward, 1 back). `j` is set by the room the caller grants.
//!
//! `D = en & !bit1(s)` (or `!bit1(s)` in place when no `en` wire is given), `amb = D & ge`.
//! The chain is held while the accumulator moves, so `amb` and `D` are erased by
//! measurement (CZ repairs) and nothing is recomputed.
//!
//! # Toffoli per call (exact, checked by the selftest)
//!
//! `[park] + [en] + j + 2 (n - j) + 1 + m`, where `m = Hreg` width (the controlled shift:
//! `m` Fredkins). Fresh wires held: `1 (amb) + [en] (D) + j`.
//! At `n = 64`: full room (`room >= n + 1 + [en]`) `n + 2 + [en] + [park] + m`, i.e. 66..67
//! plus `m`; floor (`room = 1 + [en]`) `2n + 1 + [en] + [park] + m`, i.e. 129..131 plus `m`.
//!
//! # Contract with the integration
//!
//! * `s`, `r` hold the post-state; `s.len(), r.len() >= e`; wires above `e` are not read.
//!   Values must fit in `e` bits (field envelope) for the decision to be meaningful.
//! * `en` (optional): 1 on a tick where the walk is not parked (u != 0 after the tick),
//!   0 on the park tick and after it. Omit it only on ticks where parking is impossible.
//!   When `en = 0` the decoder pushes nothing and leaves `typ` untouched (the caller keeps
//!   `typ = 0` there; the park tick's letter is B, so its `typ` is 0 anyway).
//! * `typ` = `[letter == A]`, `cflag` = `[letter == C]`, both erased by [`push`].
//! * `park = (flag, bit)`: `flag = 1` exactly on the park tick (requires `en = 0`); `bit`
//!   is the one rail bit the letters do not determine there (the add-sign / agree wire).
//!   It is pushed into `Hreg` through the same shift (1 extra CCX per call that carries the
//!   option). [`park_stash`] is the alternative: one Fredkin into a dedicated wire.
//! * `Hreg` width at tick `t` must bound the number of pushes up to and including `t`
//!   (its top wire is 0 before a push). Exceeding it is an envelope failure.
//! * Tick 0 (B impossible): use [`first_tick`] (0 CCX, self-inverse).
//!
//! [`pop`] is the exact inverse of [`push`] on the same post-state: it recomputes every
//! decision from `(s, r, en)` and restores `typ`, `cflag`, the park bit and `Hreg` (LIFO).

use crate::circuit::QubitId as Q;
use crate::point_add::builder::Builder;

/// Window bits and the scratch budget of one call.
#[derive(Clone, Copy, Debug)]
pub struct DecCfg {
    /// Window width `w` (the deciders' choice is 64).
    pub w: usize,
    /// Fresh wires this call may hold at once (amb + D + Gidney carries). Minimum `1 + [en]`.
    pub room: usize,
}

/// Window geometry: `x = r[lo..e]`, `y = s[lo+1..e]`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Window {
    pub lo: usize,
    pub e: usize,
}

impl Window {
    pub fn new(e: usize, w: usize) -> Self {
        assert!(e >= 2, "skycof decoder: field width {e} < 2");
        assert!(w >= 1, "skycof decoder: window 0");
        Window {
            lo: e.saturating_sub(w).max(1),
            e,
        }
    }
    /// Compare width (bits of x).
    pub fn n(&self) -> usize {
        self.e - self.lo
    }
}

/// Wires of one decoder call. See the module doc for the contract.
#[derive(Clone, Copy, Debug)]
pub struct TickIo<'a> {
    pub s: &'a [Q],
    pub r: &'a [Q],
    pub e: usize,
    pub en: Option<Q>,
    pub typ: Q,
    pub cflag: Option<Q>,
    /// `(flag, bit)`: push `bit` on the park tick.
    pub park: Option<(Q, Q)>,
}

/// The history accumulator: `wires[0]` holds the most recent push (LSB of `Hreg`).
#[derive(Clone, Debug, Default)]
pub struct Hreg {
    pub wires: Vec<Q>,
}

impl Hreg {
    pub fn new() -> Self {
        Hreg { wires: Vec::new() }
    }
    pub fn len(&self) -> usize {
        self.wires.len()
    }
    pub fn is_empty(&self) -> bool {
        self.wires.is_empty()
    }
    /// Widen to `m` wires (fresh zeros on top).
    pub fn grow_to(&mut self, c: &mut Builder, m: usize) {
        while self.wires.len() < m {
            let q = c.alloc_qubit();
            self.wires.push(q);
        }
    }
    /// Narrow to `m` wires; the dropped top wires must be 0 (the envelope's promise).
    pub fn shrink_to(&mut self, c: &mut Builder, m: usize) {
        while self.wires.len() > m {
            let q = self.wires.pop().unwrap();
            c.free(q);
        }
    }
}

/// Exact Toffoli count of one [`push`] / [`pop`] call.
pub fn toffoli_cost(e: usize, w: usize, m: usize, room: usize, en: bool, park: bool) -> usize {
    let n = Window::new(e, w).n();
    let j = gidney_bits(n, room, en);
    park as usize + en as usize + j + 2 * (n - j) + 1 + m
}

/// Peak fresh wires held by one call.
pub fn scratch_cost(e: usize, w: usize, room: usize, en: bool) -> usize {
    let n = Window::new(e, w).n();
    1 + en as usize + gidney_bits(n, room, en)
}

/// Minimum `room` for a call.
pub fn min_room(en: bool) -> usize {
    1 + en as usize
}

fn gidney_bits(n: usize, room: usize, en: bool) -> usize {
    let fixed = min_room(en);
    assert!(
        room >= fixed,
        "skycof decoder: room {room} below the floor {fixed}"
    );
    n.min(room - fixed)
}

fn fredkin(c: &mut Builder, ctrl: Q, a: Q, b: Q) {
    c.cx(b, a);
    c.ccx(ctrl, a, b);
    c.cx(b, a);
}

fn meas_cz(c: &mut Builder, t: Q, a: Q, b: Q) {
    let m = c.alloc_bit();
    c.hmr(t, m);
    c.cz_if(a, b, m);
    c.free_bit(m);
    c.release_clean(t);
}

/// Live state of one decode: `amb` (and `D`) computed, the compare chain held.
pub struct Scope {
    win: Window,
    j: usize,
    /// Wire holding `D` (a fresh wire when `en` is given, else `s[1]` inverted in place).
    pub d: Q,
    d_fresh: bool,
    /// Wire holding `ge` (fresh top Gidney carry, or the in-place top MAJ wire).
    pub ge: Q,
    /// `amb = D & ge`, fresh.
    pub amb: Q,
    gid: Vec<Q>,
    a: Vec<Q>,
    bb: Vec<Q>,
    r0: Q,
}

impl Scope {
    fn cin(&self, i: usize) -> Q {
        // carry entering bit i
        if i == 0 {
            self.r0
        } else if i <= self.j {
            self.gid[i - 1]
        } else {
            self.a[i - 1]
        }
    }
}

/// Compare scope for the binding enabled decoder with `amb = D & ge` kept
/// virtual.  The caller supplies an arbitrary dirty borrower for each use of
/// that predicate; the borrower is restored after every controlled action.
pub struct BorrowScope {
    win: Window,
    j: usize,
    pub d: Q,
    d_fresh: bool,
    d_r0_host: bool,
    pub ge: Q,
    gid: Vec<Q>,
    a: Vec<Q>,
    bb: Vec<Q>,
    r0: Q,
}

impl BorrowScope {
    fn cin(&self, i: usize) -> Q {
        if i == 0 {
            self.r0
        } else if i <= self.j {
            self.gid[i - 1]
        } else {
            self.a[i - 1]
        }
    }
}

struct GeScope {
    win: Window,
    j: usize,
    ge: Q,
    gid: Vec<Q>,
    a: Vec<Q>,
    bb: Vec<Q>,
    r0: Q,
}

impl GeScope {
    fn cin(&self, i: usize) -> Q {
        if i == 0 { self.r0 } else if i <= self.j { self.gid[i - 1] } else { self.a[i - 1] }
    }
}

fn open_ge_fixture(c: &mut Builder, io: &TickIo, cfg: DecCfg, dirty: &[Q; 2]) -> GeScope {
    let win = Window::new(io.e, cfg.w);
    let n = win.n();
    let j = gidney_bits(n, cfg.room, true);
    let a: Vec<Q> = (0..n).map(|i| io.r[win.lo + i]).collect();
    let bb: Vec<Q> = (0..n)
        .map(|i| if i + 1 < n { io.s[win.lo + 1 + i] } else { io.s[0] })
        .collect();
    assert!(dirty.iter().all(|q| !io.s.contains(q) && !io.r.contains(q) && *q != io.typ));
    c.x_all(&bb);
    let mut sc = GeScope { win, j, ge: io.r[0], gid: Vec::with_capacity(j), a, bb, r0: io.r[0] };
    for i in 0..j {
        let ci = sc.cin(i);
        c.cx(ci, sc.a[i]); c.cx(ci, sc.bb[i]);
        let t = c.alloc_qubit();
        c.ccx(sc.a[i], sc.bb[i], t); c.cx(ci, t);
        sc.gid.push(t);
    }
    for i in j..n {
        let ci = sc.cin(i);
        c.cx(sc.a[i], sc.bb[i]); c.cx(sc.a[i], ci); c.ccx(ci, sc.bb[i], sc.a[i]);
    }
    sc.ge = if j == n { sc.gid[n - 1] } else { sc.a[n - 1] };
    assert!(dirty[0] != sc.ge && dirty[1] != sc.ge);
    sc
}

fn close_ge_fixture(c: &mut Builder, sc: GeScope) {
    let n = sc.win.n();
    for i in (sc.j..n).rev() {
        let ci = sc.cin(i);
        c.ccx(ci, sc.bb[i], sc.a[i]); c.cx(sc.a[i], ci); c.cx(sc.a[i], sc.bb[i]);
    }
    for i in (0..sc.j).rev() {
        let ci = sc.cin(i);
        let t = sc.gid[i];
        c.cx(ci, t); meas_cz(c, t, sc.a[i], sc.bb[i]); c.cx(ci, sc.a[i]); c.cx(ci, sc.bb[i]);
    }
    c.x_all(&sc.bb);
}

fn dirty_mcx_fixture(c: &mut Builder, controls: &[Q], target: Q, dirty: &[Q; 2]) {
    match controls.len() {
        0 => c.x(target),
        1 => c.cx(controls[0], target),
        2 => c.ccx(controls[0], controls[1], target),
        m => {
            let d = &dirty[..m - 2];
            assert!(m <= 4);
            assert!(controls.iter().all(|q| *q != target && !d.contains(q)));
            assert!(!d.contains(&target));
            for bottom in [true, false] {
                if bottom { c.ccx(controls[0], controls[1], d[0]); }
                for i in 1..d.len() { c.ccx(d[i - 1], controls[i + 1], d[i]); }
                c.ccx(*d.last().unwrap(), *controls.last().unwrap(), target);
                for i in (1..d.len()).rev() { c.ccx(d[i - 1], controls[i + 1], d[i]); }
                if bottom { c.ccx(controls[0], controls[1], d[0]); }
            }
        }
    }
}

fn virtual_d_xor(c: &mut Builder, io: &TickIo, target: Q) {
    let en = io.en.expect("virtual D requires enabled decoder");
    c.x(io.s[1]); c.ccx(en, io.s[1], target); c.x(io.s[1]);
}

fn virtual_amb_xor(c: &mut Builder, io: &TickIo, ge: Q, target: Q, dirty: &[Q; 2]) {
    let en = io.en.expect("virtual amb requires enabled decoder");
    c.x(io.s[1]);
    dirty_mcx_fixture(c, &[en, io.s[1], ge], target, dirty);
    c.x(io.s[1]);
}

fn virtual_amb_fredkin(c: &mut Builder, io: &TickIo, ge: Q, x: Q, y: Q, dirty: &[Q; 2]) {
    let en = io.en.expect("virtual amb requires enabled decoder");
    c.cx(y, x);
    c.x(io.s[1]);
    dirty_mcx_fixture(c, &[en, io.s[1], ge, x], y, dirty);
    c.x(io.s[1]);
    c.cx(y, x);
}

fn mcx3_dirty(c: &mut Builder, a: Q, b: Q, d: Q, target: Q, dirty: Q) {
    assert!(a != b && a != d && b != d);
    assert!(target != a && target != b && target != d);
    assert!(dirty != a && dirty != b && dirty != d && dirty != target);
    c.ccx(a, b, dirty);
    c.ccx(dirty, d, target);
    c.ccx(a, b, dirty);
    c.ccx(dirty, d, target);
}

fn assert_borrow_disjoint(io: &TickIo, h: &Hreg, q: Q) {
    assert!(io.cflag.is_none(), "borrowed ambiguity cflag unsupported");
    assert!(io.park.is_none(), "borrowed ambiguity park unsupported");
    assert!(q != io.typ && io.en != Some(q));
    assert!(!io.s.contains(&q) && !io.r.contains(&q));
    assert!(!h.wires.contains(&q));
}

/// Compute D and the original compare core, but do not allocate/materialize
/// `amb`.  Geometry and Gidney/Cuccaro selection intentionally match [`open`].
fn open_borrow(c: &mut Builder, io: &TickIo, h: &Hreg, cfg: DecCfg, q: Q) -> BorrowScope {
    assert_borrow_disjoint(io, h, q);
    assert_eq!(
        c.tracked_condition_depth(),
        Some(0),
        "borrowed ambiguity requires an empty outer condition stack"
    );
    let win = Window::new(io.e, cfg.w);
    assert!(io.s.len() >= io.e && io.r.len() >= io.e);
    let n = win.n();
    let j = gidney_bits(n, cfg.room, io.en.is_some());
    let s1 = io.s[1];
    let (d, d_fresh) = if let Some(en) = io.en {
        let d = c.alloc_qubit();
        c.x(s1);
        c.ccx(en, s1, d);
        c.x(s1);
        (d, true)
    } else {
        c.x(s1);
        (s1, false)
    };
    let a: Vec<Q> = (0..n).map(|i| io.r[win.lo + i]).collect();
    let bb: Vec<Q> = (0..n)
        .map(|i| {
            if i + 1 < n {
                io.s[win.lo + 1 + i]
            } else {
                io.s[0]
            }
        })
        .collect();
    c.x_all(&bb);
    let mut sc = BorrowScope {
        win,
        j,
        d,
        d_fresh,
        d_r0_host: false,
        ge: io.r[0],
        gid: Vec::with_capacity(j),
        a,
        bb,
        r0: io.r[0],
    };
    for i in 0..j {
        let ci = sc.cin(i);
        c.cx(ci, sc.a[i]);
        c.cx(ci, sc.bb[i]);
        let t = c.alloc_qubit();
        c.ccx(sc.a[i], sc.bb[i], t);
        c.cx(ci, t);
        sc.gid.push(t);
    }
    for i in j..n {
        let ci = sc.cin(i);
        c.cx(sc.a[i], sc.bb[i]);
        c.cx(sc.a[i], ci);
        c.ccx(ci, sc.bb[i], sc.a[i]);
    }
    sc.ge = if j == n {
        sc.gid[n - 1]
    } else {
        sc.a[n - 1]
    };
    assert!(q != sc.d && q != sc.ge);
    sc
}

fn close_borrow(c: &mut Builder, io: &TickIo, sc: BorrowScope) {
    if sc.d_r0_host {
        let s1 = io.s[1];
        let en = io.en.expect("r0-hosted D requires enabled decoder");
        c.x(s1);
        c.ccx(en, s1, sc.r0);
        c.x(s1);
        c.x(sc.r0);
    }
    let n = sc.win.n();
    for i in (sc.j..n).rev() {
        let ci = sc.cin(i);
        c.ccx(ci, sc.bb[i], sc.a[i]);
        c.cx(sc.a[i], ci);
        c.cx(sc.a[i], sc.bb[i]);
    }
    for i in (0..sc.j).rev() {
        let ci = sc.cin(i);
        let t = sc.gid[i];
        c.cx(ci, t);
        meas_cz(c, t, sc.a[i], sc.bb[i]);
        c.cx(ci, sc.a[i]);
        c.cx(ci, sc.bb[i]);
    }
    c.x_all(&sc.bb);
    let s1 = io.s[1];
    if sc.d_fresh {
        let en = io.en.unwrap();
        let m = c.alloc_bit();
        c.hmr(sc.d, m);
        c.x(s1);
        c.cz_if(en, s1, m);
        c.x(s1);
        c.free_bit(m);
        c.release_clean(sc.d);
    } else if !sc.d_r0_host {
        c.x(s1);
    }
}

/// Isolated R6-B fixture scope. Build the compare first with logical r0=1 as
/// its carry seed, forcing at least the first carry to the non-mutating Gidney
/// form. Once ge is held, turn the restored r0 owner into D=en&!s1. The close
/// path restores r0=1 before unwinding the compare. Production dispatch does
/// not call this API pending the R6 gate.
fn open_borrow_r0_d(
    c: &mut Builder,
    io: &TickIo,
    h: &Hreg,
    cfg: DecCfg,
    q: Q,
) -> BorrowScope {
    assert_borrow_disjoint(io, h, q);
    let en = io.en.expect("r0-hosted D requires enabled decoder");
    assert_eq!(c.tracked_condition_depth(), Some(0));
    let win = Window::new(io.e, cfg.w);
    assert!(io.s.len() >= io.e && io.r.len() >= io.e);
    let n = win.n();
    let j = n.min(cfg.room.saturating_sub(1).max(1));
    let a: Vec<Q> = (0..n).map(|i| io.r[win.lo + i]).collect();
    let bb: Vec<Q> = (0..n)
        .map(|i| if i + 1 < n { io.s[win.lo + 1 + i] } else { io.s[0] })
        .collect();
    c.x_all(&bb);
    let r0 = io.r[0];
    assert!(q != r0 && io.typ != r0 && en != r0);
    let mut sc = BorrowScope {
        win,
        j,
        d: r0,
        d_fresh: false,
        d_r0_host: true,
        ge: r0,
        gid: Vec::with_capacity(j),
        a,
        bb,
        r0,
    };
    for i in 0..j {
        let ci = sc.cin(i);
        c.cx(ci, sc.a[i]);
        c.cx(ci, sc.bb[i]);
        let t = c.alloc_qubit();
        c.ccx(sc.a[i], sc.bb[i], t);
        c.cx(ci, t);
        sc.gid.push(t);
    }
    for i in j..n {
        let ci = sc.cin(i);
        c.cx(sc.a[i], sc.bb[i]);
        c.cx(sc.a[i], ci);
        c.ccx(ci, sc.bb[i], sc.a[i]);
    }
    sc.ge = if j == n { sc.gid[n - 1] } else { sc.a[n - 1] };
    let s1 = io.s[1];
    c.x(r0);
    c.x(s1);
    c.ccx(en, s1, r0);
    c.x(s1);
    assert!(q != sc.ge && r0 != sc.ge);
    sc
}

/// Apply a Fredkin whose control is the virtual predicate `d & ge`, using an
/// arbitrary dirty borrower `q`.  The two dirty echoes cancel q's unknown
/// initial contribution and restore q exactly.
fn fredkin_virtual_amb(c: &mut Builder, q: Q, d: Q, ge: Q, x: Q, y: Q) {
    assert!(q != d && q != ge && q != x && q != y);
    c.cx(y, x);
    c.ccx(d, ge, q);
    c.ccx(q, x, y);
    c.ccx(d, ge, q);
    c.ccx(q, x, y);
    c.cx(y, x);
}

fn shift_in_borrow(c: &mut Builder, q: Q, d: Q, ge: Q, typ: Q, h: &[Q]) {
    for i in (1..h.len()).rev() {
        fredkin_virtual_amb(c, q, d, ge, h[i], h[i - 1]);
    }
    if let Some(&h0) = h.first() {
        fredkin_virtual_amb(c, q, d, ge, h0, typ);
    }
}

fn shift_out_borrow(c: &mut Builder, q: Q, d: Q, ge: Q, typ: Q, h: &[Q]) {
    if let Some(&h0) = h.first() {
        fredkin_virtual_amb(c, q, d, ge, h0, typ);
    }
    for i in 1..h.len() {
        fredkin_virtual_amb(c, q, d, ge, h[i], h[i - 1]);
    }
}

/// Compute `D`, the compare chain and `amb` (see the module doc). Pair with [`close`].
pub fn open(c: &mut Builder, io: &TickIo, cfg: DecCfg) -> Scope {
    let win = Window::new(io.e, cfg.w);
    assert!(
        io.s.len() >= io.e && io.r.len() >= io.e,
        "skycof decoder: registers narrower than the field"
    );
    let n = win.n();
    let j = gidney_bits(n, cfg.room, io.en.is_some());
    let s1 = io.s[1];
    let (d, d_fresh) = match io.en {
        Some(en) => {
            let d = c.alloc_qubit();
            c.x(s1);
            c.ccx(en, s1, d);
            c.x(s1);
            (d, true)
        }
        None => {
            c.x(s1);
            (s1, false)
        }
    };
    let a: Vec<Q> = (0..n).map(|i| io.r[win.lo + i]).collect();
    let bb: Vec<Q> = (0..n)
        .map(|i| {
            if i + 1 < n {
                io.s[win.lo + 1 + i]
            } else {
                io.s[0]
            }
        })
        .collect();
    c.x_all(&bb);
    let mut sc = Scope {
        win,
        j,
        d,
        d_fresh,
        ge: io.r[0],
        amb: io.r[0],
        gid: Vec::with_capacity(j),
        a,
        bb,
        r0: io.r[0],
    };
    for i in 0..j {
        let ci = sc.cin(i);
        c.cx(ci, sc.a[i]);
        c.cx(ci, sc.bb[i]);
        let t = c.alloc_qubit();
        c.ccx(sc.a[i], sc.bb[i], t);
        c.cx(ci, t);
        sc.gid.push(t);
    }
    for i in j..n {
        let ci = sc.cin(i);
        c.cx(sc.a[i], sc.bb[i]);
        c.cx(sc.a[i], ci);
        c.ccx(ci, sc.bb[i], sc.a[i]);
    }
    sc.ge = if j == n { sc.gid[n - 1] } else { sc.a[n - 1] };
    sc.amb = c.alloc_qubit();
    c.ccx(sc.d, sc.ge, sc.amb);
    sc
}

/// Erase `amb`, the chain and `D` (0 CCX for the measured parts, `n - j` for the MAJ chain).
pub fn close(c: &mut Builder, io: &TickIo, sc: Scope) {
    meas_cz(c, sc.amb, sc.d, sc.ge);
    let n = sc.win.n();
    for i in (sc.j..n).rev() {
        let ci = sc.cin(i);
        c.ccx(ci, sc.bb[i], sc.a[i]);
        c.cx(sc.a[i], ci);
        c.cx(sc.a[i], sc.bb[i]);
    }
    for i in (0..sc.j).rev() {
        let ci = sc.cin(i);
        let t = sc.gid[i];
        c.cx(ci, t);
        meas_cz(c, t, sc.a[i], sc.bb[i]);
        c.cx(ci, sc.a[i]);
        c.cx(ci, sc.bb[i]);
    }
    c.x_all(&sc.bb);
    let s1 = io.s[1];
    if sc.d_fresh {
        let en = io.en.unwrap();
        let m = c.alloc_bit();
        c.hmr(sc.d, m);
        c.x(s1);
        c.cz_if(en, s1, m);
        c.x(s1);
        c.free_bit(m);
        c.release_clean(sc.d);
    } else {
        c.x(s1);
    }
}

/// `cflag ^= [letter C] = en & bit1(s)` (self-inverse; 0 CCX).
fn cflag_flip(c: &mut Builder, io: &TickIo, sc: &Scope) {
    if let Some(cf) = io.cflag {
        match io.en {
            Some(en) => {
                c.cx(en, cf);
                c.cx(sc.d, cf);
            }
            None => {
                c.cx(sc.d, cf);
                c.x(cf);
            }
        }
    }
}

/// `Hreg <- 2 Hreg + typ`, `typ <- old top wire`, controlled on `ctrl` (m Fredkins).
pub fn shift_in(c: &mut Builder, ctrl: Q, typ: Q, h: &[Q]) {
    let m = h.len();
    if m == 0 {
        return;
    }
    for i in (1..m).rev() {
        fredkin(c, ctrl, h[i], h[i - 1]);
    }
    fredkin(c, ctrl, h[0], typ);
}

/// Inverse of [`shift_in`].
pub fn shift_out(c: &mut Builder, ctrl: Q, typ: Q, h: &[Q]) {
    let m = h.len();
    if m == 0 {
        return;
    }
    fredkin(c, ctrl, h[0], typ);
    for i in 1..m {
        fredkin(c, ctrl, h[i], h[i - 1]);
    }
}

/// Forward: erase the tick's letter wires from the post-state, pushing `typ` on an
/// ambiguous tick (and the park bit on the park tick).
pub fn push(c: &mut Builder, io: &TickIo, h: &Hreg, cfg: DecCfg) {
    if let Some((flag, bit)) = io.park {
        fredkin(c, flag, bit, io.typ);
    }
    let sc = open(c, io, cfg);
    if let Some((flag, _)) = io.park {
        c.cx(flag, sc.amb);
    }
    shift_in(c, sc.amb, io.typ, &h.wires);
    if let Some((flag, _)) = io.park {
        c.cx(flag, sc.amb);
    }
    c.cx(sc.d, io.typ);
    c.cx(sc.amb, io.typ);
    cflag_flip(c, io, &sc);
    close(c, io, sc);
}

/// Reverse: recreate the tick's letter wires (`typ`, `cflag`, park bit; all 0 on entry)
/// from the same post-state, popping `Hreg` where the forward pass pushed.
pub fn pop(c: &mut Builder, io: &TickIo, h: &Hreg, cfg: DecCfg) {
    let sc = open(c, io, cfg);
    cflag_flip(c, io, &sc);
    c.cx(sc.amb, io.typ);
    c.cx(sc.d, io.typ);
    if let Some((flag, _)) = io.park {
        c.cx(flag, sc.amb);
    }
    shift_out(c, sc.amb, io.typ, &h.wires);
    if let Some((flag, _)) = io.park {
        c.cx(flag, sc.amb);
    }
    close(c, io, sc);
    if let Some((flag, bit)) = io.park {
        fredkin(c, flag, bit, io.typ);
    }
}

/// Binding enabled-decoder specialization with virtual `amb = D & ge`.
/// `borrower` may hold an arbitrary quantum value and is restored exactly.
pub fn push_borrow_amb(c: &mut Builder, io: &TickIo, h: &Hreg, cfg: DecCfg, borrower: Q) {
    let sc = open_borrow(c, io, h, cfg, borrower);
    shift_in_borrow(c, borrower, sc.d, sc.ge, io.typ, &h.wires);
    c.cx(sc.d, io.typ);
    c.ccx(sc.d, sc.ge, io.typ);
    close_borrow(c, io, sc);
}

/// Exact inverse of [`push_borrow_amb`].
pub fn pop_borrow_amb(c: &mut Builder, io: &TickIo, h: &Hreg, cfg: DecCfg, borrower: Q) {
    let sc = open_borrow(c, io, h, cfg, borrower);
    c.ccx(sc.d, sc.ge, io.typ);
    c.cx(sc.d, io.typ);
    shift_out_borrow(c, borrower, sc.d, sc.ge, io.typ, &h.wires);
    close_borrow(c, io, sc);
}

pub(crate) fn push_borrow_amb_r0_d_fixture(
    c: &mut Builder,
    io: &TickIo,
    h: &Hreg,
    cfg: DecCfg,
    borrower: Q,
) {
    let sc = open_borrow_r0_d(c, io, h, cfg, borrower);
    shift_in_borrow(c, borrower, sc.d, sc.ge, io.typ, &h.wires);
    c.cx(sc.d, io.typ);
    c.ccx(sc.d, sc.ge, io.typ);
    close_borrow(c, io, sc);
}

pub(crate) fn pop_borrow_amb_r0_d_fixture(
    c: &mut Builder,
    io: &TickIo,
    h: &Hreg,
    cfg: DecCfg,
    borrower: Q,
) {
    let sc = open_borrow_r0_d(c, io, h, cfg, borrower);
    c.ccx(sc.d, sc.ge, io.typ);
    c.cx(sc.d, io.typ);
    shift_out_borrow(c, borrower, sc.d, sc.ge, io.typ, &h.wires);
    close_borrow(c, io, sc);
}

pub(crate) fn push_virtual_d_amb_fixture(
    c: &mut Builder,
    io: &TickIo,
    h: &Hreg,
    cfg: DecCfg,
    dirty: [Q; 2],
) {
    assert!(io.en.is_some() && io.cflag.is_none() && io.park.is_none());
    assert!(dirty[0] != dirty[1]);
    assert!(dirty.iter().all(|q| io.en != Some(*q) && !h.wires.contains(q)));
    let sc = open_ge_fixture(c, io, cfg, &dirty);
    for i in (1..h.wires.len()).rev() {
        virtual_amb_fredkin(c, io, sc.ge, h.wires[i], h.wires[i - 1], &dirty);
    }
    if let Some(&h0) = h.wires.first() {
        virtual_amb_fredkin(c, io, sc.ge, h0, io.typ, &dirty);
    }
    virtual_d_xor(c, io, io.typ);
    virtual_amb_xor(c, io, sc.ge, io.typ, &dirty);
    close_ge_fixture(c, sc);
}

pub(crate) fn pop_virtual_d_amb_fixture(
    c: &mut Builder,
    io: &TickIo,
    h: &Hreg,
    cfg: DecCfg,
    dirty: [Q; 2],
) {
    assert!(io.en.is_some() && io.cflag.is_none() && io.park.is_none());
    assert!(dirty[0] != dirty[1]);
    assert!(dirty.iter().all(|q| io.en != Some(*q) && !h.wires.contains(q)));
    let sc = open_ge_fixture(c, io, cfg, &dirty);
    virtual_amb_xor(c, io, sc.ge, io.typ, &dirty);
    virtual_d_xor(c, io, io.typ);
    if let Some(&h0) = h.wires.first() {
        virtual_amb_fredkin(c, io, sc.ge, h0, io.typ, &dirty);
    }
    for i in 1..h.wires.len() {
        virtual_amb_fredkin(c, io, sc.ge, h.wires[i], h.wires[i - 1], &dirty);
    }
    close_ge_fixture(c, sc);
}

pub(crate) fn push_virtual_d_fresh_amb_fixture(
    c: &mut Builder,
    io: &TickIo,
    h: &Hreg,
    cfg: DecCfg,
    dirty: Q,
) {
    let en = io.en.expect("R8 requires enabled decoder");
    assert!(io.cflag.is_none() && io.park.is_none());
    assert!(dirty != en && dirty != io.typ && !io.s.contains(&dirty)
        && !io.r.contains(&dirty) && !h.wires.contains(&dirty));
    let sc = open_ge_fixture(c, io, cfg, &[dirty, dirty]);
    let amb = c.alloc_qubit();
    assert!(amb != dirty && amb != en && amb != io.s[1] && amb != sc.ge && amb != io.typ);
    c.x(io.s[1]);
    mcx3_dirty(c, en, io.s[1], sc.ge, amb, dirty);
    shift_in(c, amb, io.typ, &h.wires);
    c.ccx(en, io.s[1], io.typ);
    c.cx(amb, io.typ);
    mcx3_dirty(c, en, io.s[1], sc.ge, amb, dirty);
    c.x(io.s[1]);
    c.release_clean(amb);
    close_ge_fixture(c, sc);
}

pub(crate) fn pop_virtual_d_fresh_amb_fixture(
    c: &mut Builder,
    io: &TickIo,
    h: &Hreg,
    cfg: DecCfg,
    dirty: Q,
) {
    let en = io.en.expect("R8 requires enabled decoder");
    assert!(io.cflag.is_none() && io.park.is_none());
    assert!(dirty != en && dirty != io.typ && !io.s.contains(&dirty)
        && !io.r.contains(&dirty) && !h.wires.contains(&dirty));
    let sc = open_ge_fixture(c, io, cfg, &[dirty, dirty]);
    let amb = c.alloc_qubit();
    assert!(amb != dirty && amb != en && amb != io.s[1] && amb != sc.ge && amb != io.typ);
    c.x(io.s[1]);
    mcx3_dirty(c, en, io.s[1], sc.ge, amb, dirty);
    c.cx(amb, io.typ);
    c.ccx(en, io.s[1], io.typ);
    shift_out(c, amb, io.typ, &h.wires);
    mcx3_dirty(c, en, io.s[1], sc.ge, amb, dirty);
    c.x(io.s[1]);
    c.release_clean(amb);
    close_ge_fixture(c, sc);
}

/// Research-only implicit-R0 floor-comparator scope. Logical r[0]=1 is
/// omitted physically. On enabled lanes s[0]=0, so X(s[0]) supplies the exact
/// carry-one seed. The synthetic constant-one top step is left virtual:
/// ge = top_a OR carry_into_top.
struct ImplicitR0GeScope {
    a: Vec<Q>,
    bb: Vec<Q>,
    s0: Q,
    top_a: Q,
    top_carry: Q,
}

fn open_implicit_r0_ge_fixture(c: &mut Builder, io: &TickIo, cfg: DecCfg) -> ImplicitR0GeScope {
    let win = Window::new(io.e, cfg.w);
    let n = win.n();
    assert!(n >= 1 && cfg.room >= 1);
    assert!(io.r.len() + 1 >= io.e && io.s.len() >= io.e);
    let a: Vec<Q> = (0..n).map(|i| io.r[win.lo - 1 + i]).collect();
    let bb: Vec<Q> = (0..n - 1).map(|i| io.s[win.lo + 1 + i]).collect();
    let s0 = io.s[0];
    c.x_all(&bb);
    c.x(s0);
    for i in 0..n - 1 {
        let ci = if i == 0 { s0 } else { a[i - 1] };
        c.cx(a[i], bb[i]);
        c.cx(a[i], ci);
        c.ccx(ci, bb[i], a[i]);
    }
    let top_a = a[n - 1];
    let top_carry = if n == 1 { s0 } else { a[n - 2] };
    assert_ne!(top_a, top_carry);
    ImplicitR0GeScope { a, bb, s0, top_a, top_carry }
}

fn close_implicit_r0_ge_fixture(c: &mut Builder, sc: ImplicitR0GeScope) {
    for i in (0..sc.a.len() - 1).rev() {
        let ci = if i == 0 { sc.s0 } else { sc.a[i - 1] };
        c.ccx(ci, sc.bb[i], sc.a[i]);
        c.cx(sc.a[i], ci);
        c.cx(sc.a[i], sc.bb[i]);
    }
    c.x(sc.s0);
    c.x_all(&sc.bb);
}

fn open_implicit_r0_alias_ge_fixture(
    c: &mut Builder, io: &TickIo, cfg: DecCfg, enabled: bool,
) -> GeScope {
    let win = Window::new(io.e, cfg.w);
    let n = win.n();
    assert!(n >= 2 && io.r.len() + 1 >= io.e && io.s.len() >= io.e);
    let j = gidney_bits(n, cfg.room, enabled);
    assert!(j >= 1, "S0 alias requires a non-mutating first Gidney carry");
    let a: Vec<Q> = (0..n).map(|i| io.r[win.lo - 1 + i]).collect();
    let bb: Vec<Q> = (0..n)
        .map(|i| if i + 1 < n { io.s[win.lo + 1 + i] } else { io.s[0] })
        .collect();
    c.x_all(&bb); // S0 is simultaneously carry-one and synthetic top-one.
    let mut sc = GeScope { win, j, ge: io.s[0], gid: Vec::with_capacity(j),
        a, bb, r0: io.s[0] };
    for i in 0..j {
        let ci = sc.cin(i);
        c.cx(ci, sc.a[i]); c.cx(ci, sc.bb[i]);
        let t = c.alloc_qubit();
        c.ccx(sc.a[i], sc.bb[i], t); c.cx(ci, t);
        sc.gid.push(t);
    }
    for i in j..n {
        let ci = sc.cin(i);
        c.cx(sc.a[i], sc.bb[i]); c.cx(sc.a[i], ci); c.ccx(ci, sc.bb[i], sc.a[i]);
    }
    sc.ge = if j == n { sc.gid[n - 1] } else { sc.a[n - 1] };
    sc
}

pub(crate) fn push_implicit_r0_alias_virtual_fixture(
    c: &mut Builder, io: &TickIo, h: &Hreg, cfg: DecCfg, dirty: [Q; 2],
) {
    assert!(io.en.is_some() && dirty[0] != dirty[1]);
    let sc = open_implicit_r0_alias_ge_fixture(c, io, cfg, true);
    for i in (1..h.wires.len()).rev() {
        virtual_amb_fredkin(c, io, sc.ge, h.wires[i], h.wires[i - 1], &dirty);
    }
    if let Some(&h0) = h.wires.first() {
        virtual_amb_fredkin(c, io, sc.ge, h0, io.typ, &dirty);
    }
    virtual_d_xor(c, io, io.typ);
    virtual_amb_xor(c, io, sc.ge, io.typ, &dirty);
    close_ge_fixture(c, sc);
}

pub(crate) fn pop_implicit_r0_alias_virtual_fixture(
    c: &mut Builder, io: &TickIo, h: &Hreg, cfg: DecCfg, dirty: [Q; 2],
) {
    assert!(io.en.is_some() && dirty[0] != dirty[1]);
    let sc = open_implicit_r0_alias_ge_fixture(c, io, cfg, true);
    virtual_amb_xor(c, io, sc.ge, io.typ, &dirty);
    virtual_d_xor(c, io, io.typ);
    if let Some(&h0) = h.wires.first() {
        virtual_amb_fredkin(c, io, sc.ge, h0, io.typ, &dirty);
    }
    for i in 1..h.wires.len() {
        virtual_amb_fredkin(c, io, sc.ge, h.wires[i], h.wires[i - 1], &dirty);
    }
    close_ge_fixture(c, sc);
}

pub(crate) fn push_implicit_r0_alias_enabled_fixture(
    c: &mut Builder, io: &TickIo, h: &Hreg, cfg: DecCfg,
) {
    let en = io.en.expect("enabled implicit alias");
    assert!(io.cflag.is_none() && io.park.is_none());
    let s1 = io.s[1];
    let d = c.alloc_qubit(); c.x(s1); c.ccx(en, s1, d); c.x(s1);
    let sc = open_implicit_r0_alias_ge_fixture(c, io, cfg, true);
    let amb = c.alloc_qubit(); c.ccx(d, sc.ge, amb);
    shift_in(c, amb, io.typ, &h.wires); c.cx(d, io.typ); c.cx(amb, io.typ);
    meas_cz(c, amb, d, sc.ge); close_ge_fixture(c, sc);
    let m=c.alloc_bit(); c.hmr(d,m); c.x(s1); c.cz_if(en,s1,m); c.x(s1);
    c.free_bit(m); c.release_clean(d);
}

pub(crate) fn pop_implicit_r0_alias_enabled_fixture(
    c: &mut Builder, io: &TickIo, h: &Hreg, cfg: DecCfg,
) {
    let en = io.en.expect("enabled implicit alias");
    assert!(io.cflag.is_none() && io.park.is_none());
    let s1 = io.s[1];
    let d = c.alloc_qubit(); c.x(s1); c.ccx(en, s1, d); c.x(s1);
    let sc = open_implicit_r0_alias_ge_fixture(c, io, cfg, true);
    let amb = c.alloc_qubit(); c.ccx(d, sc.ge, amb);
    c.cx(amb, io.typ); c.cx(d, io.typ); shift_out(c, amb, io.typ, &h.wires);
    meas_cz(c, amb, d, sc.ge); close_ge_fixture(c, sc);
    let m=c.alloc_bit(); c.hmr(d,m); c.x(s1); c.cz_if(en,s1,m); c.x(s1);
    c.free_bit(m); c.release_clean(d);
}

pub(crate) fn push_implicit_r0_alias_noen_fixture(
    c: &mut Builder, io: &TickIo, h: &Hreg, cfg: DecCfg,
) {
    assert!(io.en.is_none() && io.cflag.is_none() && io.park.is_none());
    let s1 = io.s[1]; c.x(s1);
    let sc = open_implicit_r0_alias_ge_fixture(c, io, cfg, false);
    let amb = c.alloc_qubit(); c.ccx(s1, sc.ge, amb);
    shift_in(c, amb, io.typ, &h.wires); c.cx(s1, io.typ); c.cx(amb, io.typ);
    meas_cz(c, amb, s1, sc.ge); c.x(s1); close_ge_fixture(c, sc);
}

pub(crate) fn pop_implicit_r0_alias_noen_fixture(
    c: &mut Builder, io: &TickIo, h: &Hreg, cfg: DecCfg,
) {
    assert!(io.en.is_none() && io.cflag.is_none() && io.park.is_none());
    let s1 = io.s[1]; c.x(s1);
    let sc = open_implicit_r0_alias_ge_fixture(c, io, cfg, false);
    let amb = c.alloc_qubit(); c.ccx(s1, sc.ge, amb);
    c.cx(amb, io.typ); c.cx(s1, io.typ); shift_out(c, amb, io.typ, &h.wires);
    meas_cz(c, amb, s1, sc.ge); c.x(s1); close_ge_fixture(c, sc);
}

fn dirty_mcx_three_fixture(c: &mut Builder, controls: &[Q], target: Q, dirty: &[Q; 3]) {
    match controls.len() {
        0 => c.x(target),
        1 => c.cx(controls[0], target),
        2 => c.ccx(controls[0], controls[1], target),
        m => {
            assert!(m <= 5);
            let d = &dirty[..m - 2];
            assert!(controls.iter().all(|q| *q != target && !d.contains(q)));
            assert!(!d.contains(&target));
            for bottom in [true, false] {
                if bottom { c.ccx(controls[0], controls[1], d[0]); }
                for i in 1..d.len() { c.ccx(d[i - 1], controls[i + 1], d[i]); }
                c.ccx(*d.last().unwrap(), *controls.last().unwrap(), target);
                for i in (1..d.len()).rev() { c.ccx(d[i - 1], controls[i + 1], d[i]); }
                if bottom { c.ccx(controls[0], controls[1], d[0]); }
            }
        }
    }
}

fn implicit_or_amb_xor(
    c: &mut Builder, en: Q, s1_framed: Q, a: Q, carry: Q, target: Q, dirty: &[Q; 3],
) {
    // Complete typ update: D XOR amb = D*(!a)*(!carry).
    c.x(a);
    c.x(carry);
    dirty_mcx_three_fixture(c, &[en, s1_framed, a, carry], target, dirty);
    c.x(carry);
    c.x(a);
}

fn implicit_or_amb_fredkin(
    c: &mut Builder, en: Q, s1_framed: Q, a: Q, carry: Q,
    x: Q, y: Q, dirty: &[Q; 3],
) {
    c.cx(y, x);
    // amb = D XOR D*(!a)*(!carry); each transposition is involutive.
    dirty_mcx_three_fixture(c, &[en, s1_framed, x], y, dirty);
    c.x(a);
    c.x(carry);
    dirty_mcx_three_fixture(c, &[en, s1_framed, a, carry, x], y, dirty);
    c.x(carry);
    c.x(a);
    c.cx(y, x);
}

fn assert_implicit_r0_dirty(io: &TickIo, h: &Hreg, dirty: &[Q; 3]) {
    assert!(io.cflag.is_none() && io.park.is_none() && io.en.is_some());
    assert!(dirty[0] != dirty[1] && dirty[0] != dirty[2] && dirty[1] != dirty[2]);
    for &q in dirty {
        assert!(io.en != Some(q) && q != io.typ && !io.s.contains(&q) && !io.r.contains(&q));
        assert!(!h.wires.contains(&q));
    }
}

pub(crate) fn push_implicit_r0_virtual_or_fixture(
    c: &mut Builder, io: &TickIo, h: &Hreg, cfg: DecCfg, dirty: [Q; 3],
) {
    assert_implicit_r0_dirty(io, h, &dirty);
    let en = io.en.unwrap();
    let sc = open_implicit_r0_ge_fixture(c, io, cfg);
    let s1 = io.s[1];
    c.x(s1);
    for i in (1..h.wires.len()).rev() {
        implicit_or_amb_fredkin(c, en, s1, sc.top_a, sc.top_carry,
            h.wires[i], h.wires[i - 1], &dirty);
    }
    if let Some(&h0) = h.wires.first() {
        implicit_or_amb_fredkin(c, en, s1, sc.top_a, sc.top_carry, h0, io.typ, &dirty);
    }
    implicit_or_amb_xor(c, en, s1, sc.top_a, sc.top_carry, io.typ, &dirty);
    c.x(s1);
    close_implicit_r0_ge_fixture(c, sc);
}

pub(crate) fn pop_implicit_r0_virtual_or_fixture(
    c: &mut Builder, io: &TickIo, h: &Hreg, cfg: DecCfg, dirty: [Q; 3],
) {
    assert_implicit_r0_dirty(io, h, &dirty);
    let en = io.en.unwrap();
    let sc = open_implicit_r0_ge_fixture(c, io, cfg);
    let s1 = io.s[1];
    c.x(s1);
    implicit_or_amb_xor(c, en, s1, sc.top_a, sc.top_carry, io.typ, &dirty);
    if let Some(&h0) = h.wires.first() {
        implicit_or_amb_fredkin(c, en, s1, sc.top_a, sc.top_carry, h0, io.typ, &dirty);
    }
    for i in 1..h.wires.len() {
        implicit_or_amb_fredkin(c, en, s1, sc.top_a, sc.top_carry,
            h.wires[i], h.wires[i - 1], &dirty);
    }
    c.x(s1);
    close_implicit_r0_ge_fixture(c, sc);
}

fn implicit_noen_amb_xor(
    c:&mut Builder,s1_framed:Q,a:Q,carry:Q,target:Q,dirty:&[Q;2],
) {
    // Complete typ update: D XOR amb = D*(!a)*(!carry).
    c.x(a);c.x(carry);dirty_mcx_fixture(c,&[s1_framed,a,carry],target,dirty);
    c.x(carry);c.x(a);
}

fn implicit_noen_amb_fredkin(
    c:&mut Builder,s1_framed:Q,a:Q,carry:Q,x:Q,y:Q,dirty:&[Q;2],
) {
    c.cx(y,x);dirty_mcx_fixture(c,&[s1_framed,x],y,dirty);
    c.x(a);c.x(carry);dirty_mcx_fixture(c,&[s1_framed,a,carry,x],y,dirty);
    c.x(carry);c.x(a);c.cx(y,x);
}

pub(crate) fn push_implicit_r0_virtual_or_noen_fixture(
    c:&mut Builder,io:&TickIo,h:&Hreg,cfg:DecCfg,dirty:[Q;2],
) {
    assert!(io.en.is_none()&&io.cflag.is_none()&&io.park.is_none());
    let sc=open_implicit_r0_ge_fixture(c,io,cfg);let s1=io.s[1];c.x(s1);
    for i in(1..h.wires.len()).rev(){implicit_noen_amb_fredkin(c,s1,sc.top_a,sc.top_carry,h.wires[i],h.wires[i-1],&dirty)}
    if let Some(&h0)=h.wires.first(){implicit_noen_amb_fredkin(c,s1,sc.top_a,sc.top_carry,h0,io.typ,&dirty)}
    implicit_noen_amb_xor(c,s1,sc.top_a,sc.top_carry,io.typ,&dirty);c.x(s1);
    close_implicit_r0_ge_fixture(c,sc);
}

pub(crate) fn pop_implicit_r0_virtual_or_noen_fixture(
    c:&mut Builder,io:&TickIo,h:&Hreg,cfg:DecCfg,dirty:[Q;2],
) {
    assert!(io.en.is_none()&&io.cflag.is_none()&&io.park.is_none());
    let sc=open_implicit_r0_ge_fixture(c,io,cfg);let s1=io.s[1];c.x(s1);
    implicit_noen_amb_xor(c,s1,sc.top_a,sc.top_carry,io.typ,&dirty);
    if let Some(&h0)=h.wires.first(){implicit_noen_amb_fredkin(c,s1,sc.top_a,sc.top_carry,h0,io.typ,&dirty)}
    for i in 1..h.wires.len(){implicit_noen_amb_fredkin(c,s1,sc.top_a,sc.top_carry,h.wires[i],h.wires[i-1],&dirty)}
    c.x(s1);close_implicit_r0_ge_fixture(c,sc);
}

/// One-owner variant of the exact floor OR decoder. The caller must check
/// actual allocator headroom, not the clamped DecCfg.room. No fresh D or
/// measurement receipt is needed; ambiguity is coherently erased.
pub(crate) fn implicit_r0_materialized_or_fixture(
    c: &mut Builder, io: &TickIo, h: &Hreg, cfg: DecCfg, dirty: [Q; 3], inverse: bool,
) {
    assert!(!h.is_empty() && io.cflag.is_none() && io.park.is_none());
    for &q in &dirty {
        assert!(io.en != Some(q) && q != io.typ && !io.s.contains(&q)
            && !io.r.contains(&q) && !h.wires.contains(&q));
    }
    assert!(dirty[0] != dirty[1] && dirty[0] != dirty[2] && dirty[1] != dirty[2]);
    let sc = open_implicit_r0_ge_fixture(c, io, cfg);
    let amb = c.alloc_qubit();
    let s1 = io.s[1];
    c.x(s1);
    let toggle_amb = |c: &mut Builder| {
        if let Some(en) = io.en {
            c.ccx(en, s1, amb);
            implicit_or_amb_xor(c, en, s1, sc.top_a, sc.top_carry, amb, &dirty);
        } else {
            c.cx(s1, amb);
            implicit_noen_amb_xor(c, s1, sc.top_a, sc.top_carry, amb,
                &[dirty[0], dirty[1]]);
        }
    };
    let toggle_type = |c: &mut Builder| {
        if let Some(en) = io.en { c.ccx(en, s1, io.typ); }
        else { c.cx(s1, io.typ); }
        c.cx(amb, io.typ);
    };
    toggle_amb(c);
    if inverse {
        toggle_type(c);
        shift_out(c, amb, io.typ, &h.wires);
    } else {
        shift_in(c, amb, io.typ, &h.wires);
        toggle_type(c);
    }
    toggle_amb(c);
    c.release_clean(amb);
    c.x(s1);
    close_implicit_r0_ge_fixture(c, sc);
}

fn park_root_mcx_dirty(c:&mut Builder,controls:&[Q],target:Q,dirty:&[Q]) {
    let n=controls.len();
    assert!(n>=3 && dirty.len()>=n-2);
    let d=&dirty[..n-2];
    for bottom in [true,false] {
        if bottom { c.ccx(controls[0],controls[1],d[0]); }
        for i in 1..d.len() { c.ccx(d[i-1],controls[i+1],d[i]); }
        c.ccx(*d.last().unwrap(),*controls.last().unwrap(),target);
        for i in (1..d.len()).rev() { c.ccx(d[i-1],controls[i+1],d[i]); }
        if bottom { c.ccx(controls[0],controls[1],d[0]); }
    }
}

fn park_root_toggle_base(c:&mut Builder,s1:Q,a:Q,carry:Q,target:Q,dirty:&[Q]) {
    c.cx(s1,target); c.x(a); c.x(carry);
    park_root_mcx_dirty(c,&[s1,a,carry],target,dirty);
    c.x(carry); c.x(a);
}

/// Exact floor decoder using a caller-owned clean Park/parity root as amb.
/// Park masks run only after the in-place compare has fully restored R.
pub(crate) fn park_root_recycled_implicit(
    c:&mut Builder,io:&TickIo,h:&Hreg,cfg:DecCfg,root:Q,dirty:&[Q],inverse:bool,
) {
    assert_eq!(io.e,256); assert_eq!(cfg.w,64);
    assert!(io.en.is_none() && io.cflag.is_none() && io.park.is_none());
    assert_eq!(dirty.len(),13);
    assert!(root!=io.typ && !io.s.contains(&root) && !io.r.contains(&root) && !h.wires.contains(&root));
    for (i,&q) in dirty.iter().enumerate() {
        assert!(q!=root && q!=io.typ && !io.s.contains(&q) && !io.r.contains(&q) && !h.wires.contains(&q));
        assert!(!dirty[..i].contains(&q));
    }
    let park=&io.r[io.r.len()-14..]; let s1=io.s[1];
    let sc=open_implicit_r0_ge_fixture(c,io,cfg); c.x(s1);
    park_root_toggle_base(c,s1,sc.top_a,sc.top_carry,root,dirty);
    close_implicit_r0_ge_fixture(c,sc);
    let mut controls=vec![s1];controls.extend_from_slice(park);
    park_root_mcx_dirty(c,&controls,root,dirty);
    let toggle_type=|c:&mut Builder| {
        c.cx(s1,io.typ);park_root_mcx_dirty(c,&controls,io.typ,dirty);c.cx(root,io.typ);
    };
    if inverse { toggle_type(c);shift_out(c,root,io.typ,&h.wires); }
    else { shift_in(c,root,io.typ,&h.wires);toggle_type(c); }
    park_root_mcx_dirty(c,&controls,root,dirty);
    let sc=open_implicit_r0_ge_fixture(c,io,cfg);
    park_root_toggle_base(c,s1,sc.top_a,sc.top_carry,root,dirty);c.x(s1);
    close_implicit_r0_ge_fixture(c,sc);
}

/// Tick 0 (letters A or C only): `typ ^= !bit1(s)`, `cflag ^= bit1(s)`. Self-inverse, 0 CCX.
pub fn first_tick(c: &mut Builder, s: &[Q], typ: Q, cflag: Option<Q>) {
    c.cx(s[1], typ);
    c.x(typ);
    if let Some(cf) = cflag {
        c.cx(s[1], cf);
    }
}

/// Dedicated-wire alternative for the park tick's extra bit: `swap(bit, slot)` on `flag`
/// (1 CCX; self-inverse; `slot` starts at 0 and holds the bit until the walk back).
pub fn park_stash(c: &mut Builder, flag: Q, bit: Q, slot: Q) {
    fredkin(c, flag, bit, slot);
}

/// Classical model of the decision, for support models and the selftest.
pub mod model {
    use super::Window;

    /// Little-endian limbs; bits at or above `e` are ignored.
    fn bit(v: &[u64], i: usize) -> bool {
        i / 64 < v.len() && (v[i / 64] >> (i % 64)) & 1 == 1
    }

    /// `ge` exactly as the circuit computes it, for any input (constant wires included):
    /// carry out of `x + bb + r[0]` over n bits, `bb = ~s[lo+1..e]` with top bit `!s[0]`.
    pub fn ge_circuit(s: &[u64], r: &[u64], e: usize, w: usize) -> bool {
        let win = Window::new(e, w);
        let n = win.n();
        let mut carry = bit(r, 0);
        for i in 0..n {
            let a = bit(r, win.lo + i);
            let b = if i + 1 < n {
                !bit(s, win.lo + 1 + i)
            } else {
                !bit(s, 0)
            };
            carry = (a & b) | (a & carry) | (b & carry);
        }
        carry
    }

    /// `D` and `amb` as the circuit computes them.
    pub fn decide(s: &[u64], r: &[u64], e: usize, w: usize, en: bool) -> (bool, bool) {
        let d = en && !bit(s, 1);
        (d, d && ge_circuit(s, r, e, w))
    }
}
