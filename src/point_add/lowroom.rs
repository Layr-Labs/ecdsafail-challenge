//! Exact LOW-ROOM replacement for the late-cell modular-reduction folds.
//!
//! Problem. A fold adds a one-hot selected constant `m*f`, m in {-1, 0, 1, 2}, f = 2^32 + 977, to a w = 42..55 bit
//! window (`pingpong.rs` 3517 joint fold, 4176 direct fold, 4916 terminal fold). The existing exact construction
//! (`width_composition::direct_add` with `direct_plan`) needs room >= 10 for n = 49 bits: a chunk plan at room r
//! covers only r(r+1)/2 + 2 bits. The addend is never materialised (each bit is an XOR of selector wires), so a
//! Cuccaro/TTK in-place adder, which parks the carries in the addend register, is not available.
//!
//! Construction (exact on every shot, Toffoli + measurement-based uncompute only):
//! 1. Complement trick: under `minus`, b -> ~b and first -> ~first; then b += first + u*C1 + v*C2 with
//!    u = plus XOR minus, v = plus2, C1 = (f mod 2^w) >> 1, C2 = (2f mod 2^w) >> 1; then undo the complements.
//!    (~(~b + C1 + ~first) = b + first - C1 - 1 = b + first + C_{-1} mod 2^n.) The -f rows, dense above bit 10,
//!    become the sparse rows of C1 = 2^31 + 488 and C2 = 2^32 + 977: nonzero only at bits {0, 3..9, 31, 32}.
//! 2. Windowed add: the nonzero rows are covered by WINDOWS (a chunked Gidney ladder with every chunk's carry-out
//!    kept, as in direct_add, but the window's top carry is CONSUMED by a controlled increment of b[hi..n) before
//!    the boundaries are erased by exact mapped compares) and SINGLE rows (a controlled increment of b[p..n) by the
//!    row's selector XOR). A dynamic program picks the cheapest cover that fits the room.
//! 3. Controlled increments use BORROWED DIRTY wires (idle tape wires in the real circuit): x += 1 is
//!    x -= g; g = ~g; x -= g; g = ~g (Gidney's dirty-ancilla increment), each subtraction an ancilla-free TTK adder
//!    (Takahashi-Tani-Kunihiro 2010, 2k - 2 Toffoli). A control wire e is folded in as the register's low bit.
//!    Cost 4k Toffoli for a k-bit controlled increment, zero clean wires, dirty wires restored exactly.
//!
//! `probe()` (bin `lowroom_probe`) verifies every construction on random lanes (all selector cases, random b,
//! carry-in and dirty contents, random measurement outcomes, phase tracked per lane) and prints the Toffoli count
//! per (n, room) next to the existing direct_add at the room it needs.
use super::Builder;
use crate::circuit::{BitId, Op, OperationType as K, QubitId, NO_BIT};

type Q = QubitId;

thread_local! {
    /// SQ_LOWROOM: wires idle for the whole current field cell (packed P5 tape groups other than the current
    /// letter's group), lent dirty to the low-room fold. Set by heo_carry::dirty_cell.
    static POOL: std::cell::RefCell<Vec<QubitId>> = const { std::cell::RefCell::new(Vec::new()) };
}
pub(crate) fn enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SQ_LOWROOM").is_some())
}
pub(crate) fn with_pool(pool: Vec<QubitId>, body: impl FnOnce()) {
    let old = POOL.with(|p| p.replace(pool));
    body();
    POOL.with(|p| *p.borrow_mut() = old);
}

/// SQ_LOWROOM hook at a fold site: when the existing direct add has no plan at the current room, run the exact
/// low-room fold with lent dirty wires instead. Returns false (caller runs its own path) when the knob is off, the
/// existing plan fits, or the pool is too small.
#[allow(clippy::too_many_arguments)]
#[track_caller]
pub(crate) fn try_fold(c: &mut Builder, b: &[Q], f: alloy_primitives::U256, plus: &[Q], plus2: &[Q], minus: Q, first: Q) -> bool {
    if !enabled() {
        return false;
    }
    let n = b.len();
    let room = super::pingpong::heo_hooks::cap().saturating_sub(c.active_qubits() as usize);
    if super::width_composition::direct_plan_inner(n, room).is_some() {
        return false;
    }
    let lim = f.as_limbs();
    assert!(lim[2] == 0 && lim[3] == 0);
    let fu = lim[0] as u128 | (lim[1] as u128) << 64;
    let used: Vec<Q> = b.iter().chain(plus).chain(plus2).copied().chain([minus, first]).collect();
    let pool: Vec<Q> = POOL.with(|p| p.borrow().iter().copied().filter(|q| !used.contains(q)).collect());
    let loc = std::panic::Location::caller();
    if pool.len() < n + 2 {
        eprintln!("SQ_LOWROOM site={}:{} n={n} room={room} pool={} skipped", loc.file(), loc.line(), pool.len());
        return false;
    }
    let t0 = c.report_totals().map_or(0.0, |x| x.1);
    let d = lowroom_fold(c, b, fu, plus, plus2, minus, first, room, &pool[..n + 2]);
    eprintln!("SQ_LOWROOM site={}:{} n={n} room={room} pool={} T={:.1} plan=[{d}]", loc.file(), loc.line(), pool.len(),
        c.report_totals().map_or(0.0, |x| x.1) - t0);
    true
}

/// b += a (mod 2^k), a restored. Ancilla-free ripple adder of Takahashi, Tani and Kunihiro (QIC 10, 2010),
/// modular variant (no carry-out wire): 2k - 2 Toffoli.
pub(crate) fn ttk_add(c: &mut Builder, a: &[Q], b: &[Q]) {
    let k = a.len();
    assert_eq!(k, b.len());
    if k == 0 {
        return;
    }
    if k == 1 {
        c.cx(a[0], b[0]);
        return;
    }
    for i in 1..k {
        c.cx(a[i], b[i]);
    }
    for i in (1..k - 1).rev() {
        c.cx(a[i], a[i + 1]);
    }
    for i in 0..k - 1 {
        c.ccx(b[i], a[i], a[i + 1]);
    }
    for i in (1..k).rev() {
        c.cx(a[i], b[i]);
        c.ccx(b[i - 1], a[i - 1], a[i]);
    }
    for i in 1..k - 1 {
        c.cx(a[i], a[i + 1]);
    }
    for i in 0..k {
        c.cx(a[i], b[i]);
    }
}

/// b += a (mod 2^k) and z ^= carry-out, a restored, no ancilla (TTK with the carry-out wire as a_k): 2k - 1 Toffoli.
pub(crate) fn ttk_add_cout(c: &mut Builder, a: &[Q], b: &[Q], z: Q) {
    let k = a.len();
    assert_eq!(k, b.len());
    assert!(k >= 1);
    let ax = |i: usize| if i == k { z } else { a[i] };
    for i in 1..k {
        c.cx(a[i], b[i]);
    }
    for i in (1..k).rev() {
        c.cx(ax(i), ax(i + 1));
    }
    for i in 0..k {
        c.ccx(b[i], a[i], ax(i + 1));
    }
    for i in (1..k).rev() {
        c.cx(a[i], b[i]);
        c.ccx(b[i - 1], a[i - 1], a[i]);
    }
    for i in 1..k.saturating_sub(1) {
        c.cx(a[i], a[i + 1]);
    }
    for i in 0..k {
        c.cx(a[i], b[i]);
    }
}

/// x += 1 (mod 2^k) with k borrowed dirty wires `g` (restored). 4k - 4 Toffoli for k >= 4.
pub(crate) fn inc_dirty(c: &mut Builder, x: &[Q], g: &[Q]) {
    let k = x.len();
    match k {
        0 => {}
        1 => c.x(x[0]),
        2 => {
            c.cx(x[0], x[1]);
            c.x(x[0]);
        }
        3 => {
            c.ccx(x[0], x[1], x[2]);
            c.cx(x[0], x[1]);
            c.x(x[0]);
        }
        _ => {
            let g = &g[..k];
            // x - g - ~g = x + 1; x - g = ~(~x + g).
            c.x_all(x);
            ttk_add(c, g, x);
            c.x_all(g);
            ttk_add(c, g, x);
            c.x_all(x);
            c.x_all(g);
        }
    }
}

/// x += e (mod 2^k) for a control wire e (restored): increment the (k+1)-bit register [e, x] and flip e back.
pub(crate) fn cinc_dirty(c: &mut Builder, e: Q, x: &[Q], g: &[Q]) {
    if x.is_empty() {
        return;
    }
    let mut r = Vec::with_capacity(x.len() + 1);
    r.push(e);
    r.extend_from_slice(x);
    inc_dirty(c, &r, g);
    c.x(e);
}

/// Toffoli count of `cinc_dirty` on k bits.
pub(crate) fn cinc_cost(k: usize) -> usize {
    match k + 1 {
        0..=2 => 0,
        3 => 1,
        m => 4 * m - 4,
    }
}

fn host_xor(c: &mut Builder, sel: &[Q]) -> Q {
    for &s in &sel[1..] {
        c.cx(s, sel[0]);
    }
    sel[0]
}
fn unhost_xor(c: &mut Builder, sel: &[Q]) {
    for &s in sel[1..].iter().rev() {
        c.cx(s, sel[0]);
    }
}

/// One window of the cover: bits [lo, hi) of the rows as a chunked ladder (chunk sizes `sizes`), every chunk's
/// carry-out kept. If `hi < n` the window's top carry is consumed by a controlled increment of b[hi..n); if the
/// window reaches n the last chunk is wrapped. Needs a zero wire as the incoming carry when `cin` is None.
fn window(c: &mut Builder, rows: &[Vec<Q>], b: &[Q], lo: usize, sizes: &[usize], cin: Option<Q>, dirty: &[Q]) {
    use super::width_composition::{direct_chunk, mapped_compare};
    let n = b.len();
    let hi = lo + sizes.iter().sum::<usize>();
    let wrapped = hi == n;
    let base = c.active_qubits();
    let zero = if cin.is_none() { Some(c.alloc_qubit()) } else { None };
    let first_in = cin.or(zero).unwrap();
    let mut at = lo;
    let mut prev = first_in;
    // (lo, hi, incoming, out, incoming is the released zero wire)
    let mut stages: Vec<(usize, usize, Q, Q, bool)> = Vec::new();
    for (j, &w) in sizes.iter().enumerate() {
        let last = j + 1 == sizes.len();
        let out = if last && wrapped { None } else { Some(c.alloc_qubit()) };
        direct_chunk(c, &rows[..n], b, at, w, prev, out);
        if j == 0 {
            if let Some(z) = zero {
                // The chunk is unwound; the zero incoming is clean again. Re-allocated for its erase compare.
                c.release_clean(z);
            }
        }
        if let Some(q) = out {
            stages.push((at, at + w, prev, q, j == 0 && zero.is_some()));
            prev = q;
        }
        at += w;
    }
    if !wrapped {
        cinc_dirty(c, prev, &b[hi..], &dirty[..n - hi + 1]);
    }
    for (slo, shi, sin, q, zflag) in stages.into_iter().rev() {
        let m = c.alloc_bit();
        c.hmr(q, m);
        c.release_clean(q);
        let zin = if zflag { Some(c.alloc_qubit()) } else { None };
        c.push_condition(m);
        mapped_compare(c, &rows[slo..shi], &b[slo..shi], zin.unwrap_or(sin));
        c.pop_condition();
        c.free_bit(m);
        if let Some(z) = zin {
            c.release_clean(z);
        }
    }
    assert_eq!(c.active_qubits(), base);
}

/// Chunk sizes for a window of `w` bits at `room`: chunk j costs j + w_j wires (j live boundaries, w_j - 1 carries,
/// its out; +1 zero wire in chunk 0 without a carry-in; a wrapped top chunk needs only w - 2 carries).
fn window_sizes(w: usize, room: usize, has_cin: bool, wrapped: bool) -> Option<Vec<usize>> {
    if room == 0 {
        return None;
    }
    for k in 1..=room {
        let caps: Vec<isize> = (0..k)
            .map(|j| {
                let mut cap = room as isize - j as isize;
                if j == 0 && !has_cin {
                    cap -= 1;
                }
                if j + 1 == k && wrapped {
                    cap += 2;
                }
                cap
            })
            .collect();
        if caps.iter().any(|&x| x < 1) {
            continue;
        }
        let tot: isize = caps.iter().sum();
        if tot >= w as isize {
            let mut sizes: Vec<usize> = caps.iter().map(|&x| x as usize).collect();
            let mut excess = tot as usize - w;
            for s in sizes.iter_mut().rev() {
                let cut = excess.min(*s - 1);
                *s -= cut;
                excess -= cut;
            }
            if excess == 0 && k <= room {
                return Some(sizes);
            }
        }
    }
    None
}

#[derive(Clone, Debug)]
enum Piece {
    Single(usize),
    Cin,
    Window { lo: usize, sizes: Vec<usize> },
}

/// Cost model for the DP (Toffoli; ladders 1 per bit, erase compares (w-1)/2 expected each).
fn window_cost(sizes: &[usize], hi: usize, n: usize) -> f64 {
    let lad: usize = sizes.iter().sum();
    let cmp: f64 = sizes.iter().map(|&w| (w as f64 - 1.0).max(0.0) / 2.0).sum();
    lad as f64 + cmp + if hi < n { cinc_cost(n - hi) as f64 } else { 0.0 }
}

fn plan(rows: &[Vec<Q>], n: usize, has_cin: bool, room: usize, allow_inc: bool) -> Option<Vec<Piece>> {
    if !allow_inc {
        // No dirty wires: only one wrapped window from the first nonzero row to the top.
        let lo = if has_cin { 0 } else { (0..n).find(|&i| !rows[i].is_empty())? };
        let s = window_sizes(n - lo, room, has_cin && lo == 0, true)?;
        return Some(vec![Piece::Window { lo, sizes: s }]);
    }
    Some(plan_full(rows, n, has_cin, room))
}

fn plan_full(rows: &[Vec<Q>], n: usize, has_cin: bool, room: usize) -> Vec<Piece> {
    let mut pos: Vec<usize> = (0..n).filter(|&i| !rows[i].is_empty()).collect();
    if has_cin && pos.first() != Some(&0) {
        pos.insert(0, 0);
    }
    let m = pos.len();
    // best[i] = (cost, pieces) covering pos[i..]
    let mut best: Vec<(f64, Vec<Piece>)> = vec![(0.0, Vec::new()); m + 1];
    for i in (0..m).rev() {
        let p = pos[i];
        let cin_here = has_cin && p == 0;
        // singles
        let mut sc = 0.0;
        let mut sp = Vec::new();
        if !rows[p].is_empty() {
            sc += cinc_cost(n - p) as f64;
            sp.push(Piece::Single(p));
        }
        if cin_here {
            sc += cinc_cost(n) as f64;
            sp.push(Piece::Cin);
        }
        let mut cand = (sc + best[i + 1].0, {
            let mut v = sp;
            v.extend(best[i + 1].1.iter().cloned());
            v
        });
        for j in i..m {
            // window pos[i] ..= pos[j]
            let hi = pos[j] + 1;
            if let Some(s) = window_sizes(hi - p, room, cin_here, false) {
                let cost = window_cost(&s, hi, n) + best[j + 1].0;
                if cost < cand.0 {
                    let mut v = vec![Piece::Window { lo: p, sizes: s }];
                    v.extend(best[j + 1].1.iter().cloned());
                    cand = (cost, v);
                }
            }
        }
        // window to the top (wrapped): covers everything from p
        if std::env::var_os("LOWROOM_NOWRAP").is_some() {
            best[i] = cand;
            continue;
        }
        if let Some(s) = window_sizes(n - p, room, cin_here, true) {
            let cost = window_cost(&s, n, n);
            if cost < cand.0 {
                cand = (cost, vec![Piece::Window { lo: p, sizes: s }]);
            }
        }
        best[i] = cand;
    }
    best[0].1.clone()
}

/// b += sum_i 2^i XOR(rows[i]) + cin (mod 2^n), exact; never more than `room` clean wires above the caller's live
/// count; `dirty` (>= n + 1 wires, disjoint from everything else) is restored.
pub(crate) fn windowed_add(c: &mut Builder, rows: &[Vec<Q>], b: &[Q], cin: Option<Q>, room: usize, dirty: &[Q]) -> String {
    try_windowed_add(c, rows, b, cin, room, dirty).expect("windowed_add: no plan")
}

/// As [`windowed_add`]; with fewer than n + 1 dirty wires only a wrapped chunked window (no increments) is allowed,
/// and None is returned (nothing emitted) when that does not fit the room.
pub(crate) fn try_windowed_add(c: &mut Builder, rows: &[Vec<Q>], b: &[Q], cin: Option<Q>, room: usize, dirty: &[Q]) -> Option<String> {
    let n = b.len();
    assert_eq!(rows.len(), n);
    if rows.iter().all(|r| r.is_empty()) && cin.is_none() {
        return Some(String::new());
    }
    let pieces = plan(rows, n, cin.is_some(), room, dirty.len() > n)?;
    let mut desc = Vec::new();
    for pc in &pieces {
        match pc {
            Piece::Single(p) => {
                let e = host_xor(c, &rows[*p]);
                cinc_dirty(c, e, &b[*p..], &dirty[..n - p + 1]);
                unhost_xor(c, &rows[*p]);
                desc.push(format!("S{p}"));
            }
            Piece::Cin => {
                cinc_dirty(c, cin.unwrap(), b, &dirty[..n + 1]);
                desc.push("C".into());
            }
            Piece::Window { lo, sizes } => {
                let has = *lo == 0 && cin.is_some();
                window(c, rows, b, *lo, sizes, if has { cin } else { None }, dirty);
                desc.push(format!("W{lo}:{sizes:?}"));
            }
        }
    }
    Some(desc.join(" "))
}

/// SQ_LOWROOM hook for const_arith::carry_ladder (a controlled-constant ladder that allocates one carry per live
/// position regardless of the room): the same wrapped add as a chunked exact window at the current room.
/// `rows[i]` is the addend-bit wire set of position dead + i (empty = 0). Returns false if it does not fit.
pub(crate) fn try_ladder(c: &mut Builder, acc: &[Q], rows: &[Vec<Q>]) -> bool {
    let room = super::pingpong::heo_hooks::cap().saturating_sub(c.active_qubits() as usize);
    let pool: Vec<Q> = POOL.with(|p| p.borrow().iter().copied().filter(|q| !acc.contains(q) && !rows.iter().flatten().any(|r| r == q)).collect());
    let t0 = c.report_totals().map_or(0.0, |x| x.1);
    match try_windowed_add(c, rows, acc, None, room, &pool) {
        Some(d) => {
            eprintln!("SQ_LOWROOM_LADDER n={} room={room} pool={} T={:.1} plan=[{d}]", acc.len(), pool.len(), c.report_totals().map_or(0.0, |x| x.1) - t0);
            true
        }
        None => {
            eprintln!("SQ_LOWROOM_LADDER n={} room={room} pool={} skipped", acc.len(), pool.len());
            false
        }
    }
}

/// Low-room exact fold: the direct_add part of a fold (b = acc[1..w], incoming `first`), for f odd.
/// `plus`/`plus2` are the XOR sets of the plus_f / plus_2f selectors (plus2 may be empty), `minus` the minus_f wire.
#[allow(clippy::too_many_arguments)]
pub(crate) fn lowroom_fold(c: &mut Builder, b: &[Q], f: u128, plus: &[Q], plus2: &[Q], minus: Q, first: Q, room: usize, dirty: &[Q]) -> String {
    let n = b.len();
    let w = n + 1;
    let mw: u128 = if w >= 128 { u128::MAX } else { (1u128 << w) - 1 };
    let fw = f & mw;
    assert!(fw & 1 == 1, "f must be odd");
    let c1 = fw >> 1;
    let c2 = ((fw << 1) & mw) >> 1;
    let sym = |a: &[Q], b: &[Q]| -> Vec<Q> {
        let mut v: Vec<Q> = a.to_vec();
        for &x in b {
            if let Some(i) = v.iter().position(|&y| y == x) {
                v.remove(i);
            } else {
                v.push(x);
            }
        }
        v
    };
    let u = sym(plus, &[minus]);
    let rows: Vec<Vec<Q>> = (0..n)
        .map(|i| {
            let mut r = Vec::new();
            if c1 >> i & 1 == 1 {
                r = sym(&r, &u);
            }
            if c2 >> i & 1 == 1 {
                r = sym(&r, plus2);
            }
            r
        })
        .collect();
    c.cx(minus, first);
    c.cx_all(minus, b);
    let d = windowed_add(c, &rows, b, Some(first), room, dirty);
    c.cx_all(minus, b);
    c.cx(minus, first);
    d
}

// ---------------------------------------------------------------------------------------------------------------
// Verification: lane-parallel classical simulation with random measurement outcomes and a per-lane phase bit.

struct Sim {
    q: Vec<u64>,
    b: Vec<u64>,
    phase: u64,
    garbage: u64,
    rng: u64,
}
impl Sim {
    fn rnd(&mut self) -> u64 {
        self.rng ^= self.rng << 13;
        self.rng ^= self.rng >> 7;
        self.rng ^= self.rng << 17;
        self.rng
    }
    fn run(&mut self, ops: &[Op]) -> (usize, f64) {
        let mut stack: Vec<u64> = Vec::new();
        let mut active = u64::MAX;
        let (mut native, mut expected) = (0usize, 0.0f64);
        for op in ops {
            let mut en = active;
            if op.c_condition != NO_BIT && !matches!(op.kind, K::PushCondition) {
                en &= self.b[op.c_condition.0 as usize];
            }
            let (t, a, bb) = (op.q_target.0 as usize, op.q_control1.0 as usize, op.q_control2.0 as usize);
            match op.kind {
                K::PushCondition => {
                    stack.push(active);
                    active &= self.b[op.c_condition.0 as usize];
                }
                K::PopCondition => active = stack.pop().unwrap(),
                K::X => self.q[t] ^= en,
                K::CX => self.q[t] ^= self.q[a] & en,
                K::CCX => {
                    native += 1;
                    expected += 0.5f64.powi(stack.len() as i32);
                    self.q[t] ^= self.q[a] & self.q[bb] & en;
                }
                K::Swap => {
                    let d = (self.q[t] ^ self.q[a]) & en;
                    self.q[t] ^= d;
                    self.q[a] ^= d;
                }
                K::Z => self.phase ^= self.q[t] & en,
                K::CZ => self.phase ^= self.q[t] & self.q[a] & en,
                K::CCZ => {
                    native += 1;
                    expected += 0.5f64.powi(stack.len() as i32);
                    self.phase ^= self.q[t] & self.q[a] & self.q[bb] & en
                }
                K::Neg => self.phase ^= en,
                K::Hmr => {
                    let m = self.rnd();
                    let cb = op.c_target.0 as usize;
                    self.b[cb] = (self.b[cb] & !en) | (m & en);
                    self.phase ^= m & self.q[t] & en;
                    self.q[t] &= !en;
                }
                K::R => {
                    self.garbage |= self.q[t] & en;
                    self.q[t] &= !en;
                }
                K::BitStore0 => {
                    let cb = op.c_target.0 as usize;
                    self.b[cb] &= !en;
                }
                K::BitStore1 => {
                    let cb = op.c_target.0 as usize;
                    self.b[cb] |= en;
                }
                K::BitInvert => {
                    let cb = op.c_target.0 as usize;
                    self.b[cb] ^= en;
                }
                _ => {}
            }
        }
        assert!(stack.is_empty());
        (native, expected)
    }
}

fn put(q: &mut [u64], r: &[Q], x: u128, l: usize) {
    for (i, w) in r.iter().enumerate() {
        if x >> i & 1 != 0 {
            q[w.0 as usize] |= 1 << l;
        }
    }
}
fn get(q: &[u64], r: &[Q], l: usize) -> u128 {
    r.iter().enumerate().fold(0, |x, (i, w)| x | (((q[w.0 as usize] >> l & 1) as u128) << i))
}

struct Case {
    ops: Vec<Op>,
    nq: usize,
    nb: usize,
    peak_extra: u32,
    desc: String,
}

/// Build one fold (new construction at `room`, or the existing direct_add when `room` is None) for a window of w
/// bits; `joint` uses the joint-fold selector shape (plus_f = z0^s^v0^minus).
fn build_fold(w: usize, room: Option<usize>, joint: bool) -> (Case, Vec<Q>, Vec<Q>, Q, Q, Q, Vec<Q>, Vec<Q>) {
    let f: u128 = (1u128 << 32) + 977;
    let n = w - 1;
    let mut c = Builder::new();
    let b = c.alloc_qubits(n);
    let (plus_raw, plus2, minus) = (c.alloc_qubits(if joint { 3 } else { 1 }), c.alloc_qubit(), c.alloc_qubit());
    let first = c.alloc_qubit();
    let dirty = c.alloc_qubits(n + 2);
    let plus: Vec<Q> = if joint { let mut v = plus_raw.clone(); v.push(minus); v } else { plus_raw.clone() };
    let base = c.active_qubits();
    let start = c.op_count();
    let desc = match room {
        Some(r) => lowroom_fold(&mut c, &b, f, &plus, &[plus2], minus, first, r, &dirty),
        None => {
            // the existing construction: rows = selectors(i), i = 1..w, direct_add at the smallest room with a plan
            let fw = f & ((1u128 << w) - 1);
            let negf = ((1u128 << w) - fw) & ((1u128 << w) - 1);
            let sym = |a: &mut Vec<Q>, x: Q| if let Some(i) = a.iter().position(|&y| y == x) { a.remove(i); } else { a.push(x); };
            let map: Vec<Vec<Q>> = (1..w)
                .map(|i| {
                    let mut r = Vec::new();
                    if fw >> i & 1 == 1 { for &p in &plus { sym(&mut r, p); } }
                    if fw >> (i - 1) & 1 == 1 { sym(&mut r, plus2); }
                    if negf >> i & 1 == 1 { sym(&mut r, minus); }
                    r
                })
                .collect();
            let (r, p) = (0..200).find_map(|r| super::width_composition::direct_plan(n, r).map(|p| (r, p))).unwrap();
            super::width_composition::direct_add(&mut c, &map, &b, first, &p);
            format!("direct_add room {r} sizes {:?}", p.sizes)
        }
    };
    assert_eq!(c.active_qubits(), base);
    let peak_extra = c.peak_total() - base;
    let (nq, nb) = c.i13_dims();
    let ops = c.take_ops()[start..].to_vec();
    (Case { ops, nq, nb, peak_extra, desc }, b, plus_raw, plus2, minus, first, dirty, plus)
}

fn verify(w: usize, room: Option<usize>, joint: bool, trials: usize) -> (usize, f64, u32, String) {
    let f: u128 = (1u128 << 32) + 977;
    let n = w - 1;
    let (case, b, plus_raw, plus2, minus, first, dirty, _plus) = build_fold(w, room, joint);
    let mn: u128 = (1u128 << n) - 1;
    let fw = f & ((1u128 << w) - 1);
    let consts = [0u128, fw >> 1, ((fw << 1) & ((1u128 << w) - 1)) >> 1, (((1u128 << w) - fw) & ((1u128 << w) - 1)) >> 1];
    eprintln!("VERIFY w={w} room={room:?} joint={joint} plan=[{}]", case.desc);
    let mut rng: u64 = 0x9e3779b97f4a7c15 ^ (w as u64) << 8 ^ room.unwrap_or(99) as u64;
    let mut next = || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    let (mut native, mut expected) = (0, 0.0);
    for t in 0..trials {
        let mut q = vec![0u64; case.nq];
        let mut lanes = Vec::new();
        for l in 0..64 {
            let sel = (l + t) % 4; // 0 none, 1 plus, 2 plus2, 3 minus
            let bv = ((next() as u128) << 64 | next() as u128) & mn;
            let bv = match l % 16 {
                0 => 0,
                1 => mn,
                _ => bv,
            };
            let fv = (next() & 1) as u128;
            let dv = ((next() as u128) << 64 | next() as u128) & ((1u128 << dirty.len()) - 1);
            // selector wires: plus logical value = XOR(plus_raw) (^ minus in the joint shape)
            let (pl, p2, mi) = (sel == 1, sel == 2, sel == 3);
            let mut raw = (next() as u128) & ((1u128 << plus_raw.len()) - 1);
            let par = (raw.count_ones() & 1 == 1) ^ (joint && mi);
            if par != pl {
                raw ^= 1;
            }
            put(&mut q, &b, bv, l);
            put(&mut q, &plus_raw, raw, l);
            put(&mut q, &[plus2], p2 as u128, l);
            put(&mut q, &[minus], mi as u128, l);
            put(&mut q, &[first], fv, l);
            put(&mut q, &dirty, dv, l);
            lanes.push((sel, bv, raw, fv, dv));
        }
        let before = q.clone();
        let mut s = Sim { q, b: vec![0; case.nb], phase: 0, garbage: 0, rng: next() | 1 };
        let (nat, exp) = s.run(&case.ops);
        native = nat;
        expected = exp;
        assert_eq!(s.phase, 0, "phase garbage w={w} room={room:?}");
        assert_eq!(s.garbage, 0, "ancilla garbage w={w} room={room:?}");
        for (l, &(sel, bv, raw, fv, dv)) in lanes.iter().enumerate() {
            let want = (bv + fv + consts[sel]) & mn;
            assert_eq!(get(&s.q, &b, l), want, "sum w={w} room={room:?} sel={sel}");
            assert_eq!(get(&s.q, &plus_raw, l), raw);
            assert_eq!(get(&s.q, &[first], l), fv);
            assert_eq!(get(&s.q, &dirty, l), dv, "dirty not restored");
        }
        // every other wire unchanged (b excepted)
        for (i, (&x, &y)) in before.iter().zip(&s.q).enumerate() {
            if !b.iter().any(|q| q.0 as usize == i) {
                assert_eq!(x, y, "wire {i} changed");
            }
        }
    }
    (native, expected, case.peak_extra, case.desc)
}

/// Direct test of one window over generic rows (random selector XOR sets), all size patterns.
fn probe_windows() {
    let cases: Vec<(usize, usize, Vec<usize>, bool)> = vec![
        (12, 0, vec![3], true), (12, 0, vec![3, 2], true), (12, 4, vec![3], false), (12, 4, vec![2, 2], false),
        (12, 4, vec![3, 3], false), (12, 1, vec![3, 3, 2, 3], false), (14, 3, vec![3, 3, 2, 3], false), (14, 3, vec![2, 2, 2, 2], false),
        (12, 9, vec![3], false), (12, 9, vec![1, 2], false), (12, 8, vec![1, 3], false), (12, 8, vec![2, 2], false),
        (12, 6, vec![3, 3], false), (12, 6, vec![2, 4], false), (12, 6, vec![1, 5], false), (12, 6, vec![6], false),
        (12, 0, vec![12], true), (12, 0, vec![6, 6], true), (12, 2, vec![10], false), (12, 2, vec![5, 5], false),
    ];
    for (n, lo, sizes, cin) in cases {
        let mut c = Builder::new();
        let b = c.alloc_qubits(n);
        let sel = c.alloc_qubits(3);
        let ci = c.alloc_qubit();
        let dirty = c.alloc_qubits(n + 2);
        let mut rng = 777u64 + lo as u64;
        let mut nx = || { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; rng };
        let hi = lo + sizes.iter().sum::<usize>();
        let rows: Vec<Vec<Q>> = (0..n).map(|i| if i < lo || i >= hi { Vec::new() } else {
            let m = nx() % 8; (0..3).filter(|j| m >> j & 1 == 1).map(|j| sel[j]).collect() }).collect();
        let start = c.op_count();
        window(&mut c, &rows, &b, lo, &sizes, if cin { Some(ci) } else { None }, &dirty);
        let (nq, nb) = c.i13_dims();
        let ops = c.take_ops()[start..].to_vec();
        let mn: u128 = (1u128 << n) - 1;
        let mut ok = true;
        for t in 0..64 {
            let mut q = vec![0u64; nq];
            let mut lanes = Vec::new();
            for l in 0..64 {
                let (bv, sv, cv, dv) = ((nx() as u128) & mn, (nx() % 8) as u128, (nx() & 1) as u128, (nx() as u128) & ((1u128 << (n + 2)) - 1));
                put(&mut q, &b, bv, l); put(&mut q, &sel, sv, l); put(&mut q, &[ci], cv, l); put(&mut q, &dirty, dv, l);
                lanes.push((bv, sv, cv, dv));
            }
            let mut s = Sim { q, b: vec![0; nb], phase: 0, garbage: 0, rng: nx() | 1 };
            s.run(&ops);
            if s.phase != 0 || s.garbage != 0 { ok = false; }
            for (l, &(bv, sv, cv, dv)) in lanes.iter().enumerate() {
                let a: u128 = (0..n).map(|i| { let x = rows[i].iter().fold(0u128, |x, w| x ^ (sv >> sel.iter().position(|y| y == w).unwrap() & 1)); x << i }).sum();
                let want = (bv + a + if cin { cv } else { 0 }) & mn;
                if get(&s.q, &b, l) != want || get(&s.q, &dirty, l) != dv { ok = false; }
            }
            let _ = t;
        }
        println!("WINDOW n={n} lo={lo} sizes={sizes:?} cin={cin} ok={ok}");
    }
}

pub fn probe() {
    probe_windows();
    if std::env::var_os("LOWROOM_WINDOWS_ONLY").is_some() { return; }
    // unit checks of the primitives
    for k in 1..=12usize {
        let mut c = Builder::new();
        let a = c.alloc_qubits(k);
        let b = c.alloc_qubits(k);
        let e = c.alloc_qubit();
        let g = c.alloc_qubits(k + 1);
        ttk_add(&mut c, &a, &b);
        let s1 = c.op_count();
        cinc_dirty(&mut c, e, &b, &g);
        let (nq, nb) = c.i13_dims();
        let ops = c.take_ops();
        let m: u128 = (1u128 << k) - 1;
        let mut rng = 12345u64 + k as u64;
        for _ in 0..64 {
            let mut q = vec![0u64; nq];
            let mut lanes = Vec::new();
            for l in 0..64 {
                rng ^= rng << 13;
                rng ^= rng >> 7;
                rng ^= rng << 17;
                let (av, bv, ev, gv) = (rng as u128 & m, (rng >> 20) as u128 & m, (rng >> 40) as u128 & 1, (rng >> 3) as u128 & ((m << 1) | 1));
                put(&mut q, &a, av, l);
                put(&mut q, &b, bv, l);
                put(&mut q, &[e], ev, l);
                put(&mut q, &g, gv, l);
                lanes.push((av, bv, ev, gv));
            }
            let mut s = Sim { q, b: vec![0; nb], phase: 0, garbage: 0, rng: 7 };
            s.run(&ops);
            assert_eq!(s.phase, 0);
            for (l, &(av, bv, ev, gv)) in lanes.iter().enumerate() {
                assert_eq!(get(&s.q, &a, l), av);
                assert_eq!(get(&s.q, &b, l), (av + bv + ev) & m, "ttk+cinc k={k}");
                assert_eq!(get(&s.q, &g, l), gv);
                assert_eq!(get(&s.q, &[e], l), ev);
            }
        }
        let ttk = ops[..s1].iter().filter(|o| matches!(o.kind, K::CCX)).count();
        let ci = ops[s1..].iter().filter(|o| matches!(o.kind, K::CCX)).count();
        assert_eq!(ci, cinc_cost(k));
        println!("PRIM k={k} ttk_add_T={ttk} cinc_T={ci}");
        // ttk_add_cout exhaustive/random check
        let mut c2 = Builder::new();
        let a2 = c2.alloc_qubits(k);
        let b2 = c2.alloc_qubits(k);
        let z2 = c2.alloc_qubit();
        ttk_add_cout(&mut c2, &a2, &b2, z2);
        let (nq2, nb2) = c2.i13_dims();
        let ops2 = c2.take_ops();
        for _ in 0..16 {
            let mut q = vec![0u64; nq2];
            let mut lanes = Vec::new();
            for l in 0..64 {
                rng ^= rng << 13;
                rng ^= rng >> 7;
                rng ^= rng << 17;
                let (av, bv, zv) = (rng as u128 & m, (rng >> 20) as u128 & m, (rng >> 50) as u128 & 1);
                put(&mut q, &a2, av, l);
                put(&mut q, &b2, bv, l);
                put(&mut q, &[z2], zv, l);
                lanes.push((av, bv, zv));
            }
            let mut s = Sim { q, b: vec![0; nb2], phase: 0, garbage: 0, rng: 7 };
            s.run(&ops2);
            for (l, &(av, bv, zv)) in lanes.iter().enumerate() {
                assert_eq!(get(&s.q, &a2, l), av);
                assert_eq!(get(&s.q, &b2, l), (av + bv) & m, "ttk_cout k={k}");
                assert_eq!(get(&s.q, &[z2], l), zv ^ ((av + bv) >> k), "ttk_cout carry k={k}");
            }
        }
        println!("PRIM k={k} ttk_add_cout_T={}", ops2.iter().filter(|o| matches!(o.kind, K::CCX)).count());
    }
    let trials: usize = std::env::var("LOWROOM_TRIALS").ok().and_then(|s| s.parse().ok()).unwrap_or(64);
    if std::env::var_os("LOWROOM_TABLE").is_some() {
        // n = w - 1 bits, every (n, room) a fold site can have; T_expected of the new construction and of the
        // existing direct_add at the room it needs (verified with `trials` x 64 random lanes each).
        println!("TAB	n	room	T_new	T_existing	dT	peak	plan");
        for w in 40..=57usize {
            let (_, be, _, _) = verify(w, None, true, trials);
            for room in 0..=12usize {
                let (_, ne, np, nd) = verify(w, Some(room), true, trials);
                assert!(np as usize <= room);
                println!("TAB	{}	{room}	{ne:.1}	{be:.1}	{:.1}	{np}	{nd}", w - 1, ne - be);
            }
        }
        return;
    }
    for joint in [false, true] {
        for w in [43usize, 50, 54] {
            let (bn, be, bp, bd) = verify(w, None, joint, trials);
            println!("FOLD w={w} joint={} existing: T_native={bn} T_expected={be:.1} extra_peak={bp} [{bd}]", joint as u8);
            for room in 0..=12usize {
                let (nn, ne, np, nd) = verify(w, Some(room), joint, trials);
                assert!(np as usize <= room, "peak {np} > room {room}");
                println!("FOLD w={w} joint={} room={room} T_native={nn} T_expected={ne:.1} dT_expected={:.1} extra_peak={np} plan=[{nd}]", joint as u8, ne - be);
            }
        }
    }
    let _ = BitId(0);
}
