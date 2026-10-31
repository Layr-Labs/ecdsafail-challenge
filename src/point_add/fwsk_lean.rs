//! fwsk: LEAN room-0 folds for the late field cells (two selector wires fewer than the SQ_FOLDSETUP folds).
//!
//! The SQ_LOWROOM room-0 fold (`lowroom::signed_room0`) only ever READS its selectors one or two at a time:
//! `minus` drives two Clifford complement sweeps, `first ^ minus` drives one controlled increment, and the paired
//! U/V increments read `u = plus ^ minus` (a linear function of live wires) and `v = plus2`. The SQ_FOLDSETUP
//! callers nevertheless hold `first`, `minus` and `plus2` on three clean wires for the whole fold. Here each
//! selector is materialised on ONE clean wire only while it is read (a three-input AND computed with one borrowed
//! idle tape wire, 4 Toffoli), and measured out (X-basis, phase repaired under the outcome) right after. The
//! fold emits exactly the same data operations on the window as the SQ_LOWROOM room-0 path, so its output is
//! identical; only the selector bookkeeping differs. Enabled by `FWSK_LEAN` and used only where the base fold
//! setup would exceed the cap.
use super::builder::Builder;
use crate::circuit::QubitId;
use alloy_primitives::U256;

type Q = QubitId;

pub(crate) fn enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("FWSK_LEAN").is_some())
}

/// `FWSK_LEAN_ROOM=k`: also take the lean fold when the base setup would leave its fold fewer than k clean wires
/// (the base windowed fold at 1-3 wires of room costs more than the lean room-0 fold).
fn lean_margin() -> usize {
    static M: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *M.get_or_init(|| std::env::var("FWSK_LEAN_ROOM").ok().and_then(|v| v.parse().ok()).unwrap_or(0))
}

fn cap() -> usize {
    super::walk_policy::physical_cap()
}

/// `out ^= AND_i (q_i == pol_i)` for three controls, with one borrowed dirty wire `g` (restored). 4 Toffoli.
fn and3_into(c: &mut Builder, ctl: [(Q, bool); 3], out: Q, g: Q) {
    for &(q, pos) in &ctl { if !pos { c.x(q); } }
    let [(a, _), (b, _), (d, _)] = ctl;
    c.ccx(a, b, g);
    c.ccx(g, d, out);
    c.ccx(a, b, g);
    c.ccx(g, d, out);
    for &(q, pos) in &ctl { if !pos { c.x(q); } }
}

/// Phase `(-1)^(AND_i (q_i == pol_i))` under the pushed condition, with one borrowed dirty wire `g`.
fn and3_phase(c: &mut Builder, ctl: [(Q, bool); 3], g: Q) {
    for &(q, pos) in &ctl { if !pos { c.x(q); } }
    let [(a, _), (b, _), (d, _)] = ctl;
    c.ccx(a, b, g);
    c.cz(g, d);
    c.ccx(a, b, g);
    c.cz(g, d);
    for &(q, pos) in &ctl { if !pos { c.x(q); } }
}

/// Measure out a wire holding the three-input AND `ctl` (X basis) and repair its phase. Frees the wire.
fn and3_unmeasure(c: &mut Builder, ctl: [(Q, bool); 3], w: Q, g: Q) {
    let m = c.alloc_bit();
    c.hmr(w, m);
    c.push_condition(m);
    and3_phase(c, ctl, g);
    c.pop_condition();
    c.free_bit(m);
    c.free(w);
}

/// Signed-digit expansion used by `lowroom::signed_room0`.
fn digits(mut x: u128, n: usize) -> Vec<(usize, bool)> {
    let mut out = Vec::new();
    let mut i = 0;
    while x != 0 && i < n {
        if x & 1 != 0 {
            let neg = x & 3 == 3;
            if neg { x += 1; } else { x -= 1; }
            out.push((i, neg));
        }
        x >>= 1;
        i += 1;
    }
    out
}

struct Consts { c1: u128, c2: u128 }

fn consts(f: U256, n: usize) -> Option<Consts> {
    let lim = f.as_limbs();
    if lim[2] != 0 || lim[3] != 0 { return None; }
    let fu = lim[0] as u128 | (lim[1] as u128) << 64;
    let w = n + 1;
    if w >= 127 { return None; }
    let mw: u128 = (1u128 << w) - 1;
    let fw = fu & mw;
    if fw & 1 != 1 { return None; }
    let c1 = fw >> 1;
    let c2 = ((fw << 1) & mw) >> 1;
    let ud = digits(c1, n);
    let vd = digits(c2, n);
    let paired = c2 == 2 * c1 + 1 && vd.len() == ud.len() + 1 && vd[0] == (0, false)
        && ud.iter().zip(&vd[1..]).all(|(&(p, neg), &(q, sign))| q == p + 1 && sign == neg);
    paired.then_some(Consts { c1, c2 })
}

/// The paired U/V section of `lowroom::signed_room0` (V0+ then one shared suffix increment per U digit).
fn paired_uv(c: &mut Builder, b: &[Q], k: &Consts, ue: Q, ve: Q, dirty: &[Q]) {
    let _ = k.c2;
    super::lowroom::cinc_dirty(c, ve, b, &dirty[..b.len() + 1]);
    for (p, neg) in digits(k.c1, b.len()) {
        if neg { c.x_all(&b[p..]); }
        c.ccx(ue, b[p], ve);
        c.cx(ue, b[p]);
        super::lowroom::cinc_dirty(c, ve, &b[p + 1..], &dirty[..b.len() - p]);
        c.x(b[p]);
        c.ccx(ue, b[p], ve);
        c.x(b[p]);
        if neg { c.x_all(&b[p..]); }
    }
}

fn pool_for(used: &[Q], need: usize) -> Option<Vec<Q>> {
    let pool: Vec<Q> = super::lowroom::pool_snapshot().into_iter().filter(|q| !used.contains(q)).collect();
    (pool.len() >= need).then_some(pool)
}

static SITES: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// `FWSK_SPLIT=s`: split the room-0 fold's increments at bit `s` with one more clean wire `X` (the low part's
/// carry). The increments below `s` run on the (s+1)-bit register `[b[..s], X]`, `b[s..] += X` carries once, the
/// low increments are undone and replayed on `b[..s]` alone (mod 2^s), which returns `X` to zero exactly. Every
/// low increment is then `s + 1` bits long instead of `n`.
fn split_at() -> usize {
    static M: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *M.get_or_init(|| std::env::var("FWSK_SPLIT").ok().and_then(|v| v.parse().ok()).unwrap_or(0))
}

/// x -= e (mod 2^k): the complement of [`lowroom::cinc_dirty`].
fn cdec_dirty(c: &mut Builder, e: Q, x: &[Q], g: &[Q]) {
    c.x_all(x);
    super::lowroom::cinc_dirty(c, e, x, g);
    c.x_all(x);
}

/// One paired U/V digit step on register `r` at position `p` (suffix r[p+1..]), forward or inverse.
fn uv_step(c: &mut Builder, r: &[Q], p: usize, neg: bool, ue: Q, ve: Q, dirty: &[Q], inverse: bool) {
    let suf = &r[p + 1..];
    if neg { c.x_all(&r[p..]); }
    if !inverse {
        c.ccx(ue, r[p], ve);
        c.cx(ue, r[p]);
        super::lowroom::cinc_dirty(c, ve, suf, &dirty[..suf.len() + 1]);
        c.x(r[p]);
        c.ccx(ue, r[p], ve);
        c.x(r[p]);
    } else {
        c.x(r[p]);
        c.ccx(ue, r[p], ve);
        c.x(r[p]);
        cdec_dirty(c, ve, suf, &dirty[..suf.len() + 1]);
        c.cx(ue, r[p]);
        c.ccx(ue, r[p], ve);
    }
    if neg { c.x_all(&r[p..]); }
}

/// The paired U/V increments restricted to digits p < lim on register r (V0 first), forward or inverse.
fn uv_low(c: &mut Builder, r: &[Q], k: &Consts, n: usize, lim: usize, ue: Q, ve: Q, dirty: &[Q], inverse: bool) {
    let ds: Vec<(usize, bool)> = digits(k.c1, n).into_iter().filter(|&(p, _)| p < lim).collect();
    let v0 = !cv_merge();
    if !inverse {
        if v0 { super::lowroom::cinc_dirty(c, ve, r, &dirty[..r.len() + 1]); }
        for &(p, neg) in &ds { uv_step(c, r, p, neg, ue, ve, dirty, false); }
    } else {
        for &(p, neg) in ds.iter().rev() { uv_step(c, r, p, neg, ue, ve, dirty, true); }
        if v0 { cdec_dirty(c, ve, r, &dirty[..r.len() + 1]); }
    }
}

/// `FWSK_CV=1`: the carry-in `first'` and the V digit at bit 0 are exclusive (first' & v = 0 on every caller's
/// domain), so their two bit-0 increments merge into one increment controlled by `first' ^ v`.
fn cv_merge() -> bool {
    static M: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *M.get_or_init(|| std::env::var_os("FWSK_CV").is_some())
}

type WithFirst<'a> = dyn Fn(&mut Builder, &mut dyn FnMut(&mut Builder, Q)) + 'a;
type WithUv<'a> = dyn Fn(&mut Builder, &mut dyn FnMut(&mut Builder, Q, Q)) + 'a;

/// The room-0 fold increments `b += first' + u*C1 + v*C2` (complement frame already applied by the caller).
/// `with_first` / `with_uv` materialise the selectors for the duration of their body. `x` = the split wire.
fn fold_body(c: &mut Builder, b: &[Q], k: &Consts, x: Option<Q>, dirty: &[Q], with_first: &WithFirst, with_uv: &WithUv) {
    let n = b.len();
    let Some(x) = x else {
        with_first(c, &mut |c, w| super::lowroom::cinc_dirty(c, w, b, &dirty[..n + 1]));
        if cv_merge() {
            with_uv(c, &mut |c, ue, ve| uv_low(c, b, k, n, n, ue, ve, dirty, false));
        } else {
            with_uv(c, &mut |c, ue, ve| paired_uv(c, b, k, ue, ve, dirty));
        }
        return;
    };
    let s = split_at();
    // The low part must be a carry, never a borrow: the partial signed-digit sums below s are non-negative and
    // the (s+1)-bit register cannot overflow (b_low < 2^s, low addend <= 1 + max(u part, v part)).
    {
        let mut su: i128 = 0;
        for (p, neg) in digits(k.c1, n) { if p < s { su += if neg { -(1i128 << p) } else { 1i128 << p }; } }
        let mut sv: i128 = 1;
        for (p, neg) in digits(k.c1, n) { if p + 1 < s + 1 && p < s { sv += if neg { -(1i128 << (p + 1)) } else { 1i128 << (p + 1) }; } }
        assert!(su >= 0 && sv >= 0 && (1i128 << s) - 1 + 1 + su.max(sv) < (1i128 << (s + 1)), "FWSK_SPLIT={s}: low part not a pure carry (u {su}, v {sv})");
    }
    let mut reg: Vec<Q> = b[..s].to_vec();
    reg.push(x);
    let hi: Vec<(usize, bool)> = digits(k.c1, n).into_iter().filter(|&(p, _)| p >= s).collect();
    // A: low increments on [b[..s], X]; the carry into bit s lands in X.
    with_first(c, &mut |c, w| super::lowroom::cinc_dirty(c, w, &reg, &dirty[..reg.len() + 1]));
    with_uv(c, &mut |c, ue, ve| {
        uv_low(c, &reg, k, n, s, ue, ve, dirty, false);
        // carry once into the high part, then the high digits on the full window
        super::lowroom::cinc_dirty(c, x, &b[s..], &dirty[..n - s + 1]);
        for &(p, neg) in &hi { uv_step(c, b, p, neg, ue, ve, dirty, false); }
        // B (part 1): undo the low U/V increments on [b[..s], X]
        uv_low(c, &reg, k, n, s, ue, ve, dirty, true);
    });
    // B (part 2): undo the low carry-in increment; X is zero again
    with_first(c, &mut |c, w| cdec_dirty(c, w, &reg, &dirty[..reg.len() + 1]));
    // C: replay the low increments on b[..s] alone (mod 2^s)
    with_first(c, &mut |c, w| super::lowroom::cinc_dirty(c, w, &b[..s], &dirty[..s + 1]));
    with_uv(c, &mut |c, ue, ve| uv_low(c, &b[..s], k, n, s, ue, ve, dirty, false));
}

/// The split wire, when FWSK_SPLIT is set and one more clean wire fits (`extra` = wires the lean fold already holds).
fn split_wire(c: &mut Builder, n: usize, extra: usize) -> Option<Q> {
    let s = split_at();
    if s == 0 || s + 2 >= n { return None; }
    if c.active_qubits() as usize + extra + 1 > cap() { return None; }
    Some(c.alloc_qubit())
}

/// Division fold (replaces `fold_halve_reused_lowroom` when its 3-selector setup would exceed the cap).
/// Entry: `sign` holds s, `target[0]` holds p (the parity), `o` the add's overflow. Exit as the base:
/// `sign` = s, `target[0]` = p ^ o, `target[1..]` += the selected fold.
pub(crate) fn fold_halve(c: &mut Builder, target: &[Q], sign: Q, o: Q, f: U256) -> bool {
    if super::walk_zero::needed(c) {super::walk_zero::halve(c,target,sign,o,f);return true;}
    if !enabled() || !super::lowroom::enabled() { return false; }
    if c.active_qubits() as usize + 3 + lean_margin() <= cap() { return false; }
    let b = &target[1..];
    let n = b.len();
    let Some(k) = consts(f, n) else { return false };
    let mut used: Vec<Q> = target.to_vec();
    used.extend([sign, o]);
    let Some(pool) = pool_for(&used, n + 3) else { return false };
    let g = pool[n + 2];
    let dirty = &pool[..n + 2];
    let t0_before = c.report_totals().map_or(0.0, |x| x.1);
    let live0 = c.active_qubits();
    c.swap(sign, target[0]); // sign = p, t0 = s
    let t0 = target[0];
    let mi = [(o, false), (t0, false), (sign, true)]; // minus  = !o & !s & p
    let fi = [(o, true), (t0, false), (sign, true)]; // first' = first ^ minus = o & !s & p
    let vi = [(o, true), (t0, true), (sign, true)]; // plus2  = o & s & p
    // complement under minus
    let w = c.alloc_qubit();
    and3_into(c, mi, w, g);
    c.cx_all(w, b);
    and3_unmeasure(c, mi, w, g);
    let x = split_wire(c, n, 1);
    let with_first = |c: &mut Builder, body: &mut dyn FnMut(&mut Builder, Q)| {
        let w = c.alloc_qubit();
        if cv_merge() {
            // first' ^ plus2 = o & p
            c.ccx(o, sign, w);
            body(c, w);
            let m = c.alloc_bit();
            c.walk_and_marker(w,o,sign,m);c.hmr(w, m);
            c.cz_if(o, sign, m);
            c.free_bit(m);
            c.free(w);
            return;
        }
        and3_into(c, fi, w, g);
        body(c, w);
        and3_unmeasure(c, fi, w, g);
    };
    let with_uv = |c: &mut Builder, body: &mut dyn FnMut(&mut Builder, Q, Q)| {
        let w = c.alloc_qubit();
        and3_into(c, vi, w, g);
        c.cx(t0, sign); // u = p ^ s hosted in sign
        body(c, sign, w);
        c.cx(t0, sign);
        and3_unmeasure(c, vi, w, g);
    };
    fold_body(c, b, &k, x, dirty, &with_first, &with_uv);
    if let Some(x) = x { c.free(x); }
    // undo the complement
    let w = c.alloc_qubit();
    and3_into(c, mi, w, g);
    c.cx_all(w, b);
    and3_unmeasure(c, mi, w, g);
    c.swap(sign, target[0]); // sign = s, t0 = p
    c.cx(o, target[0]);
    assert_eq!(c.active_qubits(), live0);
    let i = SITES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    eprintln!("FWSK_LEAN div site={i} n={n} live={live0} split={} T={:.1}", x.is_some() as u8, c.report_totals().map_or(0.0, |x| x.1) - t0_before);
    true
}

/// Multiply fold (replaces the SQ_FOLDSETUP branch of `fold_double_joint` when its setup would exceed the cap).
/// Same contract as that function: z0 = s ^ v0 at entry; at exit z0 ^= d ^ o, z[1..] += the selected fold,
/// s, v0, d, o unchanged.
pub(crate) fn fold_double(c: &mut Builder, z: &[Q], s: Q, v0: Q, d: Q, o: Q, pre: bool, f: U256) -> bool {
    if !enabled() || !super::lowroom::enabled() { return false; }
    if c.active_qubits() as usize + 2 + lean_margin() <= cap() { return false; }
    let b = &z[1..];
    let n = b.len();
    let Some(k) = consts(f, n) else { return false };
    let mut used: Vec<Q> = z.to_vec();
    used.extend([s, v0, d, o]);
    let Some(pool) = pool_for(&used, n + 3) else { return false };
    let g = pool[n + 2];
    let dirty = &pool[..n + 2];
    let t0_before = c.report_totals().map_or(0.0, |x| x.1);
    let live0 = c.active_qubits();
    let z0 = z[0];
    // finish bit 0 and release d (d = z0' ^ s ^ v0 ^ o afterwards)
    c.cx(d, z0);
    c.cx(o, z0);
    for q in [z0, s, v0, o] { c.cx(q, d); }
    c.release_clean(d);
    let host_d = |c: &mut Builder| { c.cx(s, z0); c.cx(v0, z0); c.cx(o, z0); }; // z0' <-> d
    let mi = [(z0, true), (o, false), (s, true)]; // minus = d & !o & s   (z0 hosting d)
    let ai = [(z0, true), (o, true), (s, false)]; // plus2 = d & o & !s   (z0 hosting d)
    // complement under minus
    let w = c.alloc_qubit();
    host_d(c);
    and3_into(c, mi, w, g);
    host_d(c);
    c.cx_all(w, b);
    host_d(c);
    and3_unmeasure(c, mi, w, g);
    host_d(c);
    let first_ctl = |c: &mut Builder, out: Option<Q>, m: Option<crate::circuit::BitId>| {
        // first (non-pre) = !z0' & (v0 ^ s); (pre) = MAJ(s, v0, !z0') = (s^x)&(v0^x) ^ x with x = !z0'.
        if pre {
            c.x(z0); c.cx(z0, s); c.cx(z0, v0);
            match (out, m) { (Some(w), _) => { c.ccx(s, v0, w); c.cx(z0, w); } (None, Some(m)) => { c.cz_if(s, v0, m); c.z_if(z0, m); } _ => unreachable!() }
            c.cx(z0, s); c.cx(z0, v0); c.x(z0);
        } else {
            c.cx(s, v0); c.x(z0);
            match (out, m) { (Some(w), _) => c.ccx(z0, v0, w), (None, Some(m)) => c.cz_if(z0, v0, m), _ => unreachable!() }
            c.x(z0); c.cx(s, v0);
        }
    };
    let x = split_wire(c, n, 1);
    let with_first = |c: &mut Builder, body: &mut dyn FnMut(&mut Builder, Q)| {
        // first ^ minus on one wire
        let w = c.alloc_qubit();
        first_ctl(c, Some(w), None);
        host_d(c);
        and3_into(c, mi, w, g);
        if cv_merge() { and3_into(c, ai, w, g); }
        host_d(c);
        body(c, w);
        let m = c.alloc_bit();
        c.hmr(w, m);
        first_ctl(c, None, Some(m));
        host_d(c);
        c.push_condition(m);
        and3_phase(c, mi, g);
        if cv_merge() { and3_phase(c, ai, g); }
        c.pop_condition();
        host_d(c);
        c.free_bit(m);
        c.free(w);
    };
    let with_uv = |c: &mut Builder, body: &mut dyn FnMut(&mut Builder, Q, Q)| {
        // u = d ^ o hosted in z0, v = plus2 on one wire
        let w = c.alloc_qubit();
        host_d(c);
        and3_into(c, ai, w, g);
        c.cx(o, z0); // z0 = d ^ o = u
        body(c, z0, w);
        c.cx(o, z0); // z0 = d
        and3_unmeasure(c, ai, w, g);
        host_d(c);
    };
    fold_body(c, b, &k, x, dirty, &with_first, &with_uv);
    if let Some(x) = x { c.free(x); }
    // undo the complement
    let w = c.alloc_qubit();
    host_d(c);
    and3_into(c, mi, w, g);
    host_d(c);
    c.cx_all(w, b);
    host_d(c);
    and3_unmeasure(c, mi, w, g);
    host_d(c);
    c.reacquire(d);
    for q in [z0, s, v0, o] { c.cx(q, d); }
    assert_eq!(c.active_qubits(), live0);
    let i = SITES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    eprintln!("FWSK_LEAN mul site={i} n={n} pre={} live={live0} split={} T={:.1}", pre as u8, x.is_some() as u8, c.report_totals().map_or(0.0, |x| x.1) - t0_before);
    true
}

/// Terminal-pair fold (replaces `terminal_fold_early` when its 3-selector setup would exceed the cap).
/// Entry: z0 = Z, o = O (live, counted), d, t, q0. Exit: z0 = Z ^ O ^ d, z[1..] += the selected fold,
/// o, d, t, q0 unchanged. Selectors: minus = d & !O & t, plus2 = d & O & !t, first = Z & (O ^ d),
/// u = z0_f ^ t ^ q0_f with z0_f = Z ^ O ^ d (forward) or Z (inverse, where q0 is complemented for the fold).
pub(crate) fn fold_terminal(c: &mut Builder, z: &[Q], t: Q, q0: Q, d: Q, o: Q, inverse: bool, f: U256) -> bool {
    if super::walk_zero::needed(c) {super::walk_zero::terminal(c,z,t,q0,d,o,inverse,f);return true;}
    if !enabled() || !super::lowroom::enabled() { return false; }
    if c.active_qubits() as usize + 3 + lean_margin() <= cap() { return false; }
    let b = &z[1..];
    let n = b.len();
    let Some(k) = consts(f, n) else { return false };
    let mut used: Vec<Q> = z.to_vec();
    used.extend([t, q0, d, o]);
    let Some(pool) = pool_for(&used, n + 3) else { return false };
    let g = pool[n + 2];
    let dirty = &pool[..n + 2];
    let t0_before = c.report_totals().map_or(0.0, |x| x.1);
    let live0 = c.active_qubits();
    let z0 = z[0];
    if inverse { c.x(q0); } else { c.cx(o, z0); c.cx(d, z0); }
    let mi = [(d, true), (o, false), (t, true)];
    let ai = [(d, true), (o, true), (t, false)];
    // Z onto z0 and (O ^ d) onto o for the first-carry AND, and back.
    let host_first = |c: &mut Builder| { c.cx(d, o); if !inverse { c.cx(o, z0); } };
    let unhost_first = |c: &mut Builder| { if !inverse { c.cx(o, z0); } c.cx(d, o); };
    // complement under minus
    let w = c.alloc_qubit();
    and3_into(c, mi, w, g);
    c.cx_all(w, b);
    and3_unmeasure(c, mi, w, g);
    let x = split_wire(c, n, 1);
    let with_first = |c: &mut Builder, body: &mut dyn FnMut(&mut Builder, Q)| {
        let w = c.alloc_qubit();
        host_first(c);
        c.ccx(z0, o, w);
        unhost_first(c);
        and3_into(c, mi, w, g);
        if cv_merge() { and3_into(c, ai, w, g); }
        body(c, w);
        let m = c.alloc_bit();
        c.hmr(w, m);
        host_first(c);
        c.cz_if(z0, o, m);
        unhost_first(c);
        c.push_condition(m);
        and3_phase(c, mi, g);
        if cv_merge() { and3_phase(c, ai, g); }
        c.pop_condition();
        c.free_bit(m);
        c.free(w);
    };
    let with_uv = |c: &mut Builder, body: &mut dyn FnMut(&mut Builder, Q, Q)| {
        let w = c.alloc_qubit();
        and3_into(c, ai, w, g);
        c.cx(t, z0);
        c.cx(q0, z0);
        body(c, z0, w);
        c.cx(q0, z0);
        c.cx(t, z0);
        and3_unmeasure(c, ai, w, g);
    };
    fold_body(c, b, &k, x, dirty, &with_first, &with_uv);
    if let Some(x) = x { c.free(x); }
    // undo the complement
    let w = c.alloc_qubit();
    and3_into(c, mi, w, g);
    c.cx_all(w, b);
    and3_unmeasure(c, mi, w, g);
    if inverse { c.x(q0); c.cx(o, z0); c.cx(d, z0); }
    assert_eq!(c.active_qubits(), live0);
    let i = SITES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    eprintln!("FWSK_LEAN term site={i} n={n} inv={} live={live0} split={} T={:.1}", inverse as u8, x.is_some() as u8, c.report_totals().map_or(0.0, |x| x.1) - t0_before);
    true
}

/// `FWSK_LATE_PREV=label:t,t,...;label:...` -- decode typ_{t-1} late inside the reverse tick at these ticks.
pub(crate) fn late_prev(label: &str, t: usize) -> bool {
    static SPEC: std::sync::OnceLock<Vec<(String, usize)>> = std::sync::OnceLock::new();
    let spec = SPEC.get_or_init(|| std::env::var("FWSK_LATE_PREV").ok().map(|v| {
        v.split('/').filter(|x| !x.is_empty()).flat_map(|it| {
            let (l, ts) = it.split_once(':').expect("label:t,t");
            ts.split(',').map(|x| (l.to_string(), x.trim().parse::<usize>().unwrap())).collect::<Vec<_>>()
        }).collect()
    }).unwrap_or_default());
    spec.iter().any(|(l, u)| l == label && *u == t)
}
