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
    super::pingpong::heo_hooks::cap()
}

/// Three-input AND: 3 Toffoli with a transient clean lane, else 4 with restored dirty `g`.
fn and3_into(c: &mut Builder, ctl: [(Q, bool); 3], out: Q, g: Q) {
    for &(q, pos) in &ctl { if !pos { c.x(q); } }
    let [(a, _), (b, _), (d, _)] = ctl;
    // C60: spend a transient clean lane when it fits. It is returned before
    // the fold body, so the existing split and carry plans are unchanged.
    if (c.active_qubits() as usize) < cap() {
        let t = c.alloc_qubit();
        c.ccx(a, b, t);
        c.ccx(t, d, out);
        c.ccx(a, b, t);
        c.release_clean(t);
    } else {
        c.ccx(a, b, g); c.ccx(g, d, out);
        c.ccx(a, b, g); c.ccx(g, d, out);
    }
    for &(q, pos) in &ctl { if !pos { c.x(q); } }
}

/// Three-input phase under the pushed condition, with a zero-valued selector wire.
// C60: `w` is the selector just X-reset by the caller. Reuse its known
// zero as a coherent phase ladder and restore it without a new measurement.
fn and3_phase(c: &mut Builder, ctl: [(Q, bool); 3], w: Q) {
    for &(q, pos) in &ctl { if !pos { c.x(q); } }
    let [(a, _), (b, _), (d, _)] = ctl;
    c.ccx(a, b, w); c.cz(w, d);
    c.ccx(a, b, w);
    for &(q, pos) in &ctl { if !pos { c.x(q); } }
}

/// Measure out a wire holding the three-input AND `ctl` (X basis) and repair its phase. Frees the wire.
fn and3_unmeasure(c: &mut Builder, ctl: [(Q, bool); 3], w: Q, g: Q) {
    let m = c.alloc_bit();
    c.hmr(w, m);
    c.push_condition(m);
    and3_phase(c, ctl, w);
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
    if !enabled() || !super::lowroom::enabled() { return false; }
    if c79_window_halve(c,target,sign,o,f) {return true;}
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
            c.hmr(w, m);
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
    if c79_window_double(c,z,s,v0,d,o,pre,f) {return true;}
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
        and3_phase(c, mi, w);
        if cv_merge() { and3_phase(c, ai, w); }
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
        and3_phase(c, mi, w);
        if cv_merge() { and3_phase(c, ai, w); }
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





// C79: exact lean selectors around the existing lowroom window arithmetic.
fn c79_rows(n: usize, c1: u128, c2: u128, u: Q, v: Q) -> Vec<Vec<Q>> {
    (0..n).map(|i| {
        let mut r=Vec::new();
        if c1>>i&1!=0 {r.push(u);}
        if c2>>i&1!=0 {r.push(v);}
        r
    }).collect()
}

fn c79_quote(n: usize, f: u128, room: usize, merged: bool) -> f64 {
    use std::sync::{Mutex,OnceLock};
    static CACHE:OnceLock<Mutex<std::collections::HashMap<(usize,u128,usize,bool),f64>>>=OnceLock::new();
    let cache=CACHE.get_or_init(||Mutex::new(std::collections::HashMap::new()));
    let key=(n,f,room,merged);
    if let Some(&x)=cache.lock().unwrap().get(&key) {return x;}
    let mut b=Builder::new();let data=b.alloc_qubits(n);
    let u=b.alloc_qubit();let v=b.alloc_qubit();let m=b.alloc_qubit();let e=b.alloc_qubit();let dirty=b.alloc_qubits(n+2);
    if merged {
        let c1=f>>1;let c2=(f&((1u128<<n)-1)).wrapping_sub(1)&((1u128<<n)-1);
        let rows=c79_rows(n,c1,c2,u,v);
        super::lowroom::windowed_add(&mut b,&rows,&data,Some(e),room,&dirty);
    } else {
        super::lowroom::lowroom_fold(&mut b,&data,f,&[u],&[v],m,e,room,&dirty);
    }
    let mut depth=0i32;let mut cost=0.0;
    for o in b.take_ops() {
        use crate::circuit::OperationType as K;
        match o.kind {
            K::PushCondition=>depth+=1,K::PopCondition=>depth-=1,
            K::CCX|K::CCZ=>cost+=0.5f64.powi(depth),_=>{}
        }
    }
    assert_eq!(depth,0);cache.lock().unwrap().insert(key,cost);cost
}

fn c79_lent_quote(n:usize,k:&Consts,room:usize,mul:bool)->f64 {
    let mut c=Builder::new();let b=c.alloc_qubits(n);let u=c.alloc_qubit();let v=c.alloc_qubit();let e=c.alloc_qubit();let dirty=c.alloc_qubits(n+2);
    let rows=c79_rows(n,k.c1,k.c2-1,u,v);let cost=if mul{9.0}else{1.0};
    let loan=|c:&mut Builder,restore:bool|{if restore{c.reacquire(e);}else{c.free(e);}};
    let desc=super::lowroom::c79_windowed_add_lent(&mut c,&rows,&b,e,room,&dirty,cost,&loan);
    let mut depth=0i32;let mut price=0.0;
    for op in c.take_ops(){use crate::circuit::OperationType as K;match op.kind{K::PushCondition=>depth+=1,K::PopCondition=>depth-=1,K::CCX|K::CCZ=>price+=0.5f64.powi(depth),_=>{}}}
    price+if desc.contains("LW"){cost}else{0.0}
}

fn c79_choice(c:&Builder,n:usize,k:&Consts,mul:bool)->Option<(usize,f64,f64,bool)> {
    if std::env::var_os("C79_LEANWIN").is_none() || !enabled() || !super::lowroom::enabled() {return None;}
    let l=cap().saturating_sub(c.active_qubits() as usize);
    let setup=if mul {2}else{3};
    let lean=l<setup+lean_margin();
    // R03 is confined to folds whose original direct add did not fit.
    let force=std::env::var_os("C79_LW_FORCE").is_some();
    if !force && !lean && super::width_composition::direct_plan_inner(n,l-setup).is_some(){return None;}
    let room=l.checked_sub(if mul {1}else{2})?;
    if room<3 {return None;}
    let f=2*k.c1+1;
    let old=if lean {(if mul {169.0}else{139.0})+8.0*n as f64-12.0}
        else {c79_quote(n,f,l-setup,false)+3.0};
    // Actual clean-lane AND3 costs 3 compute + 1 expected phase repair.
    let new=c79_lent_quote(n,k,room,mul)+if mul {21.0}else{13.0};
    eprintln!("C79_LW_PRICE dir={} n={n} L={l} room={room} lean={} old={old:.1} new={new:.1} choose={}",if mul{"mul"}else{"div"},lean as u8,(new+5.0<old) as u8);
    (force||new+5.0<old).then_some((room,old,new,lean))
}

pub(crate) fn c79_window_halve(c:&mut Builder,target:&[Q],sign:Q,o:Q,f:U256)->bool {
    let b=&target[1..];let n=b.len();let Some(k)=consts(f,n)else{return false};
    let Some((room,old,quote,lean))=c79_choice(c,n,&k,false)else{return false};
    let mut used=target.to_vec();used.extend([sign,o]);
    let Some(pool)=pool_for(&used,n+3)else{return false};let g=pool[n+2];let dirty=&pool[..n+2];
    let start=c.report_totals().map_or(0.0,|x|x.1);let live=c.active_qubits();
    c.swap(sign,target[0]);let s=target[0];
    let mi=[(o,false),(s,false),(sign,true)];let vi=[(o,true),(s,true),(sign,true)];
    let w=c.alloc_qubit();and3_into(c,mi,w,g);c.cx_all(w,b);and3_unmeasure(c,mi,w,g);
    let e=c.alloc_qubit();c.ccx(o,sign,e); // e=first' XOR plus2 = o&p, disjoint terms
    let v=c.alloc_qubit();and3_into(c,vi,v,g);
    c.cx(s,sign); // U=p XOR s
    let rows=c79_rows(n,k.c1,k.c2-1,sign,v);
    let loan=|c:&mut Builder,restore:bool|{
        c.cx(s,sign);
        if restore {c.reacquire(e);c.ccx(o,sign,e);} else {let m=c.alloc_bit();c.hmr(e,m);c.cz_if(o,sign,m);c.free_bit(m);c.free(e);}
        c.cx(s,sign);
    };
    let plan=super::lowroom::c79_windowed_add_lent(c,&rows,b,e,room,dirty,1.0,&loan);
    c.cx(s,sign);and3_unmeasure(c,vi,v,g);
    let m=c.alloc_bit();c.hmr(e,m);c.cz_if(o,sign,m);c.free_bit(m);c.free(e);
    let w=c.alloc_qubit();and3_into(c,mi,w,g);c.cx_all(w,b);and3_unmeasure(c,mi,w,g);
    c.swap(sign,target[0]);c.cx(o,target[0]);
    assert_eq!(c.active_qubits(),live);
    eprintln!("C79_LEANWIN div n={n} room={room} R06={} old={old:.1} quote={quote:.1} T={:.1} plan=[{plan}]",lean as u8,c.report_totals().map_or(0.0,|x|x.1)-start);
    true
}

pub(crate) fn c79_window_double(c:&mut Builder,z:&[Q],s:Q,v0:Q,d:Q,o:Q,pre:bool,f:U256)->bool {
    let b=&z[1..];let n=b.len();let Some(k)=consts(f,n)else{return false};
    let Some((room,old,quote,lean))=c79_choice(c,n,&k,true)else{return false};
    let mut used=z.to_vec();used.extend([s,v0,d,o]);
    let Some(pool)=pool_for(&used,n+3)else{return false};let g=pool[n+2];let dirty=&pool[..n+2];
    let start=c.report_totals().map_or(0.0,|x|x.1);let live=c.active_qubits();let z0=z[0];
    c.cx(d,z0);c.cx(o,z0);for q in [z0,s,v0,o]{c.cx(q,d);}c.release_clean(d);
    let host_d=|c:&mut Builder|{c.cx(s,z0);c.cx(v0,z0);c.cx(o,z0);};
    let mi=[(z0,true),(o,false),(s,true)];let ai=[(z0,true),(o,true),(s,false)];
    let first_ctl=|c:&mut Builder,out:Option<Q>,m:Option<crate::circuit::BitId>|{
        if pre {
            c.x(z0);c.cx(z0,s);c.cx(z0,v0);
            match(out,m){(Some(w),_)=>{c.ccx(s,v0,w);c.cx(z0,w);},(None,Some(m))=>{c.cz_if(s,v0,m);c.z_if(z0,m);},_=>unreachable!()}
            c.cx(z0,s);c.cx(z0,v0);c.x(z0);
        }else{
            c.cx(s,v0);c.x(z0);
            match(out,m){(Some(w),_)=>c.ccx(z0,v0,w),(None,Some(m))=>c.cz_if(z0,v0,m),_=>unreachable!()}
            c.x(z0);c.cx(s,v0);
        }
    };
    let w=c.alloc_qubit();host_d(c);and3_into(c,mi,w,g);host_d(c);c.cx_all(w,b);host_d(c);and3_unmeasure(c,mi,w,g);host_d(c);
    let v=c.alloc_qubit();host_d(c);and3_into(c,ai,v,g);host_d(c);
    let e=c.alloc_qubit();first_ctl(c,Some(e),None);host_d(c);and3_into(c,mi,e,g);and3_into(c,ai,e,g);host_d(c);
    c.cx(s,z0);c.cx(v0,z0); // U=d XOR o
    let rows=c79_rows(n,k.c1,k.c2-1,z0,v);
    let loan=|c:&mut Builder,restore:bool|{
        c.cx(v0,z0);c.cx(s,z0);
        if restore {
            c.reacquire(e);first_ctl(c,Some(e),None);host_d(c);and3_into(c,mi,e,g);and3_into(c,ai,e,g);host_d(c);
        }else{
            let m=c.alloc_bit();c.hmr(e,m);first_ctl(c,None,Some(m));host_d(c);c.push_condition(m);and3_phase(c,mi,e);and3_phase(c,ai,e);c.pop_condition();host_d(c);c.free_bit(m);c.free(e);
        }
        c.cx(s,z0);c.cx(v0,z0);
    };
    let plan=super::lowroom::c79_windowed_add_lent(c,&rows,b,e,room,dirty,9.0,&loan);
    c.cx(v0,z0);c.cx(s,z0);
    let m=c.alloc_bit();c.hmr(e,m);first_ctl(c,None,Some(m));host_d(c);c.push_condition(m);and3_phase(c,mi,e);and3_phase(c,ai,e);c.pop_condition();host_d(c);c.free_bit(m);c.free(e);
    host_d(c);and3_unmeasure(c,ai,v,g);host_d(c);
    let w=c.alloc_qubit();host_d(c);and3_into(c,mi,w,g);host_d(c);c.cx_all(w,b);host_d(c);and3_unmeasure(c,mi,w,g);host_d(c);
    c.reacquire(d);for q in [z0,s,v0,o]{c.cx(q,d);}
    assert_eq!(c.active_qubits(),live);
    eprintln!("C79_LEANWIN mul n={n} room={room} pre={} R06={} old={old:.1} quote={quote:.1} T={:.1} plan=[{plan}]",pre as u8,lean as u8,c.report_totals().map_or(0.0,|x|x.1)-start);
    true
}
