//! SKY-COF walk tick: Skywalk signed rails (the `heo` rail tick) + Kaliski-frame integer cofactors,
//! public per-tick field widths, forward and exact reverse. Research code, inert in the default build.
//!
//! # State
//! * rails `(R1, R2)`: two's complement, LSB first, = an orientation of `(+-u, +-(u+v))` (Skywalk seed
//!   `(d + p, d)`); `v` odd.
//! * cofactors `(s, r)`: unsigned, LSB first, `s.len() == r.len()` at entry; Kaliski invariant
//!   `u s + v r = p` with `s` even and `r` odd before park (start `s = 0, r = 1`).
//!
//! # Forward tick (`fwd_tick`)
//! 1. Rail tick, gate for gate `heo::fwd_tick` (only the rail add is room-aware): `c = R1[0]`,
//!    Fredkin on `c`, `H = R1 >> 1` (relabel), `R2 -/+= H` (subtract when the signs agree). The freed
//!    rail LSB becomes `typ_t = typ_{t-1} xor c`; the add's sign wire ends as
//!    `isC = sign(R2_new) xor sign(R2_old)` (the Skywalk tape bit `s_t`).
//!    Letters: `typ = [A]` (u even), `isC = [C]` (u odd, u < v), B otherwise. At the park step
//!    (`u = v = 1`) the rails label the step C when `R2_old < 0` and B otherwise; both give `u = 0`,
//!    `r = p`; C gives `s_park = 2 r_old = -2 s_old (mod p)`, so the sign wire must count C as labelled.
//!    After park `typ = 1` and `isC = 0` on every tick.
//! 2. Cofactors: `Fredkin(isC; s, r)` (bit 0 by two CNOTs: `s0 = 0, r0 = 1` whenever `isC = 1`),
//!    `r += s` controlled on `not typ` (B or C), then `s <- 2s` by relabel (a fresh zero LSB).
//! 3. `isC` is erased by HMR with the phase repair `CZ(s_new[1], not typ)` (`isC = s_new[1] and not typ`).
//!
//! Widths: rails `wsw` at the swap, `wad` at the add (post-tick). Cofactors: `r` ends at
//! `ecof` wires; `s` ends at `ecof` wires, except when `ecof == clamp` and the entry width is already
//! `>= clamp`: then `s` ends at `clamp + 1` wires, the top wire being `2s >> clamp` (the park fold
//! flag; 0 on every pre-park tick). The caller folds it (`s <- 2s mod p`) or frees it before the next
//! tick. Trimmed wires must be zero (rails: sign copies) -- the envelope's promise.
//!
//! # Reverse tick (`rev_tick`)
//! Given `typ_t` (from the decoder) and `typ_{t-1}`: `isC = s[1] and not typ` (1 CCX), undo the
//! relabel, `r -= s` controlled on `not typ`, un-Fredkin, then the Skywalk reverse rail tick with
//! `c_t = typ_t xor typ_{t-1}`; `typ_t` becomes the rail LSB again and `isC` is uncomputed from the rails.
use super::adder::{self, Plan};
use crate::circuit::{BitId as B, QubitId as Q};
use crate::point_add::builder::Builder;
use crate::point_add::heo::Rails;

pub struct Cof {
    pub s: Vec<Q>,
    pub r: Vec<Q>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TickWidths {
    /// rail width at the swap (two's complement incl. sign)
    pub wsw: usize,
    /// common width used by the rail arithmetic
    pub wad: usize,
    /// public post-tick width of the half/source rail
    pub post_r1: usize,
    /// public post-tick width of the updated/result rail
    pub post_r2: usize,
    /// post-tick cofactor field width (unsigned), `<= clamp`
    pub ecof: usize,
    /// cofactor clamp (256 in production)
    pub clamp: usize,
}

/// Entry widths, needed by the reverse tick.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrevWidths {
    pub r1: usize,
    pub r2: usize,
    pub cof: usize,
}

/// Plans used by the two adds (for reports).
#[derive(Clone, Debug, PartialEq)]
pub struct TickPlans {
    pub rail: Plan,
    pub cof: Plan,
}

fn fredkin(c: &mut Builder, ctrl: Q, a: Q, b: Q) {
    c.cx(b, a);
    c.ccx(ctrl, a, b);
    c.cx(b, a);
}

/// Lend the physical cofactor bit `r[0]`, whose value is the invariant
/// constant one, to one scratch-closed adder call.  The arithmetic operands
/// deliberately exclude this bit.  Reacquiring the exact ID makes the loan
/// invisible to the surrounding cofactor register.
fn with_r0_loan(
    c: &mut Builder,
    r0: Option<Q>,
    g: Option<Q>,
    operand: &[Q],
    target: &[Q],
    cin: Option<Q>,
    body: impl FnOnce(&mut Builder) -> Plan,
) -> Plan {
    let enabled = super::pointadd::knob("SKYCOF_R0_LOAN")
        .map(|v| v != "0" && !v.is_empty())
        .unwrap_or(true);
    if !enabled {
        return body(c);
    }
    if r0.is_none() {
        assert!(super::pointadd::knob("SKYCOF_IMPLICIT_R0")
            .map(|v| v != "0" && !v.is_empty()).unwrap_or(true));
        return body(c);
    }
    let r0 = r0.expect("SKYCOF_R0_LOAN requires the owned cofactor r[0]");
    assert_eq!(
        c.tracked_condition_depth(),
        Some(0),
        "SKYCOF_R0_LOAN requires an empty outer condition stack"
    );
    assert!(g != Some(r0) && cin != Some(r0));
    assert!(!operand.contains(&r0) && !target.contains(&r0));
    let live = c.active_qubits();
    c.x(r0); // invariant |1> -> clean |0>
    c.release_clean(r0);
    let plan = body(c);
    assert_eq!(
        c.active_qubits() + 1,
        live,
        "SKYCOF_R0_LOAN adder leaked a scratch owner"
    );
    c.reacquire(r0);
    c.x(r0); // restore the invariant |1>
    assert_eq!(c.active_qubits(), live);
    plan
}

pub(crate) fn parity_source_carry() -> bool {
    true
}

/// Two's-complement resize (`heo`): grow = sign-extend, trim = CX from the new top + free.
pub fn resize_signed(c: &mut Builder, reg: &mut Vec<Q>, w: usize) {
    while reg.len() < w {
        let q = c.alloc_qubit();
        c.cx(*reg.last().unwrap(), q);
        reg.push(q);
    }
    while reg.len() > w {
        let top = reg.pop().unwrap();
        c.cx(*reg.last().unwrap(), top);
        c.free(top);
    }
}

/// Unsigned resize: grow = fresh zero wires, trim = free (the trimmed wires must be zero).
pub fn resize_unsigned(c: &mut Builder, reg: &mut Vec<Q>, w: usize) {
    while reg.len() < w {
        let q = c.alloc_qubit();
        reg.push(q);
    }
    while reg.len() > w {
        let top = reg.pop().unwrap();
        c.free(top);
    }
}

/// Forward rail tick (`heo::fwd_tick` with a room-aware add). Returns `(typ_t, isC, plan)`.
pub fn rail_fwd(
    c: &mut Builder,
    rails: &mut Rails,
    typ_prev: Option<Q>,
    wsw: usize,
    wad: usize,
    cap: Option<usize>,
    r0_loan: Option<Q>,
) -> (Q, Q, Plan) {
    assert!(wsw >= 3 && wad >= 2, "rail widths {wsw}/{wad}");
    resize_signed(c, &mut rails.r1, wsw);
    resize_signed(c, &mut rails.r2, wsw);
    let (r1, r2) = (&rails.r1, &rails.r2);
    let ctl = r1[0];
    for i in 1..wsw {
        fredkin(c, ctl, r1[i], r2[i]);
    }
    c.cx(ctl, r2[0]);
    let mut e2 = r1[1..].to_vec();
    resize_signed(c, &mut e2, wad);
    resize_signed(c, &mut rails.r2, wad);
    let r2 = &rails.r2;
    let tau = c.alloc_qubit();
    c.cx(e2[wad - 1], tau);
    c.cx(r2[wad - 1], tau);
    c.x(tau);
    c.cx_all(tau, &e2);
    let plan = with_r0_loan(c, r0_loan, None, &e2, r2, Some(tau), |c| {
        adder::add(c, None, &e2, r2, Some(tau), cap)
    });
    c.cx_all(tau, &e2);
    c.x(tau);
    c.cx(e2[wad - 1], tau);
    c.cx(r2[wad - 1], tau);
    if let Some(tp) = typ_prev {
        c.cx(tp, ctl);
    }
    rails.r1 = e2;
    (ctl, tau, plan)
}

/// Exact low-width rail kernel that hosts `tau`/`isC` on the doomed top
/// sign-extension wire of the source bank.  The source enters the add at
/// width `n - 1`, the target at width `n`, and the hosted wire is returned as
/// `isC` instead of being released by the post-rail contraction.
///
/// This is only valid when the source was sign-extended from `wsw - 1` to
/// `wad` and the public schedule discards that extension immediately after
/// the kernel.  Callers enforce those public-width conditions.
fn rail_fwd_signext_host_impl(
    c: &mut Builder,
    rails: &mut Rails,
    typ_prev: Option<Q>,
    wsw: usize,
    wad: usize,
    cap: Option<usize>,
    r0_loan: Option<Q>,
    scratch_loans: Option<[Q; 2]>,
) -> (Q, Q, Plan) {
    assert!(wsw >= 3 && wad >= 3, "hosted rail widths {wsw}/{wad}");
    assert!(
        wad >= wsw,
        "hosted rail needs a fresh source sign extension: {wsw}/{wad}"
    );
    resize_signed(c, &mut rails.r1, wsw);
    resize_signed(c, &mut rails.r2, wsw);
    let (r1, r2) = (&rails.r1, &rails.r2);
    let ctl = r1[0];
    for i in 1..wsw {
        fredkin(c, ctl, r1[i], r2[i]);
    }
    c.cx(ctl, r2[0]);

    let mut e2 = r1[1..].to_vec();
    resize_signed(c, &mut e2, wad);
    resize_signed(c, &mut rails.r2, wad);
    let r2 = &rails.r2;
    let host = e2.pop().expect("hosted rail source top");
    let sign = *e2.last().expect("hosted rail retained source sign");
    let target_top = *r2.last().expect("hosted rail target top");
    assert!(!e2.contains(&host));
    assert!(!r2.contains(&host));
    assert!(r0_loan != Some(host));
    if let Some(loans) = scratch_loans {
        assert!(r0_loan.is_none(), "external loans replace the r0 loan");
        assert!(!loans.contains(&host));
        assert!(loans.iter().all(|q| !e2.contains(q) && !r2.contains(q)));
    }

    // h initially equals the source sign.  h ^= target_sign; h ^= 1
    // therefore materializes the same tau as the ordinary fresh-zero path.
    c.cx(target_top, host);
    c.x(host);
    c.cx_all(host, &e2);
    let plan = if let Some(loans) = scratch_loans {
        c.set_avoid(&[]);
        let plan = adder::add(c, None, &e2, r2, Some(host), cap);
        c.set_avoid(&loans);
        plan
    } else {
        with_r0_loan(c, r0_loan, None, &e2, r2, Some(host), |c| {
            adder::add(c, None, &e2, r2, Some(host), cap)
        })
    };
    // Restore the omitted transformed top source contribution while tau's
    // complement frame is still active.
    // `sign` is currently the transformed top bit (original sign XOR tau).
    c.cx(sign, target_top);
    c.cx_all(host, &e2);
    // The ordinary post-add conversion from tau to isC, using the retained
    // sign copy because the hosted top is no longer an operand wire.
    c.x(host);
    c.cx(sign, host);
    c.cx(target_top, host);
    if let Some(tp) = typ_prev {
        c.cx(tp, ctl);
    }
    rails.r1 = e2;
    (ctl, host, plan)
}

pub(crate) fn rail_fwd_signext_host(
    c: &mut Builder,
    rails: &mut Rails,
    typ_prev: Option<Q>,
    wsw: usize,
    wad: usize,
    cap: Option<usize>,
    r0_loan: Option<Q>,
) -> (Q, Q, Plan) {
    rail_fwd_signext_host_impl(c, rails, typ_prev, wsw, wad, cap, r0_loan, None)
}

fn normalized_neg_ccx(c: &mut Builder, ca: Q, cb: Q, target: Q) {
    c.x(ca);
    c.x(cb);
    c.ccx(ca, cb, target);
    c.x(cb);
    c.x(ca);
}

fn normalized_neg_a_ccx(c: &mut Builder, a: Q, b: Q, target: Q) {
    c.x(a);
    c.ccx(a, b, target);
    c.x(a);
}

/// Exact `n/n -> (n-2,n)` normalized-MSB arithmetic core.  `source` enters
/// with n-1 bits after the parity/halving step and `target` with n bits.  The
/// source-gauge promise is SRCsign=A*sigma, TGTsign=!A*sigma, with source
/// signed-(n-2).  The old target-sign owner hosts tau/C and the doomed source
/// sign ID migrates into the new target sign.  No owner is allocated or
/// released by this core.
pub(crate) fn normalized_msb_fwd_core(
    c: &mut Builder,
    source: &mut Vec<Q>,
    target: &mut Vec<Q>,
    a: Q,
    cap: Option<usize>,
) -> (Q, Plan) {
    let n = target.len();
    assert!(n >= 4 && source.len() + 1 == n);
    assert!(!source.contains(&a) && !target.contains(&a));
    assert!(source.iter().all(|q| !target.contains(q)));
    let live = c.active_qubits();
    let source_top = source[n - 2];
    let retained_sign = source[n - 3];
    let host = target.pop().expect("normalized target sign host");
    let low_top = target[n - 2];
    let local_cap = c.active_qubits() as usize;
    if let Some(requested) = cap {
        assert!(local_cap <= requested, "normalized-MSB entered above requested cap");
    }

    c.x(a);
    fredkin(c, a, source_top, host);
    c.x(a);
    c.cx(source_top, host);
    c.x(host); // host = tau = !sigma

    c.cx_all(host, source);
    let plan = adder::add_forced(
        c, None, source, target, Some(host), Some(local_cap), adder::Force::Vented);
    assert_eq!(plan, Plan::Vented(0), "normalized-MSB plan drift");
    normalized_neg_ccx(c, a, host, low_top);
    c.cx_all(host, source);
    normalized_neg_ccx(c, a, host, source_top); // sigma -> A*sigma
    c.x(host);
    c.cx(source_top, host);
    normalized_neg_a_ccx(c, a, low_top, host); // host -> C

    c.cx(retained_sign, source_top); // promised sign extension -> zero
    normalized_neg_a_ccx(c, a, low_top, source_top);
    let migrated = source.pop().unwrap();
    assert_eq!(migrated, source_top);
    target.push(migrated);
    assert_eq!(c.active_qubits(), live, "normalized-MSB forward owner drift");
    (host, plan)
}

/// Independent exact inverse of [`normalized_msb_fwd_core`].
pub(crate) fn normalized_msb_rev_core(
    c: &mut Builder,
    source: &mut Vec<Q>,
    target: &mut Vec<Q>,
    a: Q,
    host: Q,
    cap: Option<usize>,
) -> Plan {
    let n = target.len();
    assert!(n >= 4 && source.len() + 2 == n);
    assert!(!source.contains(&a) && !target.contains(&a));
    assert!(!source.contains(&host) && !target.contains(&host) && host != a);
    assert!(source.iter().all(|q| !target.contains(q)));
    let live = c.active_qubits();
    let migrated = target.pop().expect("migrated target sign");
    let low_top = target[n - 2];
    let retained_sign = *source.last().expect("retained source sign");
    let local_cap = c.active_qubits() as usize;
    if let Some(requested) = cap {
        assert!(local_cap <= requested, "normalized-MSB inverse entered above requested cap");
    }

    normalized_neg_a_ccx(c, a, low_top, migrated);
    c.cx(retained_sign, migrated);
    source.push(migrated);
    normalized_neg_a_ccx(c, a, low_top, host);
    c.cx(migrated, host);
    c.x(host); // host = tau

    normalized_neg_ccx(c, a, host, migrated); // A*sigma -> sigma
    c.cx_all(host, source);
    normalized_neg_ccx(c, a, host, low_top);
    c.x_all(target);
    let plan = adder::add_forced(
        c, None, source, target, Some(host), Some(local_cap), adder::Force::Vented);
    c.x_all(target);
    assert_eq!(plan, Plan::Vented(0), "normalized-MSB inverse plan drift");
    c.cx_all(host, source);
    c.x(host);
    c.cx(migrated, host); // tau -> zero
    c.x(a);
    fredkin(c, a, migrated, host);
    c.x(a);
    target.push(host);
    assert_eq!(c.active_qubits(), live, "normalized-MSB reverse owner drift");
    plan
}

/// Exact normalized-MSB variant for `n/n -> (n-1,n-1)`.  The old target-sign
/// owner becomes C and both arithmetic banks remain at their n-1-bit low
/// words; unlike [`normalized_msb_fwd_core`], no source ID migrates.
pub(crate) fn normalized_msb_contract_fwd_core(
    c: &mut Builder,
    source: &mut Vec<Q>,
    target: &mut Vec<Q>,
    a: Q,
    cap: Option<usize>,
) -> (Q, Plan) {
    let n = target.len();
    assert!(n >= 4 && source.len() + 1 == n);
    assert!(!source.contains(&a) && !target.contains(&a));
    assert!(source.iter().all(|q| !target.contains(q)));
    let live = c.active_qubits();
    let source_top = source[n - 2];
    let host = target.pop().expect("normalized contracted target sign host");
    let low_top = target[n - 2];
    let local_cap = c.active_qubits() as usize;
    if let Some(requested) = cap {
        assert!(local_cap <= requested, "normalized contract entered above requested cap");
    }

    c.x(a);
    fredkin(c, a, source_top, host);
    c.x(a);
    c.cx(source_top, host);
    c.x(host); // tau
    c.cx_all(host, source);
    let plan = adder::add_forced(
        c, None, source, target, Some(host), Some(local_cap), adder::Force::Vented);
    assert_eq!(plan, Plan::Vented(0), "normalized contract plan drift");
    normalized_neg_ccx(c, a, host, low_top);
    c.cx_all(host, source);
    normalized_neg_ccx(c, a, host, source_top); // sigma -> A*sigma
    c.x(host);
    c.cx(source_top, host);
    normalized_neg_a_ccx(c, a, low_top, host); // C
    assert_eq!((source.len(), target.len()), (n - 1, n - 1));
    assert_eq!(c.active_qubits(), live, "normalized contract forward owner drift");
    (host, plan)
}

/// Independent exact inverse of [`normalized_msb_contract_fwd_core`].
pub(crate) fn normalized_msb_contract_rev_core(
    c: &mut Builder,
    source: &mut Vec<Q>,
    target: &mut Vec<Q>,
    a: Q,
    host: Q,
    cap: Option<usize>,
) -> Plan {
    assert_eq!(source.len(), target.len());
    let n = source.len() + 1;
    assert!(n >= 4 && !source.contains(&a) && !target.contains(&a));
    assert!(!source.contains(&host) && !target.contains(&host) && host != a);
    assert!(source.iter().all(|q| !target.contains(q)));
    let live = c.active_qubits();
    let source_top = source[n - 2];
    let low_top = target[n - 2];
    let local_cap = c.active_qubits() as usize;
    if let Some(requested) = cap {
        assert!(local_cap <= requested, "normalized contract inverse entered above requested cap");
    }

    normalized_neg_a_ccx(c, a, low_top, host);
    c.cx(source_top, host);
    c.x(host); // tau
    normalized_neg_ccx(c, a, host, source_top); // A*sigma -> sigma
    c.cx_all(host, source);
    normalized_neg_ccx(c, a, host, low_top);
    c.x_all(target);
    let plan = adder::add_forced(
        c, None, source, target, Some(host), Some(local_cap), adder::Force::Vented);
    c.x_all(target);
    assert_eq!(plan, Plan::Vented(0), "normalized contract inverse plan drift");
    c.cx_all(host, source);
    c.x(host);
    c.cx(source_top, host); // tau -> zero
    c.x(a);
    fredkin(c, a, source_top, host);
    c.x(a);
    target.push(host);
    assert_eq!(c.active_qubits(), live, "normalized contract reverse owner drift");
    plan
}

/// Encoded-sign body form for `n/n -> (n-1,n)`.  Both physical sign IDs stay
/// in their rail descriptors: source.top=sigma and target.top=C.  Callers may
/// use only restored low rail cells until [`encoded_msb_rev_core`] decodes the
/// signs.
pub(crate) fn encoded_msb_fwd_core(
    c: &mut Builder,
    source: &mut Vec<Q>,
    target: &mut Vec<Q>,
    a: Q,
    cap: Option<usize>,
) -> Plan {
    let n = target.len();
    assert!(n >= 4 && source.len() + 1 == n);
    assert!(!source.contains(&a) && !target.contains(&a));
    assert!(source.iter().all(|q| !target.contains(q)));
    let live = c.active_qubits();
    let source_top = source[n - 2];
    let host = target[n - 1];
    let low_top = target[n - 2];
    let local_cap = c.active_qubits() as usize;
    if let Some(requested) = cap {
        assert!(local_cap <= requested, "encoded-MSB entered above requested cap");
    }

    c.x(a);
    fredkin(c, a, source_top, host);
    c.x(a);
    c.cx(source_top, host);
    c.x(host); // tau
    c.cx_all(host, source);
    let plan = adder::add_forced(
        c, None, source, &target[..n - 1], Some(host), Some(local_cap), adder::Force::Vented);
    assert_eq!(plan, Plan::Vented(0), "encoded-MSB plan drift");
    normalized_neg_ccx(c, a, host, low_top);
    c.cx_all(host, source);
    // Leave source.top=sigma.  Convert tau to C in the retained target-top ID.
    c.x(host);
    c.cx(source_top, host);
    normalized_neg_a_ccx(c, a, source_top, host);
    normalized_neg_a_ccx(c, a, low_top, host);
    assert_eq!(c.active_qubits(), live);
    plan
}

/// Independent inverse of [`encoded_msb_fwd_core`].
pub(crate) fn encoded_msb_rev_core(
    c: &mut Builder,
    source: &mut Vec<Q>,
    target: &mut Vec<Q>,
    a: Q,
    cap: Option<usize>,
) -> Plan {
    let n = target.len();
    assert!(n >= 4 && source.len() + 1 == n);
    let source_top = source[n - 2];
    let host = target[n - 1];
    let low_top = target[n - 2];
    assert!(!source.contains(&a) && !target.contains(&a));
    assert!(source.iter().all(|q| !target.contains(q)));
    let live = c.active_qubits();
    let local_cap = c.active_qubits() as usize;
    if let Some(requested) = cap {
        assert!(local_cap <= requested, "encoded-MSB inverse entered above requested cap");
    }

    normalized_neg_a_ccx(c, a, low_top, host);
    normalized_neg_a_ccx(c, a, source_top, host);
    c.cx(source_top, host);
    c.x(host); // tau
    c.cx_all(host, source);
    normalized_neg_ccx(c, a, host, low_top);
    c.x_all(&target[..n - 1]);
    let plan = adder::add_forced(
        c, None, source, &target[..n - 1], Some(host), Some(local_cap), adder::Force::Vented);
    c.x_all(&target[..n - 1]);
    assert_eq!(plan, Plan::Vented(0), "encoded-MSB inverse plan drift");
    c.cx_all(host, source);
    c.x(host);
    c.cx(source_top, host); // tau -> zero
    c.x(a);
    fredkin(c, a, source_top, host);
    c.x(a);
    assert_eq!(c.active_qubits(), live);
    plan
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn rail_fwd_encoded_sign_fixture(
    c: &mut Builder,
    rails: &mut Rails,
    typ_prev: Q,
    w: &TickWidths,
    cap: Option<usize>,
) -> (Q, Q, Plan) {
    assert_eq!(w.wsw, w.wad);
    assert_eq!((w.post_r1, w.post_r2), (w.wad - 1, w.wad));
    resize_signed(c, &mut rails.r1, w.wsw);
    resize_signed(c, &mut rails.r2, w.wsw);
    let ctl = rails.r1[0];
    for i in 1..w.wsw { fredkin(c, ctl, rails.r1[i], rails.r2[i]); }
    c.cx(ctl, rails.r2[0]);
    let mut source = rails.r1[1..].to_vec();
    c.cx(typ_prev, ctl); // current A
    let plan = encoded_msb_fwd_core(c, &mut source, &mut rails.r2, ctl, cap);
    assert_eq!((source.len(), rails.r2.len()), (w.post_r1, w.post_r2));
    rails.r1 = source;
    let cflag = *rails.r2.last().unwrap();
    (ctl, cflag, plan)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn rail_rev_encoded_sign_fixture(
    c: &mut Builder,
    rails: &mut Rails,
    typ: Q,
    typ_prev: Q,
    w: &TickWidths,
    prev: (usize, usize),
    cap: Option<usize>,
) -> Plan {
    assert_eq!(w.wsw, w.wad);
    assert_eq!((rails.r1.len(), rails.r2.len()), (w.wad - 1, w.wad));
    let plan = encoded_msb_rev_core(c, &mut rails.r1, &mut rails.r2, typ, cap);
    c.cx(typ_prev, typ);
    rails.r1.insert(0, typ);
    c.cx(typ, rails.r2[0]);
    for i in 1..w.wsw { fredkin(c, typ, rails.r1[i], rails.r2[i]); }
    resize_signed(c, &mut rails.r1, prev.0);
    resize_signed(c, &mut rails.r2, prev.1);
    plan
}

fn normalized_msb_dispatch(tick: Option<usize>, w: &TickWidths) -> Option<bool> {
    match tick {
        Some(303) => {
            assert_eq!((w.wsw, w.wad, w.post_r1, w.post_r2), (68, 68, 66, 68));
            Some(true) // source-top ID migrates into the retained target sign
        }
        Some(305 | 306 | 314 | 317 | 319 | 320 | 333) => {
            assert_eq!(w.wsw, w.wad, "normalized contract needs wsw=wad");
            assert_eq!((w.post_r1, w.post_r2), (w.wad - 1, w.wad - 1));
            Some(false) // both arithmetic low words contract to n-1
        }
        _ => None,
    }
}

fn normalized_msb_prev(tick: usize) -> (usize, usize) {
    match tick {
        303 => (66, 68),
        305 => (67, 67),
        306 => (66, 66),
        314 => (58, 58),
        317 => (56, 56),
        319 => (54, 55),
        320 => (54, 54),
        333 => (48, 48),
        _ => panic!("normalized-MSB prior-width guard missing for tick {tick}"),
    }
}

#[allow(clippy::too_many_arguments)]
fn rail_fwd_normalized_msb(
    c: &mut Builder,
    rails: &mut Rails,
    typ_prev: Q,
    w: &TickWidths,
    cap: Option<usize>,
    tick: usize,
    migrate_target_top: bool,
) -> (Q, Q, Plan) {
    assert_eq!(cap, Some(1037));
    assert_eq!(normalized_msb_dispatch(Some(tick), w), Some(migrate_target_top));
    resize_signed(c, &mut rails.r1, w.wsw);
    resize_signed(c, &mut rails.r2, w.wsw);
    let ctl = rails.r1[0];
    for i in 1..w.wsw { fredkin(c, ctl, rails.r1[i], rails.r2[i]); }
    c.cx(ctl, rails.r2[0]);
    let mut source = rails.r1[1..].to_vec();
    // Current A is created once after the parity swap and remains stable
    // through the normalized half-add.
    c.cx(typ_prev, ctl);
    let (isc, plan) = if migrate_target_top {
        normalized_msb_fwd_core(c, &mut source, &mut rails.r2, ctl, cap)
    } else {
        normalized_msb_contract_fwd_core(c, &mut source, &mut rails.r2, ctl, cap)
    };
    assert_eq!(source.len(), w.post_r1);
    assert_eq!(rails.r2.len(), w.post_r2);
    rails.r1 = source;
    (ctl, isc, plan)
}

#[allow(clippy::too_many_arguments)]
fn rail_rev_normalized_msb(
    c: &mut Builder,
    rails: &mut Rails,
    typ: Q,
    isc: Q,
    typ_prev: Q,
    w: &TickWidths,
    prev: (usize, usize),
    cap: Option<usize>,
    tick: usize,
    migrate_target_top: bool,
) -> Plan {
    assert_eq!(normalized_msb_dispatch(Some(tick), w), Some(migrate_target_top));
    assert_eq!(prev, normalized_msb_prev(tick));
    assert_eq!(cap, Some(1037));
    assert_eq!((rails.r1.len(), rails.r2.len()), (w.post_r1, w.post_r2));
    let plan = if migrate_target_top {
        normalized_msb_rev_core(c, &mut rails.r1, &mut rails.r2, typ, isc, cap)
    } else {
        normalized_msb_contract_rev_core(c, &mut rails.r1, &mut rails.r2, typ, isc, cap)
    };
    assert_eq!((rails.r1.len(), rails.r2.len()), (w.wad - 1, w.wad));
    // Recover the pre-update parity control exactly once before undoing the
    // low-bit swap.  This branch occurs before every generic source resize.
    c.cx(typ_prev, typ);
    rails.r1.insert(0, typ);
    c.cx(typ, rails.r2[0]);
    for i in 1..w.wsw { fredkin(c, typ, rails.r1[i], rails.r2[i]); }
    resize_signed(c, &mut rails.r1, prev.0);
    resize_signed(c, &mut rails.r2, prev.1);
    plan
}

/// Research-only tick324 contract caller.  This is the audited 52/52 ->
/// 51/51 geometry but is deliberately not part of production dispatch.
pub(crate) fn rail_fwd_normalized_contract324_fixture(
    c:&mut Builder,rails:&mut Rails,typ_prev:Q,w:&TickWidths,cap:Option<usize>,
)->(Q,Q,Plan){
    assert_eq!((w.wsw,w.wad,w.post_r1,w.post_r2),(52,52,51,51));
    assert_eq!(cap,Some(1037));
    resize_signed(c,&mut rails.r1,w.wsw);resize_signed(c,&mut rails.r2,w.wsw);
    let ctl=rails.r1[0];for i in 1..w.wsw{fredkin(c,ctl,rails.r1[i],rails.r2[i]);}
    c.cx(ctl,rails.r2[0]);let mut source=rails.r1[1..].to_vec();c.cx(typ_prev,ctl);
    let(isc,plan)=normalized_msb_contract_fwd_core(c,&mut source,&mut rails.r2,ctl,cap);
    rails.r1=source;assert_eq!((rails.r1.len(),rails.r2.len()),(51,51));
    (ctl,isc,plan)
}

pub(crate) fn rail_rev_normalized_contract324_fixture(
    c:&mut Builder,rails:&mut Rails,typ:Q,isc:Q,typ_prev:Q,w:&TickWidths,
    prev:(usize,usize),cap:Option<usize>,
)->Plan{
    assert_eq!((w.wsw,w.wad,w.post_r1,w.post_r2),(52,52,51,51));
    assert_eq!(prev,(51,52));assert_eq!(cap,Some(1037));
    let plan=normalized_msb_contract_rev_core(c,&mut rails.r1,&mut rails.r2,typ,isc,cap);
    c.cx(typ_prev,typ);rails.r1.insert(0,typ);c.cx(typ,rails.r2[0]);
    for i in 1..w.wsw{fredkin(c,typ,rails.r1[i],rails.r2[i]);}
    resize_signed(c,&mut rails.r1,prev.0);resize_signed(c,&mut rails.r2,prev.1);
    plan
}

fn signext_host_tick(t: Option<usize>, w: &TickWidths) -> bool {
    let Some(t) = t else { return false };
    let selected = super::pointadd::knob("SKYCOF_SIGNEXT_ISC_HOST")
        .unwrap_or_else(|| {
            "294,303,305,306,308,312,313,314,317,318,319,320,321,323,324,325,328,329,330,331,333,334,335,337"
                .to_owned()
        })
        .split(',')
        .any(|x| x.trim().parse::<usize>() == Ok(t));
    if selected {
        assert!(
            w.wad >= w.wsw && w.post_r1 < w.wad,
            "SKYCOF_SIGNEXT_ISC_HOST tick {t} needs a doomed source sign extension"
        );
    }
    selected
}

fn late_r0_lease_tick(t: Option<usize>) -> bool {
    if super::pointadd::knob("SKYCOF_IMPLICIT_R0")
        .map(|v| v != "0" && !v.is_empty()).unwrap_or(true) { return false; }
    let Some(t) = t else { return false };
    super::pointadd::knob("SKYCOF_LATE_R0_LEASE")
        .unwrap_or_else(|| "324".to_owned())
        .split(',')
        .any(|x| x.trim().parse::<usize>() == Ok(t))
}

fn implicit_mcx15(c:&mut Builder,controls:&[Q],target:Q,dirty:&[Q]){
    assert_eq!(controls.len(),15);assert_eq!(dirty.len(),13);
    for bottom in[true,false]{
        if bottom{c.ccx(controls[0],controls[1],dirty[0]);}
        for i in 1..dirty.len(){c.ccx(dirty[i-1],controls[i+1],dirty[i]);}
        c.ccx(*dirty.last().unwrap(),*controls.last().unwrap(),target);
        for i in(1..dirty.len()).rev(){c.ccx(dirty[i-1],controls[i+1],dirty[i]);}
        if bottom{c.ccx(controls[0],controls[1],dirty[0]);}
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn rail_rev_dirty_s0_implicit(
    c:&mut Builder,rails:&mut Rails,typ:Q,isc:Q,typ_prev:Q,sigma:Q,
    park:&[Q],dirty:&[Q],n:usize,cap:usize,
)->Plan{
    assert_eq!(rails.r1.len(),n-1);assert_eq!(rails.r2.len(),n-1);
    assert_eq!(park.len(),14);assert_eq!(dirty.len(),13);
    let true_target_sign=*rails.r2.last().unwrap();
    c.cx(true_target_sign,sigma);rails.r2.push(sigma);let q=sigma;let host=isc;
    let sign=*rails.r1.last().unwrap();c.cx(sign,host);c.cx(true_target_sign,host);c.x(host);
    c.cx_all(host,&rails.r1);let plan=adder::sub(c,None,&rails.r1,&rails.r2,Some(host),Some(cap));
    assert_eq!(plan,Plan::Vented(0));c.cx(sign,q);c.cx_all(host,&rails.r1);c.x(host);
    c.cx(sign,host);c.cx(q,host);let mut controls=park.to_vec();controls.push(q);
    implicit_mcx15(c,&controls,host,dirty);c.cx(sign,host);rails.r1.push(host);
    let ctl=typ;c.cx(typ_prev,ctl);resize_signed(c,&mut rails.r1,n-1);c.reacquire(host);
    c.cx(q,host);implicit_mcx15(c,&controls,host,dirty);c.cx(host,q);
    *rails.r2.last_mut().unwrap()=host;resize_signed(c,&mut rails.r2,n);
    rails.r1.insert(0,ctl);c.cx(ctl,rails.r2[0]);
    for i in 1..n{fredkin(c,ctl,rails.r1[i],rails.r2[i]);}
    resize_signed(c,&mut rails.r1,n-1);resize_signed(c,&mut rails.r2,n);
    plan
}

/// Forward rail kernel followed by the two independently fitted public
/// contractions.  Tau/sign repair and the type update are complete before a
/// sign-extension owner is released.
pub fn rail_fwd_micro(
    c: &mut Builder,
    rails: &mut Rails,
    typ_prev: Option<Q>,
    w: &TickWidths,
    cap: Option<usize>,
    r0_loan: Option<Q>,
    tick: Option<usize>,
) -> (Q, Q, Plan) {
    assert!(w.post_r1 <= w.wad && w.post_r2 <= w.wad);
    let normalized = normalized_msb_dispatch(tick, w);
    let out = if let Some(migrate_target_top) = normalized {
        assert!(r0_loan.is_none(), "normalized-MSB dispatch is frozen for implicit R0");
        let t = tick.unwrap();
        let tp = typ_prev.expect("normalized-MSB row303 needs previous typ");
        rail_fwd_normalized_msb(c, rails, tp, w, cap, t, migrate_target_top)
    } else if signext_host_tick(tick, w) {
        rail_fwd_signext_host(c, rails, typ_prev, w.wsw, w.wad, cap, r0_loan)
    } else {
        rail_fwd(c, rails, typ_prev, w.wsw, w.wad, cap, r0_loan)
    };
    resize_signed(c, &mut rails.r1, w.post_r1);
    resize_signed(c, &mut rails.r2, w.post_r2);
    out
}

/// Tick319 half of the R3 seam. The known cofactor constants remain parked
/// across every persistent rail allocation; only the closed adder scope may
/// reuse their IDs. Tick319's doomed source sign extension still hosts isC.
#[allow(clippy::too_many_arguments)]
pub(crate) fn rail_fwd_micro_signext_loans(
    c: &mut Builder,
    rails: &mut Rails,
    typ_prev: Option<Q>,
    w: &TickWidths,
    cap: Option<usize>,
    loans: [Q; 2],
) -> (Q, Q, Plan) {
    assert!(w.post_r1 < w.wad && w.wad >= w.wsw);
    let out = rail_fwd_signext_host_impl(
        c,
        rails,
        typ_prev,
        w.wsw,
        w.wad,
        cap,
        None,
        Some(loans),
    );
    resize_signed(c, &mut rails.r1, w.post_r1);
    resize_signed(c, &mut rails.r2, w.post_r2);
    out
}

/// Exact inverse of [`rail_fwd`] (`heo::rev_tick` with a room-aware subtract); consumes `typ` (it
/// becomes the rail LSB) and `isc` (uncomputed and freed).
#[allow(clippy::too_many_arguments)]
pub fn rail_rev(
    c: &mut Builder,
    rails: &mut Rails,
    typ: Q,
    isc: Q,
    typ_prev: Option<Q>,
    wsw: usize,
    prev: (usize, usize),
    cap: Option<usize>,
    r0_loan: Option<Q>,
) -> Plan {
    let wad = rails.r1.len();
    assert_eq!(
        rails.r2.len(),
        wad,
        "rail_rev: rails must both be at the add width"
    );
    let tau = isc;
    c.cx(rails.r1[wad - 1], tau);
    c.cx(rails.r2[wad - 1], tau);
    c.x(tau);
    c.cx_all(tau, &rails.r1);
    let plan = with_r0_loan(c, r0_loan, None, &rails.r1, &rails.r2, Some(tau), |c| {
        adder::sub(c, None, &rails.r1, &rails.r2, Some(tau), cap)
    });
    c.cx_all(tau, &rails.r1);
    c.x(tau);
    c.cx(rails.r1[wad - 1], tau);
    c.cx(rails.r2[wad - 1], tau);
    c.free(tau);
    let ctl = typ;
    if let Some(tp) = typ_prev {
        c.cx(tp, ctl);
    }
    resize_signed(c, &mut rails.r1, wsw - 1);
    resize_signed(c, &mut rails.r2, wsw);
    rails.r1.insert(0, ctl);
    c.cx(ctl, rails.r2[0]);
    for i in 1..wsw {
        fredkin(c, ctl, rails.r1[i], rails.r2[i]);
    }
    resize_signed(c, &mut rails.r1, prev.0);
    resize_signed(c, &mut rails.r2, prev.1);
    plan
}

/// Exact inverse of [`rail_fwd_signext_host`].  `isc` is the physical source
/// sign-extension owner borrowed by the forward kernel.  It is restored to
/// the source sign, appended as the regrown top source bit, and is therefore
/// deliberately not freed here.
#[allow(clippy::too_many_arguments)]
pub(crate) fn rail_rev_signext_host(
    c: &mut Builder,
    rails: &mut Rails,
    typ: Q,
    isc: Q,
    typ_prev: Option<Q>,
    wsw: usize,
    prev: (usize, usize),
    cap: Option<usize>,
    r0_loan: Option<Q>,
) -> Plan {
    let n = rails.r2.len();
    assert_eq!(rails.r1.len() + 1, n, "hosted reverse source width");
    let host = isc;
    let sign = *rails.r1.last().expect("hosted reverse retained sign");
    let target_top = *rails.r2.last().expect("hosted reverse target top");
    assert!(!rails.r1.contains(&host));
    assert!(!rails.r2.contains(&host));
    assert!(r0_loan != Some(host));

    // Recover tau from the post-add sign frame.
    c.cx(sign, host);
    c.cx(target_top, host);
    c.x(host);
    c.cx_all(host, &rails.r1);
    let plan = with_r0_loan(
        c,
        r0_loan,
        None,
        &rails.r1,
        &rails.r2,
        Some(host),
        |c| adder::sub(c, None, &rails.r1, &rails.r2, Some(host), cap),
    );
    // `sign` is still in the transformed frame here.
    c.cx(sign, target_top);
    c.cx_all(host, &rails.r1);
    // Undo the ordinary pre-sign frame, then restore the exact source sign
    // copy into the same physical owner used by the forward kernel.
    c.x(host);
    c.cx(sign, host);
    c.cx(target_top, host);
    c.cx(sign, host);
    rails.r1.push(host);

    let ctl = typ;
    if let Some(tp) = typ_prev {
        c.cx(tp, ctl);
    }
    resize_signed(c, &mut rails.r1, wsw - 1);
    resize_signed(c, &mut rails.r2, wsw);
    rails.r1.insert(0, ctl);
    c.cx(ctl, rails.r2[0]);
    for i in 1..wsw {
        fredkin(c, ctl, rails.r1[i], rails.r2[i]);
    }
    resize_signed(c, &mut rails.r1, prev.0);
    resize_signed(c, &mut rails.r2, prev.1);
    plan
}

/// Reverse-tick324 late-return lease. The invariant-one cofactor `r0` owner
/// hosts the regrown target top until the hosted source-sign/isC owner is
/// cleanly contracted; two CXs then move the target data to that exact donor
/// and restore the original physical r0 owner to |1>.
#[allow(clippy::too_many_arguments)]
pub(crate) fn rail_rev_signext_late_r0(
    c: &mut Builder,
    rails: &mut Rails,
    typ: Q,
    isc: Q,
    typ_prev: Option<Q>,
    n: usize,
    prev: (usize, usize),
    cap: usize,
    r0: Q,
) -> Plan {
    assert!(n >= 4);
    assert_eq!(prev, (n - 1, n));
    assert_eq!(rails.r1.len(), n - 1);
    assert_eq!(rails.r2.len(), n - 1);
    assert_eq!(c.tracked_condition_depth(), Some(0));
    assert!(r0 != isc && !rails.r1.contains(&r0) && !rails.r2.contains(&r0));

    // Release the invariant-one owner before target growth, then reacquire
    // that exact ID as the target sign-extension top. No allocator choice or
    // avoid-set behavior is assumed.
    c.x(r0);
    c.release_clean(r0);
    c.reacquire(r0);
    c.cx(*rails.r2.last().unwrap(), r0);
    rails.r2.push(r0);

    let host = isc;
    let sign = *rails.r1.last().unwrap();
    let target_top = r0;
    assert!(!rails.r1.contains(&host) && !rails.r2.contains(&host));

    c.cx(sign, host);
    c.cx(target_top, host);
    c.x(host);
    c.cx_all(host, &rails.r1);
    // r0 is target data here. Explicitly bypass the ordinary r0 loan while
    // leaving every other circuit loan enabled.
    let plan = adder::sub(c, None, &rails.r1, &rails.r2, Some(host), Some(cap));
    assert_eq!(plan, Plan::Vented(0), "late-r0 adder plan drift");
    c.cx(sign, target_top);
    c.cx_all(host, &rails.r1);
    c.x(host);
    c.cx(sign, host);
    c.cx(target_top, host);
    c.cx(sign, host);
    rails.r1.push(host);

    let ctl = typ;
    if let Some(tp) = typ_prev {
        c.cx(tp, ctl);
    }
    // The existing source contraction proves host clean and releases this
    // exact donor. Reacquire it before any allocation can intervene.
    resize_signed(c, &mut rails.r1, n - 1);
    assert!(!rails.r1.contains(&host));
    c.reacquire(host);

    // On donor=0: (r0=data,host=0) -> (r0=0,host=data), coherently.
    c.cx(r0, host);
    c.cx(host, r0);
    let top = rails.r2.last_mut().unwrap();
    assert_eq!(*top, r0);
    *top = host;
    c.release_clean(r0);
    c.reacquire(r0);
    c.x(r0);

    resize_signed(c, &mut rails.r2, n);
    rails.r1.insert(0, ctl);
    c.cx(ctl, rails.r2[0]);
    for i in 1..n {
        fredkin(c, ctl, rails.r1[i], rails.r2[i]);
    }
    resize_signed(c, &mut rails.r1, prev.0);
    resize_signed(c, &mut rails.r2, prev.1);
    assert!(!rails.r1.contains(&r0) && !rails.r2.contains(&r0));
    assert_eq!(*rails.r2.last().unwrap(), host);
    plan
}

/// Exact reverse seam for [`rail_fwd_micro`].  Decoder and cofactor reverse
/// execute while the banks are still contracted; only the rail kernel grows
/// them back to its common arithmetic width.
#[allow(clippy::too_many_arguments)]
pub fn rail_rev_micro(
    c: &mut Builder,
    rails: &mut Rails,
    typ: Q,
    isc: Q,
    typ_prev: Option<Q>,
    w: &TickWidths,
    prev: (usize, usize),
    cap: Option<usize>,
    r0_loan: Option<Q>,
    tick: Option<usize>,
) -> Plan {
    assert_eq!(rails.r1.len(), w.post_r1);
    assert_eq!(rails.r2.len(), w.post_r2);
    if let Some(migrate_target_top) = normalized_msb_dispatch(tick, w) {
        assert!(r0_loan.is_none(), "normalized-MSB inverse is frozen for implicit R0");
        let t = tick.unwrap();
        let tp = typ_prev.expect("normalized-MSB row303 needs previous typ");
        return rail_rev_normalized_msb(
            c, rails, typ, isc, tp, w, prev, cap, t, migrate_target_top);
    }
    let hosted = signext_host_tick(tick, w);
    if late_r0_lease_tick(tick) {
        assert!(hosted, "late-r0 requires the sign-extension host");
        assert_eq!(tick, Some(324));
        assert_eq!((w.wsw, w.wad, w.post_r1, w.post_r2), (52, 52, 51, 51));
        assert_eq!(prev, (51, 52));
        let cap = cap.expect("late-r0 requires the frozen production cap");
        assert_eq!(cap, 1040, "late-r0 frozen cap drift");
        let r0 = r0_loan.expect("late-r0 requires the invariant-one cofactor owner");
        return rail_rev_signext_late_r0(
            c, rails, typ, isc, typ_prev, w.wad, prev, cap, r0);
    }
    resize_signed(c, &mut rails.r1, w.wad - usize::from(hosted));
    resize_signed(c, &mut rails.r2, w.wad);
    if hosted {
        rail_rev_signext_host(c, rails, typ, isc, typ_prev, w.wsw, prev, cap, r0_loan)
    } else {
        rail_rev(c, rails, typ, isc, typ_prev, w.wsw, prev, cap, r0_loan)
    }
}

/// Operand length of the cofactor add (`s` before the relabel).
fn add_operand_len(w: &TickWidths, e_prev: usize) -> usize {
    if w.ecof == w.clamp && e_prev >= w.clamp {
        w.ecof
    } else {
        w.ecof - 1
    }
}

/// Cofactor update of one forward tick; `typ`, `isc` from [`rail_fwd`]. Leaves `isc` live.
pub fn cof_fwd(
    c: &mut Builder,
    cof: &mut Cof,
    typ: Q,
    isc: Q,
    w: &TickWidths,
    cap: Option<usize>,
) -> Plan {
    cof_fwd_impl(c, cof, typ, isc, w, cap, None)
}

/// Isolated R4 fixture path.  It performs the ordinary full cofactor cell but
/// omits the fresh zero-head allocation: after the last controlled use, isC is
/// HMR/phase-cleared against the newly formed s[1], then the exact same clean
/// physical owner is reacquired and relabelled as the new s[0].  Production
/// dispatch never calls this function pending the R4 audit gate.
pub(crate) fn cof_fwd_rotate_isc_fixture(
    c: &mut Builder,
    cof: &mut Cof,
    typ: Q,
    isc: Q,
    w: &TickWidths,
    cap: Option<usize>,
) -> Plan {
    let e_prev = cof.s.len();
    assert_eq!(cof.r.len(), e_prev);
    for i in 1..e_prev {
        fredkin(c, isc, cof.s[i], cof.r[i]);
    }
    let n = w.ecof;
    let k = add_operand_len(w, e_prev);
    resize_unsigned(c, &mut cof.r, n);
    resize_unsigned(c, &mut cof.s, k);
    let operand = &cof.s[1..];
    c.x(typ);
    let r0 = cof.r[0];
    let plan = with_r0_loan(
        c,
        Some(r0),
        Some(typ),
        operand,
        &cof.r[1..],
        Some(cof.s[0]),
        |c| adder::add(c, Some(typ), operand, &cof.r[1..], Some(cof.s[0]), cap),
    );
    c.x(typ);
    c.cx(isc, cof.s[0]);
    let m = c.alloc_bit();
    c.hmr(isc, m);
    c.x(typ);
    c.cz_if(cof.s[0], typ, m);
    c.x(typ);
    c.free_bit(m);
    c.release_clean(isc);
    c.reacquire(isc);
    cof.s.insert(0, isc);
    plan
}

/// Public-clock specialization on the source-reachable leading-zero support.
/// Keep every original cofactor owner; only omit arithmetic on proven zeros.
/// The late/clamped path must retain its original full-width operand.
pub fn cof_fwd_at(
    c: &mut Builder,
    cof: &mut Cof,
    typ: Q,
    isc: Q,
    w: &TickWidths,
    cap: Option<usize>,
    t: usize,
) -> Plan {
    let enabled = super::pointadd::knob("SKYCOF_EARLY_COF_BOUND")
        .map(|v| v != "0" && !v.is_empty())
        .unwrap_or(true);
    let bound = (t <= 50 && enabled).then_some(t);
    cof_fwd_impl(c, cof, typ, isc, w, cap, bound)
}

/// Research implicit-R0 cofactor cell. `cof.r[j]` is logical r[j+1]; the
/// invariant logical r[0]=1 has no physical owner.
pub(crate) fn cof_fwd_at_implicit_r0(
    c: &mut Builder,
    cof: &mut Cof,
    typ: Q,
    isc: Q,
    w: &TickWidths,
    cap: Option<usize>,
    t: usize,
) -> Plan {
    cof_fwd_at_implicit_r0_impl(c, cof, typ, isc, w, cap, t, false)
}

/// Implicit-R0 forward cell whose last-use `isC` owner is measured clean and
/// immediately relabelled as the inserted zero head.  The matching reverse
/// cell must remove that head into `isC` before undoing the cofactor update.
pub(crate) fn cof_fwd_at_implicit_r0_zero_head(
    c: &mut Builder,
    cof: &mut Cof,
    typ: Q,
    isc: Q,
    w: &TickWidths,
    cap: Option<usize>,
    t: usize,
) -> Plan {
    cof_fwd_at_implicit_r0_impl(c, cof, typ, isc, w, cap, t, true)
}

/// Actual implicit-R0 cofactor cell embedded in the encoded-sign body seam.
/// `isc` is target.top=C and remains physically inside `target`.  After its
/// final controlled use and `C -> S0`, restore both true rail signs, erase C
/// with the exact graph phase, restore target.sign in the same ID, and insert
/// an ordinary fresh cofactor zero head.
#[allow(clippy::too_many_arguments)]
pub(crate) fn cof_fwd_at_implicit_r0_encoded_sign_fixture(
    c: &mut Builder,
    cof: &mut Cof,
    typ: Q,
    isc: Q,
    source: &mut Vec<Q>,
    target: &mut Vec<Q>,
    w: &TickWidths,
    cap: Option<usize>,
    t: usize,
) -> (Plan, B) {
    let e_prev = cof.s.len();
    assert_eq!(cof.r.len() + 1, e_prev);
    assert_eq!(target.last().copied(), Some(isc));
    assert!(!source.contains(&isc) && !cof.s.contains(&isc) && !cof.r.contains(&isc));
    let enabled = super::pointadd::knob("SKYCOF_EARLY_COF_BOUND")
        .map(|v| v != "0" && !v.is_empty()).unwrap_or(true);
    let bound = (t <= 50 && enabled).then_some(t);
    let swap_end = bound.map_or(e_prev, |x| e_prev.min(x + 1));
    for i in 1..swap_end { fredkin(c, isc, cof.s[i], cof.r[i - 1]); }
    let n = w.ecof;
    let k = add_operand_len(w, e_prev);
    resize_unsigned(c, &mut cof.r, n - 1);
    resize_unsigned(c, &mut cof.s, k);
    let m = bound.map_or(n, |x| n.min(x + 2));
    let operand = if bound.is_some() { &cof.s[1..m - 1] } else { &cof.s[1..] };
    c.x(typ);
    let plan = adder::add(c, Some(typ), operand, &cof.r[..m - 1], Some(cof.s[0]), cap);
    c.x(typ);
    c.cx(isc, cof.s[0]);

    let source_top = *source.last().expect("encoded source sign");
    let low_top = target[target.len() - 2];
    normalized_neg_a_ccx(c, typ, cof.s[0], source_top);
    normalized_neg_a_ccx(c, typ, low_top, source_top);
    let receipt = c.alloc_bit();
    c.hmr(isc, receipt);
    c.x(typ);
    c.cz_if(cof.s[0], typ, receipt);
    c.x(typ);
    c.free_bit(receipt);
    normalized_neg_a_ccx(c, typ, low_top, isc);
    cof.s.insert(0, c.alloc_qubit());
    (plan, receipt)
}

#[allow(clippy::too_many_arguments)]
fn cof_fwd_at_implicit_r0_impl(
    c: &mut Builder,
    cof: &mut Cof,
    typ: Q,
    isc: Q,
    w: &TickWidths,
    cap: Option<usize>,
    t: usize,
    retain_zero_head: bool,
) -> Plan {
    let e_prev = cof.s.len();
    assert_eq!(cof.r.len() + 1, e_prev);
    let enabled = super::pointadd::knob("SKYCOF_EARLY_COF_BOUND")
        .map(|v| v != "0" && !v.is_empty()).unwrap_or(true);
    let bound = (t <= 50 && enabled).then_some(t);
    let swap_end = bound.map_or(e_prev, |x| e_prev.min(x + 1));
    for i in 1..swap_end { fredkin(c, isc, cof.s[i], cof.r[i - 1]); }
    let n = w.ecof;
    let k = add_operand_len(w, e_prev);
    resize_unsigned(c, &mut cof.r, n - 1);
    resize_unsigned(c, &mut cof.s, k);
    let m = bound.map_or(n, |x| n.min(x + 2));
    let operand = if bound.is_some() { &cof.s[1..m - 1] } else { &cof.s[1..] };
    c.x(typ);
    let plan = adder::add(c, Some(typ), operand, &cof.r[..m - 1], Some(cof.s[0]), cap);
    c.x(typ);
    c.cx(isc, cof.s[0]);
    if retain_zero_head {
        // At this cut `isc = !typ & cof.s[0]`.  This is exactly the predicate
        // used by `erase_isc`, except the new zero head has not yet shifted
        // the source bit to index one.  Close the measurement phase while the
        // predicate is still available, then preserve the same clean owner as
        // the inserted s[0] instead of allocating a fresh physical qubit.
        let m = c.alloc_bit();
        c.hmr(isc, m);
        c.x(typ);
        c.cz_if(cof.s[0], typ, m);
        c.x(typ);
        c.free_bit(m);
        c.release_clean(isc);
        c.reacquire(isc);
        assert!(!cof.s.contains(&isc) && !cof.r.contains(&isc) && isc != typ);
        cof.s.insert(0, isc);
    } else {
        cof.s.insert(0, c.alloc_qubit());
    }
    plan
}

fn cof_fwd_impl(
    c: &mut Builder,
    cof: &mut Cof,
    typ: Q,
    isc: Q,
    w: &TickWidths,
    cap: Option<usize>,
    bound: Option<usize>,
) -> Plan {
    let e_prev = cof.s.len();
    assert_eq!(
        cof.r.len(),
        e_prev,
        "cof_fwd: s and r must enter at one width (fold the park flag first)"
    );
    assert!(
        e_prev >= 2 && w.ecof >= 2 && w.ecof <= w.clamp,
        "cof widths {e_prev} -> {}",
        w.ecof
    );
    let swap_end = bound.map_or(e_prev, |t| e_prev.min(t + 1));
    for i in 1..swap_end {
        fredkin(c, isc, cof.s[i], cof.r[i]);
    }
    let n = w.ecof;
    let k = add_operand_len(w, e_prev);
    resize_unsigned(c, &mut cof.r, n);
    resize_unsigned(c, &mut cof.s, k);
    // Before tick t, max(s,r) <= 2^t. After it, max(s,r) <= 2^(t+1).
    // At the bounded prefix's missing top operand position t+1 the bit is zero.
    let m = bound.map_or(n, |t| n.min(t + 2));
    let operand = if bound.is_some() {
        &cof.s[1..m - 1]
    } else {
        &cof.s[1..]
    };
    c.x(typ);
    let r0 = cof.r[0];
    let plan = with_r0_loan(
        c,
        Some(r0),
        Some(typ),
        operand,
        &cof.r[1..m],
        Some(cof.s[0]),
        |c| adder::add(c, Some(typ), operand, &cof.r[1..m], Some(cof.s[0]), cap),
    );
    c.x(typ);
    c.cx(isc, cof.s[0]);
    let z = c.alloc_qubit();
    cof.s.insert(0, z);
    plan
}

/// Erase `isC = s[1] and not typ` by measurement (0 Toffoli). Valid right after [`cof_fwd`].
pub fn erase_isc(c: &mut Builder, cof: &Cof, typ: Q, isc: Q) {
    let m = c.alloc_bit();
    c.hmr(isc, m);
    c.x(typ);
    c.cz_if(cof.s[1], typ, m);
    c.x(typ);
    c.free_bit(m);
    c.release_clean(isc);
}

/// Forward tick that leaves `isC` live (e.g. for the C-parity sign wire); the caller must
/// [`erase_isc`] it before the cofactors change again. Returns `(typ_t, isC, entry widths, plans)`.
pub fn fwd_tick_open(
    c: &mut Builder,
    rails: &mut Rails,
    cof: &mut Cof,
    typ_prev: Option<Q>,
    w: &TickWidths,
    cap: Option<usize>,
) -> (Q, Q, PrevWidths, TickPlans) {
    let prev = PrevWidths {
        r1: rails.r1.len(),
        r2: rails.r2.len(),
        cof: cof.s.len(),
    };
    let (typ, isc, rail) =
        rail_fwd_micro(c, rails, typ_prev, w, cap, Some(cof.r[0]), None);
    let cofp = cof_fwd(c, cof, typ, isc, w, cap);
    (typ, isc, prev, TickPlans { rail, cof: cofp })
}

/// One forward SKY-COF tick. Returns `typ_t` (a live wire the caller owns), the entry widths and the
/// add plans.
pub fn fwd_tick(
    c: &mut Builder,
    rails: &mut Rails,
    cof: &mut Cof,
    typ_prev: Option<Q>,
    w: &TickWidths,
    cap: Option<usize>,
) -> (Q, PrevWidths, TickPlans) {
    let (typ, isc, prev, plans) = fwd_tick_open(c, rails, cof, typ_prev, w, cap);
    erase_isc(c, cof, typ, isc);
    (typ, prev, plans)
}

/// Recompute `isC = s[1] and not typ` into a fresh wire (1 CCX), on a post-tick state.
pub fn isc_recompute(c: &mut Builder, cof: &Cof, typ: Q) -> Q {
    let isc = c.alloc_qubit();
    c.x(typ);
    c.ccx(typ, cof.s[1], isc);
    c.x(typ);
    isc
}

/// Recompute `isC` into the exact zero head inserted by [`cof_fwd_impl`].
/// The head is removed from `cof.s` but remains live as the returned wire; the
/// paired cofactor reverse must use [`cof_rev_at_zero_head`] so it does not
/// remove/free a second owner.
pub(crate) fn isc_recompute_from_zero_head(c: &mut Builder, cof: &mut Cof, typ: Q) -> Q {
    assert!(cof.s.len() >= 2, "cofactor zero-head reuse needs s[1]");
    let isc = cof.s.remove(0);
    assert!(isc != typ && !cof.s.contains(&isc) && !cof.r.contains(&isc));
    c.x(typ);
    c.ccx(typ, cof.s[0], isc);
    c.x(typ);
    isc
}

/// Reverse cofactor update given the recomputed `isC` (see [`isc_recompute`]).
pub fn cof_rev(
    c: &mut Builder,
    cof: &mut Cof,
    typ: Q,
    isc: Q,
    e_prev: usize,
    cap: Option<usize>,
) -> Plan {
    cof_rev_impl(c, cof, typ, isc, e_prev, cap, None, None)
}

/// Reverse of [`cof_fwd_at`] with the same public clock and full owner layout.
pub fn cof_rev_at(
    c: &mut Builder,
    cof: &mut Cof,
    typ: Q,
    isc: Q,
    e_prev: usize,
    cap: Option<usize>,
    t: usize,
) -> Plan {
    let enabled = super::pointadd::knob("SKYCOF_EARLY_COF_BOUND")
        .map(|v| v != "0" && !v.is_empty())
        .unwrap_or(true);
    let bound = (t <= 50 && enabled).then_some(t);
    cof_rev_impl(c, cof, typ, isc, e_prev, cap, bound, None)
}

/// Reverse a public-clock cofactor cell after
/// [`isc_recompute_from_zero_head`] has already removed the inserted zero
/// head and rotated that physical owner into `isc`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn cof_rev_at_zero_head(
    c: &mut Builder,
    cof: &mut Cof,
    typ: Q,
    isc: Q,
    e_prev: usize,
    cap: Option<usize>,
    t: usize,
) -> Plan {
    let enabled = super::pointadd::knob("SKYCOF_EARLY_COF_BOUND")
        .map(|v| v != "0" && !v.is_empty())
        .unwrap_or(true);
    let bound = (t <= 50 && enabled).then_some(t);
    cof_rev_impl(c, cof, typ, isc, e_prev, cap, bound, Some(isc))
}

/// Exact inverse of [`cof_fwd_at_implicit_r0`].
pub(crate) fn cof_rev_at_implicit_r0(
    c: &mut Builder,
    cof: &mut Cof,
    typ: Q,
    isc: Q,
    e_prev: usize,
    cap: Option<usize>,
    t: usize,
) -> Plan {
    cof_rev_at_implicit_r0_impl(c, cof, typ, isc, e_prev, cap, t, false)
}

pub(crate) fn cof_rev_at_implicit_r0_zero_head(
    c: &mut Builder,
    cof: &mut Cof,
    typ: Q,
    isc: Q,
    e_prev: usize,
    cap: Option<usize>,
    t: usize,
) -> Plan {
    cof_rev_at_implicit_r0_impl(c, cof, typ, isc, e_prev, cap, t, true)
}

/// Paired inverse of [`cof_fwd_at_implicit_r0_encoded_sign_fixture`].  The
/// ordinary fresh head is removed exactly once; true rail signs are encoded
/// before `C -> S0` and the actual implicit-R0 cofactor inverse.
#[allow(clippy::too_many_arguments)]
pub(crate) fn cof_rev_at_implicit_r0_encoded_sign_fixture(
    c: &mut Builder,
    cof: &mut Cof,
    typ: Q,
    source: &mut Vec<Q>,
    target: &mut Vec<Q>,
    e_prev: usize,
    cap: Option<usize>,
    t: usize,
) -> (Q, Plan) {
    let head = cof.s.remove(0);
    c.free(head);
    let cflag = *target.last().expect("true target sign owner");
    let low_top = target[target.len() - 2];
    let source_top = *source.last().expect("true source sign owner");
    assert!(!cof.s.contains(&cflag) && !cof.r.contains(&cflag));
    normalized_neg_a_ccx(c, typ, low_top, cflag); // true target sign -> zero
    normalized_neg_a_ccx(c, typ, cof.s[0], cflag); // zero -> C
    normalized_neg_a_ccx(c, typ, low_top, source_top);
    normalized_neg_a_ccx(c, typ, cof.s[0], source_top); // true source sign -> sigma
    let plan = cof_rev_at_implicit_r0_impl(c, cof, typ, cflag, e_prev, cap, t, true);
    (cflag, plan)
}

fn cof_rev_at_implicit_r0_impl(
    c: &mut Builder,
    cof: &mut Cof,
    typ: Q,
    isc: Q,
    e_prev: usize,
    cap: Option<usize>,
    t: usize,
    retained_zero_head: bool,
) -> Plan {
    let n = cof.r.len() + 1;
    if retained_zero_head {
        assert!(!cof.s.contains(&isc) && !cof.r.contains(&isc));
    } else {
        let z = cof.s.remove(0);
        c.free(z);
    }
    assert!(cof.s.len() == n || cof.s.len() + 1 == n);
    c.cx(isc, cof.s[0]);
    let enabled = super::pointadd::knob("SKYCOF_EARLY_COF_BOUND")
        .map(|v| v != "0" && !v.is_empty()).unwrap_or(true);
    let bound = (t <= 50 && enabled).then_some(t);
    let m = bound.map_or(n, |x| n.min(x + 2));
    let operand = if bound.is_some() { &cof.s[1..m - 1] } else { &cof.s[1..] };
    c.x(typ);
    let plan = adder::sub(c, Some(typ), operand, &cof.r[..m - 1], Some(cof.s[0]), cap);
    c.x(typ);
    resize_unsigned(c, &mut cof.r, e_prev - 1);
    resize_unsigned(c, &mut cof.s, e_prev);
    let swap_end = bound.map_or(e_prev, |x| e_prev.min(x + 1));
    for i in 1..swap_end { fredkin(c, isc, cof.s[i], cof.r[i - 1]); }
    plan
}

fn cof_rev_impl(
    c: &mut Builder,
    cof: &mut Cof,
    typ: Q,
    isc: Q,
    e_prev: usize,
    cap: Option<usize>,
    bound: Option<usize>,
    retained_zero_head: Option<Q>,
) -> Plan {
    let n = cof.r.len();
    if let Some(z) = retained_zero_head {
        assert!(!cof.s.contains(&z) && !cof.r.contains(&z));
        assert_eq!(z, isc, "retained zero head must be the live isc owner");
    } else {
        let z = cof.s.remove(0);
        c.free(z);
    }
    assert!(
        cof.s.len() == n || cof.s.len() + 1 == n,
        "cof_rev: s {} vs r {n}",
        cof.s.len()
    );
    c.cx(isc, cof.s[0]);
    let m = bound.map_or(n, |t| n.min(t + 2));
    let operand = if bound.is_some() {
        &cof.s[1..m - 1]
    } else {
        &cof.s[1..]
    };
    c.x(typ);
    let r0 = cof.r[0];
    let plan = with_r0_loan(
        c,
        Some(r0),
        Some(typ),
        operand,
        &cof.r[1..m],
        Some(cof.s[0]),
        |c| adder::sub(c, Some(typ), operand, &cof.r[1..m], Some(cof.s[0]), cap),
    );
    c.x(typ);
    resize_unsigned(c, &mut cof.r, e_prev);
    resize_unsigned(c, &mut cof.s, e_prev);
    let swap_end = bound.map_or(e_prev, |t| e_prev.min(t + 1));
    for i in 1..swap_end {
        fredkin(c, isc, cof.s[i], cof.r[i]);
    }
    plan
}

/// Exact inverse of [`fwd_tick_open`]: consumes `typ` (`typ_t`) and `isc` (a live `isC`, e.g. from
/// [`isc_recompute`]).
#[allow(clippy::too_many_arguments)]
pub fn rev_tick_with_isc(
    c: &mut Builder,
    rails: &mut Rails,
    cof: &mut Cof,
    typ: Q,
    isc: Q,
    typ_prev: Option<Q>,
    w: &TickWidths,
    prev: &PrevWidths,
    cap: Option<usize>,
) -> TickPlans {
    let cofp = cof_rev(c, cof, typ, isc, prev.cof, cap);
    let rail = rail_rev_micro(
        c,
        rails,
        typ,
        isc,
        typ_prev,
        w,
        (prev.r1, prev.r2),
        cap,
        Some(cof.r[0]),
        None,
    );
    TickPlans { rail, cof: cofp }
}

/// Exact inverse of [`fwd_tick`]: consumes `typ` (`typ_t`, as the forward tick left it).
#[allow(clippy::too_many_arguments)]
pub fn rev_tick(
    c: &mut Builder,
    rails: &mut Rails,
    cof: &mut Cof,
    typ: Q,
    typ_prev: Option<Q>,
    w: &TickWidths,
    prev: &PrevWidths,
    cap: Option<usize>,
) -> TickPlans {
    let isc = isc_recompute(c, cof, typ);
    rev_tick_with_isc(c, rails, cof, typ, isc, typ_prev, w, prev, cap)
}
