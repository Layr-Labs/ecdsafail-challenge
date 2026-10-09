use alloy_primitives::U256;

use super::compare::erase_with_compare;
use super::const_arith::cadd_const_trunc;
use super::pingpong::walk_max_qubits;
use super::{fold_guard, pinned_env, Builder, SECP256K1_P};
use crate::circuit::{BitId, QubitId};

fn peak_cmp_bits() -> Option<usize> {
    static SLOT: std::sync::OnceLock<Option<usize>> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| super::optional_env("PP_F_PEAKCMP"))
}

// Width of the measured-erasure comparisons in this file, and nowhere else in
// the tree. One bit finer than `fold_guard` by the balance rule derived in
// `mod.rs`: a compare's Toffoli sit under a `push_condition` and execute half
// the time, so the same `d(lambda)/d(Toffoli)` buys it half the error. Change
// one of the two and you have to re-derive the other.
// (Plain `//`: a `///` here would document nothing -- the doc comment does not
// reach the `fn` the macro expands to.)
pinned_env!(pub(crate) erase_compare, "ERASE_COMPARE");

/// `2^256 - p == 2^32 + 977`: what a wrapped `2^256` reduces to mod p, and the
/// only constant any modular fold in this tree folds by. Derived from the
/// modulus rather than written out, so the coordinate shell, the square and the
/// ping-pong replay cannot drift apart on it.
pub fn f() -> U256 {
    U256::MAX
        .wrapping_sub(SECP256K1_P)
        .wrapping_add(U256::from(1))
}

/// Slice width for a truncated fold of `f` (or `f - 1`, the same width): the
/// constant's own 33 bits plus the tree-wide [`fold_guard`] of headroom for the
/// carry it can generate. The dropped carry off the top of the slice is the
/// whole approximation, so the error is `~2^-fold_guard()` per call.
///
/// One width for every such fold in the tree, coordinate shell and square
/// alike: the balance rule makes them all want the same per-call error whatever
/// their call counts are.
pub fn f_slice() -> usize {
    33 + fold_guard()
}
pub fn go_g(k: &str) -> usize { (fold_guard() as isize + super::env_raw(k).and_then(|v| v.parse::<isize>().ok()).unwrap_or(0)) as usize }
pub fn go_fs(k: &str) -> usize { 33 + go_g(k) }

/// `acc += addend`, rippling once through both registers and leaving `addend`
/// exactly as it found it.
///
/// One Toffoli per carry, and every carry is measurement-uncomputed, so the
/// unwind is free -- this is the floor for exact ripple arithmetic and it is the
/// only register-plus-register adder in the tree. Every one of its callers goes
/// through here: the coordinate shell, the square, the replay's chunked adder
/// and the walk's two split adders.
///
/// `carry_in` is a live carry entering bit 0. `carry_out`, when given, receives
/// the carry off the top: `width` Toffoli over `width - 1` owned carry wires.
/// When it is `None` the top carry has nowhere to go, so the top position costs
/// no Toffoli and the second-from-top one emits its carry straight into the top
/// sum bit instead of onto a wire of its own -- `width - 1` Toffoli over
/// `width - 2` owned wires. See [`terminal_step`].
pub fn ripple_add(
    circ: &mut Builder,
    addend: &[QubitId],
    acc: &[QubitId],
    carry_in: Option<QubitId>,
    carry_out: Option<QubitId>,
) {
    // y16 trace (no effect on the gates)
    let y16 = super::leapfrog::y16_enter(circ);
    ripple_add_y16(circ, addend, acc, carry_in, carry_out);
    super::leapfrog::y16_leave(circ, 0, y16);
}
fn ripple_add_y16(
    circ: &mut Builder,
    addend: &[QubitId],
    acc: &[QubitId],
    carry_in: Option<QubitId>,
    carry_out: Option<QubitId>,
) {
    if carry_out.is_none() && result_top_loan_enabled(acc) {ripple_add_result_top_loan(circ,addend,acc,carry_in,None,false);return;}
    let owned=if carry_out.is_some(){acc.len().saturating_sub(1)}else{acc.len().saturating_sub(2)};
    let missing=(circ.active_qubits()as usize+owned).saturating_sub(walk_max_qubits());
    if addend.len()==acc.len() && acc.len()>=3 && !has_top_copy(acc)
        && missing>0 && missing<=super::bridge::budget() && missing<owned {
        if super::env_flag("I35_TRACE"){eprintln!("I35_BRIDGE plain {} {}",acc.len(),missing);}
        super::bridge::add(circ,addend,acc,carry_in,carry_out,missing);return;
    }
    ripple_add_proved(circ, addend, acc, carry_in, carry_out, Carry0::Full, Carry1::Full, None, None, None, None);
}

/// Finish a vented sum, consume its overflow while the top arithmetic carry
/// is still live, then perform the ordinary measured internal unwind.
///
/// The consumer receives (overflow, unchanged source top, sum top, carry into
/// top). It must preserve the source/sum/carry frame and may mutate only
/// disjoint operands. The lower positions in this slice remain folded until
/// the unwind, so they are not yet readable as source or sum bits.
pub(crate) fn ripple_add_consume(
    circ: &mut Builder, addend: &[QubitId], acc: &[QubitId],
    carry_in: Option<QubitId>, carry_out: QubitId,
    consumer: impl FnOnce(&mut Builder, QubitId, QubitId, QubitId, Option<QubitId>),
) {
    // y16 trace (no effect on the gates): the consumer is counted apart from the ripple
    let y16 = super::leapfrog::y16_enter(circ);
    ripple_add_consume_y16(circ, addend, acc, carry_in, carry_out, |c, o, a, s, p| {
        let y16c = super::leapfrog::y16_enter(c);
        super::pingpong::y17_fold_true_cap();
        consumer(c, o, a, s, p);
        super::leapfrog::y16_leave(c, 2, y16c);
    });
    super::leapfrog::y16_leave(circ, 0, y16);
}
fn ripple_add_consume_y16(
    circ: &mut Builder, addend: &[QubitId], acc: &[QubitId],
    carry_in: Option<QubitId>, carry_out: QubitId,
    consumer: impl FnOnce(&mut Builder, QubitId, QubitId, QubitId, Option<QubitId>),
) {
    let n=acc.len(); assert!(n>=1); assert_eq!(addend.len(),n);
    let missing=(circ.active_qubits()as usize+n-1).saturating_sub(walk_max_qubits());
    if n>=3 && missing>0 && missing<=super::bridge::budget() && missing<n-1 {
        if super::env_flag("I35_TRACE"){eprintln!("I35_BRIDGE consume {} {}",n,missing);}
        super::bridge::run(circ,addend,acc,carry_in,Some(carry_out),missing,|c,o,a,s,p|consumer(c,o.unwrap(),a,s,p));return;
    }
    let carries=circ.alloc_qubits(n-1);
    let previous=|i:usize|if i==0 {carry_in} else {Some(carries[i-1])};
    for i in 0..n {
        carry_step(circ,addend[i],acc[i],previous(i),
            if i+1==n {carry_out} else {carries[i]});
    }
    if let Some(p)=previous(n-1) {circ.cx(p,addend[n-1]);}
    circ.cx(addend[n-1],acc[n-1]);
    consumer(circ,carry_out,addend[n-1],acc[n-1],previous(n-1));
    for i in (0..n-1).rev() {
        unwind_carry_step(circ,addend[i],acc[i],previous(i),carries[i]);
    }
}

/// X-erase an outgoing carry using the live completed top-bit frame.
/// o = a*s XOR a XOR a*c XOR s*c XOR c, with c=0 when absent.
pub(crate) fn erase_overflow_from_frame(
    circ: &mut Builder, overflow: QubitId, source_top: QubitId,
    sum_top: QubitId, carry_into_top: Option<QubitId>,
) {
    let m=circ.alloc_bit(); circ.hmr(overflow,m);
    circ.z_if(source_top,m); circ.cz_if(source_top,sum_top,m);
    if let Some(c)=carry_into_top {
        circ.z_if(c,m); circ.cz_if(source_top,c,m); circ.cz_if(sum_top,c,m);
    }
    circ.free_bit(m); circ.free(overflow);
}

/// [`ripple_add`] with one deferred X-measurement phase applied to an arithmetic
/// carry before that carry's own measurement unwind changes its representation.
/// `carry_index == 0` names the carry out of the slice's bit 0.
pub fn ripple_add_with_deferred_phase(
    circ: &mut Builder,
    addend: &[QubitId],
    acc: &[QubitId],
    carry_in: Option<QubitId>,
    carry_out: Option<QubitId>,
    deferred: Option<(usize, BitId)>,
) {
    if carry_out.is_none() && deferred.is_none() && result_top_loan_enabled(acc) {ripple_add_result_top_loan(circ,addend,acc,carry_in,None,false);return;}
    ripple_add_proved(
        circ, addend, acc, carry_in, carry_out, Carry0::Full, Carry1::Full, deferred, None, None, None,
    );
}

pub(crate) fn ripple_add_proved(
    circ: &mut Builder, addend: &[QubitId], acc: &[QubitId],
    carry_in: Option<QubitId>, carry_out: Option<QubitId>, c0: Carry0, c1: Carry1,
    mut deferred: Option<(usize, BitId)>,
    known_output: Option<&[(bool, Vec<QubitId>)]>,
    known_terminal: Option<bool>,
    borrowed: Option<&[QubitId]>,
) {
    let width = acc.len();
    let k = addend.len();
    assert!(k >= 1 && k <= width, "ripple_add: addend must be 1..=acc bits wide");
    if width == 0 {
        return;
    }
    // Consume supplied carry before exact splitting so the first subchunk inherits it.
    let c0=if let Some(q)=GO_C0.with(|g|g.take()){assert!(c0==Carry0::Full && carry_in.is_none());Carry0::Known(q)}else{c0};
    // One owned carry per position that needs one: below the top when the top's
    // carry is the caller's `carry_out`, below the position under it when there
    // is no carry-out and that position's carry is fused into the top sum bit.
    let vented = carry_out.is_some();
    let owned = if vented {
        width - 1
    } else {
        width.saturating_sub(2)
    };
    // B3b (HEO builds only): a ladder that cannot fit under the cap is split into exact
    // chunks whose boundary carries are erased top-down by exact whole-chunk compares.
    if super::heo::fit_adds() && borrowed.is_none() && known_output.is_none() && !HEO_SPLIT_GUARD.with(|g| g.get()) {
        let room = walk_max_qubits().saturating_sub(circ.active_qubits() as usize);
        if owned > room && width >= 8
            && heo_split_ripple(circ, addend, acc, carry_in, carry_out, c0, c1, deferred, known_terminal, room) {
            return;
        }
    }
    if super::heo::research_on() && owned > 100 && std::env::var("HEO_BIG_RIPPLE_TRACE").is_ok() {
        eprintln!("HEO_BIG_RIPPLE owned={owned} active={} op={}
{}", circ.active_qubits(), circ.op_count(),
            std::backtrace::Backtrace::force_capture());
    }
    // Copy request is consumed only by the actual first ladder, after fitting.
    let go_copy0=GO_COPY0.with(|g|g.take());
    if go_copy0.is_some(){assert!(carry_in.is_none() && known_output.is_none() && owned>0);}
    let mut carries = if let Some(qs)=borrowed {
        assert!(carry_out.is_none() && k+1==width);
        assert_eq!(qs.len(),owned);
        assert!(qs.iter().all(|q|!acc.contains(q) && !addend.contains(q)));
        qs.to_vec()
    } else {if std::env::var_os("SKY_OVERSHOOT").is_some() && circ.active_qubits() as usize+owned>walk_max_qubits(){eprintln!("SKY_OVER owned={owned} active={} width={width} op={} k={k} fit={} ko={} guard={} cin={} cout={}",circ.active_qubits(),circ.op_count(),super::heo::fit_adds(),known_output.is_some(),HEO_SPLIT_GUARD.with(|g| g.get()),carry_in.is_some(),carry_out.is_some());} circ.alloc_qubits(owned)};
    carries.extend(carry_out);
    let previous = |i: usize| {
        if i == 0 {
            carry_in
        } else {
            Some(carries[i - 1])
        }
    };
    // A position at or above `k` has no addend bit: its stage is the same
    // ladder step with the addend fixed at zero, `carry = acc AND previous`,
    // and it always has a previous carry because `k >= 1`.
    let zero_prev = |i: usize| previous(i).expect("a zero-addend position always has a carry in");

    if let Some(output)=known_output {
        // The pre-pass reads carry[j-1] = addend[j]^acc[j]^sum[j] for j >= 1 only,
        // which does not involve a carry-in, so SQ_CIN_SPREAD's rows may pass one.
        assert!(carry_out.is_none() && deferred.is_none());
        assert_eq!(k+1,width);assert_eq!(output.len(),width);
        // sum[j] = original_addend[j] XOR original_acc[j] XOR carry[j-1].
        // The caller supplies a proved affine expression for the resulting
        // sum. Compute ALL carries while those original source bits are still
        // intact, before the normal ripple folds anything into its operands.
        for (i,&q) in carries.iter().enumerate() {
            let j=i+1;
            circ.cx(addend[j],q);circ.cx(acc[j],q);
            if output[j].0 {circ.x(q);}
            for &s in &output[j].1 {circ.cx(s,q);}
        }
    }

    for i in 0..carries.len() {
        if known_output.is_some() {
            // Carries already contain arithmetic carries. Preserve the usual
            // folded operand state so the terminal step and exact measured
            // unwind below remain unchanged.
            if let Some(prev)=previous(i) {circ.cx(prev,addend[i]);circ.cx(prev,acc[i]);}
        } else if i == 0 && c0 == Carry0::IsAddend0 && carry_in.is_some() {
            // SQ_CIN_SPREAD row 0: the caller proves acc[0] == NOT carry_in, so
            // MAJ(addend0, acc0, carry_in) == addend0. Copy it, then fold the
            // carry-in into both operands exactly as carry_step leaves them.
            let cin = carry_in.unwrap();
            circ.cx(addend[0], carries[0]);
            circ.cx(cin, addend[0]);
            circ.cx(cin, acc[0]);
        } else if i == 0 && c0 != Carry0::Full {
            assert!(carry_in.is_none() && k >= 2 && width >= 4);
            if c0 == Carry0::IsAddend0 { circ.cx(addend[0], carries[0]); }
            if let Carry0::Known(q)=c0 {assert!(!carries.contains(&q));circ.cx(q,carries[0]);}
        } else if i == 1 && c1 == Carry1::CopiesCarry0 {
            assert!(carry_in.is_none() && k >= 2 && width >= 4);
            let prev = previous(i).unwrap();
            circ.cx(prev, addend[i]);
            circ.cx(prev, acc[i]);
            circ.cx(prev, carries[i]);
        } else if (i == 1 || i == 2) && c1 == Carry1::SquareLeaf && carry_in.is_none() && c0 == Carry0::IsAddend0 && i < k && i + 1 < width {
            // carry_step with its Toffoli product written as CX gates (see `Carry1::SquareLeaf`)
            let prev = previous(i).unwrap();
            circ.cx(prev, addend[i]);
            circ.cx(prev, acc[i]);
            if i == 2 {
                circ.cx(addend[2], carries[2]);
                circ.cx(addend[1], carries[2]);
            }
            circ.cx(acc[i + 1], carries[i]);
            circ.x(carries[i]);
            circ.cx(prev, carries[i]);
        } else if i < k {
            carry_step(circ, addend[i], acc[i], previous(i), carries[i]);
        } else {
            circ.ccx(zero_prev(i), acc[i], carries[i]);
        }
    }

    if let Some(q)=go_copy0{circ.cx(carries[0],q);}
    if vented || width == 1 {
        // The top sum bit. With a carry-out the loop above already folded the
        // incoming carry into both operands and only `addend` needs restoring;
        // without one the position is untouched and the carry has yet to be
        // applied. A width-1 wrapped add is all top and no ladder.
        let top = width - 1;
        if let Some(previous) = previous(top) {
            let into = if vented && top < k { addend[top] } else { acc[top] };
            circ.cx(previous, into);
        }
        if top < k {
            circ.cx(addend[top], acc[top]);
        }
    } else {
        let terminal=known_terminal.or_else(|| {
            known_output.filter(|_|super::env_flag("SQ_ROW0_MEASURE_TOP") || super::env_flag("SQ_ROW_ALL_MEASURE_TOP"))
                .map(|output| {assert!(output[width-1].1.is_empty());output[width-1].0})
        });
        if let Some(desired)=terminal {
            terminal_step_known(circ,addend,acc,previous(width-2),desired);
        } else {terminal_step(circ, addend, acc, previous(width - 2));}
    }

    for i in (0..owned).rev() {
        if deferred.as_ref().is_some_and(|(at, _)| *at == i) {
            let (_, phase) = deferred.take().unwrap();
            // At this point `carries[i]` is still the arithmetic carry. The
            // first CX in `unwind_carry_step` changes it to the CCX product.
            circ.z_if(carries[i], phase);
            circ.free_bit(phase);
        }
        if i < k {
            if borrowed.is_some() {unwind_carry_step_lent(circ,addend[i],acc[i],previous(i),carries[i]);}
            else {unwind_carry_step(circ, addend[i], acc[i], previous(i), carries[i]);}
        } else {
            unwind_zero_step(circ, acc[i], zero_prev(i), carries[i]);
        }
    }
    assert!(deferred.is_none(), "deferred phase did not name an owned ripple carry");
}

thread_local! { static HEO_SPLIT_GUARD: std::cell::Cell<bool> = const { std::cell::Cell::new(false) }; }

/// B3b: the chunked form of [`ripple_add_proved`] (see its HEO block). Returns false
/// (nothing emitted) when no layout with every chunk inside the addend exists.
#[allow(clippy::too_many_arguments)]
fn sky_trim_last() -> bool { std::env::var("SKY_SPLIT_TRIM_LAST").is_ok_and(|v| v == "1") }

fn heo_split_ripple(circ: &mut Builder, addend: &[QubitId], acc: &[QubitId], carry_in: Option<QubitId>,
                    carry_out: Option<QubitId>, c0: Carry0, c1: Carry1, deferred: Option<(usize, BitId)>,
                    known_terminal: Option<bool>, room: usize) -> bool {
    let width = acc.len();
    let k = addend.len();
    let vented = carry_out.is_some();
    let min0 = if c0 != Carry0::Full || c1 != Carry1::Full { 4 } else { 2 };
    let win = if SHARED_SPLIT_EXACT.with(|x|x.get()) {0} else {super::heo::fit_window()};
    let mut sizes: Option<Vec<usize>> = None;
    for nk in 2..64usize {
        let mut caps: Vec<isize> = if win > 0 {
            // immediate windowed erasure: chunk j holds its carry-in and carry-out only
            let mut v = vec![room as isize];
            v.extend(std::iter::repeat_n(room as isize - 1, nk - 2));
            v
        } else {
            (0..nk - 1).map(|j| room as isize - j as isize).collect()
        };
        caps.push(if win > 0 { room as isize + if vented { 0 } else { 1 } }
                  else { room as isize - (nk as isize - 1) + if vented { 1 } else { 2 } });
        if caps[0] < min0 as isize || caps.iter().skip(1).any(|&c| c < 2) {
            return false;
        }
        let sum: isize = caps.iter().sum();
        if sum < width as isize {
            continue;
        }
        let mut sz: Vec<usize> = caps.iter().map(|&c| c as usize).collect();
        let mut excess = sum as usize - width;
        for (j, w) in sz.iter_mut().enumerate().take(nk - 1) {
            let floor = if j == 0 { min0 } else { 2 };
            let cut = excess.min(*w - floor);
            *w -= cut;
            excess -= cut;
        }
        if excess > 0 {
            // SKY_SPLIT_TRIM_LAST (fallback only): the last chunk may shrink too, so a
            // ladder whose addend fills the last cap still splits under the cap.
            if sky_trim_last() && sz[nk - 1] >= excess + 2 { sz[nk - 1] -= excess; sizes = Some(sz); break; }
            continue;
        }
        sizes = Some(sz);
        break;
    }
    let Some(sizes) = sizes else { return false };
    let nk = sizes.len();
    // every chunk must start inside the addend, and every compared chunk lie inside it
    let mut bounds = Vec::with_capacity(nk);
    let mut lo = 0;
    for &w in &sizes {
        bounds.push((lo, lo + w));
        lo += w;
    }
    if bounds[nk - 1].0 >= k || bounds[nk - 2].1 > k {
        return false;
    }
    HEO_SPLIT_GUARD.with(|g| g.set(true));
    let mut deferred = deferred;
    let mut cin = carry_in;
    let mut kept: Vec<(QubitId, usize, usize, Option<QubitId>)> = Vec::new();
    for (j, &(lo, hi)) in bounds.iter().enumerate() {
        let last = j + 1 == nk;
        let out = if last { carry_out } else { Some(circ.alloc_qubit()) };
        let (cc0, cc1) = if j == 0 { (c0, c1) } else { (Carry0::Full, Carry1::Full) };
        let owned_hi = if last { if vented { hi - 1 } else { hi.saturating_sub(2).max(lo) } } else { hi - 1 };
        let def_j = match deferred {
            Some((i, m)) if i >= lo && i < owned_hi => { deferred = None; Some((i - lo, m)) }
            _ => None,
        };
        ripple_add_proved(circ, &addend[lo..hi.min(k)], &acc[lo..hi], cin, out, cc0, cc1, def_j, None,
                          if last { known_terminal } else { None }, None);
        if win > 0 {
            // erase the boundary this chunk just consumed (the previous chunk's carry-out)
            if let Some((b, plo, phi, pcin)) = kept.pop() {
                if plo == 0 && phi - plo <= win {
                    erase_with_compare(circ, b, &acc[plo..phi], &addend[plo..phi], pcin);
                } else {
                    let kw = win.min(phi - plo);
                    erase_with_compare(circ, b, &acc[phi - kw..phi], &addend[phi - kw..phi], None);
                }
                circ.free(b);
            }
        }
        if !last {
            let b = out.unwrap();
            if let Some((i, m)) = deferred {
                if i == hi - 1 {
                    circ.z_if(b, m);
                    circ.free_bit(m);
                    deferred = None;
                }
            }
            kept.push((b, lo, hi, cin));
        }
        cin = out;
    }
    assert!(deferred.is_none(), "split ripple: deferred phase not placed");
    assert!(win == 0 || kept.is_empty());
    for (b, lo, hi, cin_j) in kept.into_iter().rev() {
        erase_with_compare(circ, b, &acc[lo..hi], &addend[lo..hi], cin_j);
        circ.free(b);
    }
    HEO_SPLIT_GUARD.with(|g| g.set(false));
    true
}

/// Undo a zero-addend stage: erase `carry = acc AND previous` in the X basis,
/// repair its phase from the two wires that produced it, and apply the sum bit.
fn unwind_zero_step(circ: &mut Builder, acc: QubitId, previous: QubitId, carry: QubitId) {
    let measured = circ.alloc_bit();
    circ.hmr(carry, measured);
    circ.cz_if(previous, acc, measured);
    circ.free_bit(measured);
    circ.free(carry);
    circ.cx(previous, acc);
}

/// One ripple stage: `carry = MAJ(addend, acc, previous)`, with the incoming
/// carry folded into the operands and back out again. A `None` `previous` is a
/// position whose carry-in is provably zero, and costs the bare Toffoli.
fn carry_step(
    circ: &mut Builder,
    addend: QubitId,
    acc: QubitId,
    previous: Option<QubitId>,
    carry: QubitId,
) {
    if let Some(previous) = previous {
        circ.cx(previous, addend);
        circ.cx(previous, acc);
    }
    circ.ccx(addend, acc, carry);
    if let Some(previous) = previous {
        circ.cx(previous, carry);
    }
}

/// Undo one [`carry_step`]: erase the carry in the X basis, repair the phase
/// from the operands that produced it, and apply the position's sum bit. Zero
/// Toffoli, and the carry wire goes back to the allocator here.
fn unwind_carry_step(
    circ: &mut Builder,
    addend: QubitId,
    acc: QubitId,
    previous: Option<QubitId>,
    carry: QubitId,
) {
    if let Some(previous) = previous {
        circ.cx(previous, carry);
    }
    // The erasure `carry_step`'s Toffoli asks for: measure the carry out in
    // the X basis and pay for it with a CZ on the two operands that made it.
    let measured = circ.alloc_bit();
    circ.hmr(carry, measured);
    circ.cz_if(addend, acc, measured);
    circ.free_bit(measured);
    circ.free(carry);
    if let Some(previous) = previous {
        circ.cx(previous, addend);
    }
    circ.cx(addend, acc);
}

/// The stage below the top of a wrapped add. Its carry is wanted only as an XOR
/// into the top output bit, so it is emitted straight there instead of onto a
/// wire of its own -- which is why the wrapped mode holds one carry fewer than
/// the vented one at the same Toffoli count, and why this stage needs no unwind.
fn terminal_step(
    circ: &mut Builder,
    addend: &[QubitId],
    acc: &[QubitId],
    previous: Option<QubitId>,
) {
    if has_top_copy(acc){terminal_top_copy(circ,addend,acc,previous);return;}
    let n = acc.len();
    let k = addend.len();
    let i = n - 2;
    if i >= k {
        // Zero-addend stage below a zero-addend top: `acc_top ^= acc_i AND
        // previous`, then the sum bit `acc_i ^= previous`.
        let previous = previous.expect("a zero-addend position always has a carry in");
        circ.ccx(previous, acc[i], acc[n - 1]);
        circ.cx(previous, acc[i]);
        return;
    }
    if let Some(previous) = previous {
        circ.cx(previous, addend[i]);
        circ.cx(previous, acc[i]);
    }
    circ.ccx(addend[i], acc[i], acc[n - 1]);
    if let Some(previous) = previous {
        circ.cx(previous, acc[n - 1]);
    }
    if n - 1 < k {
        circ.cx(addend[n - 1], acc[n - 1]);
    }
    if let Some(previous) = previous {
        circ.cx(previous, addend[i]);
    }
    circ.cx(addend[i], acc[i]);
}

/// Exact inverse producer only: if the resulting top bit is the known
/// constant d, recover its OLD value from the terminal carry expression and
/// any top addend. X-measure it and repair all terms with Clifford gates.
/// This replaces one terminal CCX with one extra measurement, no scratch wire.
fn terminal_step_known(circ:&mut Builder,addend:&[QubitId],acc:&[QubitId],previous:Option<QubitId>,desired:bool) {
    let n=acc.len();let k=addend.len();assert!(n>=2 && k<=n);let i=n-2;
    if i>=k {
        let p=previous.expect("padded stage has incoming carry");
        let m=circ.alloc_bit();circ.hmr(acc[n-1],m);
        if desired {circ.x(acc[n-1]);circ.z_if(acc[n-1],m);}
        circ.cz_if(p,acc[i],m);circ.free_bit(m);
        circ.cx(p,acc[i]);return;
    }
    if let Some(p)=previous {circ.cx(p,addend[i]);circ.cx(p,acc[i]);}
    let m=circ.alloc_bit();circ.hmr(acc[n-1],m);
    if desired {circ.x(acc[n-1]);circ.z_if(acc[n-1],m);}
    if let Some(p)=previous {circ.z_if(p,m);}
    if n-1<k {circ.z_if(addend[n-1],m);}
    circ.cz_if(addend[i],acc[i],m);circ.free_bit(m);
    if let Some(p)=previous {circ.cx(p,addend[i]);}
    circ.cx(addend[i],acc[i]);
}

/// Controlled add of the folding constant `f = 2^32 + 977` into the low `lsbs`
/// bits of `reg`, conditioned on `ctrl`. Carries past bit `lsbs` are dropped.
///
/// `f` is the only constant this is ever folded with -- it is what `2^256`
/// reduces to mod p -- so it is baked in rather than threaded through every
/// caller. The window width still varies and stays a parameter.
///
/// This is `cadd_const_trunc` over the slice: cutting `reg` down to `lsbs`
/// makes the slice itself the accumulator, so the carry off its top is the one
/// that gets dropped. `f` is odd, so position 0 carries whenever `ctrl` and
/// `reg[0]` are both set and needs a wire of its own -- unless the caller can
/// prove that away, which is what `first_carry_is_zero` says.
pub fn add_f_window(
    circ: &mut Builder,
    ctrl: QubitId,
    reg: &[QubitId],
    lsbs: usize,
    first_carry_is_zero: bool,
) {
    assert!(lsbs <= reg.len(), "register too short for +f window");
    cadd_const_trunc(circ, &reg[..lsbs], f(), ctrl, first_carry_is_zero);
}

/// `acc += addend`, or `acc -= addend` when `inverse` -- subtraction is the
/// complement-add-complement identity `~(~acc + v) == acc - v`.
/// [`ripple_add`] with the carry out of position `width - 3` on a LENT wire
/// instead of an owned one: one fewer allocation, one narrower ladder.
///
/// `lent` must arrive clean (|0>) and is returned clean: its unwind is the
/// same measurement erasure the owned carries get, minus the `free` -- the
/// wire stays the caller's. Gate sequence, wire values and phase repairs are
/// otherwise identical to [`ripple_add`] with one more owned carry, so the sum
/// computed is bit-for-bit the same.
///
/// Wrapped mode only (no carry-out): both walk-adder callers wrap. With
/// `width < 3` there is no carry position below the terminal fusion to lend,
/// so this falls back to [`ripple_add`] and `lent` is never touched.
pub fn ripple_add_lent(
    circ: &mut Builder,
    addend: &[QubitId],
    acc: &[QubitId],
    carry_in: Option<QubitId>,
    lent: QubitId,
) {
    ripple_add_lent_with_deferred_phase(circ, addend, acc, carry_in, lent, None);
}

/// [`ripple_add_lent`] with a deferred phase attached to one arithmetic carry.
/// The hook also supports the final carry stored on `lent` (index `width - 3`).
pub fn ripple_add_lent_with_deferred_phase(
    circ: &mut Builder,
    addend: &[QubitId],
    acc: &[QubitId],
    carry_in: Option<QubitId>,
    lent: QubitId,
    mut deferred: Option<(usize, BitId)>,
) {
    let width = addend.len();
    assert_eq!(width, acc.len(), "ripple_add_lent: width mismatch");
    if deferred.is_none() && result_top_loan_enabled(acc) {ripple_add_result_top_loan(circ,addend,acc,carry_in,Some(lent),false);return;}
    if width < 3 {
        ripple_add_with_deferred_phase(circ, addend, acc, carry_in, None, deferred);
        return;
    }
    // Owned carries for positions 0..width-3; the lent wire takes the carry out
    // of position width - 3, which the terminal fusion reads.
    let owned = width - 3;
    let carries = circ.alloc_qubits(owned);
    let previous = |i: usize| {
        if i == 0 {
            carry_in
        } else {
            Some(carries[i - 1])
        }
    };

    for i in 0..owned {
        carry_step(circ, addend[i], acc[i], previous(i), carries[i]);
    }
    carry_step(circ, addend[owned], acc[owned], previous(owned), lent);
    terminal_step(circ, addend, acc, Some(lent));

    if deferred.as_ref().is_some_and(|(at, _)| *at == owned) {
        let (_, phase) = deferred.take().unwrap();
        circ.z_if(lent, phase);
        circ.free_bit(phase);
    }
    unwind_carry_step_lent(circ, addend[owned], acc[owned], previous(owned), lent);
    for i in (0..owned).rev() {
        if deferred.as_ref().is_some_and(|(at, _)| *at == i) {
            let (_, phase) = deferred.take().unwrap();
            circ.z_if(carries[i], phase);
            circ.free_bit(phase);
        }
        unwind_carry_step(circ, addend[i], acc[i], previous(i), carries[i]);
    }
    assert!(deferred.is_none(), "deferred phase did not name a lent-ripple carry");
}

/// [`unwind_carry_step`] for a lent carry wire: same erasure and phase repair,
/// but the wire is the caller's, so there is no `free` -- the `hmr` has
/// already left it clean, which is exactly the state it was lent in.
fn unwind_carry_step_lent(
    circ: &mut Builder,
    addend: QubitId,
    acc: QubitId,
    previous: Option<QubitId>,
    carry: QubitId,
) {
    if let Some(previous) = previous {
        circ.cx(previous, carry);
    }
    let measured = circ.alloc_bit();
    circ.hmr(carry, measured);
    circ.cz_if(addend, acc, measured);
    circ.free_bit(measured);
    if let Some(previous) = previous {
        circ.cx(previous, addend);
    }
    circ.cx(addend, acc);
}

/// Wrapped add on the structural subspace addend[n-1]==addend[n-2].
/// Borrow the redundant top source bit for the last carry, in addition to an
/// optional already-clean caller loan. Both are restored, with exact phase.
pub(crate) fn ripple_add_source_sign_loan(
    circ:&mut Builder,addend:&[QubitId],acc:&[QubitId],carry_in:Option<QubitId>,
    lent:Option<QubitId>,mut deferred:Option<(usize,BitId)>,
) {
    let n=addend.len();assert_eq!(n,acc.len());
    assert!(n>=3+usize::from(lent.is_some()));
    if deferred.is_none() && result_top_loan_enabled(acc) && n>=4+usize::from(lent.is_some()) && super::env_flag("I76_SOURCE_TOP_LOAN") {
        ripple_add_result_top_loan(circ,addend,acc,carry_in,lent,true);return;
    }
    let owned=n-3-usize::from(lent.is_some());
    let high=addend[n-1];let copy=addend[n-2];
    assert!(!acc.contains(&high));
    if let Some(q)=lent{assert!(!acc.contains(&q)&&!addend.contains(&q));}
    circ.cx(copy,high);
    let mut carries=circ.alloc_qubits(owned);
    carries.extend(lent);carries.push(high);
    let previous=|i:usize|if i==0{carry_in}else{Some(carries[i-1])};
    for i in 0..carries.len(){carry_step(circ,addend[i],acc[i],previous(i),carries[i]);}
    // The terminal's incoming carry occupies the old source top. Restore the
    // original penultimate source before adding the identical top source bit.
    let i=n-2;
    circ.cx(high,copy);circ.cx(high,acc[i]);
    if has_top_copy(acc){
      let m=circ.alloc_bit();circ.hmr(acc[n-1],m);
      circ.cz_if(copy,acc[i],m);circ.z_if(high,m);circ.z_if(acc[i],m);circ.free_bit(m);
      circ.cx(high,copy);circ.cx(copy,acc[i]);circ.cx(acc[i],acc[n-1]);
    }else{
      circ.ccx(copy,acc[i],acc[n-1]);circ.cx(high,acc[n-1]);
      circ.cx(high,copy);circ.cx(copy,acc[n-1]);circ.cx(copy,acc[i]);
    }
    for i in (0..carries.len()).rev(){
        if deferred.as_ref().is_some_and(|(at,_)|*at==i){
            let(_,m)=deferred.take().unwrap();circ.z_if(carries[i],m);circ.free_bit(m);
        }
        if i<owned{unwind_carry_step(circ,addend[i],acc[i],previous(i),carries[i]);}
        else{unwind_carry_step_lent(circ,addend[i],acc[i],previous(i),carries[i]);}
    }
    assert!(deferred.is_none());circ.cx(copy,high);
}

pub fn addsub_full(circ: &mut Builder, addend: &[QubitId], acc: &[QubitId], inverse: bool) {
    // B3b (HEO builds only): fit a wide exact add under the cap instead of overshooting it.
    if super::heo::fit_adds() && heo_fitted_addsub(circ, addend, acc, inverse) {
        return;
    }
    if inverse {
        circ.x_all(acc);
    }
    ripple_add(circ, addend, acc, None, None);
    if inverse {
        circ.x_all(acc);
    }
}

/// B3b: HEO-only room-fitted exact add (the square's wide window adds ignore the cap
/// otherwise). Exact chunked ripple with top-down exact boundary compares
/// (`width_composition::direct_add`); returns false (caller emits the plain ripple)
/// when the plain ladder already fits.
fn heo_fitted_addsub(circ: &mut Builder, addend: &[QubitId], acc: &[QubitId], inverse: bool) -> bool {
    let n = acc.len();
    if n < 4 || !super::heo::fit_adds() || result_top_loan_enabled(acc) || super::heo::fit_mode_split() {
        return false;
    }
    let room = walk_max_qubits().saturating_sub(circ.active_qubits() as usize);
    if n - 2 <= room {
        return false;
    }
    let zero = circ.alloc_qubit();
    let room = walk_max_qubits().saturating_sub(circ.active_qubits() as usize);
    let plan = (room..=n.max(room)).find_map(|r| super::width_composition::direct_plan(n, r)).unwrap();
    let map: Vec<Vec<QubitId>> = (0..n).map(|i| addend.get(i).copied().into_iter().collect()).collect();
    if inverse {
        circ.x_all(acc);
    }
    super::width_composition::direct_add(circ, &map, acc, zero, &plan);
    if inverse {
        circ.x_all(acc);
    }
    circ.release_clean(zero);
    true
}

/// Same, for a `value` narrower than `acc`: the positions above the value are
/// zero-addend stages of the one ladder (`carry = acc AND previous`), so this
/// costs the same `acc.len() - 1` Toffoli a zero-extended full ripple does but
/// keeps no pad qubits live -- the pads used to be what let the square's
/// cross-term add set the peak.
pub fn addsub_wide(circ: &mut Builder, value: &[QubitId], acc: &[QubitId], inverse: bool) {
    assert!(value.len() <= acc.len(), "addsub_wide: value wider than acc");
    addsub_full(circ, value, acc, inverse);
}

pub fn add_wide(circ: &mut Builder, value: &[QubitId], acc: &[QubitId]) {
    addsub_wide(circ, value, acc, false);
}

pub fn sub_wide(circ: &mut Builder, value: &[QubitId], acc: &[QubitId]) {
    addsub_wide(circ, value, acc, true);
}

/// `ripple_add` with a carry-out, whose carry ladder is made to fit under the
/// tree-wide peak ([`walk_max_qubits`]) when the plain ladder would not.
///
/// The plain ripple keeps `width - 1` carries plus the overflow live at once.
/// When that overshoots the peak, the add is cut into an exact leading chunk
/// and the rest: the leading chunk ripples into a carry wire `mid`, unwinds its
/// own carries, the high chunk ripples on from `mid` to `carry_out`, and `mid`
/// is then erased by comparing the WHOLE leading chunk (`sum < addend`, exact
/// because chunk 0 has no carry-in -- the same lambda-free repair
/// `pingpong::chunk_layout` gives its leading chunk). Cost: one Toffoli per
/// leading-chunk bit under a half-time condition; no new failure site. The
/// leading chunk is the narrowest that fits, so the plain add is emitted
/// unchanged wherever it already fits -- the coordinate shell is byte-identical.
pub(super) fn peak_fitted_add(circ: &mut Builder, value: &[QubitId], acc: &[QubitId], carry_out: QubitId) {
    let width = value.len();
    let room = walk_max_qubits().saturating_sub(circ.active_qubits() as usize);
    // Plain ladder: `width - 1` owned carries (the overflow is already counted
    // in the live set).
    if width < 3 || room >= width - 1 {
        ripple_add(circ, value, acc, None, Some(carry_out));
        return;
    }
    // Split: the high chunk of `high` bits owns `high - 1` carries with `mid`
    // live beside them, so `high <= room`. The leading chunk needs >= 2 bits
    // for the comparison.
    let high = room.clamp(1, width - 2);
    let low = width - high;
    let mid = circ.alloc_qubit();
    ripple_add(circ, &value[..low], &acc[..low], None, Some(mid));
    ripple_add(circ, &value[low..], &acc[low..], Some(mid), Some(carry_out));
    // PP_F_PEAKCMP=k: compare only the top k bits of the leading chunk
    // (approximate, fails only when those k bits tie). Unset: exact.
    match peak_cmp_bits() {
        Some(k) if k >= 2 && low > k => {
            erase_with_compare(circ, mid, &acc[low - k..low], &value[low - k..low], None)
        }
        _ => erase_with_compare(circ, mid, &acc[..low], &value[..low], None),
    }
    circ.free(mid);
}

/// B3b (HEO builds only): `acc += value` with the carry-out on a fresh wire, laid out by
/// `width_composition::plan` whenever the head's two-chunk `peak_fitted_add` cannot fit
/// (both of its chunks must be under the room). Exact; None = use the head path.
pub(super) fn heo_vented_ripple(circ: &mut Builder, value: &[QubitId], acc: &[QubitId]) -> QubitId {
    heo_fitted_vented_add(circ, value, acc).unwrap_or_else(|| {
        let overflow = circ.alloc_qubit();
        peak_fitted_add(circ, value, acc, overflow);
        overflow
    })
}

pub(crate) fn heo_fitted_vented_add(circ: &mut Builder, value: &[QubitId], acc: &[QubitId]) -> Option<QubitId> {
    if !super::heo::fit_adds() || value.len() != acc.len() || value.len() < 3 {
        return None;
    }
    if super::heo::fit_mode_split() {
        // plain ripple; `ripple_add_proved`'s HEO block chunks it to the room
        let overflow = circ.alloc_qubit();
        ripple_add(circ, value, acc, None, Some(overflow));
        return Some(overflow);
    }
    let width = value.len();
    let room = walk_max_qubits().saturating_sub(circ.active_qubits() as usize);
    // head path fits: plain (width <= room), or two chunks each within the room left after `mid`
    if room >= width || width + 1 <= 2 * room.saturating_sub(1) {
        return None;
    }
    let plan = (room..=width.max(room)).find_map(|r| super::width_composition::plan(width, r))?;
    Some(super::width_composition::add(circ, value, acc, &plan))
}

/// `acc += value (mod p)`, or `acc -= value` when `negate`.
///
/// The carry out of the top bit is caught on a scratch wire, folded back in as
/// `+f` over [`f_slice`] bits (since `2^256 = f (mod p)`), and then erased by
/// measurement with an [`erase_compare`]-wide comparison. Those two widths are
/// the whole approximation. Both are the tree-wide knobs rather than arguments:
/// the balance rule wants one value per shape, not one per caller.
pub fn mod_addsub(circ: &mut Builder, negate: bool, value: &[QubitId], acc: &[QubitId]) {
    mod_addsub_with(circ, negate, value, acc, go_fs("GO_FG_M"), erase_compare(), f(), None)
}

/// R4_YSUB_FUSE head of [`mod_addsub`] with `negate`: complement `acc`, add, return the live vented overflow.
pub(crate) fn r4_addsub_head(circ: &mut Builder, value: &[QubitId], acc: &[QubitId]) -> QubitId {
    assert_eq!(value.len(), acc.len(), "r4_addsub_head: width mismatch");
    circ.x_all(acc);
    heo_fitted_vented_add(circ, value, acc).unwrap_or_else(|| {
        let overflow = circ.alloc_qubit();
        peak_fitted_add(circ, value, acc, overflow);
        overflow
    })
}

/// R5_CBITS bitmask (sky-PM Round 5): 1 coord_x_sub, 2 ysub head, 4 back seam Div leg, 8 back seam
/// Mul leg run their classical-operand adds with [`r5_ripple_add_cbits`] (bit 0 carry is a CX).
pub(crate) fn r5_ccmp(bit: u32) -> bool {
    std::env::var("R5_CCMP").ok().and_then(|v| v.trim().parse::<u32>().ok()).unwrap_or(0) & bit != 0
}

pub(crate) fn r5_cbits(bit: u32) -> bool {
    std::env::var("R5_CBITS").ok().and_then(|v| v.trim().parse::<u32>().ok()).unwrap_or(0) & bit != 0
}

/// R5 (sky-PM Round 5): `acc += a` for a classical operand `a` (runtime bits), vented carry into
/// `carry_out`. The same Gidney ladder as [`ripple_add`] without addend wires: the folded addend
/// `a_i ^ c_i` is the previous carry wire under a classically conditioned X, so it needs only the
/// `width - 1` owned carries (no temp register). Bit 0's carry is `a_0 AND acc_0`: a conditioned CX.
pub(crate) fn r5_ripple_add_cbits(circ: &mut Builder, a: &[BitId], acc: &[QubitId], carry_out: QubitId) {
    r5_ripple_add_cbits_sel(circ, a, None, acc, carry_out);
}

/// Flips `q` by addend bit `i >= 1`: `a[i] ^ (D[i] & (s ^ inv))` where `sel = (s, inv, D)`.
fn r5_cbits_flip(circ: &mut Builder, q: QubitId, a: &[BitId], sel: Option<(QubitId, bool, &[BitId])>, i: usize) {
    circ.x_if_bit(q, a[i]);
    if let Some((s, inv, d)) = sel {
        circ.push_condition(d[i]);
        circ.cx(s, q);
        if inv {
            circ.x(q);
        }
        circ.pop_condition();
    }
}

/// [`r5_ripple_add_cbits`] with an optional selected addend: bits `i >= 1` add
/// `a[i] ^ (D[i] & (s ^ inv))`, where `s` must be `acc[0]` (it is read before the sum touches it:
/// bit 0's addend is `a[0]` only, and `acc[0]` is restored to its value only at the very end).
pub(crate) fn r5_ripple_add_cbits_sel(
    circ: &mut Builder,
    a: &[BitId],
    sel: Option<(QubitId, bool, &[BitId])>,
    acc: &[QubitId],
    carry_out: QubitId,
) {
    let n = acc.len();
    assert_eq!(a.len(), n, "r5_ripple_add_cbits: width mismatch");
    assert!(n >= 2);
    if let Some((s, _, d)) = sel {
        assert_eq!(s, acc[0], "r5_ripple_add_cbits_sel: selector must be acc[0]");
        assert!(d.len() >= n);
    }
    let mut carries = circ.alloc_qubits(n - 1);
    carries.push(carry_out);
    circ.push_condition(a[0]);
    circ.cx(acc[0], carries[0]);
    circ.pop_condition();
    for i in 1..n {
        let p = carries[i - 1];
        circ.cx(p, acc[i]);
        r5_cbits_flip(circ, p, a, sel, i);
        circ.ccx(p, acc[i], carries[i]);
        r5_cbits_flip(circ, p, a, sel, i);
        circ.cx(p, carries[i]);
    }
    // top sum bit: acc[top] holds b ^ c.
    r5_cbits_flip(circ, acc[n - 1], a, sel, n - 1);
    for i in (1..n - 1).rev() {
        let p = carries[i - 1];
        let q = carries[i];
        circ.cx(p, q);
        let m = circ.alloc_bit();
        circ.hmr(q, m);
        r5_cbits_flip(circ, p, a, sel, i);
        circ.cz_if(p, acc[i], m);
        r5_cbits_flip(circ, p, a, sel, i);
        circ.free_bit(m);
        circ.free(q);
        r5_cbits_flip(circ, acc[i], a, sel, i);
    }
    let q = carries[0];
    let m = circ.alloc_bit();
    circ.hmr(q, m);
    let t = circ.alloc_bit();
    circ.bit_store0(t);
    circ.bit_and_xor_into(t, a[0], m);
    circ.z_if(acc[0], t);
    circ.bit_store0(t);
    circ.free_bit(t);
    circ.free_bit(m);
    circ.free(q);
    circ.x_if_bit(acc[0], a[0]);
}

/// [`mod_addsub`] with the fold window `fs`, erasure width `k` and fold constant `fconst` as
/// arguments, and an optional `mid` hook run between the fold and the carry erasure with the
/// vented carry wire (the I-2 back seam unloads its selected operand bits there).
pub fn mod_addsub_with(
    circ: &mut Builder,
    negate: bool,
    value: &[QubitId],
    acc: &[QubitId],
    fs: usize,
    k: usize,
    fconst: U256,
    mid: Option<&mut dyn FnMut(&mut Builder, QubitId)>,
) {
    assert_eq!(value.len(), acc.len(), "mod_addsub: width mismatch");
    if negate {
        circ.x_all(acc);
    }
    let overflow = heo_fitted_vented_add(circ, value, acc).unwrap_or_else(|| {
        let overflow = circ.alloc_qubit();
        peak_fitted_add(circ, value, acc, overflow);
        overflow
    });
    assert!(fs <= acc.len(), "register too short for +f window");
    cadd_const_trunc(circ, &acc[..fs], fconst, overflow, false);
    if let Some(mid) = mid {
        mid(circ, overflow);
    }
    let cmp_bits = k;
    let (top_acc, top_value) = (
        &acc[acc.len() - cmp_bits..],
        &value[value.len() - cmp_bits..],
    );
    erase_with_compare(circ, overflow, top_acc, top_value, None);
    circ.free(overflow);
    if negate {
        circ.x_all(acc);
    }
}

/// Fold the wrapped `2^256` back in as `+f`, inside a complemented frame.
fn fold_f_complemented(circ: &mut Builder, anc: QubitId, y: &[QubitId]) {
    fold_f_complemented_at(circ, anc, y, go_fs("GO_FG_M"), f())
}

pub(crate) fn fold_f_complemented_at(circ: &mut Builder, anc: QubitId, y: &[QubitId], fs: usize, fconst: U256) {
    circ.x_all(&y[..fs]);
    assert!(fs <= y.len(), "register too short for +f window");
    cadd_const_trunc(circ, &y[..fs], fconst, anc, false);
    circ.x_all(&y[..fs]);
}

/// `y <- t1 - y - 1 (mod p)`. The caller loads `t1` already carrying the `+1`.
///
/// `~y + t1 == t1 - y - 1`, so unlike [`mod_sub_vented`] this one *wants* the
/// complemented frame it adds in and never leaves it. That is the whole
/// difference between them, and it has two consequences: the vented carry means
/// the opposite thing, so it is inverted around the fold, and the erasure
/// compares the operands the other way round with neither complemented.
pub fn mod_rsub_vented_loaded(circ: &mut Builder, t1: &[QubitId], y: &[QubitId]) {
    assert_eq!(y.len(), t1.len(), "mod_rsub_vented_loaded: equal widths");
    assert_eq!(
        t1.len(),
        256,
        "secp256k1 mod_rsub_vented_loaded expects n=256"
    );
    mod_rsub_vented_loaded_with(circ, t1, y, go_fs("GO_FG_M"), erase_compare(), f(), None)
}

/// [`mod_rsub_vented_loaded`] with the fold window, erasure width and fold constant as arguments
/// and the same optional `mid` hook as [`mod_addsub_with`] (run with the vented carry restored to
/// its true polarity, before its erasure).
pub fn mod_rsub_vented_loaded_with(
    circ: &mut Builder,
    t1: &[QubitId],
    y: &[QubitId],
    fs: usize,
    k: usize,
    fconst: U256,
    mid: Option<&mut dyn FnMut(&mut Builder, QubitId)>,
) {
    assert_eq!(y.len(), t1.len(), "mod_rsub_vented_loaded: equal widths");
    let anc = circ.alloc_qubit();
    circ.x_all(y);
    ripple_add(circ, t1, y, None, Some(anc));
    circ.x(anc);
    fold_f_complemented_at(circ, anc, y, fs, fconst);
    circ.x(anc);
    if let Some(mid) = mid {
        mid(circ, anc);
    }
    erase_with_compare(circ, anc, &y[y.len() - k..], &t1[t1.len() - k..], None);
    circ.free(anc);
}

pub fn mod_add(circ: &mut Builder, x: &[QubitId], y: &[QubitId]) {
    assert_eq!(y.len(), x.len(), "mod_add: x,y must both be n=256 bits");
    assert_eq!(x.len(), 256, "secp256k1 mod_add expects n=256");
    mod_addsub(circ, false, x, y);
}

/// `y -= x (mod p)`.
///
/// Exactly [`mod_addsub`]'s subtracting mode, and not a routine of its own:
/// ending the complement frame in a different place looks like it would make one
/// and does not. Both spellings compute `y - x - f*borrow`, and both erasures are
/// the same predicate, because `~y_top < x_top` and `~x_top < y_top` are both
/// `x_top + y_top >= 2^k`. Verified by simulation -- 64/64 lanes agree bit for
/// bit, at 326 Toffoli either way.
pub fn mod_sub_vented(circ: &mut Builder, x: &[QubitId], y: &[QubitId]) {
    assert_eq!(
        y.len(),
        x.len(),
        "mod_sub_vented: x,y must both be n=256 bits"
    );
    assert_eq!(x.len(), 256, "secp256k1 mod_sub_vented expects n=256");
    mod_addsub(circ, true, x, y);
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Carry0 { Full, IsAddend0, Zero, Known(QubitId) }
#[derive(Clone, Copy, PartialEq, Eq)]
/// `SquareLeaf` (y9-span): the add is the correction a square leaf's inverse starts with, `acc` holds x^2 - 2 and
/// the addend's low bits are x (with `Carry0::IsAddend0`). Then the Toffoli products of positions 1 and 2 are affine
/// in live wires: p1 = NOT acc[2] and p2 = NOT (addend[2] ^ addend[1] ^ acc[3]) on the folded operands (integer model
/// `sq_leaf_model.py`: every x up to 10 bits; both read bits 0..3 only). Two CX chains replace two Toffoli.
pub enum Carry1 { Full, CopiesCarry0, SquareLeaf }
/// Wrapped wide add on a subspace with a proved affine output word. This is
/// NOT an unrestricted adder: incorrect output expressions violate its ABI.
pub(crate) fn add_wide_known_output(circ:&mut Builder, value:&[QubitId], acc:&[QubitId], output:&[(bool,Vec<QubitId>)],borrowed:Option<&[QubitId]>) {
    ripple_add_proved(circ,value,acc,None,None,Carry0::Full,Carry1::Full,None,Some(output),None,borrowed);
}
/// Borrowed carries arrive zero and remain owned by the caller. This receiver
/// is restricted to a wide triangular row, where every carry has an addend.
pub(crate) fn addsub_wide_borrowed(circ:&mut Builder,value:&[QubitId],acc:&[QubitId],inverse:bool,c0:Carry0,c1:Carry1,result_top:Option<bool>,borrowed:&[QubitId]) {
    if inverse {circ.x_all(acc);}
    ripple_add_proved(circ,value,acc,None,None,c0,c1,None,None,result_top.map(|v|v^inverse),Some(borrowed));
    if inverse {circ.x_all(acc);}
}
/// Caller proves the top result bit, without claiming any other output bits.
/// The complement frame flips that bit for the inner adder when subtracting.
pub(crate) fn addsub_wide_known_top(circ:&mut Builder,value:&[QubitId],acc:&[QubitId],inverse:bool,c0:Carry0,c1:Carry1,result_top:bool) {
    if inverse {circ.x_all(acc);}
    ripple_add_proved(circ,value,acc,None,None,c0,c1,None,None,Some(result_top^inverse),None);
    if inverse {circ.x_all(acc);}
}
pub fn addsub_full_low(circ: &mut Builder, value: &[QubitId], acc: &[QubitId], inverse: bool, c0: Carry0, c1: Carry1) {
    if inverse { circ.x_all(acc); }
    ripple_add_proved(circ, value, acc, None, None, c0, c1, None, None, None, None);
    if inverse { circ.x_all(acc); }
}
pub fn addsub_wide_low(circ: &mut Builder, value: &[QubitId], acc: &[QubitId], inverse: bool, c0: Carry0, c1: Carry1) {
    assert!(value.len() <= acc.len());
    addsub_full_low(circ, value, acc, inverse, c0, c1);
}


// Research: known final top is a copy of its neighboring output bit.
thread_local! {static TOP_COPY:std::cell::Cell<Option<(QubitId,QubitId)>>=const{std::cell::Cell::new(None)};}
pub(crate) fn with_top_copy(c:&mut Builder,acc:&[QubitId],enabled:bool,body:impl FnOnce(&mut Builder)){
 let pair=enabled.then(||(acc[acc.len()-1],acc[acc.len()-2]));
 TOP_COPY.with(|v|{assert!(v.replace(pair).is_none());});body(c);TOP_COPY.with(|v|v.set(None));
}
fn has_top_copy(acc:&[QubitId])->bool{acc.len()>=2 && TOP_COPY.with(|v|v.get()==Some((acc[acc.len()-1],acc[acc.len()-2])))}
fn terminal_top_copy(c:&mut Builder,a:&[QubitId],b:&[QubitId],previous:Option<QubitId>){
 let n=b.len();let i=n-2;assert_eq!(a.len(),n);
 if let Some(p)=previous{c.cx(p,a[i]);c.cx(p,b[i]);}
 let m=c.alloc_bit();c.hmr(b[n-1],m);
 c.z_if(a[n-1],m);c.cz_if(a[i],b[i],m);c.z_if(a[i],m);c.z_if(b[i],m);c.free_bit(m);
 if let Some(p)=previous{c.cx(p,a[i]);}c.cx(a[i],b[i]);c.cx(b[i],b[n-1]);
}

include!("top_result_loan.rs");

/// Exact wrapped add/subtract retaining all n-1 arithmetic carries. The source
/// is restored on return; carries belong to the later matching inverse.
pub(crate) fn shared_carry_forward(c:&mut Builder,a:&[QubitId],b:&[QubitId],negative:bool)->Vec<QubitId>{
    let n=b.len();let k=a.len();assert!(n>=2&&k>=1&&k<=n);
    assert!(a.iter().all(|q|!b.contains(q)));
    if negative{c.x_all(b);}
    let cs=c.alloc_qubits(n-1);
    for i in 0..n-1{
        let prev=if i==0{None}else{Some(cs[i-1])};
        if i<k{carry_step(c,a[i],b[i],prev,cs[i]);}
        else{c.ccx(prev.unwrap(),b[i],cs[i]);}
    }
    c.cx(cs[n-2],b[n-1]);if n-1<k{c.cx(a[n-1],b[n-1]);}
    for i in(0..n-1).rev(){
        if i<k{if i>0{c.cx(cs[i-1],a[i]);}c.cx(a[i],b[i]);}
        else{c.cx(cs[i-1],b[i]);}
    }
    if negative{c.x_all(b);}
    cs
}

/// Separately emitted inverse: restore b with sum XORs, then erase carries
/// from the original operand frame. No inverse CCX, no outcome reversal.
pub(crate) fn shared_carry_inverse(c:&mut Builder,a:&[QubitId],b:&[QubitId],negative:bool,cs:Vec<QubitId>){
    let n=b.len();let k=a.len();assert_eq!(cs.len(),n-1);
    for i in 0..n{if i<k{c.cx(a[i],b[i]);}if i>0{c.cx(cs[i-1],b[i]);}}
    for i in(0..n-1).rev(){
        let m=c.alloc_bit();c.hmr(cs[i],m);
        if i<k{
            c.cz_if(a[i],b[i],m);
            if i>0{c.cz_if(a[i],cs[i-1],m);c.cz_if(b[i],cs[i-1],m);}
            if negative{c.z_if(a[i],m);if i>0{c.z_if(cs[i-1],m);}}
        }else{
            c.cz_if(b[i],cs[i-1],m);if negative{c.z_if(cs[i-1],m);}
        }
        c.free_bit(m);c.free(cs[i]);
    }
}

// Exact supplied b_m2 carry hooks; source/target ownership is explicit at call sites.
thread_local! {
 static GO_C0: std::cell::Cell<Option<QubitId>> = const { std::cell::Cell::new(None) };
 static GO_COPY0: std::cell::Cell<Option<QubitId>> = const { std::cell::Cell::new(None) };
}
pub(crate) fn go_given_c0(q:QubitId){GO_C0.with(|g|assert!(g.replace(Some(q)).is_none()));}
pub(crate) fn go_copy_c0(q:QubitId){GO_COPY0.with(|g|assert!(g.replace(Some(q)).is_none()));}
pub(crate) fn go_c0_clear()->bool{GO_C0.with(|g|g.get().is_none())&&GO_COPY0.with(|g|g.get().is_none())}

pub(crate) fn add_low_keep(circ:&mut Builder,value:&[QubitId],acc:&[QubitId],keep:usize)->Vec<QubitId>{
    assert!(keep>=1 && value.len()>keep+1 && acc.len()>=value.len());
    let kept=circ.alloc_qubits(keep);
    let prev=|i:usize|if i==1{None}else{Some(kept[i-2])};
    for i in 1..=keep{carry_step(circ,value[i],acc[i],prev(i),kept[i-1]);}
    ripple_add_proved(circ,&value[keep+1..],&acc[keep+1..],Some(kept[keep-1]),None,Carry0::Full,Carry1::Full,None,None,None,None);
    for i in (1..=keep).rev(){
        if let Some(p)=prev(i){circ.cx(p,value[i]);}
        circ.cx(value[i],acc[i]);
    }
    kept
}

/// GO-B3: `acc -= value` for [`add_low_keep`], in the complement frame. The
/// complemented add has the same carries, so the kept wires replace the low
/// Toffoli and are then erased by the ordinary measured unwind.
pub(crate) fn sub_low_kept(circ:&mut Builder,value:&[QubitId],acc:&[QubitId],kept:Vec<QubitId>){
    let keep=kept.len();
    assert!(keep>=1 && value.len()>keep+1 && acc.len()>=value.len());
    circ.x_all(acc);
    let prev=|i:usize|if i==1{None}else{Some(kept[i-2])};
    for i in 1..=keep{if let Some(p)=prev(i){circ.cx(p,value[i]);circ.cx(p,acc[i]);}}
    ripple_add_proved(circ,&value[keep+1..],&acc[keep+1..],Some(kept[keep-1]),None,Carry0::Full,Carry1::Full,None,None,None,None);
    for i in (1..=keep).rev(){unwind_carry_step(circ,value[i],acc[i],prev(i),kept[i-1]);}
    circ.x_all(acc);
}

/// GO_KEEP_SUM: `acc += value` for a wrapped add with `acc` wider than `value`
/// (the in-place Karatsuba sum `t = a + b`), leaving the ripple carries
/// c_1..c_{n-2} LIVE instead of erasing them. Same Toffoli count as `add_wide`;
/// the returned wires let [`sub_wide_kept`] undo the add with zero Toffoli,
/// provided `value` and `acc` hold the same values when it runs.
pub(crate) fn add_wide_keep(circ: &mut Builder, value: &[QubitId], acc: &[QubitId]) -> Vec<QubitId> {
    let n = acc.len();
    let k = value.len();
    assert!(k >= 1 && k + 1 <= n && n >= 3, "add_wide_keep: acc must be wider than value");
    assert!(!has_top_copy(acc));
    let carries = circ.alloc_qubits(n - 2);
    let prev = |i: usize| if i == 0 { None } else { Some(carries[i - 1]) };
    let go_c0 = GO_C0.with(|g| g.take());
    for i in 0..n - 2 {
        if i < k {
            if let (0, Some(src)) = (i, go_c0) {circ.cx(src, carries[0]);}
            else {carry_step(circ, value[i], acc[i], prev(i), carries[i]);}
        } else {
            circ.ccx(prev(i).unwrap(), acc[i], carries[i]);
        }
    }
    terminal_step(circ, value, acc, prev(n - 2));
    for i in (0..n - 2).rev() {
        if i < k {
            if let Some(p) = prev(i) {
                circ.cx(p, value[i]);
            }
            circ.cx(value[i], acc[i]);
        } else {
            circ.cx(prev(i).unwrap(), acc[i]);
        }
    }
    carries
}

/// GO_KEEP_SUM: undo [`add_wide_keep`] (`acc -= value`, the top bit returning to
/// |0>) from its live carries. Every sum bit is restored with CX, and each carry
/// (the top bit included) is erased in the X basis with the same CZ phase repair
/// `unwind_carry_step` / `unwind_zero_step` use. Zero Toffoli.
pub(crate) fn sub_wide_kept(circ: &mut Builder, value: &[QubitId], acc: &[QubitId], carries: Vec<QubitId>) {
    let n = acc.len();
    let k = value.len();
    assert!(k >= 1 && k + 1 <= n && carries.len() == n - 2);
    let prev = |i: usize| if i == 0 { None } else { Some(carries[i - 1]) };
    for i in 0..n - 1 {
        if i < k {
            circ.cx(value[i], acc[i]);
        }
        if let Some(p) = prev(i) {
            circ.cx(p, acc[i]);
        }
    }
    for i in (0..n - 1).rev() {
        let out = if i == n - 2 { acc[n - 1] } else { carries[i] };
        let m = circ.alloc_bit();
        if i < k {
            if let Some(p) = prev(i) {
                circ.cx(p, value[i]);
                circ.cx(p, acc[i]);
                circ.cx(p, out);
            }
            circ.hmr(out, m);
            circ.cz_if(value[i], acc[i], m);
            if let Some(p) = prev(i) {
                circ.cx(p, value[i]);
                circ.cx(p, acc[i]);
            }
        } else {
            circ.hmr(out, m);
            circ.cz_if(prev(i).unwrap(), acc[i], m);
        }
        circ.free_bit(m);
        if i < n - 2 {
            circ.free(out);
        }
    }
}


// Local source-loan callback: retain boundary carry-ins until their exact
// reverse-order repairs. Do not alter any other caller's finite window.
thread_local!{static SHARED_SPLIT_EXACT:std::cell::Cell<bool>=const{std::cell::Cell::new(false)};}
pub(crate) fn shared_exact_split_scope(c:&mut Builder,f:impl FnOnce(&mut Builder)){
    let old=SHARED_SPLIT_EXACT.with(|x|x.replace(true));
    f(c);
    SHARED_SPLIT_EXACT.with(|x|x.set(old));
}
