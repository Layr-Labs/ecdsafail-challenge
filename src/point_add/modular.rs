use alloy_primitives::U256;

use super::compare::erase_with_compare;
use super::const_arith::cadd_const_trunc;
use super::{fold_guard, pinned_env, Builder, SECP256K1_P};
use crate::circuit::QubitId;

// Width of the measured-erasure comparisons in this file, and nowhere else in
// the tree. One bit finer than `fold_guard` by the balance rule derived in
// `mod.rs`: a compare's Toffoli sit under a `push_condition` and execute half
// the time, so the same `d(lambda)/d(Toffoli)` buys it half the error. Change
// one of the two and you have to re-derive the other.
// (Plain `//`: a `///` here would document nothing -- the doc comment does not
// reach the `fn` the macro expands to.)
pinned_env!(erase_compare, "ERASE_COMPARE");

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
    let width = addend.len();
    assert_eq!(width, acc.len(), "ripple_add: width mismatch");
    if width == 0 {
        return;
    }
    // One owned carry per position that needs one: below the top when the top's
    // carry is the caller's `carry_out`, below the position under it when there
    // is no carry-out and that position's carry is fused into the top sum bit.
    let vented = carry_out.is_some();
    let owned = if vented {
        width - 1
    } else {
        width.saturating_sub(2)
    };
    let mut carries = circ.alloc_qubits(owned);
    carries.extend(carry_out);
    let previous = |i: usize| {
        if i == 0 {
            carry_in
        } else {
            Some(carries[i - 1])
        }
    };

    for i in 0..carries.len() {
        carry_step(circ, addend[i], acc[i], previous(i), carries[i]);
    }

    if vented || width == 1 {
        // The top sum bit. With a carry-out the loop above already folded the
        // incoming carry into both operands and only `addend` needs restoring;
        // without one the position is untouched and the carry has yet to be
        // applied. A width-1 wrapped add is all top and no ladder.
        let top = width - 1;
        if let Some(previous) = previous(top) {
            let into = if vented { addend[top] } else { acc[top] };
            circ.cx(previous, into);
        }
        circ.cx(addend[top], acc[top]);
    } else {
        terminal_step(circ, addend, acc, previous(width - 2));
    }

    for i in (0..owned).rev() {
        unwind_carry_step(circ, addend[i], acc[i], previous(i), carries[i]);
    }
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
    let n = addend.len();
    let i = n - 2;
    if let Some(previous) = previous {
        circ.cx(previous, addend[i]);
        circ.cx(previous, acc[i]);
    }
    circ.ccx(addend[i], acc[i], acc[n - 1]);
    if let Some(previous) = previous {
        circ.cx(previous, acc[n - 1]);
    }
    circ.cx(addend[n - 1], acc[n - 1]);
    if let Some(previous) = previous {
        circ.cx(previous, addend[i]);
    }
    circ.cx(addend[i], acc[i]);
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
pub fn addsub_full(circ: &mut Builder, addend: &[QubitId], acc: &[QubitId], inverse: bool) {
    if inverse {
        circ.x_all(acc);
    }
    ripple_add(circ, addend, acc, None, None);
    if inverse {
        circ.x_all(acc);
    }
}

/// Same, for a `value` narrower than `acc`: zero-extend it with throwaway pads
/// for the duration of the ripple.
pub fn addsub_wide(circ: &mut Builder, value: &[QubitId], acc: &[QubitId], inverse: bool) {
    let pads = circ.alloc_qubits(acc.len() - value.len());
    let mut wide = value.to_vec();
    wide.extend_from_slice(&pads);
    addsub_full(circ, &wide, acc, inverse);
    circ.free_vec(&pads);
}

pub fn add_wide(circ: &mut Builder, value: &[QubitId], acc: &[QubitId]) {
    addsub_wide(circ, value, acc, false);
}

pub fn sub_wide(circ: &mut Builder, value: &[QubitId], acc: &[QubitId]) {
    addsub_wide(circ, value, acc, true);
}

/// `acc += value (mod p)`, or `acc -= value` when `negate`.
///
/// The carry out of the top bit is caught on a scratch wire, folded back in as
/// `+f` over [`f_slice`] bits (since `2^256 = f (mod p)`), and then erased by
/// measurement with an [`erase_compare`]-wide comparison. Those two widths are
/// the whole approximation. Both are the tree-wide knobs rather than arguments:
/// the balance rule wants one value per shape, not one per caller.
pub fn mod_addsub(circ: &mut Builder, negate: bool, value: &[QubitId], acc: &[QubitId]) {
    assert_eq!(value.len(), acc.len(), "mod_addsub: width mismatch");
    if negate {
        circ.x_all(acc);
    }
    let overflow = circ.alloc_qubit();
    ripple_add(circ, value, acc, None, Some(overflow));
    add_f_window(circ, overflow, acc, f_slice(), false);
    let cmp_bits = erase_compare();
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
    circ.x_all(&y[..f_slice()]);
    add_f_window(circ, anc, y, f_slice(), false);
    circ.x_all(&y[..f_slice()]);
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
    let anc = circ.alloc_qubit();
    circ.x_all(y);
    ripple_add(circ, t1, y, None, Some(anc));
    circ.x(anc);
    fold_f_complemented(circ, anc, y);
    circ.x(anc);
    let k = erase_compare();
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
