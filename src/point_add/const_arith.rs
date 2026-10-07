use super::Builder;
use crate::circuit::QubitId;
use alloy_primitives::U256;

/// One position's addend bit: a hard zero, a hard one, or the wire `q`. The
/// constant forms only ever produce `Zero`/`One`, the controlled forms only
/// ever `Zero`/`Wire` -- one ladder serves all of them.
#[derive(Clone, Copy)]
enum Addend {
    Zero,
    One,
    Wire(QubitId),
}

impl Addend {
    /// A constant addend bit.
    fn constant(set: bool) -> Self {
        if set {
            Self::One
        } else {
            Self::Zero
        }
    }

    /// A wired addend bit; no wire means the position adds nothing.
    fn wired(q: Option<QubitId>) -> Self {
        q.map_or(Self::Zero, Self::Wire)
    }

    /// The wire this addend bit contributes as a gate operand. A hard one has
    /// no wire of its own, so it collapses onto the gate's other operand:
    /// `Builder::cz_if` turns the degenerate two-qubit CZ into the plain `Z` the
    /// constant form wants, and `emit_fold_maj1` wants the carry wire there for
    /// the same reason.
    fn operand(self, other: QubitId) -> QubitId {
        match self {
            Self::One => other,
            Self::Wire(q) => q,
            Self::Zero => unreachable!("a zero addend bit is never an operand"),
        }
    }
}

fn maj1_inputs_distinct(a: QubitId, k: QubitId, carry: QubitId, target: QubitId) -> bool {
    a != k && a != carry && a != target && k != carry && k != target && carry != target
}

/// `target ^= MAJ(a, k, carry)`: fold the carry in, one Toffoli, fold it back
/// out. For a hard-one `k` the Toffoli's second control is `carry ^ 1`, so the
/// carry wire itself stands in for the absent addend wire and the fold that
/// would flip that wire becomes a plain `X`.
fn emit_fold_maj1(circ: &mut Builder, a: QubitId, k: Addend, carry: QubitId, target: QubitId) {
    let kq = k.operand(carry);
    if let Addend::Wire(q) = k {
        assert!(maj1_inputs_distinct(a, q, carry, target));
    }
    let flip = |circ: &mut Builder| {
        if kq == carry {
            circ.x(carry);
        } else {
            circ.cx(carry, kq);
        }
    };
    circ.cx(carry, target);
    circ.cx(carry, a);
    flip(circ);
    circ.ccx(a, kq, target);
    flip(circ);
    circ.cx(carry, a);
}

/// `acc += c (mod 2^acc.len())`.
pub fn add_const(circ: &mut Builder, acc: &[QubitId], c: U256) {
    let n = acc.len();
    assert!(n >= 2, "the ladder needs at least two positions");
    let last = n - 2;
    let dead = dead_low_carry_run(|i| c.bit(i), last, false);
    carry_ladder(circ, acc, |i| Addend::constant(c.bit(i)), dead, last, None);
}

/// `acc -= c (mod 2^n)`.
///
/// Subtracting `c` is adding its two's complement, so this is `add_const` with
/// a different constant rather than a second ladder. The cost is unaffected:
/// `add_const` emits `n - 2 - ctz(c)` Toffoli -- every live position costs one,
/// a set bit as a `maj1` fold and a clear bit as a plain `ccx` -- and negation
/// preserves `ctz`, so the choice of constant moves only Clifford gates.
///
/// Bits at or above `n` are never read, so the 256-bit negation already carries
/// the right low `n` bits and needs no mask.
pub fn sub_const(circ: &mut Builder, acc: &[QubitId], c: U256) {
    add_const(circ, acc, U256::ZERO.wrapping_sub(c));
}

/// Returns the number of low carry or borrow positions that are exactly zero.
///
/// The first position is zero when the constant bit is clear or when the
/// caller has proved the first carry or borrow is zero. Each following clear
/// constant bit extends that dead run.
///
/// A set low constant bit with no such proof leaves the run empty: position 0
/// then carries `acc[0] & ctrl` and needs a wire of its own.
fn dead_low_carry_run(
    addend_bit: impl Fn(usize) -> bool,
    last: usize,
    first_carry_is_zero: bool,
) -> usize {
    if addend_bit(0) && !first_carry_is_zero {
        return 0;
    }
    let mut dead = 1usize;
    while dead <= last && !addend_bit(dead) {
        dead += 1;
    }
    dead
}

/// The one carry ladder. `controls[i]` is the addend's bit `i`: `Some(q)` means
/// the bit is the wire `q`, `None` means it is a constant zero. Carries run
/// over `dead..=last`; the positions below `dead` are the ones proved to carry
/// nothing.
///
/// Every carry is computed from the *original* `acc`, applied in a second pass,
/// then measured out and phase-repaired in a third -- which is why the ladder
/// costs one Toffoli per live position and none at all to unwind.
///
/// `host`, when given, is a caller-owned wire lent to the ladder to carry the
/// *top* position instead of one allocated here. It is HMR-cleared back to |0>
/// with the rest but stays the caller's, so the ladder ends one wire lighter --
/// which is the whole of what `csub_const_trunc_ctrl_low0` buys.
fn carry_ladder(
    circ: &mut Builder,
    acc: &[QubitId],
    kctrl: impl Fn(usize) -> Addend,
    dead: usize,
    last: usize,
    host: Option<QubitId>,
) {
    let n = acc.len();
    assert!(dead <= last && last < n);
    assert!(host.is_none_or(|h| !acc[dead..].contains(&h)));
    let owned = circ.alloc_qubits(last + 1 - dead - usize::from(host.is_some()));
    let mut carries = owned.clone();
    carries.extend(host);
    // The carry into position `i` is the carry out of `i - 1`, which is a live
    // wire only once that position is past the dead run.
    let carry_into = |i: usize| -> Option<QubitId> { (i > dead).then(|| carries[i - 1 - dead]) };

    for i in dead..=last {
        let target = carries[i - dead];
        match (kctrl(i), carry_into(i)) {
            (Addend::Zero, None) => {}
            (Addend::One, None) => circ.cx(acc[i], target),
            (Addend::Wire(kq), None) => circ.ccx(acc[i], kq, target),
            (Addend::Zero, Some(ci)) => circ.ccx(acc[i], ci, target),
            (k, Some(ci)) => emit_fold_maj1(circ, acc[i], k, ci, target),
        }
    }

    for (i, &acc_i) in acc.iter().enumerate() {
        match kctrl(i) {
            Addend::Zero => {}
            Addend::One => circ.x(acc_i),
            Addend::Wire(kq) => circ.cx(kq, acc_i),
        }
        if i > 0 && i - 1 <= last {
            if let Some(ci) = carry_into(i) {
                circ.cx(ci, acc_i);
            }
        }
    }

    for i in (dead..=last).rev() {
        let m = circ.alloc_bit();
        circ.hmr(carries[i - dead], m);
        match (kctrl(i), carry_into(i)) {
            (Addend::Zero, None) => {}
            (Addend::Zero, Some(ci)) => {
                circ.x(acc[i]);
                circ.cz_if(acc[i], ci, m);
                circ.x(acc[i]);
            }
            (k, None) => {
                circ.x(acc[i]);
                circ.cz_if(acc[i], k.operand(acc[i]), m);
                circ.x(acc[i]);
            }
            (k, Some(ci)) => {
                circ.x(acc[i]);
                circ.cz_if(acc[i], k.operand(acc[i]), m);
                circ.cz_if(acc[i], ci, m);
                circ.x(acc[i]);
                circ.cz_if(k.operand(ci), ci, m);
            }
        }
        circ.free_bit(m);
    }

    circ.free_vec(&owned);
}

/// `acc += c` when `ctrl`, over the whole of `acc` and mod `2^acc.len()`, with
/// provably dead low carry positions removed.
///
/// The only carry dropped is the one off the top of `acc`, so a caller wanting
/// a narrower truncation passes a narrower slice -- the slice *is* the window.
pub fn cadd_const_trunc(
    circ: &mut Builder,
    acc: &[QubitId],
    c: U256,
    ctrl: QubitId,
    first_carry_is_zero: bool,
) {
    let n = acc.len();
    assert!(n >= 2, "the ladder needs at least two positions");
    let last = n - 2;
    let dead = dead_low_carry_run(|i| c.bit(i), last, first_carry_is_zero);
    carry_ladder(
        circ,
        acc,
        |i| Addend::wired(c.bit(i).then_some(ctrl)),
        dead,
        last,
        None,
    );
}

/// `acc -= c` when `ctrl`, over the whole of `acc`. Slice `acc` to truncate it
/// further.
///
/// Subtracting is adding the two's complement, exactly as `sub_const` is
/// `add_const` negated. That this costs nothing is the non-obvious part, and it
/// is why a dedicated borrow ladder would buy nothing: `cadd_const_trunc`'s
/// saving is the dead low carry run, which is the constant's trailing-zero
/// count -- and negation preserves it, since `-c = 2^k * -(c >> k)` for
/// `k = ctz(c)`. The dead run, the carry register and the Toffoli count
/// therefore all come out the same either way.
///
/// Bits at or above `acc.len()` are never read, so the 256-bit negation already
/// carries the right low bits and needs no mask.
pub fn csub_const_trunc(circ: &mut Builder, acc: &[QubitId], c: U256, ctrl: QubitId) {
    cadd_const_trunc(circ, acc, U256::ZERO.wrapping_sub(c), ctrl, false);
}

/// Variant for a controlled odd subtraction whose low accumulator bit equals
/// `ctrl` at entry, which is worth one qubit.
///
/// Bit 0's sum is `acc[0] ^ ctrl`, and the precondition makes that 0. Applying it
/// up front both finishes that position and leaves `acc[0]` clean, so it can host
/// the ladder's top carry instead of a wire of its own.
///
/// What is left is an ordinary subtraction. The borrow out of bit 0 is
/// `~acc[0] & ctrl`, which the precondition also makes 0, so bits 1.. are a
/// self-contained `acc[1..] -= (c >> 1) * ctrl` with no borrow-in -- and that is
/// `cadd_const_trunc` with the constant negated, exactly as `csub_const_trunc`
/// is. The negation identity looks like it cannot reach a variant with a
/// carry-in, and it does -- but only once bit 0 is split off first, which is
/// what leaves no borrow-in to carry. Negation preserves `ctz`, so the dead run,
/// the carry register and the Toffoli count are a dedicated borrow ladder's.
pub fn csub_const_trunc_ctrl_low0(circ: &mut Builder, acc: &[QubitId], c: U256, ctrl: QubitId) {
    let n = acc.len();
    assert!(
        n > 2 && c.bit(0),
        "an odd constant over at least three bits"
    );
    assert!(acc[0] != ctrl, "the host must not be the control itself");
    circ.cx(ctrl, acc[0]);

    let high = &acc[1..];
    let k = U256::ZERO.wrapping_sub(c >> 1);
    let last = high.len() - 2;
    let dead = dead_low_carry_run(|i| k.bit(i), last, false);
    carry_ladder(
        circ,
        high,
        |i| Addend::wired(k.bit(i).then_some(ctrl)),
        dead,
        last,
        Some(acc[0]),
    );
}

/// The same ladder, but each position's addend bit is its own wire instead of a
/// constant bit. The dead low run is derived the same way -- a leading `None`
/// control is a zero addend bit, which carries nothing.
///
/// As with `cadd_const_trunc`, the slice *is* the window: only the carry off the
/// top of `acc` is dropped.
pub fn cadd_const_per_position_trunc(
    circ: &mut Builder,
    acc: &[QubitId],
    controls: &[Option<QubitId>],
) {
    let n = acc.len();
    assert!(n >= 2, "the ladder needs at least two positions");
    assert!(controls.len() <= n);
    let last = n - 2;
    let dead = dead_low_carry_run(
        |i| controls.get(i).is_some_and(Option::is_some),
        last,
        false,
    );
    carry_ladder(
        circ,
        acc,
        |i| Addend::wired(controls.get(i).copied().flatten()),
        dead,
        last,
        None,
    );
}
