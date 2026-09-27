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

pub(crate) fn multi_controlled_x_dirty(
    circ: &mut Builder,
    controls: &[QubitId],
    target: QubitId,
    dirty: &[QubitId],
) {
    match controls.len() {
        0 => circ.x(target),
        1 => circ.cx(controls[0], target),
        2 => circ.ccx(controls[0], controls[1], target),
        count => {
            assert!(dirty.len() >= count - 2);
            // Echo the dirty ladder with/without c0*c1. Every unknown dirty
            // contribution cancels; only the complete control product remains.
            for _ in 0..2 {
                circ.ccx(controls[0], controls[1], dirty[0]);
                for i in 1..count - 2 {
                    circ.ccx(controls[i + 1], dirty[i - 1], dirty[i]);
                }
                circ.ccx(controls[count - 1], dirty[count - 3], target);
                for i in (1..count - 2).rev() {
                    circ.ccx(controls[i + 1], dirty[i - 1], dirty[i]);
                }
            }
        }
    }
}

fn non_adjacent_digits(constant: U256, width: usize) -> Vec<(usize, bool)> {
    let mut digits = Vec::new();
    let mut carry = false;
    for bit in 0..width {
        match (constant.bit(bit), carry) {
            (false, false) | (true, true) => {}
            _ => {
                let negative = bit + 1 < width && constant.bit(bit + 1);
                digits.push((bit, negative));
                carry = negative;
            }
        }
    }
    digits
}

/// Exact controlled constant arithmetic, restoring a disjoint dirty register.
/// A full borrowed word enables linear-cost increments. Use a clean carry when
/// available to save Cliffords, or an ancilla-free adder when the budget is full.
/// A shorter pool uses the multi-control echo ladder instead.
pub(crate) fn controlled_const_dirty(
    circ: &mut Builder,
    acc: &[QubitId],
    constant: U256,
    control: QubitId,
    dirty: &[QubitId],
    inverse: bool,
) {
    assert!(!acc.is_empty() && acc.len() <= 256);
    assert!(!acc.contains(&control));
    assert!(dirty.len() >= acc.len().saturating_sub(2));
    assert!(dirty.iter().all(|q| *q != control && !acc.contains(q)));
    let digits = non_adjacent_digits(constant, acc.len());
    if digits.is_empty() {
        return;
    }
    let full_word = dirty.len() > acc.len();
    let carry = (full_word && (circ.active_qubits() as usize) < super::pingpong::walk_max_qubits())
        .then(|| circ.alloc_qubit());
    for (shift, negative) in digits {
        let inverse = inverse ^ negative;
        let word = &acc[shift..];
        if full_word {
            // x-d-(~d)=x+1. Put the control below x so an unconditional
            // increment propagates into x exactly when that control is one.
            let mut extended = Vec::with_capacity(word.len() + 1);
            extended.push(control);
            extended.extend_from_slice(word);
            let source = &dirty[..extended.len()];
            if inverse {
                circ.x(control);
            } else {
                circ.x_all(&extended);
            }
            let add = |circ: &mut Builder| {
                if let Some(carry) = carry {
                    super::width_composition::add_wrapped_with_carry(
                        circ, source, &extended, carry, None,
                    );
                } else {
                    super::width_composition::add_wrapped(circ, source, &extended);
                }
            };
            add(circ);
            circ.x_all(source);
            add(circ);
            circ.x_all(source);
            if !inverse {
                circ.x_all(&extended);
                circ.x(control);
            }
            continue;
        }
        let mut controls = Vec::with_capacity(word.len());
        controls.push(control);
        for step in 0..word.len() {
            let bit = if inverse { step } else { word.len() - 1 - step };
            controls.truncate(1);
            controls.extend_from_slice(&word[..bit]);
            multi_controlled_x_dirty(circ, &controls, word[bit], dirty);
        }
    }
    if let Some(carry) = carry {
        circ.release_clean(carry);
    }
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

/// Scratch width of the controlled-constant ladder, including dead low carries.
pub(crate) fn cadd_const_workspace(
    width: usize,
    constant: U256,
    first_carry_is_zero: bool,
) -> usize {
    assert!(width >= 2);
    let last = width - 2;
    width - 1 - dead_low_carry_run(|bit| constant.bit(bit), last, first_carry_is_zero)
}

/// Apply the same finite-width constant addition with a budgeted carry ladder.
/// Bits above the window are borrowed only as dirty workspace and restored.
pub(crate) fn cadd_const_fitted(
    circ: &mut Builder,
    reg: &[QubitId],
    constant: U256,
    control: QubitId,
    width: usize,
    first_carry_is_zero: bool,
) {
    assert!((2..=reg.len()).contains(&width));
    let work = cadd_const_workspace(width, constant, first_carry_is_zero);
    let acc = &reg[..width];
    if work == 0 {
        for (bit, &q) in acc.iter().enumerate() {
            if constant.bit(bit) {
                circ.cx(control, q);
            }
        }
        return;
    }
    let room = super::pingpong::walk_max_qubits().saturating_sub(circ.active_qubits() as usize);
    if work <= room {
        cadd_const_trunc(circ, acc, constant, control, first_carry_is_zero);
    } else if let Some(plan) = super::width_composition::direct_plan(width, room) {
        let map = (0..width)
            .map(|bit| {
                if constant.bit(bit) {
                    vec![control]
                } else {
                    Vec::new()
                }
            })
            .collect::<Vec<_>>();
        super::width_composition::direct_add_zero(circ, &map, acc, &plan);
    } else {
        controlled_const_dirty(circ, acc, constant, control, &reg[width..], false);
    }
}

/// `acc += c` when `ctrl`, modulo the width of `acc`, omitting provably dead
/// low carries. Only the carry past the slice's top is dropped.
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

#[cfg(test)]
mod dirty_tests {
    use super::*;
    use crate::circuit::analyze_ops;
    use crate::sim::Simulator;
    use sha3::{digest::ExtendableOutput, Shake256};

    #[test]
    fn fitted_constant_add_preserves_high_workspace_at_every_budget() {
        for width in 3usize..=5 {
            let mask = (1usize << width) - 1;
            for constant in [0, 1, 3, mask] {
                for room in [0, 2, width] {
                    let mut circ = Builder::new();
                    let reg = circ.alloc_qubits(2 * width + 1);
                    let control = circ.alloc_qubit();
                    let input_width = circ.active_qubits();
                    circ.alloc_qubits(
                        super::super::pingpong::walk_max_qubits() - input_width as usize - room,
                    );
                    let base = circ.active_qubits();
                    cadd_const_fitted(&mut circ, &reg, U256::from(constant), control, width, false);
                    assert_eq!(circ.active_qubits(), base);
                    let ops = circ.take_ops();
                    let (nq, nb, _, _) = analyze_ops(ops.iter());
                    assert!(nq <= super::super::pingpong::walk_max_qubits() as u64);
                    let assignments = 1usize << input_width;
                    for start in (0..assignments).step_by(64) {
                        let mut rng = Shake256::default().finalize_xof();
                        let mut sim = Simulator::new(
                            (nq as usize).max(input_width as usize),
                            nb as usize,
                            &mut rng,
                        );
                        let mut sums = vec![0; width];
                        for lane in 0..64.min(assignments - start) {
                            let value = start + lane;
                            for bit in 0..input_width as usize {
                                sim.qubits[bit] |= (((value >> bit) & 1) as u64) << lane;
                            }
                            let sum =
                                ((value & mask) + constant * ((value >> control.0) & 1)) & mask;
                            for bit in 0..width {
                                sums[bit] |= (((sum >> bit) & 1) as u64) << lane;
                            }
                        }
                        let mut expected = sim.qubits.clone();
                        expected[..width].copy_from_slice(&sums);
                        sim.apply_iter(ops.iter());
                        assert_eq!(
                            sim.qubits, expected,
                            "width={width}, constant={constant}, room={room}"
                        );
                        assert_eq!(sim.phase, 0);
                    }
                }
            }
        }
    }

    #[test]
    fn signed_digits_reconstruct_constants_without_adjacent_terms() {
        for width in 1..=12 {
            let mask = (1usize << width) - 1;
            for value in 0..=mask {
                let digits = non_adjacent_digits(U256::from(value), width);
                let reconstructed = digits.iter().fold(0isize, |sum, &(bit, negative)| {
                    sum + if negative {
                        -(1isize << bit)
                    } else {
                        1isize << bit
                    }
                });
                assert_eq!(reconstructed as usize & mask, value);
                assert!(digits.windows(2).all(|pair| pair[0].0 + 1 < pair[1].0));
            }
        }
        assert_eq!(non_adjacent_digits(U256::MAX, 256), [(0, true)]);
        assert_eq!(
            non_adjacent_digits(super::super::modular::f(), 256),
            [(0, false), (4, false), (6, true), (10, false), (32, false)]
        );
    }

    #[test]
    fn signed_field_offset_reduces_the_exact_toffoli_cost() {
        let mut circ = Builder::new();
        let acc = circ.alloc_qubits(64);
        let control = circ.alloc_qubit();
        let dirty = circ.alloc_qubits(65);
        controlled_const_dirty(
            &mut circ,
            &acc,
            super::super::modular::f(),
            control,
            &dirty,
            false,
        );
        let ops = circ.take_ops();
        let toffoli = ops
            .iter()
            .filter(|op| op.kind == crate::circuit::OperationType::CCX)
            .count();
        assert_eq!(toffoli, 1072);
        assert!(toffoli < 1528, "binary expansion needs seven increments");
    }

    #[test]
    fn constant_workspace_matches_the_emitted_carry_ladder() {
        for width in [33, 40, 57, 73, 96] {
            for constant in [
                super::super::modular::f(),
                super::super::modular::f() - U256::from(1),
                (super::super::modular::f() - U256::from(1)) >> 1usize,
            ] {
                for first_zero in [false, true] {
                    let mut circ = Builder::new();
                    let acc = circ.alloc_qubits(width);
                    let control = circ.alloc_qubit();
                    let base = circ.active_qubits();
                    cadd_const_trunc(&mut circ, &acc, constant, control, first_zero);
                    let ops = circ.take_ops();
                    assert_eq!(
                        analyze_ops(ops.iter()).0 - base as u64,
                        cadd_const_workspace(width, constant, first_zero) as u64,
                    );
                }
            }
        }
    }

    #[test]
    fn borrowed_register_increment_has_linear_toffoli_cost() {
        for width in [16, 64, 128] {
            let mut circ = Builder::new();
            let acc = circ.alloc_qubits(width);
            let control = circ.alloc_qubit();
            let dirty = circ.alloc_qubits(width + 1);
            let base = circ.active_qubits();
            controlled_const_dirty(&mut circ, &acc, U256::from(1), control, &dirty, false);
            assert_eq!(circ.active_qubits(), base);
            let ops = circ.take_ops();
            let toffoli = ops
                .iter()
                .filter(|op| op.kind == crate::circuit::OperationType::CCX)
                .count();
            assert_eq!(toffoli, 4 * width);
            assert_eq!(analyze_ops(ops.iter()).0, base as u64 + 1);
        }
    }

    #[test]
    fn dirty_echo_restores_every_workspace_bit() {
        for count in 0usize..=10 {
            let mut circ = Builder::new();
            let controls = circ.alloc_qubits(count);
            let target = circ.alloc_qubit();
            let dirty = circ.alloc_qubits(count.saturating_sub(2));
            let base = circ.active_qubits();
            multi_controlled_x_dirty(&mut circ, &controls, target, &dirty);
            assert_eq!(circ.active_qubits(), base);
            let ops = circ.take_ops();
            let (nq, nb, _, _) = analyze_ops(ops.iter());
            assert!(nq <= base as u64);
            let assignments = 1usize << base;
            for start in (0..assignments).step_by(64) {
                let mut rng = Shake256::default().finalize_xof();
                let mut sim = Simulator::new(base as usize, nb as usize, &mut rng);
                let mut toggle = 0;
                for lane in 0..64.min(assignments - start) {
                    let value = start + lane;
                    for bit in 0..base as usize {
                        sim.qubits[bit] |= (((value >> bit) & 1) as u64) << lane;
                    }
                    let mask = (1usize << count) - 1;
                    toggle |= u64::from(value & mask == mask) << lane;
                }
                let mut expected = sim.qubits.clone();
                expected[target.0 as usize] ^= toggle;
                sim.apply_iter(ops.iter());
                let mask = if assignments - start >= 64 {
                    u64::MAX
                } else {
                    (1u64 << (assignments - start)) - 1
                };
                for word in &mut sim.qubits {
                    *word &= mask;
                }
                assert_eq!(sim.qubits, expected, "controls={count}");
                assert_eq!(sim.phase, 0);
            }
        }
    }

    #[test]
    fn dirty_constant_arithmetic_is_exact_in_both_directions() {
        for width in 1usize..=6 {
            let mask = (1usize << width) - 1;
            for constant in [0, 1, 3 & mask, mask, 977 & mask, 488 & mask] {
                for inverse in [false, true] {
                    for mode in 0..3 {
                        let linear = mode != 0;
                        let mut circ = Builder::new();
                        let acc = circ.alloc_qubits(width);
                        let control = circ.alloc_qubit();
                        let dirty = circ.alloc_qubits(if linear {
                            width + 1
                        } else {
                            width.saturating_sub(2)
                        });
                        let base = circ.active_qubits();
                        if mode == 2 {
                            circ.alloc_qubits(
                                super::super::pingpong::walk_max_qubits() - base as usize,
                            );
                        }
                        let active = circ.active_qubits();
                        controlled_const_dirty(
                            &mut circ,
                            &acc,
                            U256::from(constant),
                            control,
                            &dirty,
                            inverse,
                        );
                        assert_eq!(circ.active_qubits(), active);
                        let ops = circ.take_ops();
                        let (nq, nb, _, _) = analyze_ops(ops.iter());
                        assert!(nq <= base as u64 + u64::from(mode == 1));
                        let assignments = 1usize << base;
                        for start in (0..assignments).step_by(64) {
                            let mut rng = Shake256::default().finalize_xof();
                            let mut sim = Simulator::new(
                                (nq as usize).max(base as usize),
                                nb as usize,
                                &mut rng,
                            );
                            let mut sums = vec![0; width];
                            for lane in 0..64.min(assignments - start) {
                                let value = start + lane;
                                for bit in 0..base as usize {
                                    sim.qubits[bit] |= (((value >> bit) & 1) as u64) << lane;
                                }
                                let old = value & mask;
                                let delta = constant * ((value >> width) & 1);
                                let sum = if inverse {
                                    old.wrapping_sub(delta)
                                } else {
                                    old + delta
                                } & mask;
                                for bit in 0..width {
                                    sums[bit] |= (((sum >> bit) & 1) as u64) << lane;
                                }
                            }
                            let mut expected = sim.qubits.clone();
                            expected[..width].copy_from_slice(&sums);
                            sim.apply_iter(ops.iter());
                            assert_eq!(sim.qubits, expected, "width={width}, constant={constant}, inverse={inverse}, mode={mode}");
                            assert_eq!(sim.phase, 0);
                        }
                    }
                }
            }
        }
    }
}
