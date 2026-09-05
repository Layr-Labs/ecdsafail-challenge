import hashlib
import json
from functools import lru_cache
from pathlib import Path
from typing import Literal, Optional, Sequence

from qiskit import QuantumCircuit, QuantumRegister
from qiskit.circuit import Gate, Qubit

import eea_circuit_updated as _e

C_EEA = _e.C_EEA
N_CONFIG = _e.N_CONFIG
paper_len_width = _e.paper_len_width
paper_shift_width = _e.paper_shift_width
Nmax_steps = _e.Nmax_steps
active_windows = _e.active_windows
get_n_config = getattr(_e, "get_n_config")
set_measurement_uncompute = _e.set_measurement_uncompute
count_circuit_ops_recursive = getattr(_e, "count_circuit_ops_recursive", None)

_CERTIFIED_WINDOW_SHA256 = "3e1961f5550249604bf044edb65f1d1bc403ed75bd7178e283685ddb4f3cb880"
_CERTIFIED_WINDOW_PATH = Path(__file__).with_name("active_windows_1616.json")
_certified_window_bytes = _CERTIFIED_WINDOW_PATH.read_bytes()
_certified_window_canonical = _certified_window_bytes.replace(b"\r\n", b"\n")
if hashlib.sha256(_certified_window_canonical).hexdigest() != _CERTIFIED_WINDOW_SHA256:
    raise RuntimeError("secp256k1 active-window certificate hash mismatch")
_certified_window_table = json.loads(_certified_window_bytes)
if (
    _certified_window_table.get("schema") != "luo-secp256k1-active-windows-v2"
    or len(_certified_window_table.get("rows", ())) != 1616
):
    raise RuntimeError("invalid secp256k1 active-window certificate")
_CERTIFIED_WINDOW_ROWS = tuple(row["safe"] for row in _certified_window_table["rows"])

LT_WIDTH = 8
LQ_WIDTH = 9
LS_WIDTH = 9
LRP_WIDTH = 8
LS_MODULUS = 259
LS_ZERO = LS_MODULUS - 1
LRP_ZERO = (1 << LRP_WIDTH) - 1
CLEAN_AUX_SIZE = 1
TIGHT_ANC_SIZE = 9
DIRTY_PASSENGER_SIZE = 10


def __getattr__(name: str):
    return getattr(_e, name)


def _tight_unary_depth_for_labels(labels: Sequence[int]) -> int:
    labels = sorted(set(labels))
    if len(labels) <= 1:
        return 0
    bit = _e._split_bit(labels)
    z = [x for x in labels if ((x >> bit) & 1) == 0]
    o = [x for x in labels if ((x >> bit) & 1) == 1]
    return 1 + max(_tight_unary_depth_for_labels(z), _tight_unary_depth_for_labels(o))


def unary_iteration_tight(qc: QuantumCircuit, *, index_reg: Sequence[Qubit], labels: Sequence[int],
                          ctrl: Qubit, ancillas: Sequence[Qubit], leaf_fn, order: Literal["inc", "dec"] = "inc") -> None:
    labels = sorted(set(labels))
    if not labels:
        return
    need = _tight_unary_depth_for_labels(labels)
    if len(ancillas) < need:
        raise ValueError(f"tight unary iteration needs {need} ancillas, got {len(ancillas)}")
    def rec(sub_labels, g, depth):
        if len(sub_labels) == 1:
            leaf_fn(sub_labels[0], g); return
        b = _e._split_bit(sub_labels)
        z = [x for x in sub_labels if ((x >> b) & 1) == 0]
        o = [x for x in sub_labels if ((x >> b) & 1) == 1]
        h = ancillas[depth]
        _e._and_with_index_bit(qc, g, index_reg[b], h, 0)
        if order == "inc":
            rec(z, h, depth+1)
            qc.cx(g, h)
            rec(o, h, depth+1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(o, h, depth+1)
            qc.cx(g, h)
            rec(z, h, depth+1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[b], h, 0)
    rec(labels, ctrl, 0)


def unary_range_iteration_tight_dropin(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    labels: Sequence[int],
    ctrl: Qubit,
    range_acc: Qubit,
    ancillas: Sequence[Qubit],
    borrowed: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"] = "inc",
    toggle_before_leaf: bool,
) -> None:
    """Signature-compatible tight replacement for unary_range_iteration_dirty_*raw.

    The raw iterators already hand the leaf a single qubit (range_acc); their whole cost
    is the per-label _toggle_raw_controls_dirty (an MCX over 8-10 raw index bits, ~4*n-8
    CCX) needed to maintain it. A prefix-shared decode gives a single clean line g per
    label, so that toggle collapses to one CX. Leaves are untouched.

    Costs len(ancillas) >= _tight_unary_depth_for_labels(labels) CLEAN lanes (~8), which
    the aux=1 layout does not have -- callers must supply them.
    """
    labels = sorted(set(labels))
    if not labels:
        return

    def tight_leaf(label: int, g: Qubit) -> None:
        if toggle_before_leaf:
            qc.cx(g, range_acc)
            leaf_fn(label, range_acc)
        else:
            leaf_fn(label, range_acc)
            qc.cx(g, range_acc)

    unary_iteration_tight(
        qc, index_reg=index_reg, labels=labels, ctrl=ctrl,
        ancillas=ancillas, leaf_fn=tight_leaf, order=order,
    )


def unary_range_iteration_direct_leaf(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    labels: Sequence[int],
    ctrl: Qubit,
    range_acc: Qubit,
    ancillas: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"] = "inc",
    toggle_before_leaf: bool,
    before_toggle_fn=None,
    after_toggle_fn=None,
) -> None:
    """Range scan with the final decoder bit applied directly to the accumulator.

    A conventional unary tree materializes every equality into a clean lane.
    At a two-label leaf, this variant instead toggles ``range_acc`` directly
    from the parent path and the distinguishing index bit.  It therefore uses
    one fewer clean path lane without increasing the decoder Toffoli count.
    """
    labels = sorted(set(labels))
    if not labels:
        return
    need = max(0, _tight_unary_depth_for_labels(labels) - 1)
    if len(ancillas) < need:
        raise ValueError(
            f"direct-leaf range iteration needs {need} ancillas, got {len(ancillas)}"
        )

    def visit(label: int, equality_toggle) -> None:
        if toggle_before_leaf:
            if before_toggle_fn is not None:
                before_toggle_fn(label, range_acc)
            equality_toggle()
            if after_toggle_fn is not None:
                after_toggle_fn(label, range_acc)
            leaf_fn(label, range_acc)
        else:
            leaf_fn(label, range_acc)
            if before_toggle_fn is not None:
                before_toggle_fn(label, range_acc)
            equality_toggle()
            if after_toggle_fn is not None:
                after_toggle_fn(label, range_acc)

    def rec(sub_labels, g, depth):
        if len(sub_labels) == 1:
            visit(sub_labels[0], lambda: qc.cx(g, range_acc))
            return
        bit = _e._split_bit(sub_labels)
        zero = [x for x in sub_labels if ((x >> bit) & 1) == 0]
        one = [x for x in sub_labels if ((x >> bit) & 1) == 1]
        if len(sub_labels) == 2:
            low, high = sorted(sub_labels)

            def toggle(label: int) -> None:
                if ((label >> bit) & 1) == 0:
                    qc.x(index_reg[bit])
                qc.ccx(g, index_reg[bit], range_acc)
                if ((label >> bit) & 1) == 0:
                    qc.x(index_reg[bit])

            branch_order = [low, high] if order == "inc" else [high, low]
            for label in branch_order:
                visit(label, lambda label=label: toggle(label))
            return

        h = ancillas[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    rec(labels, ctrl, 0)


def unary_range_iteration_dirty_quartet(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    labels: Sequence[int],
    ctrl: Qubit,
    range_acc: Qubit,
    ancillas: Sequence[Qubit],
    borrowed: Qubit,
    leaf_fn,
    order: Literal["inc", "dec"] = "inc",
    toggle_before_leaf: bool,
    before_toggle_fn=None,
    after_toggle_fn=None,
) -> None:
    """Range scan with the final two decoder levels applied as raw controls."""
    labels = sorted(set(labels))
    if not labels:
        return
    need = max(0, _tight_unary_depth_for_labels(labels) - 2)
    if len(ancillas) < need:
        raise ValueError(
            f"dirty-quartet range iteration needs {need} ancillas, "
            f"got {len(ancillas)}"
        )

    def visit(label: int, controls: Sequence[Qubit]) -> None:
        def toggle() -> None:
            _toggle_raw_controls_dirty(
                qc, controls, range_acc, [borrowed]
            )

        if toggle_before_leaf:
            if before_toggle_fn is not None:
                before_toggle_fn(label, range_acc)
            toggle()
            if after_toggle_fn is not None:
                after_toggle_fn(label, range_acc)
            leaf_fn(label, range_acc)
        else:
            leaf_fn(label, range_acc)
            if before_toggle_fn is not None:
                before_toggle_fn(label, range_acc)
            toggle()
            if after_toggle_fn is not None:
                after_toggle_fn(label, range_acc)

    def direct(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            visit(sub_labels[0], controls)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

        def branch(values, bit_value: int) -> None:
            if not values:
                return
            if bit_value == 0:
                qc.x(index_reg[bit])
            direct(values, list(controls) + [index_reg[bit]])
            if bit_value == 0:
                qc.x(index_reg[bit])

        if order == "inc":
            branch(zero, 0)
            branch(one, 1)
        else:
            branch(one, 1)
            branch(zero, 0)

    def rec(sub_labels, g, depth):
        if _tight_unary_depth_for_labels(sub_labels) <= 2:
            direct(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = ancillas[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    rec(labels, ctrl, 0)


def unary_range_iteration_dirty_octet(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    labels: Sequence[int],
    ctrl: Qubit,
    range_acc: Qubit,
    ancillas: Sequence[Qubit],
    borrowed: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"] = "inc",
    toggle_before_leaf: bool,
    before_toggle_fn=None,
    after_toggle_fn=None,
    equality_guards: Sequence[Qubit] = (),
) -> None:
    """Range scan with the final three decoder levels as raw controls."""
    labels = sorted(set(labels))
    if not labels:
        return
    need = max(0, _tight_unary_depth_for_labels(labels) - 3)
    if len(ancillas) < need:
        raise ValueError(
            f"dirty-octet range iteration needs {need} ancillas, "
            f"got {len(ancillas)}"
        )
    if len(borrowed) < 2:
        raise ValueError("dirty-octet range iteration needs two lenders")

    def visit(label: int, controls: Sequence[Qubit]) -> None:
        def toggle() -> None:
            _toggle_raw_controls_dirty(
                qc, list(controls) + list(equality_guards),
                range_acc, borrowed,
            )

        if toggle_before_leaf:
            if before_toggle_fn is not None:
                before_toggle_fn(label, range_acc)
            toggle()
            if after_toggle_fn is not None:
                after_toggle_fn(label, range_acc)
            leaf_fn(label, range_acc)
        else:
            leaf_fn(label, range_acc)
            if before_toggle_fn is not None:
                before_toggle_fn(label, range_acc)
            toggle()
            if after_toggle_fn is not None:
                after_toggle_fn(label, range_acc)

    def direct(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            visit(sub_labels[0], controls)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

        def branch(values, bit_value: int) -> None:
            if not values:
                return
            if bit_value == 0:
                qc.x(index_reg[bit])
            direct(values, list(controls) + [index_reg[bit]])
            if bit_value == 0:
                qc.x(index_reg[bit])

        if order == "inc":
            branch(zero, 0)
            branch(one, 1)
        else:
            branch(one, 1)
            branch(zero, 0)

    def rec(sub_labels, g, depth):
        if _tight_unary_depth_for_labels(sub_labels) <= 3:
            direct(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = ancillas[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    rec(labels, ctrl, 0)



def unary_range_iteration_dirty_hexadecet(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    labels: Sequence[int],
    ctrl: Qubit,
    range_acc: Qubit,
    ancillas: Sequence[Qubit],
    borrowed: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"] = "inc",
    toggle_before_leaf: bool,
    before_toggle_fn=None,
    after_toggle_fn=None,
) -> None:
    """Range scan with the final four decoder levels as raw controls."""
    labels = sorted(set(labels))
    if not labels:
        return
    need = max(0, _tight_unary_depth_for_labels(labels) - 4)
    if len(ancillas) < need:
        raise ValueError(
            f"dirty-hexadecet range iteration needs {need} ancillas, "
            f"got {len(ancillas)}"
        )
    if len(borrowed) < 3:
        raise ValueError("dirty-hexadecet range iteration needs three lenders")

    def visit(label: int, controls: Sequence[Qubit]) -> None:
        def toggle() -> None:
            _toggle_raw_controls_dirty(qc, controls, range_acc, borrowed)
        if toggle_before_leaf:
            if before_toggle_fn is not None:
                before_toggle_fn(label, range_acc)
            toggle()
            if after_toggle_fn is not None:
                after_toggle_fn(label, range_acc)
            leaf_fn(label, range_acc)
        else:
            leaf_fn(label, range_acc)
            if before_toggle_fn is not None:
                before_toggle_fn(label, range_acc)
            toggle()
            if after_toggle_fn is not None:
                after_toggle_fn(label, range_acc)

    def direct(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            visit(sub_labels[0], controls)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

        def branch(values, bit_value: int) -> None:
            if not values:
                return
            if bit_value == 0:
                qc.x(index_reg[bit])
            direct(values, list(controls) + [index_reg[bit]])
            if bit_value == 0:
                qc.x(index_reg[bit])

        if order == "inc":
            branch(zero, 0)
            branch(one, 1)
        else:
            branch(one, 1)
            branch(zero, 0)

    def rec(sub_labels, g, depth):
        if _tight_unary_depth_for_labels(sub_labels) <= 4:
            direct(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = ancillas[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    rec(labels, ctrl, 0)


def unary_range_iteration_dirty_32raw(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    labels: Sequence[int],
    ctrl: Qubit,
    range_acc: Qubit,
    ancillas: Sequence[Qubit],
    borrowed: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"] = "inc",
    toggle_before_leaf: bool,
    before_toggle_fn=None,
    after_toggle_fn=None,
    conditional_clean_helper: Optional[Qubit] = None,
) -> None:
    """Range scan with the final five decoder levels as raw controls."""
    labels = sorted(set(labels))
    if not labels:
        return
    need = max(0, _tight_unary_depth_for_labels(labels) - 5)
    if len(ancillas) < need:
        raise ValueError(
            f"dirty-32raw range iteration needs {need} ancillas, "
            f"got {len(ancillas)}"
        )
    if len(borrowed) < 4:
        raise ValueError("dirty-32raw range iteration needs four lenders")

    def visit(label: int, controls: Sequence[Qubit]) -> None:
        def toggle() -> None:
            if (
                conditional_clean_helper is not None
                and conditional_clean_helper not in controls
                and len(controls) >= 4
            ):
                # The materialized path control implies the original block
                # control.  Temporarily inverting that control therefore gives
                # the one-clean ladder a zero helper on every live path while
                # leaving inactive paths exactly palindromic.
                qc.x(conditional_clean_helper)
                _toggle_raw_controls_conditionally_clean(
                    qc, controls, range_acc, borrowed,
                    conditional_clean_helper,
                )
                qc.x(conditional_clean_helper)
            else:
                _toggle_raw_controls_dirty(qc, controls, range_acc, borrowed)

        if toggle_before_leaf:
            if before_toggle_fn is not None:
                before_toggle_fn(label, range_acc)
            toggle()
            if after_toggle_fn is not None:
                after_toggle_fn(label, range_acc)
            leaf_fn(label, range_acc)
        else:
            leaf_fn(label, range_acc)
            if before_toggle_fn is not None:
                before_toggle_fn(label, range_acc)
            toggle()
            if after_toggle_fn is not None:
                after_toggle_fn(label, range_acc)

    def direct(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            visit(sub_labels[0], controls)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

        def branch(values, bit_value: int) -> None:
            if not values:
                return
            if bit_value == 0:
                qc.x(index_reg[bit])
            direct(values, list(controls) + [index_reg[bit]])
            if bit_value == 0:
                qc.x(index_reg[bit])

        if order == "inc":
            branch(zero, 0)
            branch(one, 1)
        else:
            branch(one, 1)
            branch(zero, 0)

    def rec(sub_labels, g, depth):
        if _tight_unary_depth_for_labels(sub_labels) <= 5:
            direct(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = ancillas[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    rec(labels, ctrl, 0)


def unary_range_iteration_dirty_64raw(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    labels: Sequence[int],
    ctrl: Qubit,
    range_acc: Qubit,
    ancillas: Sequence[Qubit],
    borrowed: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"] = "inc",
    toggle_before_leaf: bool,
    before_toggle_fn=None,
    after_toggle_fn=None,
    conditional_clean_helper: Optional[Qubit] = None,
) -> None:
    """Range scan with the final six decoder levels as raw controls."""
    labels = sorted(set(labels))
    if not labels:
        return
    need = max(0, _tight_unary_depth_for_labels(labels) - 6)
    if len(ancillas) < need:
        raise ValueError(
            f"dirty-64raw range iteration needs {need} ancillas, "
            f"got {len(ancillas)}"
        )
    if len(borrowed) < 5:
        raise ValueError("dirty-64raw range iteration needs five lenders")

    def visit(label: int, controls: Sequence[Qubit]) -> None:
        def toggle() -> None:
            if (
                conditional_clean_helper is not None
                and conditional_clean_helper not in controls
                and len(controls) >= 4
            ):
                qc.x(conditional_clean_helper)
                _toggle_raw_controls_conditionally_clean(
                    qc, controls, range_acc, borrowed,
                    conditional_clean_helper,
                )
                qc.x(conditional_clean_helper)
            else:
                _toggle_raw_controls_dirty(qc, controls, range_acc, borrowed)
        if toggle_before_leaf:
            if before_toggle_fn is not None:
                before_toggle_fn(label, range_acc)
            toggle()
            if after_toggle_fn is not None:
                after_toggle_fn(label, range_acc)
            leaf_fn(label, range_acc)
        else:
            leaf_fn(label, range_acc)
            if before_toggle_fn is not None:
                before_toggle_fn(label, range_acc)
            toggle()
            if after_toggle_fn is not None:
                after_toggle_fn(label, range_acc)

    def direct(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            visit(sub_labels[0], controls)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

        def branch(values, bit_value: int) -> None:
            if not values:
                return
            if bit_value == 0:
                qc.x(index_reg[bit])
            direct(values, list(controls) + [index_reg[bit]])
            if bit_value == 0:
                qc.x(index_reg[bit])

        if order == "inc":
            branch(zero, 0)
            branch(one, 1)
        else:
            branch(one, 1)
            branch(zero, 0)

    def rec(sub_labels, g, depth):
        if _tight_unary_depth_for_labels(sub_labels) <= 6:
            direct(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = ancillas[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    rec(labels, ctrl, 0)


def unary_iteration_dirty_quartet_raw(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    labels: Sequence[int],
    ctrl: Qubit,
    ancillas: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"] = "inc",
) -> None:
    """Unary iteration exposing the final equality as raw controls."""
    labels = sorted(set(labels))
    if not labels:
        return
    need = max(0, _tight_unary_depth_for_labels(labels) - 2)
    if len(ancillas) < need:
        raise ValueError(
            f"raw dirty-quartet iteration needs {need} ancillas, "
            f"got {len(ancillas)}"
        )

    def direct(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            leaf_fn(sub_labels[0], controls)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

        def branch(values, bit_value: int) -> None:
            if not values:
                return
            if bit_value == 0:
                qc.x(index_reg[bit])
            direct(values, list(controls) + [index_reg[bit]])
            if bit_value == 0:
                qc.x(index_reg[bit])

        if order == "inc":
            branch(zero, 0)
            branch(one, 1)
        else:
            branch(one, 1)
            branch(zero, 0)

    def rec(sub_labels, g, depth):
        if _tight_unary_depth_for_labels(sub_labels) <= 2:
            direct(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = ancillas[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    rec(labels, ctrl, 0)


def unary_iteration_dirty_octet_raw(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    labels: Sequence[int],
    ctrl: Qubit,
    ancillas: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"] = "inc",
) -> None:
    """Unary iteration exposing the final three index bits as raw controls."""
    labels = sorted(set(labels))
    if not labels:
        return
    need = max(0, _tight_unary_depth_for_labels(labels) - 3)
    if len(ancillas) < need:
        raise ValueError(
            f"raw dirty-octet iteration needs {need} ancillas, "
            f"got {len(ancillas)}"
        )

    def direct(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            leaf_fn(sub_labels[0], controls)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

        def branch(values, bit_value: int) -> None:
            if not values:
                return
            if bit_value == 0:
                qc.x(index_reg[bit])
            direct(values, list(controls) + [index_reg[bit]])
            if bit_value == 0:
                qc.x(index_reg[bit])

        if order == "inc":
            branch(zero, 0)
            branch(one, 1)
        else:
            branch(one, 1)
            branch(zero, 0)

    def rec(sub_labels, g, depth):
        if _tight_unary_depth_for_labels(sub_labels) <= 3:
            direct(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = ancillas[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    rec(labels, ctrl, 0)


def unary_iteration_dirty_hexadecet_raw(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    labels: Sequence[int],
    ctrl: Qubit,
    ancillas: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"] = "inc",
) -> None:
    """Unary iteration exposing the final four index bits as raw controls."""
    labels = sorted(set(labels))
    if not labels:
        return
    need = max(0, _tight_unary_depth_for_labels(labels) - 4)
    if len(ancillas) < need:
        raise ValueError(
            f"raw dirty-hexadecet iteration needs {need} ancillas, "
            f"got {len(ancillas)}"
        )

    def direct(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            leaf_fn(sub_labels[0], controls)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

        def branch(values, bit_value: int) -> None:
            if not values:
                return
            if bit_value == 0:
                qc.x(index_reg[bit])
            direct(values, list(controls) + [index_reg[bit]])
            if bit_value == 0:
                qc.x(index_reg[bit])

        if order == "inc":
            branch(zero, 0)
            branch(one, 1)
        else:
            branch(one, 1)
            branch(zero, 0)

    def rec(sub_labels, g, depth):
        if _tight_unary_depth_for_labels(sub_labels) <= 4:
            direct(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = ancillas[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    rec(labels, ctrl, 0)


def unary_iteration_dirty_32raw(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    labels: Sequence[int],
    ctrl: Qubit,
    ancillas: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"] = "inc",
) -> None:
    """Unary iteration exposing the final five index bits as raw controls."""
    labels = sorted(set(labels))
    if not labels:
        return
    need = max(0, _tight_unary_depth_for_labels(labels) - 5)
    if len(ancillas) < need:
        raise ValueError(
            f"raw dirty-32 iteration needs {need} ancillas, "
            f"got {len(ancillas)}"
        )

    def direct(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            leaf_fn(sub_labels[0], controls)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

        def branch(values, bit_value: int) -> None:
            if not values:
                return
            if bit_value == 0:
                qc.x(index_reg[bit])
            direct(values, list(controls) + [index_reg[bit]])
            if bit_value == 0:
                qc.x(index_reg[bit])

        if order == "inc":
            branch(zero, 0)
            branch(one, 1)
        else:
            branch(one, 1)
            branch(zero, 0)

    def rec(sub_labels, g, depth):
        if _tight_unary_depth_for_labels(sub_labels) <= 5:
            direct(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = ancillas[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    rec(labels, ctrl, 0)


def unary_range_iteration_dirty_128raw(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    labels: Sequence[int],
    ctrl: Qubit,
    range_acc: Qubit,
    ancillas: Sequence[Qubit],
    borrowed: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"] = "inc",
    toggle_before_leaf: bool,
    before_toggle_fn=None,
    after_toggle_fn=None,
    conditional_clean_helper: Optional[Qubit] = None,
) -> None:
    """Range scan with the final seven decoder levels as raw controls."""
    labels = sorted(set(labels))
    if not labels:
        return
    need = max(0, _tight_unary_depth_for_labels(labels) - 7)
    if len(ancillas) < need:
        raise ValueError(
            f"dirty-128raw range iteration needs {need} ancillas, "
            f"got {len(ancillas)}"
        )
    if len(borrowed) < 6:
        raise ValueError("dirty-128raw range iteration needs six lenders")

    def visit(label: int, controls: Sequence[Qubit]) -> None:
        def toggle() -> None:
            if (
                conditional_clean_helper is not None
                and conditional_clean_helper not in controls
                and len(controls) >= 4
            ):
                qc.x(conditional_clean_helper)
                _toggle_raw_controls_conditionally_clean(
                    qc, controls, range_acc, borrowed,
                    conditional_clean_helper,
                )
                qc.x(conditional_clean_helper)
            else:
                _toggle_raw_controls_dirty(qc, controls, range_acc, borrowed)
        if toggle_before_leaf:
            if before_toggle_fn is not None:
                before_toggle_fn(label, range_acc)
            toggle()
            if after_toggle_fn is not None:
                after_toggle_fn(label, range_acc)
            leaf_fn(label, range_acc)
        else:
            leaf_fn(label, range_acc)
            if before_toggle_fn is not None:
                before_toggle_fn(label, range_acc)
            toggle()
            if after_toggle_fn is not None:
                after_toggle_fn(label, range_acc)

    def direct(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            visit(sub_labels[0], controls)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

        def branch(values, bit_value: int) -> None:
            if not values:
                return
            if bit_value == 0:
                qc.x(index_reg[bit])
            direct(values, list(controls) + [index_reg[bit]])
            if bit_value == 0:
                qc.x(index_reg[bit])

        if order == "inc":
            branch(zero, 0)
            branch(one, 1)
        else:
            branch(one, 1)
            branch(zero, 0)

    def rec(sub_labels, g, depth):
        if _tight_unary_depth_for_labels(sub_labels) <= 7:
            direct(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = ancillas[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    rec(labels, ctrl, 0)


def unary_range_iteration_dirty_256raw(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    labels: Sequence[int],
    ctrl: Qubit,
    range_acc: Qubit,
    ancillas: Sequence[Qubit],
    borrowed: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"] = "inc",
    toggle_before_leaf: bool,
) -> None:
    """Range scan exposing all eight endpoint bits as raw controls."""
    labels = sorted(set(labels))
    if not labels:
        return
    need = max(0, _tight_unary_depth_for_labels(labels) - 8)
    if len(ancillas) < need:
        raise ValueError(
            f"dirty-256raw range iteration needs {need} ancillas, "
            f"got {len(ancillas)}"
        )
    if len(borrowed) < 7:
        raise ValueError("dirty-256raw range iteration needs seven lenders")

    def visit(label: int, controls: Sequence[Qubit]) -> None:
        if toggle_before_leaf:
            _toggle_raw_controls_dirty(qc, controls, range_acc, borrowed)
            leaf_fn(label, range_acc)
        else:
            leaf_fn(label, range_acc)
            _toggle_raw_controls_dirty(qc, controls, range_acc, borrowed)

    def direct(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            visit(sub_labels[0], controls)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

        def branch(values, bit_value: int) -> None:
            if not values:
                return
            if bit_value == 0:
                qc.x(index_reg[bit])
            direct(values, list(controls) + [index_reg[bit]])
            if bit_value == 0:
                qc.x(index_reg[bit])

        if order == "inc":
            branch(zero, 0)
            branch(one, 1)
        else:
            branch(one, 1)
            branch(zero, 0)

    def rec(sub_labels, g, depth):
        if _tight_unary_depth_for_labels(sub_labels) <= 8:
            direct(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = ancillas[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    rec(labels, ctrl, 0)


def unary_iteration_dirty_64raw(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    labels: Sequence[int],
    ctrl: Qubit,
    ancillas: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"] = "inc",
) -> None:
    """Unary iteration exposing the final six index bits as raw controls."""
    labels = sorted(set(labels))
    if not labels:
        return
    need = max(0, _tight_unary_depth_for_labels(labels) - 6)
    if len(ancillas) < need:
        raise ValueError(
            f"raw dirty-64 iteration needs {need} ancillas, "
            f"got {len(ancillas)}"
        )

    def direct(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            leaf_fn(sub_labels[0], controls)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

        def branch(values, bit_value: int) -> None:
            if not values:
                return
            if bit_value == 0:
                qc.x(index_reg[bit])
            direct(values, list(controls) + [index_reg[bit]])
            if bit_value == 0:
                qc.x(index_reg[bit])

        if order == "inc":
            branch(zero, 0)
            branch(one, 1)
        else:
            branch(one, 1)
            branch(zero, 0)

    def rec(sub_labels, g, depth):
        if _tight_unary_depth_for_labels(sub_labels) <= 6:
            direct(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = ancillas[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    rec(labels, ctrl, 0)


def unary_iteration_dirty_128raw(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    labels: Sequence[int],
    ctrl: Qubit,
    ancillas: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"] = "inc",
) -> None:
    """Unary iteration exposing the final seven index bits as raw controls."""
    labels = sorted(set(labels))
    if not labels:
        return
    need = max(0, _tight_unary_depth_for_labels(labels) - 7)
    if len(ancillas) < need:
        raise ValueError(
            f"raw dirty-128 iteration needs {need} ancillas, "
            f"got {len(ancillas)}"
        )

    def direct(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            leaf_fn(sub_labels[0], controls)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

        def branch(values, bit_value: int) -> None:
            if not values:
                return
            if bit_value == 0:
                qc.x(index_reg[bit])
            direct(values, list(controls) + [index_reg[bit]])
            if bit_value == 0:
                qc.x(index_reg[bit])

        if order == "inc":
            branch(zero, 0)
            branch(one, 1)
        else:
            branch(one, 1)
            branch(zero, 0)

    def rec(sub_labels, g, depth):
        if _tight_unary_depth_for_labels(sub_labels) <= 7:
            direct(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = ancillas[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    rec(labels, ctrl, 0)


def unary_iteration_dirty_512raw(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    labels: Sequence[int],
    ctrl: Qubit,
    ancillas: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"] = "inc",
) -> None:
    """Unary iteration exposing all nine quotient bits as raw controls."""
    labels = sorted(set(labels))
    if not labels:
        return
    need = max(0, _tight_unary_depth_for_labels(labels) - 9)
    if len(ancillas) < need:
        raise ValueError(
            f"raw dirty-512 iteration needs {need} ancillas, "
            f"got {len(ancillas)}"
        )

    def direct(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            leaf_fn(sub_labels[0], controls)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

        def branch(values, bit_value: int) -> None:
            if not values:
                return
            if bit_value == 0:
                qc.x(index_reg[bit])
            direct(values, list(controls) + [index_reg[bit]])
            if bit_value == 0:
                qc.x(index_reg[bit])

        if order == "inc":
            branch(zero, 0)
            branch(one, 1)
        else:
            branch(one, 1)
            branch(zero, 0)

    def rec(sub_labels, g, depth):
        if _tight_unary_depth_for_labels(sub_labels) <= 9:
            direct(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = ancillas[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    rec(labels, ctrl, 0)


def dual_unary_iteration_tight(qc: QuantumCircuit, *, index_a: Sequence[Qubit], index_b: Sequence[Qubit], labels: Sequence[int],
                               ctrl_a: Qubit, ctrl_b: Qubit, ancillas_a: Sequence[Qubit], ancillas_b: Sequence[Qubit],
                               leaf_fn, order: Literal["inc", "dec"] = "inc") -> None:
    labels = sorted(set(labels))
    if not labels:
        return
    need = _tight_unary_depth_for_labels(labels)
    if len(ancillas_a) < need or len(ancillas_b) < need:
        raise ValueError(f"tight dual unary iteration needs {need} ancillas per endpoint")
    def rec(sub_labels, ga, gb, depth):
        if len(sub_labels) == 1:
            leaf_fn(sub_labels[0], ga, gb); return
        bit = _e._split_bit(sub_labels)
        z = [x for x in sub_labels if ((x >> bit) & 1) == 0]
        o = [x for x in sub_labels if ((x >> bit) & 1) == 1]
        ha = ancillas_a[depth]; hb = ancillas_b[depth]
        _e._and_with_index_bit(qc, ga, index_a[bit], ha, 0)
        _e._and_with_index_bit(qc, gb, index_b[bit], hb, 0)
        if order == "inc":
            rec(z, ha, hb, depth+1)
            qc.cx(ga, ha); qc.cx(gb, hb)
            rec(o, ha, hb, depth+1)
            qc.cx(gb, hb); qc.cx(ga, ha)
        else:
            qc.cx(ga, ha); qc.cx(gb, hb)
            rec(o, ha, hb, depth+1)
            qc.cx(gb, hb); qc.cx(ga, ha)
            rec(z, ha, hb, depth+1)
        _e._uncompute_and_with_index_bit(qc, gb, index_b[bit], hb, 0)
        _e._uncompute_and_with_index_bit(qc, ga, index_a[bit], ha, 0)
    rec(labels, ctrl_a, ctrl_b, 0)


def kg_prefix_ancilla_count(n: int) -> int:
    """Exact port of ``arith/khattar_gidney.rs::kg_prefix_ancilla_count``."""
    if n <= 1:
        return 0
    targets_len = _kg_get_layer_id(n - 1) + 1
    if targets_len <= 2:
        return 1
    return 2 + kg_prefix_ancilla_count(targets_len)


def _kg_get_layer_id(x: int) -> int:
    layer_id = 0
    start = 0
    while start <= x:
        start += (1 << layer_id) + 1
        layer_id += 1
    return layer_id - 1


def _kg_start_layer(layer_id: int) -> int:
    return sum((1 << i) + 1 for i in range(layer_id))


def _kg_get_layers_for_prefix_and(q: Sequence[Qubit], ancillas: Sequence[Qubit]):
    """Return the exact conditionally-clean KG layer schedule used by Rust."""
    q = list(q)
    ancillas = list(ancillas)
    if not q:
        raise ValueError("KG prefix input must be non-empty")
    if len(q) == 1:
        return [dict(ctrls=[], ops=[]), dict(ctrls=[q[0]], ops=[])]
    need = kg_prefix_ancilla_count(len(q))
    if len(ancillas) < need:
        raise ValueError(f"KG prefix needs {need} ancillas, got {len(ancillas)}")

    n = len(q)
    n_layers = _kg_get_layer_id(n - 1)
    layers = [dict(ctrls=[], ops=[])]
    targets: list[Qubit] = []
    anc = [ancillas[0]]

    for layer_id in range(n_layers + 1):
        start = _kg_start_layer(layer_id)
        end = min(n, _kg_start_layer(layer_id + 1))
        layers.append(dict(ctrls=targets + [q[start]], ops=[]))
        for i in range(start + 1, end):
            offset = i - start
            if offset == 1:
                q1, target = q[i - 1], anc[-1]
            else:
                q1, target = anc[-(offset - 1)], anc[-offset]
            ops = []
            if target is ancillas[0]:
                ops.append(("ccx", q[i], q1, target))
            else:
                ops.append(("x", target))
                ops.append(("ccx", q[i], q1, target))
            layers.append(dict(ctrls=targets + [target], ops=ops))

        layer_len = end - start
        targets.append(anc[1 - layer_len])
        anc = anc[2 - layer_len:] + q[start:end]

    if len(targets) <= 2:
        return layers

    layers.append(dict(ctrls=[], ops=[]))
    target_layers = _kg_get_layers_for_prefix_and(targets, ancillas[2:])
    for layer_id in range(1, n_layers + 1):
        start = _kg_start_layer(layer_id)
        end = min(n, _kg_start_layer(layer_id + 1))
        target_ctrls = list(target_layers[layer_id]["ctrls"])
        layers[start + 1]["ops"].extend(target_layers[layer_id]["ops"])
        if len(target_ctrls) == 1:
            temp_target = target_ctrls[0]
        elif len(target_ctrls) == 2:
            temp_target = ancillas[1]
            layers[start + 1]["ops"].append(
                ("ccx", target_ctrls[0], target_ctrls[1], temp_target)
            )
        else:
            raise AssertionError("KG recursive target prefix must expose one or two controls")
        for i in range(start, end):
            local = layers[i + 1]["ctrls"][-1]
            layers[i + 1]["ctrls"] = [temp_target, local]
        if len(target_ctrls) == 2:
            layers[end + 1]["ops"].append(
                ("ccx", target_ctrls[0], target_ctrls[1], temp_target)
            )
    return layers


def _kg_emit_op(qc: QuantumCircuit, op) -> None:
    if op[0] == "x":
        qc.x(op[1])
    elif op[0] == "ccx":
        qc.ccx(op[1], op[2], op[3])
    else:
        raise AssertionError(f"unknown KG op {op[0]}")


def _kg_emit_layers(qc: QuantumCircuit, layers, *, reverse: bool = False) -> None:
    layer_order = reversed(layers) if reverse else layers
    for layer in layer_order:
        op_order = reversed(layer["ops"]) if reverse else layer["ops"]
        for op in op_order:
            _kg_emit_op(qc, op)


def _kg_lowest_layer_touching(layers, changed: Sequence[Qubit]) -> Optional[int]:
    changed_ids = {id(q) for q in changed}
    for index, layer in enumerate(layers):
        for op in layer["ops"]:
            if any(id(q) in changed_ids for q in op[1:]):
                return index
    return None


def _kg_toggle_equality(qc: QuantumCircuit, *, base: Sequence[Qubit], c0: Qubit,
                        flag: Qubit, clean_temp: Optional[Qubit] = None,
                        borrowed_temp: Optional[Qubit] = None) -> None:
    controls = list(base) + [c0]
    if len(controls) == 1:
        qc.cx(controls[0], flag)
    elif len(controls) == 2:
        qc.ccx(controls[0], controls[1], flag)
    elif len(controls) == 3:
        if (clean_temp is None) == (borrowed_temp is None):
            raise ValueError("KG equality needs exactly one clean or borrowed temporary")
        if clean_temp is not None:
            _clean_c3x_mbu(
                qc, controls[0], controls[1], controls[2], flag, clean_temp,
            )
        else:
            _borrowed_c3x(
                qc, controls[0], controls[1], controls[2], flag, borrowed_temp,
            )
    else:
        raise ValueError(f"KG equality expected at most three controls, got {len(controls)}")


def dual_unary_iteration_log_star(qc: QuantumCircuit, *,
                                  index_a: Sequence[Qubit], index_b: Sequence[Qubit],
                                  labels: Sequence[int], ancillas_a: Sequence[Qubit],
                                  ancillas_b: Sequence[Qubit], flag_a: Qubit,
                                  flag_b: Qubit, common_ctrl: Qubit,
                                  leaf_fn,
                                  clean_temp: Optional[Qubit] = None,
                                  borrowed_temp: Optional[Qubit] = None,
                                  order: Literal["inc", "dec"] = "inc") -> None:
    """Dual exact KG unary iterator with synchronized Gray updates.

    Each callback sees cleanly materialized raw equality flags for both
    endpoints.  Prefix and equality ancillas, borrowed lanes, and endpoints
    are restored exactly on return.
    """
    labels = sorted(set(labels), reverse=(order == "dec"))
    if not labels:
        return
    if len(index_a) != len(index_b) or len(index_a) < 2:
        raise ValueError("dual KG iterator requires equal endpoint widths >= 2")
    n = len(index_a)
    # Fold the common control into each prefix input.  Keep it LAST so the
    # conditionally-clean KG schedule never borrows the shared Ctrl as a
    # target; both endpoint engines can then remain live simultaneously.
    # The prefix product is AND(c[n-1],...,c[1],Ctrl), while c[0] remains the
    # separate final control.
    need = kg_prefix_ancilla_count(n)
    if len(ancillas_a) < need or len(ancillas_b) < need:
        raise ValueError(f"dual KG iterator needs {need} ancillas per endpoint")

    def complement_for(index: Sequence[Qubit], value: int) -> None:
        for bit, lane in enumerate(index):
            if ((value >> bit) & 1) == 0:
                qc.x(lane)

    start = labels[0]
    complement_for(index_a, start)
    complement_for(index_b, start)
    bits_a = list(reversed(index_a))
    bits_b = list(reversed(index_b))
    prefix_a = bits_a[:-1] + [common_ctrl]
    prefix_b = bits_b[:-1] + [common_ctrl]
    layers_a = _kg_get_layers_for_prefix_and(prefix_a, ancillas_a[:need])
    layers_b = _kg_get_layers_for_prefix_and(prefix_b, ancillas_b[:need])
    for layers in (layers_a, layers_b):
        if any(op[-1] == common_ctrl for layer in layers for op in layer["ops"]):
            raise AssertionError("dual KG schedule must not target shared Ctrl")
    _kg_emit_layers(qc, layers_a)
    _kg_emit_layers(qc, layers_b)
    base_a = list(layers_a[len(prefix_a)]["ctrls"])
    base_b = list(layers_b[len(prefix_b)]["ctrls"])

    for position, label in enumerate(labels):
        _kg_toggle_equality(
            qc, base=base_a, c0=index_a[0], flag=flag_a,
            clean_temp=clean_temp, borrowed_temp=borrowed_temp,
        )
        _kg_toggle_equality(
            qc, base=base_b, c0=index_b[0], flag=flag_b,
            clean_temp=clean_temp, borrowed_temp=borrowed_temp,
        )
        leaf_fn(label, flag_a, flag_b)
        _kg_toggle_equality(
            qc, base=base_b, c0=index_b[0], flag=flag_b,
            clean_temp=clean_temp, borrowed_temp=borrowed_temp,
        )
        _kg_toggle_equality(
            qc, base=base_a, c0=index_a[0], flag=flag_a,
            clean_temp=clean_temp, borrowed_temp=borrowed_temp,
        )

        if position + 1 == len(labels):
            continue
        next_label = labels[position + 1]
        delta = label ^ next_label
        changed_a = [bits_a[n - 1 - bit] for bit in range(1, n) if (delta >> bit) & 1]
        changed_b = [bits_b[n - 1 - bit] for bit in range(1, n) if (delta >> bit) & 1]
        first_a = _kg_lowest_layer_touching(layers_a, changed_a)
        first_b = _kg_lowest_layer_touching(layers_b, changed_b)
        if first_b is not None:
            _kg_emit_layers(qc, layers_b[first_b:], reverse=True)
        if first_a is not None:
            _kg_emit_layers(qc, layers_a[first_a:], reverse=True)
        for bit in range(n):
            if (delta >> bit) & 1:
                qc.x(index_a[bit])
                qc.x(index_b[bit])
        if first_a is not None:
            _kg_emit_layers(qc, layers_a[first_a:])
        if first_b is not None:
            _kg_emit_layers(qc, layers_b[first_b:])

    _kg_emit_layers(qc, layers_b, reverse=True)
    _kg_emit_layers(qc, layers_a, reverse=True)
    complement_for(index_b, labels[-1])
    complement_for(index_a, labels[-1])


def dual_unary_iteration_log_star_lqmod256(qc: QuantumCircuit, *,
                                  index_a: Sequence[Qubit], index_b: Sequence[Qubit],
                                  labels: Sequence[int], ancillas_a: Sequence[Qubit],
                                  ancillas_b: Sequence[Qubit], flag_a: Qubit,
                                  flag_b: Qubit, common_ctrl: Qubit,
                                  leaf_fn,
                                  clean_temp: Optional[Qubit] = None,
                                  borrowed_temp: Optional[Qubit] = None,
                                  order: Literal["inc", "dec"] = "inc") -> None:
    """Dual KG iterator: index_a decoded over full labels, index_b over the low
    byte (label & 0xFF) -- the mod-256 R-quotient encoding.  The q flag is omitted
    (None) at sentinel labels 2 and 259, matching the raw mod-256 iterator.
    """
    labels = sorted(set(labels), reverse=(order == "dec"))
    if not labels:
        return
    na = len(index_a)
    nb = len(index_b)
    need_a = kg_prefix_ancilla_count(na)
    need_b = kg_prefix_ancilla_count(nb)
    if len(ancillas_a) < need_a or len(ancillas_b) < need_b:
        raise ValueError("dual KG lqmod256 iterator needs prefix ancillas")

    def complement_a(value: int) -> None:
        for bit, lane in enumerate(index_a):
            if ((value >> bit) & 1) == 0:
                qc.x(lane)

    def complement_b(value: int) -> None:
        v = value & 0xFF
        for bit, lane in enumerate(index_b):
            if ((v >> bit) & 1) == 0:
                qc.x(lane)

    start = labels[0]
    complement_a(start)
    complement_b(start)
    bits_a = list(reversed(index_a))
    bits_b = list(reversed(index_b))
    prefix_a = bits_a[:-1] + [common_ctrl]
    prefix_b = bits_b[:-1] + [common_ctrl]
    layers_a = _kg_get_layers_for_prefix_and(prefix_a, ancillas_a[:need_a])
    layers_b = _kg_get_layers_for_prefix_and(prefix_b, ancillas_b[:need_b])
    for layers in (layers_a, layers_b):
        if any(op[-1] == common_ctrl for layer in layers for op in layer["ops"]):
            raise AssertionError("dual KG lqmod256 schedule must not target shared Ctrl")
    _kg_emit_layers(qc, layers_a)
    _kg_emit_layers(qc, layers_b)
    base_a = list(layers_a[len(prefix_a)]["ctrls"])
    base_b = list(layers_b[len(prefix_b)]["ctrls"])

    for position, label in enumerate(labels):
        _kg_toggle_equality(qc, base=base_a, c0=index_a[0], flag=flag_a,
                            clean_temp=clean_temp, borrowed_temp=borrowed_temp)
        _kg_toggle_equality(qc, base=base_b, c0=index_b[0], flag=flag_b,
                            clean_temp=clean_temp, borrowed_temp=borrowed_temp)
        leaf_fn(label, flag_a, None if label in (2, 259) else flag_b)
        _kg_toggle_equality(qc, base=base_b, c0=index_b[0], flag=flag_b,
                            clean_temp=clean_temp, borrowed_temp=borrowed_temp)
        _kg_toggle_equality(qc, base=base_a, c0=index_a[0], flag=flag_a,
                            clean_temp=clean_temp, borrowed_temp=borrowed_temp)

        if position + 1 == len(labels):
            continue
        next_label = labels[position + 1]
        delta_a = label ^ next_label
        delta_b = (label & 0xFF) ^ (next_label & 0xFF)
        changed_a = [bits_a[na - 1 - bit] for bit in range(1, na) if (delta_a >> bit) & 1]
        changed_b = [bits_b[nb - 1 - bit] for bit in range(1, nb) if (delta_b >> bit) & 1]
        first_a = _kg_lowest_layer_touching(layers_a, changed_a)
        first_b = _kg_lowest_layer_touching(layers_b, changed_b)
        if first_b is not None:
            _kg_emit_layers(qc, layers_b[first_b:], reverse=True)
        if first_a is not None:
            _kg_emit_layers(qc, layers_a[first_a:], reverse=True)
        for bit in range(na):
            if (delta_a >> bit) & 1:
                qc.x(index_a[bit])
        for bit in range(nb):
            if (delta_b >> bit) & 1:
                qc.x(index_b[bit])
        if first_a is not None:
            _kg_emit_layers(qc, layers_a[first_a:])
        if first_b is not None:
            _kg_emit_layers(qc, layers_b[first_b:])

    _kg_emit_layers(qc, layers_b, reverse=True)
    _kg_emit_layers(qc, layers_a, reverse=True)
    complement_b(labels[-1])
    complement_a(labels[-1])


def dual_unary_iteration_log_star_raw_b(
    qc: QuantumCircuit,
    *,
    index_a: Sequence[Qubit],
    index_b: Sequence[Qubit],
    labels: Sequence[int],
    ancillas_a: Sequence[Qubit],
    ancillas_b: Sequence[Qubit],
    flag_a: Qubit,
    common_ctrl: Qubit,
    leaf_fn,
    borrowed_temp: Qubit,
    order: Literal["inc", "dec"] = "inc",
) -> None:
    """Dual KG iterator with endpoint B exposed as raw equality controls.

    Endpoint A is materialized in ``flag_a``.  Endpoint B remains the
    at-most-three-control product returned by the KG prefix schedule, allowing
    callers to apply it directly and avoid a second clean equality flag.
    """
    labels = sorted(set(labels), reverse=(order == "dec"))
    if not labels:
        return
    if len(index_a) != len(index_b) or len(index_a) < 2:
        raise ValueError("raw-B dual KG iterator requires equal widths >= 2")
    n = len(index_a)
    need = kg_prefix_ancilla_count(n)
    if len(ancillas_a) < need or len(ancillas_b) < need:
        raise ValueError(f"raw-B dual KG iterator needs {need} lanes per endpoint")

    def complement_for(index: Sequence[Qubit], value: int) -> None:
        for bit, lane in enumerate(index):
            if ((value >> bit) & 1) == 0:
                qc.x(lane)

    start = labels[0]
    complement_for(index_a, start)
    complement_for(index_b, start)
    bits_a = list(reversed(index_a))
    bits_b = list(reversed(index_b))
    prefix_a = bits_a[:-1] + [common_ctrl]
    prefix_b = bits_b[:-1] + [common_ctrl]
    layers_a = _kg_get_layers_for_prefix_and(prefix_a, ancillas_a[:need])
    layers_b = _kg_get_layers_for_prefix_and(prefix_b, ancillas_b[:need])
    for layers in (layers_a, layers_b):
        if any(op[-1] == common_ctrl for layer in layers for op in layer["ops"]):
            raise AssertionError("raw-B KG schedule must not target shared Ctrl")
    _kg_emit_layers(qc, layers_a)
    _kg_emit_layers(qc, layers_b)
    base_a = list(layers_a[len(prefix_a)]["ctrls"])
    base_b = list(layers_b[len(prefix_b)]["ctrls"])

    for position, label in enumerate(labels):
        _kg_toggle_equality(
            qc, base=base_a, c0=index_a[0], flag=flag_a,
            borrowed_temp=borrowed_temp,
        )
        raw_b = base_b + [index_b[0]]
        if not 1 <= len(raw_b) <= 3:
            raise AssertionError(f"raw-B equality has {len(raw_b)} controls")
        leaf_fn(label, flag_a, raw_b)
        _kg_toggle_equality(
            qc, base=base_a, c0=index_a[0], flag=flag_a,
            borrowed_temp=borrowed_temp,
        )

        if position + 1 == len(labels):
            continue
        next_label = labels[position + 1]
        delta = label ^ next_label
        changed_a = [
            bits_a[n - 1 - bit] for bit in range(1, n) if (delta >> bit) & 1
        ]
        changed_b = [
            bits_b[n - 1 - bit] for bit in range(1, n) if (delta >> bit) & 1
        ]
        first_a = _kg_lowest_layer_touching(layers_a, changed_a)
        first_b = _kg_lowest_layer_touching(layers_b, changed_b)
        if first_b is not None:
            _kg_emit_layers(qc, layers_b[first_b:], reverse=True)
        if first_a is not None:
            _kg_emit_layers(qc, layers_a[first_a:], reverse=True)
        for bit in range(n):
            if (delta >> bit) & 1:
                qc.x(index_a[bit])
                qc.x(index_b[bit])
        if first_a is not None:
            _kg_emit_layers(qc, layers_a[first_a:])
        if first_b is not None:
            _kg_emit_layers(qc, layers_b[first_b:])

    _kg_emit_layers(qc, layers_b, reverse=True)
    _kg_emit_layers(qc, layers_a, reverse=True)
    complement_for(index_b, labels[-1])
    complement_for(index_a, labels[-1])


def dual_unary_iteration_log_star_raw_ab(
    qc: QuantumCircuit,
    *,
    index_a: Sequence[Qubit],
    index_b: Sequence[Qubit],
    labels: Sequence[int],
    ancillas_a: Sequence[Qubit],
    ancillas_b: Sequence[Qubit],
    common_ctrl: Qubit,
    leaf_fn,
    order: Literal["inc", "dec"] = "inc",
) -> None:
    """Dual KG iterator exposing both endpoint equalities as raw controls."""
    labels = sorted(set(labels), reverse=(order == "dec"))
    if not labels:
        return
    if len(index_a) != len(index_b) or len(index_a) < 2:
        raise ValueError("raw-AB dual KG iterator requires equal widths >= 2")
    n = len(index_a)
    need = kg_prefix_ancilla_count(n)
    if len(ancillas_a) < need or len(ancillas_b) < need:
        raise ValueError(f"raw-AB dual KG iterator needs {need} lanes per endpoint")

    def complement_for(index: Sequence[Qubit], value: int) -> None:
        for bit, lane in enumerate(index):
            if ((value >> bit) & 1) == 0:
                qc.x(lane)

    start = labels[0]
    complement_for(index_a, start)
    complement_for(index_b, start)
    bits_a = list(reversed(index_a))
    bits_b = list(reversed(index_b))
    prefix_a = bits_a[:-1] + [common_ctrl]
    prefix_b = bits_b[:-1] + [common_ctrl]
    layers_a = _kg_get_layers_for_prefix_and(prefix_a, ancillas_a[:need])
    layers_b = _kg_get_layers_for_prefix_and(prefix_b, ancillas_b[:need])
    for layers in (layers_a, layers_b):
        if any(op[-1] == common_ctrl for layer in layers for op in layer["ops"]):
            raise AssertionError("raw-AB KG schedule must not target shared Ctrl")
    _kg_emit_layers(qc, layers_a)
    _kg_emit_layers(qc, layers_b)
    base_a = list(layers_a[len(prefix_a)]["ctrls"])
    base_b = list(layers_b[len(prefix_b)]["ctrls"])

    for position, label in enumerate(labels):
        raw_a = base_a + [index_a[0]]
        raw_b = base_b + [index_b[0]]
        if not 1 <= len(raw_a) <= 3 or not 1 <= len(raw_b) <= 3:
            raise AssertionError(
                f"raw-AB equality sizes {len(raw_a)}, {len(raw_b)}"
            )
        leaf_fn(label, raw_a, raw_b)

        if position + 1 == len(labels):
            continue
        next_label = labels[position + 1]
        delta = label ^ next_label
        changed_a = [
            bits_a[n - 1 - bit] for bit in range(1, n) if (delta >> bit) & 1
        ]
        changed_b = [
            bits_b[n - 1 - bit] for bit in range(1, n) if (delta >> bit) & 1
        ]
        first_a = _kg_lowest_layer_touching(layers_a, changed_a)
        first_b = _kg_lowest_layer_touching(layers_b, changed_b)
        if first_b is not None:
            _kg_emit_layers(qc, layers_b[first_b:], reverse=True)
        if first_a is not None:
            _kg_emit_layers(qc, layers_a[first_a:], reverse=True)
        for bit in range(n):
            if (delta >> bit) & 1:
                qc.x(index_a[bit])
                qc.x(index_b[bit])
        if first_a is not None:
            _kg_emit_layers(qc, layers_a[first_a:])
        if first_b is not None:
            _kg_emit_layers(qc, layers_b[first_b:])

    _kg_emit_layers(qc, layers_b, reverse=True)
    _kg_emit_layers(qc, layers_a, reverse=True)
    complement_for(index_b, labels[-1])
    complement_for(index_a, labels[-1])


def dual_unary_iteration_direct_raw_ab(
    qc: QuantumCircuit,
    *,
    index_a: Sequence[Qubit],
    index_b: Sequence[Qubit],
    labels: Sequence[int],
    common_ctrl: Qubit,
    leaf_fn,
    order: Literal["inc", "dec"] = "inc",
) -> None:
    """Dual Gray iterator exposing full endpoint equalities as raw controls."""
    labels = sorted(set(labels), reverse=(order == "dec"))
    if not labels:
        return
    if len(index_a) != len(index_b):
        raise ValueError("direct raw-AB iterator requires equal endpoint widths")

    def complement_for(index: Sequence[Qubit], value: int) -> None:
        for bit, lane in enumerate(index):
            if ((value >> bit) & 1) == 0:
                qc.x(lane)

    start = labels[0]
    complement_for(index_a, start)
    complement_for(index_b, start)
    raw_a = [common_ctrl] + list(index_a)
    raw_b = [common_ctrl] + list(index_b)
    for position, label in enumerate(labels):
        leaf_fn(label, raw_a, raw_b)
        if position + 1 == len(labels):
            continue
        delta = label ^ labels[position + 1]
        for bit in range(len(index_a)):
            if (delta >> bit) & 1:
                qc.x(index_a[bit])
                qc.x(index_b[bit])
    complement_for(index_b, labels[-1])
    complement_for(index_a, labels[-1])


def dual_unary_iteration_direct_raw_a_mod256_b(
    qc: QuantumCircuit,
    *,
    index_a: Sequence[Qubit],
    index_b: Sequence[Qubit],
    labels: Sequence[int],
    common_ctrl: Qubit,
    leaf_fn,
    order: Literal["inc", "dec"] = "inc",
) -> None:
    """Dual raw iterator with B encoded modulo 256.

    The live R boundary is exactly in 3..258.  Codes 256..258 are represented
    by low bytes 0..2 while B[8] stores the borrowed Iter value.  Semantic
    labels 2 and 259 are not reachable B boundaries, so their B equalities are
    deliberately absent even when they remain in the conservative arithmetic
    carry envelope.
    """
    labels = sorted(set(labels), reverse=(order == "dec"))
    if not labels:
        return
    if len(index_a) != 9 or len(index_b) != 9:
        raise ValueError("mod256-B raw iterator requires two nine-bit endpoints")

    def complement_for(index: Sequence[Qubit], value: int, width: int) -> None:
        for bit, lane in enumerate(index[:width]):
            if ((value >> bit) & 1) == 0:
                qc.x(lane)

    start = labels[0]
    complement_for(index_a, start, 9)
    complement_for(index_b, start & 0xFF, 8)
    raw_a = [common_ctrl] + list(index_a)
    raw_b = [common_ctrl] + list(index_b[:8])
    for position, label in enumerate(labels):
        leaf_fn(label, raw_a, None if label in (2, 259) else raw_b)
        if position + 1 == len(labels):
            continue
        next_label = labels[position + 1]
        delta_a = label ^ next_label
        for bit in range(9):
            if (delta_a >> bit) & 1:
                qc.x(index_a[bit])
        delta_b = (label & 0xFF) ^ (next_label & 0xFF)
        for bit in range(8):
            if (delta_b >> bit) & 1:
                qc.x(index_b[bit])
    complement_for(index_b, labels[-1] & 0xFF, 8)
    complement_for(index_a, labels[-1], 9)


def _toggle_eq_const_under_ctrl_direct(qc: QuantumCircuit, *, endpoint: Sequence[Qubit], const: int, ctrl: Qubit, acc: Qubit, scratch: Sequence[Qubit]) -> None:
    # scratch supplies a temporary eq flag followed by mcx scratch.
    eq = scratch[0]
    pool = list(scratch[1:])
    _e.compute_eq_const(qc, endpoint, const, eq, pool)
    qc.ccx(ctrl, eq, acc)
    _e.compute_eq_const(qc, endpoint, const, eq, pool)


def _const_scratch(Scratch, width: int, carry: Qubit) -> list[Qubit]:
    # add_const_mod_2n expects width constant bits followed by one clean carry.
    return list(Scratch[:width]) + [carry]


def _controlled_adjacent_basis_swap(qc: QuantumCircuit, *, ctrl: Qubit,
                                    reg: Sequence[Qubit], a: int, b: int,
                                    scratch: Sequence[Qubit]) -> None:
    """Swap adjacent basis labels a/b under ctrl, restoring clean scratch."""
    diff = a ^ b
    if diff == 0 or diff & (diff - 1):
        raise ValueError("adjacent basis labels must differ in exactly one bit")
    target_bit = diff.bit_length() - 1
    controls = [ctrl]
    inverted: list[Qubit] = []
    for bit, qubit in enumerate(reg):
        if bit == target_bit:
            continue
        if ((a >> bit) & 1) == 0:
            qc.x(qubit)
            inverted.append(qubit)
        controls.append(qubit)
    _e.mcx_vchain(qc, controls, reg[target_bit], scratch)
    for qubit in reversed(inverted):
        qc.x(qubit)


def _controlled_basis_swap(qc: QuantumCircuit, *, ctrl: Qubit,
                           reg: Sequence[Qubit], a: int, b: int,
                           scratch: Sequence[Qubit]) -> None:
    """Exact controlled transposition of two computational-basis labels."""
    if a == b:
        return
    path = [a]
    current = a
    for bit in range(len(reg)):
        if ((a ^ b) >> bit) & 1:
            current ^= 1 << bit
            path.append(current)
    if path[-1] != b:
        raise AssertionError("basis-swap Gray path")
    edges = list(zip(path, path[1:]))
    for left, right in edges:
        _controlled_adjacent_basis_swap(
            qc, ctrl=ctrl, reg=reg, a=left, b=right, scratch=scratch,
        )
    for left, right in reversed(edges[:-1]):
        _controlled_adjacent_basis_swap(
            qc, ctrl=ctrl, reg=reg, a=left, b=right, scratch=scratch,
        )


def _controlled_zero_259_swap_linear(qc: QuantumCircuit, *, ctrl: Qubit,
                                     reg: Sequence[Qubit],
                                     scratch: Sequence[Qubit]) -> None:
    """Swap |0> and |259> with one high-control toggle, globally exactly.

    The difference word 259 has bits {0,1,8}.  Conjugating by
    x0 ^= x8; x1 ^= x8 maps it to the unit word 256, so the transposition
    needs one adjacent basis swap instead of a five-swap Gray palindrome.
    """
    if len(reg) != LS_WIDTH:
        raise ValueError("0/259 transposition requires a 9-bit register")
    qc.cx(reg[8], reg[0])
    qc.cx(reg[8], reg[1])
    _controlled_adjacent_basis_swap(
        qc, ctrl=ctrl, reg=reg, a=0, b=1 << 8, scratch=scratch,
    )
    qc.cx(reg[8], reg[1])
    qc.cx(reg[8], reg[0])


def inc_mod259_1ctrl(qc: QuantumCircuit, ctrl: Qubit,
                     reg: Sequence[Qubit], scratch: Sequence[Qubit]) -> None:
    """Controlled +1 on 0..258, extended to a permutation on all 9-bit words."""
    if len(reg) != LS_WIDTH:
        raise ValueError("mod-259 increment requires a 9-bit register")
    _e.inc_mod2n_1ctrl(qc, ctrl, list(reg), scratch[: LS_WIDTH - 1])
    _controlled_zero_259_swap_linear(qc, ctrl=ctrl, reg=reg, scratch=scratch)


def dec_mod259_1ctrl(qc: QuantumCircuit, ctrl: Qubit,
                     reg: Sequence[Qubit], scratch: Sequence[Qubit]) -> None:
    """Exact inverse of inc_mod259_1ctrl."""
    if len(reg) != LS_WIDTH:
        raise ValueError("mod-259 decrement requires a 9-bit register")
    _controlled_zero_259_swap_linear(qc, ctrl=ctrl, reg=reg, scratch=scratch)
    _e.dec_mod2n_1ctrl(qc, ctrl, list(reg), scratch[: LS_WIDTH - 1])


def _controlled_zero_259_swap_dirty(
    qc: QuantumCircuit,
    *,
    ctrl: Qubit,
    reg: Sequence[Qubit],
    dirty: Sequence[Qubit],
    clean_helper: Optional[Qubit] = None,
) -> None:
    """Swap 0 and 259 using restored dirty lenders instead of clean scratch."""
    if len(reg) != LS_WIDTH:
        raise ValueError("dirty 0/259 transposition requires a 9-bit register")
    qc.cx(reg[8], reg[0])
    qc.cx(reg[8], reg[1])
    for lane in reg[:8]:
        qc.x(lane)
    controls = [ctrl] + [reg[bit] for bit in range(LS_WIDTH) if bit != 8]
    if clean_helper is None:
        _toggle_raw_controls_dirty(qc, controls, reg[8], dirty)
    else:
        _toggle_one_clean_mcx_9(qc, controls, reg[8], clean_helper)
    for lane in reversed(reg[:8]):
        qc.x(lane)
    qc.cx(reg[8], reg[1])
    qc.cx(reg[8], reg[0])


def inc_mod259_1ctrl_dirty(
    qc: QuantumCircuit,
    ctrl: Qubit,
    reg: Sequence[Qubit],
    dirty: Sequence[Qubit],
    clean_helper: Optional[Qubit] = None,
) -> None:
    """Controlled +1 modulo 259 with arbitrary restored dirty lenders."""
    if clean_helper is None:
        _increment_by_dirty_carry(qc, reg, dirty, ctrl)
    else:
        _increment_by_one_clean_carry_9(qc, reg, ctrl, clean_helper)
    _controlled_zero_259_swap_dirty(
        qc, ctrl=ctrl, reg=reg, dirty=dirty, clean_helper=clean_helper,
    )


def dec_mod259_1ctrl_dirty(
    qc: QuantumCircuit,
    ctrl: Qubit,
    reg: Sequence[Qubit],
    dirty: Sequence[Qubit],
    clean_helper: Optional[Qubit] = None,
) -> None:
    """Exact inverse of inc_mod259_1ctrl_dirty."""
    _controlled_zero_259_swap_dirty(
        qc, ctrl=ctrl, reg=reg, dirty=dirty, clean_helper=clean_helper,
    )
    if clean_helper is None:
        _decrement_by_dirty_carry(qc, reg, dirty, ctrl)
    else:
        _decrement_by_one_clean_carry_9(qc, reg, ctrl, clean_helper)


def _swap_zero_259_uncontrolled(qc: QuantumCircuit, reg: Sequence[Qubit],
                                one: Qubit, scratch: Sequence[Qubit]) -> None:
    """Swap basis labels 0 and 259, restoring a temporary constant-one bit."""
    qc.x(one)
    _controlled_zero_259_swap_linear(qc, ctrl=one, reg=reg, scratch=scratch)
    qc.x(one)


def _swap_zero_259_uncontrolled_dirty(
    qc: QuantumCircuit,
    reg: Sequence[Qubit],
    one: Qubit,
    dirty: Sequence[Qubit],
    clean_helper: Optional[Qubit] = None,
) -> None:
    """Uncontrolled 0/259 transposition using a restored constant-one lane."""
    qc.x(one)
    _controlled_zero_259_swap_dirty(
        qc, ctrl=one, reg=reg, dirty=dirty, clean_helper=clean_helper,
    )
    qc.x(one)


@lru_cache(maxsize=None)
def clean_c3x_mbu_gate() -> Gate:
    """Self-inverse C^3X with a clean temporary lowered by KMX HMR."""
    wires = QuantumRegister(5, "c3x")
    qc = QuantumCircuit(wires, name="CLEAN_C3X_MBU")
    qc.ccx(wires[0], wires[1], wires[4])
    qc.ccx(wires[2], wires[4], wires[3])
    qc.ccx(wires[0], wires[1], wires[4])
    return qc.to_gate()


def _clean_c3x_mbu(qc: QuantumCircuit, a: Qubit, b: Qubit, c: Qubit,
                    target: Qubit, clean_temp: Qubit) -> None:
    """Toggle ``target`` by ``a & b & c`` and HMR-clean ``clean_temp``."""
    qc.append(clean_c3x_mbu_gate(), [a, b, c, target, clean_temp])


def _dirty_c3x(qc: QuantumCircuit, a: Qubit, b: Qubit, c: Qubit, target: Qubit, dirty: Qubit) -> None:
    qc.append(clean_c3x_mbu_gate(), [a, b, c, target, dirty])


def _controlled_toffoli_dirty(qc: QuantumCircuit, ctrl: Qubit, a: Qubit, b: Qubit, target: Qubit, dirty: Qubit) -> None:
    _dirty_c3x(qc, ctrl, a, b, target, dirty)


def controlled_maj_dirty(qc: QuantumCircuit, ctrl: Qubit, a: Qubit, b: Qubit, c: Qubit, dirty: Qubit) -> None:
    qc.ccx(ctrl, a, b)
    qc.ccx(ctrl, a, c)
    _controlled_toffoli_dirty(qc, ctrl, c, b, a, dirty)


def controlled_uma_dirty(qc: QuantumCircuit, ctrl: Qubit, a: Qubit, b: Qubit, c: Qubit, dirty: Qubit) -> None:
    _controlled_toffoli_dirty(qc, ctrl, c, b, a, dirty)
    qc.ccx(ctrl, a, c)
    qc.ccx(ctrl, c, b)


def controlled_maj_inv_dirty(qc: QuantumCircuit, ctrl: Qubit, a: Qubit, b: Qubit, c: Qubit, dirty: Qubit) -> None:
    _controlled_toffoli_dirty(qc, ctrl, c, b, a, dirty)
    qc.ccx(ctrl, a, c)
    qc.ccx(ctrl, a, b)


def controlled_uma_inv_dirty(qc: QuantumCircuit, ctrl: Qubit, a: Qubit, b: Qubit, c: Qubit, dirty: Qubit) -> None:
    qc.ccx(ctrl, c, b)
    qc.ccx(ctrl, a, c)
    _controlled_toffoli_dirty(qc, ctrl, c, b, a, dirty)


def _apply_cell_dirty(qc: QuantumCircuit, mode: Literal["add", "sub"], pass_kind: Literal["first", "second"],
                      ctrl: Qubit, addend: Qubit, target: Qubit, carry: Qubit, dirty: Qubit) -> None:
    if mode == "add" and pass_kind == "first":
        controlled_maj_dirty(qc, ctrl, addend, target, carry, dirty)
    elif mode == "add" and pass_kind == "second":
        controlled_uma_dirty(qc, ctrl, addend, target, carry, dirty)
    elif mode == "sub" and pass_kind == "first":
        controlled_uma_inv_dirty(qc, ctrl, addend, target, carry, dirty)
    elif mode == "sub" and pass_kind == "second":
        controlled_maj_inv_dirty(qc, ctrl, addend, target, carry, dirty)
    else:
        raise ValueError("bad arithmetic cell mode/pass")


@lru_cache(maxsize=None)
def lc_swap_unary_gate(*, k: int, K: int, len_width: int, name: str = "LC_SWAP_S835_FAST") -> Gate:
    if k > K:
        raise ValueError("need k <= K")
    M = K - k + 1
    depth = _e.unary_depth(M)
    base = max(len_width, depth)
    scratch_size = base + 2
    Ctrl = QuantumRegister(1, "Ctrl")
    Direction = QuantumRegister(1, "Direction")
    Sign = QuantumRegister(1, "Sign")
    Work1 = QuantumRegister(M + 1, "Work1")
    l_t = QuantumRegister(len_width, "l_t")
    l_q = QuantumRegister(len_width, "l_q")
    Scratch = QuantumRegister(scratch_size, "Scratch")
    qc = _e._block_circuit(Ctrl, Direction, Sign, Work1, l_t, l_q, Scratch, name=name)
    carry = Scratch[base]
    direction_flag = Scratch[base + 1]
    cs = list(Scratch[:len_width]) + [carry]
    qc.append(_e.cuccaro_add_mod_2n_no_z_gate(len_width, name="ADD_lt_to_lq"), list(l_t) + list(l_q) + [carry])
    _e.add_const_mod_2n(qc, l_q, 3, cs)
    path = list(Scratch[:depth])
    def leaf(j: int, ej: Qubit) -> None:
        # Phase 2 inserts the next quotient bit at physical j.  Phase 3 removes
        # the current low quotient bit at physical j-1.  Direction (Phase1) is
        # retained by the caller, so this branch is exactly reversible.
        _e._and_with_index_bit(qc, ej, Direction[0], direction_flag, 0)
        _e.cswap_toffoli(qc, direction_flag, Sign[0], Work1[j - k + 1])
        qc.cx(ej, direction_flag)
        _e.cswap_toffoli(qc, direction_flag, Sign[0], Work1[j - k])
        qc.cx(ej, direction_flag)
        _e._uncompute_and_with_index_bit(qc, ej, Direction[0], direction_flag, 0)
    unary_iteration_tight(qc, index_reg=l_q, labels=list(range(k, K + 1)), ctrl=Ctrl[0], ancillas=path, leaf_fn=leaf, order="inc")
    _e.sub_const_mod_2n(qc, l_q, 3, cs)
    qc.append(_e.cuccaro_sub_mod_2n_no_z_gate(len_width, name="SUB_lt_from_lq"), list(l_t) + list(l_q) + [carry])
    return _e._finalize_block(qc)


@lru_cache(maxsize=None)
def lc_interval_addsub_unary_gate(*, n: int, k: int, K: int, len_width: int, shift_width: int,
                                  mode: Literal["add", "sub"], sign_update: bool,
                                  target: Literal["work1", "work2"], name: str) -> Gate:
    if k > K:
        raise ValueError("need k <= K")
    M = K - k + 1
    endpoint_width = max(len_width, shift_width)
    # Decode the complete interval.  Splitting a 2^d+1 interval into a 2^d
    # unary tree plus a special top label is unsound unless the tree is also
    # conditioned on the omitted high bit: the top endpoint otherwise aliases
    # label zero.  The full tree costs one additional path qubit per endpoint
    # and is injective over every in-range endpoint.
    labels_all_abs = list(range(k, K + 1))
    rel_count = len(labels_all_abs)
    labels_main = list(range(rel_count))
    top_special = False
    top_rel = rel_count - 1
    depth = _tight_unary_depth_for_labels(labels_main)
    # Layout note:
    #   anc_a/anc_b occupy the first 2*depth wires and are used only by
    #   the unary endpoint scans.  Endpoint affine transforms need
    #   endpoint_width scratch wires plus a carry.  For late steps the unary
    #   depth can be smaller than endpoint_width; placing carry immediately
    #   after the unary paths would then alias it with the constant-adder
    #   scratch.  We therefore place carry/acc/cell_pool after the larger of
    #   the unary-scratch region and the endpoint-transform scratch region.
    base = max(2 * depth, endpoint_width)
    scratch_size = base + 3
    Ctrl = QuantumRegister(1, "Ctrl")
    Sign = QuantumRegister(1, "Sign")
    Work1 = QuantumRegister(M, "Work1")
    Work2 = QuantumRegister(M, "Work2")
    l_t = QuantumRegister(len_width, "l_t")
    l_q = QuantumRegister(len_width, "l_q")
    l_s = QuantumRegister(shift_width, "l_s")
    Scratch = QuantumRegister(scratch_size, "Scratch")
    qc = _e._block_circuit(Ctrl, Sign, Work1, Work2, l_t, l_q, l_s, Scratch, name=name)
    anc_a = list(Scratch[:depth])
    anc_b = list(Scratch[depth:2*depth])
    carry = Scratch[base]
    acc = Scratch[base + 1]
    cell_pool = [Scratch[base + 2]]
    # Top-special equality controls reuse one clean unary-path wire as the
    # one-hot flag.  The remaining clean paths plus cell_pool form its MCX
    # scratch; this keeps the n=256 block within the 20-qubit shared pool.
    top_flag = Scratch[0]
    eq_scratch = [Scratch[base + 2]] + [q for q in Scratch[:base] if q != top_flag]
    cs = _const_scratch(Scratch, endpoint_width, carry)
    # Prepare L=(ell_t-1)+(ell_q-1)+4 and R=n+2-(ell_s-1).
    qc.append(_e.cuccaro_add_mod_2n_no_z_gate(len_width, name="ADD_lt_to_lq"), list(l_t) + list(l_q) + [carry])
    _e.add_const_mod_2n(qc, l_q, 4, cs[:len_width] + [carry])
    _e.const_minus_inplace(qc, l_s, n + 2, cs[:shift_width] + [carry])
    # Convert absolute endpoints to relative offsets in [0, K-k].
    _e.sub_const_mod_2n(qc, l_q, k, cs[:len_width] + [carry])
    _e.sub_const_mod_2n(qc, l_s, k, cs[:shift_width] + [carry])
    def qpair(j: int) -> tuple[Qubit, Qubit]:
        j_abs = k + j
        idx = j_abs - k
        if target == "work1":
            return Work2[idx], Work1[idx]
        if target == "work2":
            return Work1[idx], Work2[idx]
        raise ValueError("bad target")
    def leaf_first(j: int, rj: Qubit, lj: Qubit) -> None:
        addend, tgt = qpair(j)
        idx = j
        # Work1/Work2's r fields are big endian.  The low boundary R uses the
        # clean carry; cells toward L use the transformed lower addend bit as
        # the Cuccaro carry chain.
        if idx + 1 < rel_count:
            _apply_cell_dirty(
                qc, mode, "first", acc, addend, tgt, qpair(idx + 1)[0], cell_pool[0]
            )
        _apply_cell_dirty(qc, mode, "first", rj, addend, tgt, carry, cell_pool[0])
        if sign_update:
            qc.ccx(lj, addend, Sign[0])
        qc.cx(rj, acc)
        qc.cx(lj, acc)
    if top_special:
        addend, tgt = qpair(top_rel)
        _toggle_eq_const_under_ctrl_direct(qc, endpoint=l_s, const=top_rel, ctrl=Ctrl[0], acc=top_flag, scratch=eq_scratch)
        _apply_cell_dirty(qc, mode, "first", top_flag, addend, tgt, carry, cell_pool[0])
        qc.cx(top_flag, acc)
        _toggle_eq_const_under_ctrl_direct(qc, endpoint=l_s, const=top_rel, ctrl=Ctrl[0], acc=top_flag, scratch=eq_scratch)
        _toggle_eq_const_under_ctrl_direct(qc, endpoint=l_q, const=top_rel, ctrl=Ctrl[0], acc=top_flag, scratch=eq_scratch)
        if sign_update:
            qc.ccx(top_flag, addend, Sign[0])
        qc.cx(top_flag, acc)
        _toggle_eq_const_under_ctrl_direct(qc, endpoint=l_q, const=top_rel, ctrl=Ctrl[0], acc=top_flag, scratch=eq_scratch)
    dual_unary_iteration_tight(qc, index_a=l_s, index_b=l_q, labels=labels_main,
                            ctrl_a=Ctrl[0], ctrl_b=Ctrl[0], ancillas_a=anc_a,
                            ancillas_b=anc_b, leaf_fn=leaf_first, order="dec")
    def leaf_second(j: int, rj: Qubit, lj: Qubit) -> None:
        addend, tgt = qpair(j)
        idx = j
        qc.cx(lj, acc)
        qc.cx(rj, acc)
        if idx + 1 < rel_count:
            _apply_cell_dirty(
                qc, mode, "second", acc, addend, tgt, qpair(idx + 1)[0], cell_pool[0]
            )
        _apply_cell_dirty(qc, mode, "second", rj, addend, tgt, carry, cell_pool[0])
    dual_unary_iteration_tight(qc, index_a=l_s, index_b=l_q, labels=labels_main,
                            ctrl_a=Ctrl[0], ctrl_b=Ctrl[0], ancillas_a=anc_a,
                            ancillas_b=anc_b, leaf_fn=leaf_second, order="inc")
    if top_special:
        addend, tgt = qpair(top_rel)
        _toggle_eq_const_under_ctrl_direct(qc, endpoint=l_q, const=top_rel, ctrl=Ctrl[0], acc=top_flag, scratch=eq_scratch)
        qc.cx(top_flag, acc)
        _toggle_eq_const_under_ctrl_direct(qc, endpoint=l_q, const=top_rel, ctrl=Ctrl[0], acc=top_flag, scratch=eq_scratch)
        _toggle_eq_const_under_ctrl_direct(qc, endpoint=l_s, const=top_rel, ctrl=Ctrl[0], acc=top_flag, scratch=eq_scratch)
        qc.cx(top_flag, acc)
        _apply_cell_dirty(qc, mode, "second", top_flag, addend, tgt, carry, cell_pool[0])
        _toggle_eq_const_under_ctrl_direct(qc, endpoint=l_s, const=top_rel, ctrl=Ctrl[0], acc=top_flag, scratch=eq_scratch)
    _e.add_const_mod_2n(qc, l_s, k, cs[:shift_width] + [carry])
    _e.add_const_mod_2n(qc, l_q, k, cs[:len_width] + [carry])
    _e.const_minus_inplace(qc, l_s, n + 2, cs[:shift_width] + [carry])
    _e.sub_const_mod_2n(qc, l_q, 4, cs[:len_width] + [carry])
    qc.append(_e.cuccaro_sub_mod_2n_no_z_gate(len_width, name="SUB_lt_from_lq"), list(l_t) + list(l_q) + [carry])
    return _e._finalize_block(qc)


@lru_cache(maxsize=None)
def lc_prefix_addsub_unary_gate(*, k: int, K: int, len_width: int,
                                mode: Literal["add", "sub"], sign_update: bool,
                                target: Literal["work1", "work2"], name: str,
                                endpoint_offset: int = 2) -> Gate:
    if k > K:
        raise ValueError("need k <= K")
    M = K - k + 1
    depth = _e.unary_depth(M)
    base = max(depth, len_width)
    scratch_size = base + 3
    Ctrl = QuantumRegister(1, "Ctrl")
    Sign = QuantumRegister(1, "Sign")
    Work1 = QuantumRegister(M, "Work1")
    Work2 = QuantumRegister(M, "Work2")
    l_t = QuantumRegister(len_width, "l_t")
    Scratch = QuantumRegister(scratch_size, "Scratch")
    qc = _e._block_circuit(Ctrl, Sign, Work1, Work2, l_t, Scratch, name=name)
    path = list(Scratch[:depth])
    carry = Scratch[base]
    acc = Scratch[base + 1]
    cell_pool = [Scratch[base + 2]]
    cs = list(Scratch[:len_width]) + [carry]
    _e.add_const_mod_2n(qc, l_t, endpoint_offset, cs)
    def qpair(j: int) -> tuple[Qubit, Qubit]:
        idx = j - k
        if target == "work1":
            return Work2[idx], Work1[idx]
        if target == "work2":
            return Work1[idx], Work2[idx]
        raise ValueError("bad target")
    qc.cx(Ctrl[0], acc)
    def leaf_first(j: int, ej: Qubit) -> None:
        addend, tgt = qpair(j)
        if j == k:
            _apply_cell_dirty(qc, mode, "first", Ctrl[0], addend, tgt, carry, cell_pool[0])
        else:
            _apply_cell_dirty(qc, mode, "first", acc, addend, tgt, qpair(j - 1)[0], cell_pool[0])
        if sign_update:
            qc.ccx(ej, addend, Sign[0])
        qc.cx(ej, acc)
    unary_iteration_tight(qc, index_reg=l_t, labels=list(range(k, K + 1)), ctrl=Ctrl[0], ancillas=path, leaf_fn=leaf_first, order="inc")
    def leaf_second(j: int, ej: Qubit) -> None:
        addend, tgt = qpair(j)
        qc.cx(ej, acc)
        if j == k:
            _apply_cell_dirty(qc, mode, "second", Ctrl[0], addend, tgt, carry, cell_pool[0])
        else:
            _apply_cell_dirty(qc, mode, "second", acc, addend, tgt, qpair(j - 1)[0], cell_pool[0])
    unary_iteration_tight(qc, index_reg=l_t, labels=list(range(k, K + 1)), ctrl=Ctrl[0], ancillas=path, leaf_fn=leaf_second, order="dec")
    qc.cx(Ctrl[0], acc)
    _e.sub_const_mod_2n(qc, l_t, endpoint_offset, cs)
    return _e._finalize_block(qc)


def _upper_zero_map_controlled(qc: QuantumCircuit, *, ctrl: Qubit,
                               boundary_B: Sequence[Qubit], bits: Sequence[Qubit],
                               dirty: Sequence[Qubit], k: int, K: int,
                               scratch: Sequence[Qubit]) -> None:
    """Controlled upper-zero dirty map with one shared palindromic scan."""
    depth = _e.unary_depth(K - k + 1)
    if len(scratch) < depth + 2:
        raise ValueError("controlled upper-zero map scratch shortage")
    path = list(scratch[:depth])
    range_acc = scratch[depth]
    a_tmp = scratch[depth + 1]

    def compute_factor(bctrl: Qubit, bit: Qubit) -> None:
        # ctrl & !(bctrl & bit): out-of-range positions contribute the
        # multiplicative identity when active, while ctrl=0 is exact identity.
        qc.cx(ctrl, a_tmp)
        qc.ccx(bctrl, bit, a_tmp)

    def leaf_forward(j: int, bctrl: Qubit) -> None:
        idx = j - k
        if j == K:
            # At the pivot, a_K = ctrl xor ([K <= B] & bit_K).  Applying it
            # directly removes one compute/action/uncompute Toffoli.
            qc.cx(ctrl, dirty[idx])
            qc.ccx(bctrl, bits[idx], dirty[idx])
            return
        compute_factor(bctrl, bits[idx])
        qc.ccx(a_tmp, dirty[idx + 1], dirty[idx])
        compute_factor(bctrl, bits[idx])

    def leaf_reverse(j: int, bctrl: Qubit) -> None:
        idx = j - k
        compute_factor(bctrl, bits[idx])
        qc.ccx(a_tmp, dirty[idx + 1], dirty[idx])
        compute_factor(bctrl, bits[idx])

    labels = list(range(k, K + 1))

    def scan_forward(sub_labels: list[int], g: Qubit, level: int) -> None:
        if len(sub_labels) == 1:
            leaf_forward(sub_labels[0], range_acc)
            qc.cx(g, range_acc)
            return
        bit = _e._split_bit(sub_labels)
        zero = [j for j in sub_labels if ((j >> bit) & 1) == 0]
        one = [j for j in sub_labels if ((j >> bit) & 1) == 1]
        h = path[level]
        _e._and_with_index_bit(qc, g, boundary_B[bit], h, 0)
        scan_forward(zero, h, level + 1)
        qc.cx(g, h)
        scan_forward(one, h, level + 1)
        qc.cx(g, h)
        _e._uncompute_and_with_index_bit(qc, g, boundary_B[bit], h, 0)

    def scan_reverse(sub_labels: list[int], g: Qubit, level: int) -> None:
        if len(sub_labels) == 1:
            qc.cx(g, range_acc)
            leaf_reverse(sub_labels[0], range_acc)
            return
        bit = _e._split_bit(sub_labels)
        zero = [j for j in sub_labels if ((j >> bit) & 1) == 0]
        one = [j for j in sub_labels if ((j >> bit) & 1) == 1]
        h = path[level]
        _e._and_with_index_bit(qc, g, boundary_B[bit], h, 0)
        qc.cx(g, h)
        scan_reverse(one, h, level + 1)
        qc.cx(g, h)
        scan_reverse(zero, h, level + 1)
        _e._uncompute_and_with_index_bit(qc, g, boundary_B[bit], h, 0)

    def scan_palindrome(sub_labels: list[int], g: Qubit, level: int) -> None:
        if len(sub_labels) == 1:
            leaf_forward(sub_labels[0], range_acc)
            return
        bit = _e._split_bit(sub_labels)
        zero = [j for j in sub_labels if ((j >> bit) & 1) == 0]
        one = [j for j in sub_labels if ((j >> bit) & 1) == 1]
        h = path[level]
        _e._and_with_index_bit(qc, g, boundary_B[bit], h, 0)
        scan_forward(zero, h, level + 1)
        qc.cx(g, h)
        scan_palindrome(one, h, level + 1)
        qc.cx(g, h)
        scan_reverse(zero, h, level + 1)
        _e._uncompute_and_with_index_bit(qc, g, boundary_B[bit], h, 0)

    qc.cx(ctrl, range_acc)
    scan_palindrome(labels, ctrl, 0)
    qc.cx(ctrl, range_acc)


@lru_cache(maxsize=None)
def t_tail_zero_toggle_gate(*, n: int, len_width: int, shift_width: int,
                            name: str = "T_TAIL_ZERO_S835_FAST") -> Gate:
    """Toggle Tail iff Work2[A..=B] is zero for the dynamic t' tail."""
    work_size = n + 3
    labels = list(range(work_size))
    depth = _tight_unary_depth_for_labels(labels)
    map_need = _e.unary_depth(work_size) + 2

    def pivot_depth(sub_labels: list[int], pivot: int) -> int:
        if len(sub_labels) <= 1:
            return 0
        bit = _e._split_bit(sub_labels)
        branch = [j for j in sub_labels if ((j >> bit) & 1) == ((pivot >> bit) & 1)]
        return 1 + pivot_depth(branch, pivot)

    live_select_depth = pivot_depth(labels, labels[-1])

    Ctrl = QuantumRegister(1, "Ctrl")
    Tail = QuantumRegister(1, "Tail")
    Work1 = QuantumRegister(work_size, "Work1")
    Work2 = QuantumRegister(work_size, "Work2")
    l_t = QuantumRegister(len_width, "l_t")
    l_s = QuantumRegister(shift_width, "l_s")
    l_rp = QuantumRegister(len_width, "l_rp")
    map_offset = 0
    select_offset = map_need
    carry_offset = select_offset + live_select_depth
    Scratch = QuantumRegister(carry_offset + 1, "Scratch")
    qc = _e._block_circuit(Ctrl, Tail, Work1, Work2, l_t, l_s, l_rp, Scratch, name=name)
    length_carry = Scratch[carry_offset]

    def shift_lower_endpoint(forward: bool) -> None:
        # Adding two modulo 2^w is an increment of bits 1..w-1.
        if len_width <= 1:
            return
        upper = list(l_t[1:])
        ancillas = list(Scratch[:max(0, len(upper) - 1)])
        if forward:
            _e.inc_mod2n_uncontrolled(qc, upper, ancillas)
        else:
            _e.dec_mod2n_uncontrolled(qc, upper, ancillas)

    def reflect_upper_endpoint() -> None:
        # l_rp <- n-l_rp.  At n=256 the constant is the top bit of the
        # 9-bit endpoint, so its modular addition is a single X.
        for q in l_rp:
            qc.x(q)
        _e.inc_mod2n_uncontrolled(qc, l_rp, list(Scratch[:max(0, len_width - 1)]))
        if n == (1 << (len_width - 1)):
            qc.x(l_rp[len_width - 1])
        else:
            _e.add_const_mod_2n(
                qc, l_rp, n, list(Scratch[:len_width]) + [length_carry]
            )

    def transform_endpoints() -> None:
        # A=l_t+1 (after the appended zero lane) and
        # B=n+2-l_r'-l_s in zero-based physical coordinates.
        shift_lower_endpoint(True)
        qc.append(
            _e.cuccaro_add_mod_2n_no_z_gate(len_width, name="ADD_ls_to_lrp"),
            list(l_s[:len_width]) + list(l_rp) + [length_carry],
        )
        reflect_upper_endpoint()

    def restore_endpoints() -> None:
        reflect_upper_endpoint()
        qc.append(
            _e.cuccaro_sub_mod_2n_no_z_gate(len_width, name="SUB_ls_from_lrp"),
            list(l_s[:len_width]) + list(l_rp) + [length_carry],
        )
        shift_lower_endpoint(False)

    map_scratch = list(Scratch[map_offset:map_offset + map_need])
    # Only the path to the maximum label remains live across the central map.
    # Give those levels dedicated wires; all deeper selector levels are clean
    # before the map and can alias its scratch without widening the EEA step.
    select_path = (
        list(Scratch[select_offset:select_offset + live_select_depth])
        + map_scratch[:depth - live_select_depth]
    )

    def apply_upper_map() -> None:
        _upper_zero_map_controlled(
            qc, ctrl=Ctrl[0], boundary_B=l_rp, bits=Work2, dirty=Work1,
            k=0, K=work_size - 1, scratch=map_scratch,
        )

    def selected_leaf(j: int, ej: Qubit) -> None:
        qc.ccx(ej, Work1[j], Tail[0])

    def select_forward(sub_labels: list[int], g: Qubit, level: int) -> None:
        if len(sub_labels) == 1:
            selected_leaf(sub_labels[0], g)
            return
        bit = _e._split_bit(sub_labels)
        zero = [j for j in sub_labels if ((j >> bit) & 1) == 0]
        one = [j for j in sub_labels if ((j >> bit) & 1) == 1]
        h = select_path[level]
        _e._and_with_index_bit(qc, g, l_t[bit], h, 0)
        select_forward(zero, h, level + 1)
        qc.cx(g, h)
        select_forward(one, h, level + 1)
        qc.cx(g, h)
        _e._uncompute_and_with_index_bit(qc, g, l_t[bit], h, 0)

    def select_reverse(sub_labels: list[int], g: Qubit, level: int) -> None:
        if len(sub_labels) == 1:
            selected_leaf(sub_labels[0], g)
            return
        bit = _e._split_bit(sub_labels)
        zero = [j for j in sub_labels if ((j >> bit) & 1) == 0]
        one = [j for j in sub_labels if ((j >> bit) & 1) == 1]
        h = select_path[level]
        _e._and_with_index_bit(qc, g, l_t[bit], h, 0)
        qc.cx(g, h)
        select_reverse(one, h, level + 1)
        qc.cx(g, h)
        select_reverse(zero, h, level + 1)
        _e._uncompute_and_with_index_bit(qc, g, l_t[bit], h, 0)

    def select_map_palindrome(sub_labels: list[int], g: Qubit, level: int) -> None:
        if len(sub_labels) == 1:
            selected_leaf(sub_labels[0], g)
            apply_upper_map()
            selected_leaf(sub_labels[0], g)
            return
        bit = _e._split_bit(sub_labels)
        zero = [j for j in sub_labels if ((j >> bit) & 1) == 0]
        one = [j for j in sub_labels if ((j >> bit) & 1) == 1]
        h = select_path[level]
        _e._and_with_index_bit(qc, g, l_t[bit], h, 0)
        select_forward(zero, h, level + 1)
        qc.cx(g, h)
        select_map_palindrome(one, h, level + 1)
        qc.cx(g, h)
        select_reverse(zero, h, level + 1)
        _e._uncompute_and_with_index_bit(qc, g, l_t[bit], h, 0)

    transform_endpoints()
    select_map_palindrome(labels, Ctrl[0], 0)
    apply_upper_map()
    restore_endpoints()
    return _e._finalize_block(qc)


@lru_cache(maxsize=None)
def t_lower_borrow_toggle_gate(*, n: int, len_width: int,
                               name: str = "T_LOWER_BORROW_S835_FAST") -> Gate:
    """Toggle Neg by Tail times the exact borrow through the t prefix."""
    work_size = n + 3
    labels = list(range(1, work_size + 1))
    depth = _tight_unary_depth_for_labels(labels)
    base = max(depth, len_width)
    Ctrl = QuantumRegister(1, "Ctrl")
    Tail = QuantumRegister(1, "Tail")
    Neg = QuantumRegister(1, "Neg")
    Work1 = QuantumRegister(work_size, "Work1")
    Work2 = QuantumRegister(work_size, "Work2")
    l_t = QuantumRegister(len_width, "l_t")
    Scratch = QuantumRegister(base + 2, "Scratch")
    qc = _e._block_circuit(Ctrl, Tail, Neg, Work1, Work2, l_t, Scratch, name=name)
    carry = Scratch[base]
    active = Scratch[base + 1]

    # The first inverse-UMA pass of the controlled prefix subtractor stores
    # the borrow through position j in Work1[j].  Execute that pass without a
    # location control, use its intermediate value at the selected endpoint,
    # then reverse it.  The surrounding permutation cancels even when the
    # output control is inactive, so only the unary selector needs Ctrl&Tail.
    if len_width > 1:
        _e.inc_mod2n_uncontrolled(
            qc, l_t[1:], list(Scratch[:max(0, len_width - 2)])
        )
    qc.ccx(Ctrl[0], Tail[0], active)

    def first_pass_cell(idx: int) -> None:
        addend = Work1[idx]
        target = Work2[idx]
        carry_in = carry if idx == 0 else Work1[idx - 1]
        qc.cx(carry_in, target)
        qc.cx(addend, carry_in)
        qc.ccx(carry_in, target, addend)

    def leaf(j: int, ej: Qubit) -> None:
        idx = j - 1
        first_pass_cell(idx)
        qc.ccx(ej, Work1[idx], Neg[0])

    unary_iteration_tight(
        qc, index_reg=l_t, labels=labels, ctrl=active,
        ancillas=list(Scratch[:depth]), leaf_fn=leaf, order="inc",
    )

    for idx in range(work_size - 1, -1, -1):
        addend = Work1[idx]
        target = Work2[idx]
        carry_in = carry if idx == 0 else Work1[idx - 1]
        qc.ccx(carry_in, target, addend)
        qc.cx(addend, carry_in)
        qc.cx(carry_in, target)

    qc.ccx(Ctrl[0], Tail[0], active)
    if len_width > 1:
        _e.dec_mod2n_uncontrolled(
            qc, l_t[1:], list(Scratch[:max(0, len_width - 2)])
        )
    return _e._finalize_block(qc)

# Reuse the low-aux length update; it is already the paper dirty-work construction with live-range shared scratch.
import eea_circuit_s835_lowaux as _low
len_update_lt_unary_gate = _low.len_update_lt_unary_gate
len_update_lrp_unary_gate = _low.len_update_lrp_unary_gate


def _borrowed_c3x(qc: QuantumCircuit, a: Qubit, b: Qubit, c: Qubit,
                  target: Qubit, borrowed: Qubit) -> None:
    """Exact C3X using one unknown borrowed bit, restored with no phase."""
    lanes = [a, b, c, target, borrowed]
    if len(set(lanes)) != len(lanes):
        raise ValueError("borrowed C3X lanes must be distinct")
    qc.ccx(a, b, borrowed)
    qc.ccx(borrowed, c, target)
    qc.ccx(a, b, borrowed)
    qc.ccx(borrowed, c, target)


def _borrowed_c2swap(qc: QuantumCircuit, a: Qubit, b: Qubit,
                     left: Qubit, right: Qubit, borrowed: Qubit) -> None:
    """Swap two lanes under two controls using one restored dirty lender."""
    lanes = [a, b, left, right, borrowed]
    if len(set(lanes)) != len(lanes):
        raise ValueError("borrowed C2SWAP lanes must be distinct")
    qc.cx(right, left)
    _borrowed_c3x(qc, a, b, left, right, borrowed)
    qc.cx(right, left)


def _dirty_mcswap(
    qc: QuantumCircuit,
    controls: Sequence[Qubit],
    left: Qubit,
    right: Qubit,
    dirty: Sequence[Qubit],
    clean_helper: Optional[Qubit] = None,
) -> None:
    """Swap two lanes under raw controls using restored dirty lenders."""
    controls = list(controls)
    qc.cx(right, left)
    _toggle_raw_controls_dirty(
        qc, controls + [left], right, dirty, clean_helper=clean_helper,
    )
    qc.cx(right, left)


def _mcx_dirty_ladder(qc: QuantumCircuit, controls: Sequence[Qubit],
                      target: Qubit, dirty: Sequence[Qubit],
                      clean_helper: Optional[Qubit] = None) -> None:
    """Toggle ``target`` by all controls, restoring unknown dirty lenders.

    This is the exact ``4*k - 8``-CCX construction used by the Rust KMX
    lowerer in ``arith/mcx.rs``.  The first cascade includes the seed link;
    the second omits it, cancelling every dirty-seeded term while retaining
    the complete control product once.
    """
    k = len(controls)
    if k == 0:
        qc.x(target)
        return
    if k == 1:
        qc.cx(controls[0], target)
        return
    if k == 2:
        qc.ccx(controls[0], controls[1], target)
        return
    if (
        clean_helper is not None
        and clean_helper != target
        and clean_helper not in controls
    ):
        _toggle_one_clean_mcx(qc, controls, target, clean_helper)
        return
    if len(dirty) < k - 2:
        raise ValueError(f"dirty MCX needs {k - 2} lenders, got {len(dirty)}")
    lenders = list(dirty[:k - 2])
    lanes = list(controls) + [target] + lenders
    if len(set(lanes)) != len(lanes):
        raise ValueError("dirty MCX lanes must be distinct")

    def cascade(include_seed: bool) -> None:
        if include_seed:
            qc.ccx(controls[0], controls[1], lenders[0])
        for index in range(1, len(lenders)):
            qc.ccx(lenders[index - 1], controls[index + 1], lenders[index])
        qc.ccx(lenders[-1], controls[k - 1], target)
        for index in range(len(lenders) - 1, 0, -1):
            qc.ccx(lenders[index - 1], controls[index + 1], lenders[index])
        if include_seed:
            qc.ccx(controls[0], controls[1], lenders[0])

    cascade(True)
    cascade(False)


def _dirty_carry_add_raw(
    qc: QuantumCircuit,
    target: Sequence[Qubit],
    addend: Sequence[Qubit],
    carry: Qubit,
) -> None:
    """Map target to target+addend+carry while restoring addend and carry."""
    target = list(target)
    addend = list(addend)
    if len(target) != len(addend):
        raise ValueError("dirty-carry add width mismatch")
    for target_bit, addend_bit in zip(target, addend):
        qc.cx(carry, addend_bit)
        qc.cx(carry, target_bit)
        qc.ccx(target_bit, addend_bit, carry)
    for target_bit, addend_bit in reversed(list(zip(target, addend))):
        qc.ccx(target_bit, addend_bit, carry)
        qc.cx(carry, target_bit)
        qc.cx(addend_bit, target_bit)
        qc.cx(carry, addend_bit)


def _decrement_by_dirty_carry(
    qc: QuantumCircuit,
    target: Sequence[Qubit],
    lenders: Sequence[Qubit],
    carry: Qubit,
    clean_prefix: Sequence[Qubit] = (),
    clean_helper: Optional[Qubit] = None,
) -> None:
    target = list(target)
    if clean_prefix:
        # x - carry = NOT(NOT(x) + carry).  Complementing the register once
        # exposes the same clean-prefix increment kernel and avoids rebuilding
        # each negative-control product independently.
        for lane in target:
            qc.x(lane)
        _increment_by_dirty_carry(
            qc, target, lenders, carry, clean_prefix=clean_prefix,
            clean_helper=clean_helper,
        )
        for lane in target:
            qc.x(lane)
        return
    if clean_helper is not None and len(target) == 9:
        _decrement_by_one_clean_carry_9(qc, target, carry, clean_helper)
        return
    for bit in range(len(target) - 1, -1, -1):
        for lane in target[:bit]:
            qc.x(lane)
        _mcx_dirty_ladder(
            qc, [carry] + target[:bit], target[bit], lenders,
            clean_helper=clean_helper,
        )
        for lane in reversed(target[:bit]):
            qc.x(lane)


def _increment_by_dirty_carry(
    qc: QuantumCircuit,
    target: Sequence[Qubit],
    lenders: Sequence[Qubit],
    carry: Qubit,
    clean_prefix: Sequence[Qubit] = (),
    clean_helper: Optional[Qubit] = None,
) -> None:
    target = list(target)
    prefix_count = min(len(clean_prefix), max(0, len(target) - 1))
    if prefix_count:
        prefix = list(clean_prefix[:prefix_count])
        lanes = [carry] + target + prefix
        if len(set(lanes)) != len(lanes):
            raise ValueError("clean-prefix increment lanes must be distinct")

        # Materialize carry&t[0]&...&t[i] once.  High target bits use the
        # deepest prefix as a shortened dirty-ladder control.  Descending
        # toggles then expose each still-original lower target bit in time to
        # uncompute its prefix lane exactly.
        qc.ccx(carry, target[0], prefix[0])
        for index in range(1, prefix_count):
            qc.ccx(prefix[index - 1], target[index], prefix[index])
        deepest = prefix[-1]
        for bit in range(len(target) - 1, prefix_count, -1):
            _mcx_dirty_ladder(
                qc,
                [deepest] + target[prefix_count:bit],
                target[bit],
                lenders,
            )
        for bit in range(prefix_count, 0, -1):
            qc.cx(prefix[bit - 1], target[bit])
            if bit == 1:
                qc.ccx(carry, target[0], prefix[0])
            else:
                qc.ccx(prefix[bit - 2], target[bit - 1], prefix[bit - 1])
        qc.cx(carry, target[0])
        return
    if clean_helper is not None and len(target) == 9:
        _increment_by_one_clean_carry_9(qc, target, carry, clean_helper)
        return
    for bit in range(len(target) - 1, -1, -1):
        _mcx_dirty_ladder(
            qc, [carry] + target[:bit], target[bit], lenders,
            clean_helper=clean_helper,
        )


def _one_clean_carry_9_ops(
    target: Sequence[Qubit], carry: Qubit, clean_helper: Qubit,
) -> list[tuple[str, tuple[Qubit, ...]]]:
    """Exact 9-bit controlled increment using one restored clean helper.

    This is the width-nine conditionally-clean construction independently
    reconstructed from the public Q819 circuit artifact.  The helper must
    enter in |0>; it is restored to |0>, while ``carry`` is restored for both
    values.  Every primitive is self-inverse, so reversing this list gives the
    exact controlled decrement.
    """
    target = list(target)
    if len(target) != 9:
        raise ValueError("one-clean carry kernel is certified at width nine")
    lanes = [carry] + target + [clean_helper]
    if len(set(lanes)) != len(lanes):
        raise ValueError("one-clean carry lanes must be distinct")
    t0, t1, t2, t3, t4, t5, t6, t7, t8 = target
    h = clean_helper
    return [
        ("ccx", (carry, t0, h)),
        ("ccx", (t1, t2, t0)),
        ("ccx", (t3, t4, t2)),
        ("ccx", (t5, t6, t4)),
        ("x", (t0,)), ("x", (t2,)), ("x", (t4,)),
        ("x", (t3,)), ("x", (t1,)), ("x", (carry,)),
        ("ccx", (t7, t4, t3)),
        ("ccx", (t3, t2, t1)),
        ("ccx", (t1, t0, carry)),
        ("ccx", (h, carry, t8)),
        ("ccx", (t1, t0, carry)),
        ("ccx", (t3, t2, t1)),
        ("ccx", (t7, t4, t3)),
        ("x", (t3,)),
        ("ccx", (t4, t2, t1)),
        ("ccx", (t1, t0, carry)),
        ("ccx", (h, carry, t7)),
        ("ccx", (t1, t0, carry)),
        ("ccx", (t4, t2, t1)),
        ("x", (t4,)),
        ("ccx", (t5, t6, t4)),
        ("ccx", (t5, t2, t1)),
        ("ccx", (t1, t0, carry)),
        ("ccx", (h, carry, t6)),
        ("ccx", (t1, t0, carry)),
        ("ccx", (t5, t2, t1)),
        ("x", (t1,)),
        ("ccx", (t2, t0, carry)),
        ("ccx", (h, carry, t5)),
        ("ccx", (t2, t0, carry)),
        ("x", (t2,)),
        ("ccx", (t3, t4, t2)),
        ("ccx", (t3, t0, carry)),
        ("ccx", (h, carry, t4)),
        ("ccx", (t3, t0, carry)),
        ("x", (carry,)),
        ("ccx", (h, t0, t3)),
        ("x", (t0,)),
        ("ccx", (t1, t2, t0)),
        ("ccx", (h, t1, t2)),
        ("ccx", (carry, t0, h)),
        ("ccx", (carry, t0, t1)),
        ("cx", (carry, t0)),
    ]


def _emit_one_clean_carry_9(
    qc: QuantumCircuit,
    target: Sequence[Qubit],
    carry: Qubit,
    clean_helper: Qubit,
    *,
    inverse: bool,
) -> None:
    ops = _one_clean_carry_9_ops(target, carry, clean_helper)
    if inverse:
        ops = list(reversed(ops))
    for kind, qubits in ops:
        if kind == "x":
            qc.x(qubits[0])
        elif kind == "cx":
            qc.cx(qubits[0], qubits[1])
        else:
            qc.ccx(qubits[0], qubits[1], qubits[2])


def _increment_by_one_clean_carry_9(
    qc: QuantumCircuit,
    target: Sequence[Qubit],
    carry: Qubit,
    clean_helper: Qubit,
) -> None:
    _emit_one_clean_carry_9(
        qc, target, carry, clean_helper, inverse=False,
    )


def _decrement_by_one_clean_carry_9(
    qc: QuantumCircuit,
    target: Sequence[Qubit],
    carry: Qubit,
    clean_helper: Qubit,
) -> None:
    _emit_one_clean_carry_9(
        qc, target, carry, clean_helper, inverse=True,
    )


def _one_clean_mcx_ops(
    controls: Sequence[Qubit], target: Qubit, clean_helper: Qubit,
) -> list[tuple[str, tuple[Qubit, ...]]]:
    """Exact CkX using one clean helper and conditionally-clean controls."""
    controls = list(controls)
    if len(controls) < 3:
        raise ValueError("one-clean MCX kernel requires at least three controls")
    lanes = controls + [target, clean_helper]
    if len(set(lanes)) != len(lanes):
        raise ValueError("one-clean MCX lanes must be distinct")
    ladder = [clean_helper] + controls
    up_ccx: list[tuple[str, tuple[Qubit, ...]]] = []
    up_x: list[tuple[str, tuple[Qubit, ...]]] = []
    for index in range(0, len(ladder) - 2, 2):
        up_ccx.append((
            "ccx", (ladder[index + 1], ladder[index + 2], ladder[index]),
        ))
        if index:
            up_x.append(("x", (ladder[index],)))

    down_ccx: list[tuple[str, tuple[Qubit, ...]]] = []
    down_x: list[tuple[str, tuple[Qubit, ...]]] = []
    if len(ladder) & 1:
        x_index, y_index, target_index = (
            len(ladder) - 3, len(ladder) - 5, len(ladder) - 6,
        )
    else:
        x_index, y_index, target_index = (
            len(ladder) - 1, len(ladder) - 4, len(ladder) - 5,
        )
    if target_index > 0:
        down_ccx.append((
            "ccx",
            (ladder[x_index], ladder[y_index], ladder[target_index]),
        ))
        down_x.append(("x", (ladder[target_index],)))
    for index in range(target_index, 2, -2):
        down_ccx.append((
            "ccx", (ladder[index], ladder[index - 1], ladder[index - 2]),
        ))
        down_x.append(("x", (ladder[index - 2],)))

    forward = up_ccx + up_x + down_x + down_ccx
    second_control = 1 + max(0, 6 - len(ladder))
    middle = [("ccx", (clean_helper, ladder[second_control], target))]
    return forward + middle + list(reversed(forward))


def _one_clean_mcx_9_ops(
    controls: Sequence[Qubit], target: Qubit, clean_helper: Qubit,
) -> list[tuple[str, tuple[Qubit, ...]]]:
    if len(controls) != 9:
        raise ValueError("one-clean MCX wrapper requires nine controls")
    return _one_clean_mcx_ops(controls, target, clean_helper)


def _toggle_one_clean_mcx(
    qc: QuantumCircuit,
    controls: Sequence[Qubit],
    target: Qubit,
    clean_helper: Qubit,
) -> None:
    for kind, qubits in _one_clean_mcx_ops(
        controls, target, clean_helper,
    ):
        if kind == "x":
            qc.x(qubits[0])
        else:
            qc.ccx(qubits[0], qubits[1], qubits[2])


def _toggle_one_clean_mcx_9(
    qc: QuantumCircuit,
    controls: Sequence[Qubit],
    target: Qubit,
    clean_helper: Qubit,
) -> None:
    if len(controls) != 9:
        raise ValueError("one-clean MCX wrapper requires nine controls")
    _toggle_one_clean_mcx(qc, controls, target, clean_helper)


def _add_dirty_carry(
    qc: QuantumCircuit,
    target: Sequence[Qubit],
    addend: Sequence[Qubit],
    carry: Qubit,
    clean_helper: Optional[Qubit] = None,
) -> None:
    _dirty_carry_add_raw(qc, target, addend, carry)
    _decrement_by_dirty_carry(
        qc, target, addend, carry, clean_helper=clean_helper,
    )


def _sub_dirty_carry(
    qc: QuantumCircuit,
    target: Sequence[Qubit],
    addend: Sequence[Qubit],
    carry: Qubit,
    clean_helper: Optional[Qubit] = None,
) -> None:
    for lane in target:
        qc.x(lane)
    _dirty_carry_add_raw(qc, target, addend, carry)
    for lane in target:
        qc.x(lane)
    _increment_by_dirty_carry(
        qc, target, addend, carry, clean_helper=clean_helper,
    )


def _increment_dirty(
    qc: QuantumCircuit,
    register: Sequence[Qubit],
    dirty: Sequence[Qubit],
    clean_helper: Optional[Qubit] = None,
) -> None:
    register = list(register)
    for bit in range(len(register) - 1, 0, -1):
        _mcx_dirty_ladder(
            qc, register[:bit], register[bit], dirty,
            clean_helper=clean_helper,
        )
    qc.x(register[0])


def _decrement_dirty(
    qc: QuantumCircuit,
    register: Sequence[Qubit],
    dirty: Sequence[Qubit],
    clean_helper: Optional[Qubit] = None,
) -> None:
    register = list(register)
    qc.x(register[0])
    for bit in range(1, len(register)):
        _mcx_dirty_ladder(
            qc, register[:bit], register[bit], dirty,
            clean_helper=clean_helper,
        )


def _add_const_dirty(
    qc: QuantumCircuit,
    register: Sequence[Qubit],
    constant: int,
    dirty: Sequence[Qubit],
    clean_helper: Optional[Qubit] = None,
) -> None:
    register = list(register)
    for bit in range(len(register)):
        if (constant >> bit) & 1:
            _increment_dirty(
                qc, register[bit:], dirty, clean_helper=clean_helper,
            )


def _sub_const_dirty(
    qc: QuantumCircuit,
    register: Sequence[Qubit],
    constant: int,
    dirty: Sequence[Qubit],
    clean_helper: Optional[Qubit] = None,
) -> None:
    register = list(register)
    for bit in range(len(register) - 1, -1, -1):
        if (constant >> bit) & 1:
            _decrement_dirty(
                qc, register[bit:], dirty, clean_helper=clean_helper,
            )


def _const_minus_dirty(
    qc: QuantumCircuit,
    register: Sequence[Qubit],
    constant: int,
    dirty: Sequence[Qubit],
    clean_helper: Optional[Qubit] = None,
) -> None:
    """Apply y -> constant-y modulo 2**len(register), exactly involutively."""
    for lane in register:
        qc.x(lane)
    _add_const_dirty(
        qc, register, constant + 1, dirty, clean_helper=clean_helper,
    )


def _toggle_raw_controls_dirty(qc: QuantumCircuit, controls: Sequence[Qubit],
                               target: Qubit, dirty: Sequence[Qubit],
                               clean_helper: Optional[Qubit] = None) -> None:
    """Toggle a target by raw controls, restoring arbitrary dirty lenders."""
    controls = list(controls)
    if target in controls:
        raise ValueError("raw-control target aliases a control")
    if len(controls) == 1:
        qc.cx(controls[0], target)
    elif len(controls) == 2:
        qc.ccx(controls[0], controls[1], target)
    elif (
        clean_helper is not None
        and clean_helper != target
        and clean_helper not in controls
    ):
        _toggle_one_clean_mcx(qc, controls, target, clean_helper)
    elif len(controls) == 3:
        if not dirty:
            raise ValueError("raw C3X needs one dirty lender")
        _borrowed_c3x(
            qc, controls[0], controls[1], controls[2], target, dirty[0],
        )
    else:
        _mcx_dirty_ladder(
            qc, controls, target, dirty, clean_helper=clean_helper,
        )


def _toggle_raw_controls_conditionally_clean(
    qc: QuantumCircuit,
    controls: Sequence[Qubit],
    target: Qubit,
    dirty: Sequence[Qubit],
    clean_helper: Qubit,
) -> None:
    """Toggle by raw controls when helper=0 only on live-control branches.

    ``controls[0]`` is kept out of the one-clean ladder and added to its sole
    target-changing midpoint.  The surrounding ladder is an exact palindrome,
    so an arbitrary helper on inactive branches is restored without touching
    the target.  On live branches the helper is clean and this is the usual
    exact one-clean MCX.
    """
    controls = list(controls)
    if len(controls) < 4:
        raise ValueError("conditional-clean raw MCX needs at least four controls")
    if not dirty:
        raise ValueError("conditional-clean raw MCX needs one dirty lender")
    live_ctrl = controls[0]
    tail = controls[1:]
    ops = _one_clean_mcx_ops(tail, target, clean_helper)
    target_ops = [
        index for index, (_, qubits) in enumerate(ops) if target in qubits
    ]
    if len(target_ops) != 1:
        raise AssertionError("one-clean MCX must have one target midpoint")
    midpoint = target_ops[0]
    for index, (kind, qubits) in enumerate(ops):
        if index == midpoint:
            if kind != "ccx" or qubits[2] != target:
                raise AssertionError("unexpected one-clean MCX midpoint")
            _borrowed_c3x(
                qc, live_ctrl, qubits[0], qubits[1], target, dirty[0],
            )
        elif kind == "x":
            qc.x(qubits[0])
        else:
            qc.ccx(qubits[0], qubits[1], qubits[2])


def _apply_cell_raw_conditionally_clean(
    qc: QuantumCircuit,
    mode: Literal["add", "sub"],
    pass_kind: Literal["first", "second"],
    controls: Sequence[Qubit],
    addend: Qubit,
    target: Qubit,
    carry: Qubit,
    dirty: Sequence[Qubit],
    clean_helper: Qubit,
) -> None:
    controls = list(controls)

    def toggle(extra: Sequence[Qubit], out: Qubit) -> None:
        _toggle_raw_controls_conditionally_clean(
            qc, controls + list(extra), out, dirty, clean_helper,
        )

    def cmaj() -> None:
        toggle([addend], target)
        toggle([addend], carry)
        toggle([carry, target], addend)

    def cuma() -> None:
        toggle([carry, target], addend)
        toggle([addend], carry)
        toggle([carry], target)

    def cmaj_inv() -> None:
        toggle([carry, target], addend)
        toggle([addend], carry)
        toggle([addend], target)

    def cuma_inv() -> None:
        toggle([carry], target)
        toggle([addend], carry)
        toggle([carry, target], addend)

    table = {
        ("add", "first"): cmaj,
        ("add", "second"): cuma,
        ("sub", "first"): cuma_inv,
        ("sub", "second"): cmaj_inv,
    }
    try:
        table[(mode, pass_kind)]()
    except KeyError as exc:
        raise ValueError("bad conditional-clean arithmetic cell mode/pass") from exc


def _apply_cell_borrowed(qc: QuantumCircuit, mode: Literal["add", "sub"],
                         pass_kind: Literal["first", "second"], ctrl: Qubit,
                         addend: Qubit, target: Qubit, carry: Qubit,
                         borrowed: Qubit) -> None:
    def cmaj() -> None:
        qc.ccx(ctrl, addend, target)
        qc.ccx(ctrl, addend, carry)
        _borrowed_c3x(qc, ctrl, carry, target, addend, borrowed)

    def cuma() -> None:
        _borrowed_c3x(qc, ctrl, carry, target, addend, borrowed)
        qc.ccx(ctrl, addend, carry)
        qc.ccx(ctrl, carry, target)

    def cmaj_inv() -> None:
        _borrowed_c3x(qc, ctrl, carry, target, addend, borrowed)
        qc.ccx(ctrl, addend, carry)
        qc.ccx(ctrl, addend, target)

    def cuma_inv() -> None:
        qc.ccx(ctrl, carry, target)
        qc.ccx(ctrl, addend, carry)
        _borrowed_c3x(qc, ctrl, carry, target, addend, borrowed)

    table = {
        ("add", "first"): cmaj,
        ("add", "second"): cuma,
        ("sub", "first"): cuma_inv,
        ("sub", "second"): cmaj_inv,
    }
    try:
        table[(mode, pass_kind)]()
    except KeyError as exc:
        raise ValueError("bad borrowed arithmetic cell mode/pass") from exc


def _apply_cell_raw(
    qc: QuantumCircuit,
    mode: Literal["add", "sub"],
    pass_kind: Literal["first", "second"],
    controls: Sequence[Qubit],
    addend: Qubit,
    target: Qubit,
    carry: Qubit,
    dirty: Sequence[Qubit],
    clean_helper: Optional[Qubit] = None,
) -> None:
    """Arithmetic cell under an unmaterialized equality product."""
    controls = list(controls)

    def toggle(extra: Sequence[Qubit], out: Qubit) -> None:
        _toggle_raw_controls_dirty(
            qc, controls + list(extra), out, dirty,
            clean_helper=clean_helper,
        )

    def cmaj() -> None:
        toggle([addend], target)
        toggle([addend], carry)
        toggle([carry, target], addend)

    def cuma() -> None:
        toggle([carry, target], addend)
        toggle([addend], carry)
        toggle([carry], target)

    def cmaj_inv() -> None:
        toggle([carry, target], addend)
        toggle([addend], carry)
        toggle([addend], target)

    def cuma_inv() -> None:
        toggle([carry], target)
        toggle([addend], carry)
        toggle([carry, target], addend)

    table = {
        ("add", "first"): cmaj,
        ("add", "second"): cuma,
        ("sub", "first"): cuma_inv,
        ("sub", "second"): cmaj_inv,
    }
    try:
        table[(mode, pass_kind)]()
    except KeyError as exc:
        raise ValueError("bad raw arithmetic cell mode/pass") from exc


def _apply_cell_clean_hmr(qc: QuantumCircuit, mode: Literal["add", "sub"],
                          pass_kind: Literal["first", "second"], ctrl: Qubit,
                          addend: Qubit, target: Qubit, carry: Qubit,
                          clean_temp: Qubit) -> None:
    def cmaj() -> None:
        qc.ccx(ctrl, addend, target)
        qc.ccx(ctrl, addend, carry)
        _clean_c3x_mbu(qc, ctrl, carry, target, addend, clean_temp)

    def cuma() -> None:
        _clean_c3x_mbu(qc, ctrl, carry, target, addend, clean_temp)
        qc.ccx(ctrl, addend, carry)
        qc.ccx(ctrl, carry, target)

    def cmaj_inv() -> None:
        _clean_c3x_mbu(qc, ctrl, carry, target, addend, clean_temp)
        qc.ccx(ctrl, addend, carry)
        qc.ccx(ctrl, addend, target)

    def cuma_inv() -> None:
        qc.ccx(ctrl, carry, target)
        qc.ccx(ctrl, addend, carry)
        _clean_c3x_mbu(qc, ctrl, carry, target, addend, clean_temp)

    table = {
        ("add", "first"): cmaj,
        ("add", "second"): cuma,
        ("sub", "first"): cuma_inv,
        ("sub", "second"): cmaj_inv,
    }
    try:
        table[(mode, pass_kind)]()
    except KeyError as exc:
        raise ValueError("bad clean-HMR arithmetic cell mode/pass") from exc


def _apply_r_fused_second_cell_borrowed(
    qc: QuantumCircuit,
    *,
    mode: Qubit,
    ctrl: Qubit,
    addend: Qubit,
    target: Qubit,
    carry: Qubit,
    borrowed: Qubit,
) -> None:
    """Finish R subtraction or undo its first half, selected by ``mode``.

    ``mode=0`` is the normal controlled-MAJ inverse second subtraction cell.
    ``mode=1`` is controlled-UMA, the inverse of the first subtraction cell.
    The two Fredkins restore ``addend`` and ``carry`` for arbitrary basis
    states, including inactive cells and arbitrary borrowed workspace.
    """
    _borrowed_c3x(qc, ctrl, carry, target, addend, borrowed)
    qc.ccx(ctrl, addend, carry)
    _e.cswap_toffoli(qc, mode, addend, carry)
    qc.ccx(ctrl, addend, target)
    _e.cswap_toffoli(qc, mode, addend, carry)


def _apply_r_fused_second_cell_raw(
    qc: QuantumCircuit,
    *,
    mode: Qubit,
    controls: Sequence[Qubit],
    addend: Qubit,
    target: Qubit,
    carry: Qubit,
    dirty: Sequence[Qubit],
    clean_helper: Optional[Qubit] = None,
) -> None:
    """Raw-control form of the fused R second-scan cell."""
    controls = list(controls)
    _toggle_raw_controls_dirty(
        qc, controls + [carry, target], addend, dirty,
        clean_helper=clean_helper,
    )
    _toggle_raw_controls_dirty(
        qc, controls + [addend], carry, dirty,
        clean_helper=clean_helper,
    )
    _e.cswap_toffoli(qc, mode, addend, carry)
    _toggle_raw_controls_dirty(
        qc, controls + [addend], target, dirty,
        clean_helper=clean_helper,
    )
    _e.cswap_toffoli(qc, mode, addend, carry)


def _borrowed_swap_unless_both(
    qc: QuantumCircuit,
    *,
    left_control: Qubit,
    right_control: Qubit,
    left: Qubit,
    right: Qubit,
    borrowed: Qubit,
) -> None:
    """Swap unless both controls are one, restoring an arbitrary lender."""
    qc.cx(right, left)
    qc.cx(left, right)
    qc.cx(right, left)
    _borrowed_c2swap(
        qc, left_control, right_control, left, right, borrowed,
    )


def _apply_r_fused_second_cell_implicit_mode_borrowed(
    qc: QuantumCircuit,
    *,
    phase2: Qubit,
    sign: Qubit,
    ctrl: Qubit,
    addend: Qubit,
    target: Qubit,
    carry: Qubit,
    borrowed: Qubit,
) -> None:
    """Fused R second cell with mode = NOT(phase2 AND sign)."""
    _borrowed_c3x(qc, ctrl, carry, target, addend, borrowed)
    qc.ccx(ctrl, addend, carry)
    _borrowed_swap_unless_both(
        qc, left_control=phase2, right_control=sign,
        left=addend, right=carry, borrowed=borrowed,
    )
    qc.ccx(ctrl, addend, target)
    _borrowed_swap_unless_both(
        qc, left_control=phase2, right_control=sign,
        left=addend, right=carry, borrowed=borrowed,
    )


def _apply_r_fused_second_cell_implicit_mode_conditionally_clean(
    qc: QuantumCircuit,
    *,
    phase2: Qubit,
    sign: Qubit,
    controls: Sequence[Qubit],
    addend: Qubit,
    target: Qubit,
    carry: Qubit,
    dirty: Sequence[Qubit],
    clean_helper: Qubit,
) -> None:
    """Raw-control fused R second cell with an implicit restore mode."""
    controls = list(controls)

    def toggle(extra: Sequence[Qubit], out: Qubit) -> None:
        _toggle_raw_controls_conditionally_clean(
            qc, controls + list(extra), out, dirty, clean_helper,
        )

    toggle([carry, target], addend)
    toggle([addend], carry)
    _borrowed_swap_unless_both(
        qc, left_control=phase2, right_control=sign,
        left=addend, right=carry, borrowed=dirty[0],
    )
    toggle([addend], target)
    _borrowed_swap_unless_both(
        qc, left_control=phase2, right_control=sign,
        left=addend, right=carry, borrowed=dirty[0],
    )


def _apply_r_fused_second_cell_implicit_mode_raw(
    qc: QuantumCircuit,
    *,
    phase2: Qubit,
    sign: Qubit,
    controls: Sequence[Qubit],
    addend: Qubit,
    target: Qubit,
    carry: Qubit,
    dirty: Sequence[Qubit],
) -> None:
    """Dirty-ladder form of the fused R cell with implicit restore mode."""
    controls = list(controls)

    def toggle(extra: Sequence[Qubit], out: Qubit) -> None:
        _toggle_raw_controls_dirty(
            qc, controls + list(extra), out, dirty,
        )

    toggle([carry, target], addend)
    toggle([addend], carry)
    _borrowed_swap_unless_both(
        qc, left_control=phase2, right_control=sign,
        left=addend, right=carry, borrowed=dirty[0],
    )
    toggle([addend], target)
    _borrowed_swap_unless_both(
        qc, left_control=phase2, right_control=sign,
        left=addend, right=carry, borrowed=dirty[0],
    )


def _apply_r_fused_second_cell_clean_hmr(
    qc: QuantumCircuit,
    *,
    mode: Qubit,
    ctrl: Qubit,
    addend: Qubit,
    target: Qubit,
    carry: Qubit,
    clean_temp: Qubit,
) -> None:
    """Finish subtraction or undo its first half with a restored clean lane."""
    _clean_c3x_mbu(qc, ctrl, carry, target, addend, clean_temp)
    qc.ccx(ctrl, addend, carry)
    _e.cswap_toffoli(qc, mode, addend, carry)
    qc.ccx(ctrl, addend, target)
    _e.cswap_toffoli(qc, mode, addend, carry)


def _toggle_live_r_phase2_mode(
    qc: QuantumCircuit,
    *,
    ctrl: Qubit,
    mode: Qubit,
    phase2: Qubit,
    l_q: Sequence[Qubit],
    dirty: Sequence[Qubit],
    inverse: bool = False,
) -> None:
    """Move live-R Phase2 into/out of Mode after the sentinel/T-add map."""
    marker = l_q[LQ_WIDTH - 1]

    def toggle_low_domain() -> None:
        qc.x(marker)
        qc.ccx(ctrl, marker, mode)
        qc.x(marker)

    def toggle_swapped_255() -> None:
        qc.ccx(ctrl, phase2, mode)

    def clear_or_restore_swapped_255_phase() -> None:
        _borrowed_c3x(qc, ctrl, mode, marker, phase2, dirty[0])

    if not inverse:
        toggle_low_domain()
        toggle_swapped_255()
        clear_or_restore_swapped_255_phase()
    else:
        clear_or_restore_swapped_255_phase()
        toggle_swapped_255()
        toggle_low_domain()


@lru_cache(maxsize=None)
def compact_lc_swap_gate(*, k: int, K: int,
                         name: str = "LC_SWAP_COMPACT") -> Gate:
    if k > K:
        raise ValueError("need k <= K")
    M = K - k + 1
    Ctrl = QuantumRegister(1, "Ctrl")
    Direction = QuantumRegister(1, "Direction")
    Sign = QuantumRegister(1, "Sign")
    Work1 = QuantumRegister(M + 1, "Work1")
    l_t = QuantumRegister(LT_WIDTH, "l_t")
    l_q = QuantumRegister(LQ_WIDTH, "l_q")
    Dirty = QuantumRegister(7, "DirtyPassenger")
    depth = _tight_unary_depth_for_labels(list(range(k, K + 1)))
    if depth > 9:
        raise ValueError("one-clean LC swap supports decoder depth at most nine")
    Scratch = QuantumRegister(1, "Scratch")
    qc = _e._block_circuit(
        Ctrl, Direction, Sign, Work1, l_t, l_q, Dirty, Scratch, name=name,
    )
    # Decode all nine quotient bits directly.  The sole clean lane remains the
    # Cuccaro carry and one-clean MCX helper throughout the scan.
    path: list[Qubit] = []
    extension = Dirty[0]
    carry = Scratch[0]
    qc.append(_e.cuccaro_add_mod_2n_no_z_gate(LQ_WIDTH, name="ADD_lt8_to_lq9"),
              list(l_t) + [extension] + list(l_q) + [carry])
    qc.cx(extension, l_q[LQ_WIDTH - 1])
    _add_const_dirty(
        qc, l_q, 3, list(Dirty) + list(Work1[:2]), clean_helper=carry,
    )

    def leaf(j: int, controls: Sequence[Qubit]) -> None:
        # Direction selects exactly one adjacent lane.  Select it into the
        # upper slot, apply one common equality-controlled swap with Sign,
        # then undo the selection.  This is basis-state exact and removes
        # Direction from the expensive raw-control product.
        low = Work1[j - k]
        high = Work1[j - k + 1]
        _e.cswap_toffoli(qc, Direction[0], low, high)
        _dirty_mcswap(
            qc,
            controls,
            Sign[0],
            high,
            Dirty,
            clean_helper=carry,
        )
        _e.cswap_toffoli(qc, Direction[0], low, high)

    unary_iteration_dirty_512raw(
        qc, index_reg=l_q, labels=list(range(k, K + 1)), ctrl=Ctrl[0],
        ancillas=path, leaf_fn=leaf, order="inc",
    )
    _sub_const_dirty(
        qc, l_q, 3, list(Dirty) + list(Work1[:2]), clean_helper=carry,
    )
    qc.cx(extension, l_q[LQ_WIDTH - 1])
    qc.append(_e.cuccaro_sub_mod_2n_no_z_gate(LQ_WIDTH, name="SUB_lt8_from_lq9"),
              list(l_t) + [extension] + list(l_q) + [carry])
    return _e._finalize_block(qc)


@lru_cache(maxsize=None)
def compact_interval_addsub_gate(*, n: int, k: int, K: int,
                                 mode: Literal["add", "sub"], sign_update: bool,
                                 target: Literal["work1", "work2"], name: str) -> Gate:
    if k > K:
        raise ValueError("need k <= K")
    M = K - k + 1
    Ctrl = QuantumRegister(1, "Ctrl")
    Sign = QuantumRegister(1, "Sign")
    Work1 = QuantumRegister(M, "Work1")
    Work2 = QuantumRegister(M, "Work2")
    l_t = QuantumRegister(LT_WIDTH, "l_t")
    l_q = QuantumRegister(LQ_WIDTH, "l_q")
    l_s = QuantumRegister(LS_WIDTH, "l_s")
    Dirty = QuantumRegister(DIRTY_PASSENGER_SIZE, "DirtyPassenger")
    Scratch = QuantumRegister(11, "Scratch")
    qc = _e._block_circuit(Ctrl, Sign, Work1, Work2, l_t, l_q, l_s,
                           Dirty, Scratch, name=name)
    kg_s = list(Scratch[0:3])
    kg_q = list(Scratch[3:6])
    eq_s = Scratch[6]
    eq_q = Scratch[7]
    carry = Scratch[8]
    acc = Scratch[9]
    extension = Scratch[10]
    cell_borrowed = Dirty[9]
    qc.append(_e.cuccaro_add_mod_2n_no_z_gate(LQ_WIDTH, name="ADD_lt8_to_lq9"),
              list(l_t) + [extension] + list(l_q) + [carry])
    affine_scratch = list(Scratch[:8]) + [extension, carry]
    _e.add_const_mod_2n(qc, l_q, 4, affine_scratch)
    _e.const_minus_inplace(qc, l_s, n + 2, affine_scratch)
    # In the modulo-259 encoding ell_s=0 is stored as integer 258.  The
    # affine endpoint reflection first maps that word to 0, whereas the
    # Aux22/v2 signed-sentinel endpoint is physical label 259.  This basis
    # transposition repairs exactly that case and is its own inverse.
    _swap_zero_259_uncontrolled(qc, l_s, extension, list(Scratch[:9]))

    def qpair(j: int) -> tuple[Qubit, Qubit]:
        idx = j - k
        if target == "work1":
            return Work2[idx], Work1[idx]
        if target == "work2":
            return Work1[idx], Work2[idx]
        raise ValueError("bad compact interval target")

    def leaf_first(j: int, sj: Qubit, qj: Qubit) -> None:
        addend, tgt = qpair(j)
        if j < K:
            next_addend, _ = qpair(j + 1)
            _apply_cell_borrowed(
                qc, mode, "first", acc, addend, tgt,
                next_addend, cell_borrowed,
            )
        _apply_cell_borrowed(
            qc, mode, "first", sj, addend, tgt, carry, cell_borrowed,
        )
        qc.cx(sj, acc)
        qc.cx(qj, acc)
        if sign_update:
            qc.ccx(qj, addend, Sign[0])

    dual_unary_iteration_log_star(
        qc, index_a=l_s, index_b=l_q, labels=list(range(k, K + 1)),
        ancillas_a=kg_s, ancillas_b=kg_q, flag_a=eq_s, flag_b=eq_q,
        common_ctrl=Ctrl[0], clean_temp=extension,
        leaf_fn=leaf_first, order="dec",
    )

    def leaf_second(j: int, sj: Qubit, qj: Qubit) -> None:
        addend, tgt = qpair(j)
        qc.cx(qj, acc)
        qc.cx(sj, acc)
        if j < K:
            next_addend, _ = qpair(j + 1)
            _apply_cell_borrowed(
                qc, mode, "second", acc, addend, tgt,
                next_addend, cell_borrowed,
            )
        _apply_cell_borrowed(
            qc, mode, "second", sj, addend, tgt, carry, cell_borrowed,
        )

    dual_unary_iteration_log_star(
        qc, index_a=l_s, index_b=l_q, labels=list(range(k, K + 1)),
        ancillas_a=kg_s, ancillas_b=kg_q, flag_a=eq_s, flag_b=eq_q,
        common_ctrl=Ctrl[0], clean_temp=extension,
        leaf_fn=leaf_second, order="inc",
    )
    _swap_zero_259_uncontrolled(qc, l_s, extension, list(Scratch[:9]))
    _e.const_minus_inplace(qc, l_s, n + 2, affine_scratch)
    _e.sub_const_mod_2n(qc, l_q, 4, affine_scratch)
    qc.append(_e.cuccaro_sub_mod_2n_no_z_gate(LQ_WIDTH, name="SUB_lt8_from_lq9"),
              list(l_t) + [extension] + list(l_q) + [carry])
    return _e._finalize_block(qc)


@lru_cache(maxsize=None)
def compact_r_subrestore_fused_gate(*, n: int, k: int, K: int,
                                    name: str = "R_SUBRESTORE_FUSED") -> Gate:
    """Two-scan exact R block with a phase-derived clean accumulator.

    The caller maps the live original Phase2 value into Mode and clears Phase2.
    Phase2 can therefore replace the eliminated equality-accumulator Aux lane.
    Mode remains the original phase bit across both scans, so the trusted
    implicit restore predicate is unchanged.  A controlled sentinel swap plus
    compensated ninth affine source preserves the exact original l_q index.
    """
    if k > K:
        raise ValueError("need k <= K")
    M = K - k + 1
    Ctrl = QuantumRegister(1, "Ctrl")
    Phase2 = QuantumRegister(1, "Phase2")
    Mode = QuantumRegister(1, "Mode")
    Sign = QuantumRegister(1, "Sign")
    Work1 = QuantumRegister(M, "Work1")
    Work2 = QuantumRegister(M, "Work2")
    l_t = QuantumRegister(LT_WIDTH, "l_t")
    l_q = QuantumRegister(LQ_WIDTH, "l_q")
    l_s = QuantumRegister(LS_WIDTH, "l_s")
    Dirty = QuantumRegister(DIRTY_PASSENGER_SIZE, "DirtyPassenger")
    Scratch = QuantumRegister(1 + TIGHT_ANC_SIZE, "Scratch")
    qc = _e._block_circuit(
        Ctrl, Phase2, Mode, Sign, Work1, Work2, l_t, l_q, l_s,
        Dirty, Scratch, name=name,
    )
    carry = Scratch[0]
    kg_s = list(Scratch[1:4])
    kg_q = list(Scratch[4:7])
    eq_s = Scratch[7]
    eq_q = Scratch[8]
    acc = Phase2[0]
    affine_helper = acc
    extension = acc
    affine_addend = list(l_t) + [Mode[0]]

    # The outer phase loan swaps physical phase-B l_q labels 255 and 511.
    # Mode is the original live Phase2 bit, so this restores the trusted label
    # without touching inactive phase-C/D branches.
    marker = l_q[LQ_WIDTH - 1]
    _toggle_raw_controls_dirty(
        qc, [Ctrl[0], Mode[0]] + list(l_q[: LQ_WIDTH - 1]), marker, Dirty,
    )

    # Adding Mode as bit eight and then XORing bit eight cancels exactly modulo
    # 512.  It supplies an implicit zero extension while Mode remains live.
    _add_dirty_carry(
        qc, l_q, affine_addend, Dirty[9], clean_helper=affine_helper,
    )
    qc.cx(Mode[0], marker)
    _add_const_dirty(qc, l_q, 4, Dirty, clean_helper=affine_helper)
    _const_minus_dirty(qc, l_s, n + 2, Dirty, clean_helper=affine_helper)
    _swap_zero_259_uncontrolled_dirty(
        qc, l_s, extension, Dirty,
    )

    # On every live R branch the transformed quotient boundary is in 3..258.
    # Fold 256..258 onto the otherwise unreachable low codes 0..2, then store
    # the incoming borrowed-carry value in bit eight and clear the carry.  The
    # paired decoder below interprets the low byte modulo 256 and never treats
    # semantic label 2 as a quotient endpoint.  Inactive branches are untouched.
    def toggle_live_high_boundary_codes() -> None:
        for low_code in range(3):
            inverted = []
            for bit, lane in enumerate(l_q[:8]):
                if ((low_code >> bit) & 1) == 0:
                    qc.x(lane)
                    inverted.append(lane)
            _toggle_raw_controls_dirty(
                qc, [Ctrl[0]] + list(l_q[:8]), marker, Dirty,
            )
            for lane in reversed(inverted):
                qc.x(lane)

    toggle_live_high_boundary_codes()
    qc.ccx(Ctrl[0], carry, marker)
    qc.ccx(Ctrl[0], marker, carry)

    def qpair(j: int) -> tuple[Qubit, Qubit]:
        idx = j - k
        return Work2[idx], Work1[idx]

    def leaf_first(
        j: int,
        fa: Optional[Qubit],
        fb: Optional[Qubit],
    ) -> None:
        addend, target = qpair(j)
        if j < K:
            next_addend, _ = qpair(j + 1)
            _apply_cell_borrowed(
                qc, "sub", "first", acc, addend, target,
                next_addend, Dirty[0],
            )
        _apply_cell_raw(
            qc, "sub", "first", [fa], addend, target, carry, Dirty,
        )
        qc.cx(fa, acc)
        if fb is not None:
            qc.cx(fb, acc)
            qc.ccx(fb, addend, Sign[0])

    dual_unary_iteration_log_star_lqmod256(
        qc, index_a=l_s, index_b=l_q[:8], labels=list(range(k, K + 1)),
        ancillas_a=kg_s, ancillas_b=kg_q, flag_a=eq_s, flag_b=eq_q,
        common_ctrl=Ctrl[0],
        borrowed_temp=Dirty[1],
        leaf_fn=leaf_first, order="dec",
    )

    # This is the exact trusted historical update.  Mode is original Phase2.
    qc.ccx(Ctrl[0], Mode[0], Sign[0])

    def leaf_second(
        j: int,
        fa: Optional[Qubit],
        fb: Optional[Qubit],
    ) -> None:
        addend, target = qpair(j)
        if fb is not None:
            qc.cx(fb, acc)
        qc.cx(fa, acc)
        if j < K:
            next_addend, _ = qpair(j + 1)
            _apply_r_fused_second_cell_implicit_mode_borrowed(
                qc, phase2=Mode[0], sign=Sign[0], ctrl=acc,
                addend=addend, target=target, carry=next_addend,
                borrowed=Dirty[0],
            )
        _apply_r_fused_second_cell_implicit_mode_raw(
            qc, phase2=Mode[0], sign=Sign[0], controls=[fa],
            addend=addend,
            target=target, carry=carry, dirty=Dirty,
        )

    dual_unary_iteration_log_star_lqmod256(
        qc, index_a=l_s, index_b=l_q[:8], labels=list(range(k, K + 1)),
        ancillas_a=kg_s, ancillas_b=kg_q, flag_a=eq_s, flag_b=eq_q,
        common_ctrl=Ctrl[0],
        borrowed_temp=Dirty[1],
        leaf_fn=leaf_second, order="inc",
    )

    qc.ccx(Ctrl[0], marker, carry)
    qc.ccx(Ctrl[0], carry, marker)
    toggle_live_high_boundary_codes()

    _swap_zero_259_uncontrolled_dirty(
        qc, l_s, extension, Dirty,
    )
    _const_minus_dirty(qc, l_s, n + 2, Dirty, clean_helper=affine_helper)
    _sub_const_dirty(qc, l_q, 4, Dirty, clean_helper=affine_helper)
    qc.cx(Mode[0], marker)
    _sub_dirty_carry(
        qc, l_q, affine_addend, Dirty[9], clean_helper=affine_helper,
    )

    _toggle_raw_controls_dirty(
        qc, [Ctrl[0], Mode[0]] + list(l_q[: LQ_WIDTH - 1]), marker, Dirty,
    )
    return _e._finalize_block(qc)


@lru_cache(maxsize=None)
def compact_prefix_addsub_gate(*, k: int, K: int,
                               mode: Literal["add", "sub"], sign_update: bool,
                               capture_borrow_sign: bool,
                               target: Literal["work1", "work2"], name: str) -> Gate:
    if k > K:
        raise ValueError("need k <= K")
    if k != 1 or K > 257:
        raise ValueError("compact T prefix is certified for physical labels 1..257")
    if sign_update:
        raise ValueError("compact T prefix sign update must use selected midpoint capture")
    if capture_borrow_sign:
        raise ValueError("compact T prefix retained-tail mode is not used by this route")
    M = K - k + 1
    Ctrl = QuantumRegister(1, "Ctrl")
    Sign = QuantumRegister(1, "Sign")
    Work1 = QuantumRegister(M, "Work1")
    Work2 = QuantumRegister(M, "Work2")
    l_t = QuantumRegister(LT_WIDTH, "l_t")
    Borrowed = QuantumRegister(5, "Borrowed")
    # l_t is stored as truth-minus-one.  Keep it unmodified and decode
    # residues x=0..K-2 as physical cells j=x+2.  Physical cell 1 is the
    # unconditional lower boundary and is emitted explicitly.
    encoded_labels = list(range(0, K - 1))
    depth = _tight_unary_depth_for_labels(encoded_labels)
    Scratch = QuantumRegister(2 + depth, "Scratch")
    qc = _e._block_circuit(Ctrl, Sign, Work1, Work2, l_t,
                           Borrowed, Scratch, name=name)
    path: list[Qubit] = list(Scratch[2:2 + depth])
    carry = Scratch[0]
    acc = Scratch[1]

    def qpair(j: int) -> tuple[Qubit, Qubit]:
        idx = j - k
        if target == "work1":
            return Work2[idx], Work1[idx]
        if target == "work2":
            return Work1[idx], Work2[idx]
        raise ValueError("bad compact prefix target")

    def leaf_first(encoded: int, ej: Qubit) -> None:
        j = encoded + 2
        addend, tgt = qpair(j)
        previous_addend, _ = qpair(j - 1)
        _apply_cell_borrowed(
            qc, mode, "first", acc, addend, tgt,
            previous_addend, Borrowed[0],
        )

    qc.cx(Ctrl[0], acc)
    addend1, tgt1 = qpair(1)
    _apply_cell_borrowed(
        qc, mode, "first", Ctrl[0], addend1, tgt1, carry, Borrowed[0],
    )
    if encoded_labels:
        unary_range_iteration_tight_dropin(
            qc, index_reg=l_t, labels=encoded_labels, ctrl=Ctrl[0],
            range_acc=acc, ancillas=path,
            borrowed=[carry, Sign[0]] + list(Borrowed),
            leaf_fn=leaf_first, order="inc",
            toggle_before_leaf=False,
        )

    def leaf_second(encoded: int, ej: Qubit) -> None:
        j = encoded + 2
        addend, tgt = qpair(j)
        previous_addend, _ = qpair(j - 1)
        _apply_cell_borrowed(
            qc, mode, "second", acc, addend, tgt,
            previous_addend, Borrowed[0],
        )

    if encoded_labels:
        unary_range_iteration_tight_dropin(
            qc, index_reg=l_t, labels=encoded_labels, ctrl=Ctrl[0],
            range_acc=acc, ancillas=path,
            borrowed=[carry, Sign[0]] + list(Borrowed),
            leaf_fn=leaf_second, order="dec",
            toggle_before_leaf=True,
        )
    _apply_cell_borrowed(
        qc, mode, "second", Ctrl[0], addend1, tgt1, carry, Borrowed[0],
    )
    qc.cx(Ctrl[0], acc)
    return _e._finalize_block(qc)


def _apply_not_factor_with_borrowed(qc: QuantumCircuit, *, boundary_control: Qubit,
                                    data_bit: Qubit, neighbor: Optional[Qubit],
                                    target: Qubit, borrowed: Qubit) -> None:
    """Apply X or neighbor-controlled X under NOT(boundary_control & data_bit)."""
    if neighbor is None:
        qc.x(target)
        qc.cx(borrowed, target)
        qc.ccx(boundary_control, data_bit, borrowed)
        qc.cx(borrowed, target)
        qc.ccx(boundary_control, data_bit, borrowed)
    else:
        qc.cx(neighbor, target)
        qc.ccx(borrowed, neighbor, target)
        qc.ccx(boundary_control, data_bit, borrowed)
        qc.ccx(borrowed, neighbor, target)
        qc.ccx(boundary_control, data_bit, borrowed)


def _apply_not_factor_with_clean(qc: QuantumCircuit, *, boundary_control: Qubit,
                                 data_bit: Qubit, neighbor: Optional[Qubit],
                                 target: Qubit, clean_temp: Qubit) -> None:
    """Apply the upper-zero factor with one clean, phase-clean HMR lane."""
    if neighbor is None:
        qc.x(target)
        qc.ccx(boundary_control, data_bit, target)
    else:
        qc.cx(neighbor, target)
        _dirty_c3x(
            qc, boundary_control, data_bit, neighbor, target, clean_temp,
        )


def _apply_not_factor_with_conditional_zero(
    qc: QuantumCircuit,
    *,
    boundary_control: Qubit,
    data_bit: Qubit,
    neighbor: Optional[Qubit],
    target: Qubit,
    conditional_zero: Qubit,
) -> None:
    """Upper-zero factor when helper=0 on boundary_control=1 branches.

    Placing ``boundary_control`` on the final Toffoli makes the arbitrary
    helper value irrelevant when the boundary is zero.  On the active branch
    the promised zero helper gives the exact three-Toffoli control product;
    the two outer Toffolis restore it with no measurement or phase contract.
    """
    if neighbor is None:
        qc.x(target)
        qc.ccx(boundary_control, data_bit, target)
    else:
        qc.cx(neighbor, target)
        qc.ccx(data_bit, neighbor, conditional_zero)
        qc.ccx(boundary_control, conditional_zero, target)
        qc.ccx(data_bit, neighbor, conditional_zero)


def _toggle_four_controls_conditional_zero(
    qc: QuantumCircuit,
    *,
    controls: Sequence[Qubit],
    target: Qubit,
    conditional_zero: Qubit,
    borrowed: Qubit,
) -> None:
    """Exact C4X using a helper that is zero whenever controls[0] is one."""
    controls = list(controls)
    if len(controls) != 4:
        raise ValueError("conditional-zero toggle requires four controls")
    guard, left, right, final = controls
    lanes = controls + [target, conditional_zero, borrowed]
    if len(set(lanes)) != len(lanes):
        raise ValueError("conditional-zero C4X lanes must be distinct")
    # If guard=1, conditional_zero starts at zero and receives left&right.
    # If guard=0 its arbitrary entry value cannot reach target.  The exact
    # borrowed C3X and closing Toffoli restore both workspace lanes.
    qc.ccx(left, right, conditional_zero)
    _borrowed_c3x(
        qc, guard, final, conditional_zero, target, borrowed,
    )
    qc.ccx(left, right, conditional_zero)


def _range_scan_tight(qc: QuantumCircuit, *, leq: bool,
                      boundary: Sequence[Qubit], k: int, K: int,
                      ctrl: Qubit, range_acc: Qubit,
                      path: Sequence[Qubit], leaf_fn,
                      order: Literal["inc", "dec"]) -> None:
    labels = list(range(k, K + 1))
    if leq and order == "inc":
        qc.cx(ctrl, range_acc)
        def wrapped(j: int, ej: Qubit) -> None:
            leaf_fn(j, range_acc)
            qc.cx(ej, range_acc)
        unary_iteration_tight(qc, index_reg=boundary, labels=labels, ctrl=ctrl,
                              ancillas=path, leaf_fn=wrapped, order=order)
    elif leq and order == "dec":
        def wrapped(j: int, ej: Qubit) -> None:
            qc.cx(ej, range_acc)
            leaf_fn(j, range_acc)
        unary_iteration_tight(qc, index_reg=boundary, labels=labels, ctrl=ctrl,
                              ancillas=path, leaf_fn=wrapped, order=order)
        qc.cx(ctrl, range_acc)
    elif not leq and order == "inc":
        def wrapped(j: int, ej: Qubit) -> None:
            qc.cx(ej, range_acc)
            leaf_fn(j, range_acc)
        unary_iteration_tight(qc, index_reg=boundary, labels=labels, ctrl=ctrl,
                              ancillas=path, leaf_fn=wrapped, order=order)
        qc.cx(ctrl, range_acc)
    elif not leq and order == "dec":
        qc.cx(ctrl, range_acc)
        def wrapped(j: int, ej: Qubit) -> None:
            leaf_fn(j, range_acc)
            qc.cx(ej, range_acc)
        unary_iteration_tight(qc, index_reg=boundary, labels=labels, ctrl=ctrl,
                              ancillas=path, leaf_fn=wrapped, order=order)
    else:
        raise ValueError("bad tight range-scan order")


def _range_scan_tight_direct(qc: QuantumCircuit, *, leq: bool,
                             boundary: Sequence[Qubit], k: int, K: int,
                             ctrl: Qubit, scratch: Sequence[Qubit], leaf_fn,
                             order: Literal["inc", "dec"]) -> None:
    """Tight inclusive range scan using one fewer clean decoder lane."""
    labels = list(range(k, K + 1))
    depth = _tight_unary_depth_for_labels(labels)
    path_depth = max(0, depth - 1)
    required = path_depth + 1
    if len(scratch) < required:
        raise ValueError(
            f"direct tight range scan needs {required} lanes, got {len(scratch)}"
        )
    path = list(scratch[:path_depth])
    range_acc = scratch[path_depth]

    def scan(*, toggle_before_leaf: bool) -> None:
        unary_range_iteration_direct_leaf(
            qc,
            index_reg=boundary,
            labels=labels,
            ctrl=ctrl,
            range_acc=range_acc,
            ancillas=path,
            leaf_fn=leaf_fn,
            order=order,
            toggle_before_leaf=toggle_before_leaf,
        )

    if leq and order == "inc":
        qc.cx(ctrl, range_acc)
        scan(toggle_before_leaf=False)
    elif leq and order == "dec":
        scan(toggle_before_leaf=True)
        qc.cx(ctrl, range_acc)
    elif not leq and order == "inc":
        scan(toggle_before_leaf=True)
        qc.cx(ctrl, range_acc)
    elif not leq and order == "dec":
        qc.cx(ctrl, range_acc)
        scan(toggle_before_leaf=False)
    else:
        raise ValueError("bad direct tight range-scan order")


def _range_scan_tight_dirty_quartet(
    qc: QuantumCircuit,
    *,
    leq: bool,
    boundary: Sequence[Qubit],
    k: int,
    K: int,
    ctrl: Qubit,
    scratch: Sequence[Qubit],
    borrowed: Qubit,
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Tight inclusive range scan with at most eight clean lanes."""
    labels = list(range(k, K + 1))
    depth = _tight_unary_depth_for_labels(labels)
    path_depth = max(0, depth - 2)
    required = path_depth + 1
    if len(scratch) < required:
        raise ValueError(
            f"dirty-quartet tight range scan needs {required} lanes, "
            f"got {len(scratch)}"
        )
    path = list(scratch[:path_depth])
    range_acc = scratch[path_depth]

    def scan(*, toggle_before_leaf: bool) -> None:
        unary_range_iteration_dirty_quartet(
            qc,
            index_reg=boundary,
            labels=labels,
            ctrl=ctrl,
            range_acc=range_acc,
            ancillas=path,
            borrowed=borrowed,
            leaf_fn=leaf_fn,
            order=order,
            toggle_before_leaf=toggle_before_leaf,
        )

    if leq and order == "inc":
        qc.cx(ctrl, range_acc)
        scan(toggle_before_leaf=False)
    elif leq and order == "dec":
        scan(toggle_before_leaf=True)
        qc.cx(ctrl, range_acc)
    elif not leq and order == "inc":
        scan(toggle_before_leaf=True)
        qc.cx(ctrl, range_acc)
    elif not leq and order == "dec":
        qc.cx(ctrl, range_acc)
        scan(toggle_before_leaf=False)
    else:
        raise ValueError("bad dirty-quartet tight range-scan order")


def _range_scan_tight_dirty_octet(
    qc: QuantumCircuit,
    *,
    leq: bool,
    boundary: Sequence[Qubit],
    k: int,
    K: int,
    ctrl: Qubit,
    scratch: Sequence[Qubit],
    borrowed: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"],
    equality_guards: Sequence[Qubit] = (),
) -> None:
    """Tight inclusive range scan with one fewer clean path lane."""
    labels = list(range(k, K + 1))
    depth = _tight_unary_depth_for_labels(labels)
    path_depth = max(0, depth - 3)
    required = path_depth + 1
    if len(scratch) < required:
        raise ValueError(
            f"dirty-octet tight range scan needs {required} lanes, "
            f"got {len(scratch)}"
        )
    path = list(scratch[:path_depth])
    range_acc = scratch[path_depth]

    def scan(*, toggle_before_leaf: bool) -> None:
        unary_range_iteration_dirty_octet(
            qc,
            index_reg=boundary,
            labels=labels,
            ctrl=ctrl,
            range_acc=range_acc,
            ancillas=path,
            borrowed=borrowed,
            leaf_fn=leaf_fn,
            order=order,
            toggle_before_leaf=toggle_before_leaf,
            equality_guards=equality_guards,
        )

    if leq and order == "inc":
        qc.cx(ctrl, range_acc)
        scan(toggle_before_leaf=False)
    elif leq and order == "dec":
        scan(toggle_before_leaf=True)
        qc.cx(ctrl, range_acc)
    elif not leq and order == "inc":
        scan(toggle_before_leaf=True)
        qc.cx(ctrl, range_acc)
    elif not leq and order == "dec":
        qc.cx(ctrl, range_acc)
        scan(toggle_before_leaf=False)
    else:
        raise ValueError("bad dirty-octet tight range-scan order")


def _range_scan_tight_dirty_hexadecet(
    qc: QuantumCircuit,
    *,
    leq: bool,
    boundary: Sequence[Qubit],
    k: int,
    K: int,
    ctrl: Qubit,
    scratch: Sequence[Qubit],
    borrowed: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Tight inclusive range scan with four raw endpoint controls."""
    labels = list(range(k, K + 1))
    depth = _tight_unary_depth_for_labels(labels)
    path_depth = max(0, depth - 4)
    required = path_depth + 1
    if len(scratch) < required:
        raise ValueError(
            f"dirty-hexadecet tight range scan needs {required} lanes, "
            f"got {len(scratch)}"
        )
    path = list(scratch[:path_depth])
    range_acc = scratch[path_depth]

    def scan(*, toggle_before_leaf: bool) -> None:
        unary_range_iteration_dirty_hexadecet(
            qc,
            index_reg=boundary,
            labels=labels,
            ctrl=ctrl,
            range_acc=range_acc,
            ancillas=path,
            borrowed=borrowed,
            leaf_fn=leaf_fn,
            order=order,
            toggle_before_leaf=toggle_before_leaf,
        )

    if leq and order == "inc":
        qc.cx(ctrl, range_acc)
        scan(toggle_before_leaf=False)
    elif leq and order == "dec":
        scan(toggle_before_leaf=True)
        qc.cx(ctrl, range_acc)
    elif not leq and order == "inc":
        scan(toggle_before_leaf=True)
        qc.cx(ctrl, range_acc)
    elif not leq and order == "dec":
        qc.cx(ctrl, range_acc)
        scan(toggle_before_leaf=False)
    else:
        raise ValueError("bad dirty-hexadecet tight range-scan order")


def _range_scan_tight_dirty_32raw(
    qc: QuantumCircuit,
    *,
    leq: bool,
    boundary: Sequence[Qubit],
    k: int,
    K: int,
    ctrl: Qubit,
    scratch: Sequence[Qubit],
    borrowed: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Tight inclusive range scan with five raw endpoint controls."""
    labels = list(range(k, K + 1))
    depth = _tight_unary_depth_for_labels(labels)
    path_depth = max(0, depth - 5)
    required = path_depth + 1
    if len(scratch) < required:
        raise ValueError(
            f"dirty-32raw tight range scan needs {required} lanes, "
            f"got {len(scratch)}"
        )
    path = list(scratch[:path_depth])
    range_acc = scratch[path_depth]

    def scan(*, toggle_before_leaf: bool) -> None:
        unary_range_iteration_dirty_32raw(
            qc,
            index_reg=boundary,
            labels=labels,
            ctrl=ctrl,
            range_acc=range_acc,
            ancillas=path,
            borrowed=borrowed,
            leaf_fn=leaf_fn,
            order=order,
            toggle_before_leaf=toggle_before_leaf,
        )

    if leq and order == "inc":
        qc.cx(ctrl, range_acc)
        scan(toggle_before_leaf=False)
    elif leq and order == "dec":
        scan(toggle_before_leaf=True)
        qc.cx(ctrl, range_acc)
    elif not leq and order == "inc":
        scan(toggle_before_leaf=True)
        qc.cx(ctrl, range_acc)
    elif not leq and order == "dec":
        qc.cx(ctrl, range_acc)
        scan(toggle_before_leaf=False)
    else:
        raise ValueError("bad dirty-32raw tight range-scan order")


def _range_scan_tight_dirty_64raw(
    qc: QuantumCircuit,
    *,
    leq: bool,
    boundary: Sequence[Qubit],
    k: int,
    K: int,
    ctrl: Qubit,
    scratch: Sequence[Qubit],
    borrowed: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Tight inclusive range scan with six raw endpoint controls."""
    labels = list(range(k, K + 1))
    depth = _tight_unary_depth_for_labels(labels)
    path_depth = max(0, depth - 6)
    required = path_depth + 1
    if len(scratch) < required:
        raise ValueError(
            f"dirty-64raw tight range scan needs {required} lanes, "
            f"got {len(scratch)}"
        )
    path = list(scratch[:path_depth])
    range_acc = scratch[path_depth]

    def scan(*, toggle_before_leaf: bool) -> None:
        unary_range_iteration_dirty_64raw(
            qc,
            index_reg=boundary,
            labels=labels,
            ctrl=ctrl,
            range_acc=range_acc,
            ancillas=path,
            borrowed=borrowed,
            leaf_fn=leaf_fn,
            order=order,
            toggle_before_leaf=toggle_before_leaf,
        )

    if leq and order == "inc":
        qc.cx(ctrl, range_acc)
        scan(toggle_before_leaf=False)
    elif leq and order == "dec":
        scan(toggle_before_leaf=True)
        qc.cx(ctrl, range_acc)
    elif not leq and order == "inc":
        scan(toggle_before_leaf=True)
        qc.cx(ctrl, range_acc)
    elif not leq and order == "dec":
        qc.cx(ctrl, range_acc)
        scan(toggle_before_leaf=False)
    else:
        raise ValueError("bad dirty-64raw tight range-scan order")


def _range_scan_tight_dirty_256raw(
    qc: QuantumCircuit,
    *,
    leq: bool,
    boundary: Sequence[Qubit],
    k: int,
    K: int,
    ctrl: Qubit,
    scratch: Sequence[Qubit],
    borrowed: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Certified-window nine-bit scan with eight raw endpoint controls.

    A 259-label terminal window has decoder depth nine.  Exposing the final
    eight endpoint bits directly leaves only one path lane plus the restored
    range accumulator, so the scan fits the two-clean Q813 terminal budget.
    As with the surrounding active-window construction, live boundaries are
    required to lie in the pinned per-step interval; the control-off action is
    identity on the complete physical endpoint domain.
    """
    labels = list(range(k, K + 1))
    depth = _tight_unary_depth_for_labels(labels)
    path_depth = max(0, depth - 8)
    required = path_depth + 1
    if len(scratch) < required:
        raise ValueError(
            f"dirty-256raw tight range scan needs {required} lanes, "
            f"got {len(scratch)}"
        )
    path = list(scratch[:path_depth])
    range_acc = scratch[path_depth]

    def scan(*, toggle_before_leaf: bool) -> None:
        unary_range_iteration_dirty_256raw(
            qc,
            index_reg=boundary,
            labels=labels,
            ctrl=ctrl,
            range_acc=range_acc,
            ancillas=path,
            borrowed=borrowed,
            leaf_fn=leaf_fn,
            order=order,
            toggle_before_leaf=toggle_before_leaf,
        )

    if leq and order == "inc":
        qc.cx(ctrl, range_acc)
        scan(toggle_before_leaf=False)
    elif leq and order == "dec":
        scan(toggle_before_leaf=True)
        qc.cx(ctrl, range_acc)
    elif not leq and order == "inc":
        scan(toggle_before_leaf=True)
        qc.cx(ctrl, range_acc)
    elif not leq and order == "dec":
        qc.cx(ctrl, range_acc)
        scan(toggle_before_leaf=False)
    else:
        raise ValueError("bad dirty-256raw tight range-scan order")


def _low256_range_scan_conditioned_hmr(qc: QuantumCircuit, *,
                                       index_reg: Sequence[Qubit], ctrl: Qubit,
                                       range_acc: Qubit,
                                       ancillas: Sequence[Qubit], leaf_fn,
                                       order: Literal["inc", "dec"]) -> None:
    """Scan labels 0..255 while retaining one clean HMR lane.

    The last decoder bit is applied directly to ``range_acc`` instead of
    being materialized.  This has the same two-Toffoli cost per label pair as
    compute/toggle/uncompute, but it shortens the live decoder path by one.
    The freed lane lowers every upper-zero C3X from the exact dirty four-T
    construction to the phase-clean two-T HMR construction.
    """
    if len(index_reg) != LS_WIDTH:
        raise ValueError("conditioned low decoder requires a 9-bit index")
    if len(ancillas) < 8:
        raise ValueError("conditioned low decoder requires eight clean lanes")
    path = list(ancillas[:7])
    clean_temp = ancillas[7]
    high = index_reg[8]
    bit7 = index_reg[7]
    root = path[0]

    qc.x(high)
    qc.x(bit7)
    _dirty_c3x(qc, ctrl, high, bit7, root, clean_temp)
    qc.x(bit7)
    qc.x(high)

    def rec(labels: Sequence[int], g: Qubit, depth: int) -> None:
        labels = list(labels)
        if len(labels) == 2:
            low_label, high_label = sorted(labels)
            bit = _e._split_bit(labels)

            def toggle_equality(label: int) -> None:
                if ((label >> bit) & 1) == 0:
                    qc.x(index_reg[bit])
                qc.ccx(g, index_reg[bit], range_acc)
                if ((label >> bit) & 1) == 0:
                    qc.x(index_reg[bit])

            if order == "inc":
                leaf_fn(low_label, range_acc, clean_temp)
                toggle_equality(low_label)
                leaf_fn(high_label, range_acc, clean_temp)
                toggle_equality(high_label)
            else:
                toggle_equality(high_label)
                leaf_fn(high_label, range_acc, clean_temp)
                toggle_equality(low_label)
                leaf_fn(low_label, range_acc, clean_temp)
            return
        bit = _e._split_bit(labels)
        zero = [label for label in labels if ((label >> bit) & 1) == 0]
        one = [label for label in labels if ((label >> bit) & 1) == 1]
        h = path[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    low = list(range(0, 128))
    high_labels = list(range(128, 256))

    def toggle_root_branch() -> None:
        qc.x(high)
        qc.ccx(ctrl, high, root)
        qc.x(high)

    if order == "inc":
        rec(low, root, 1)
        toggle_root_branch()
        rec(high_labels, root, 1)
        toggle_root_branch()
    else:
        toggle_root_branch()
        rec(high_labels, root, 1)
        toggle_root_branch()
        rec(low, root, 1)

    qc.x(high)
    qc.x(bit7)
    _dirty_c3x(qc, ctrl, high, bit7, root, clean_temp)
    qc.x(bit7)
    qc.x(high)


def _top3_range_scan_valid259(qc: QuantumCircuit, *,
                              index_reg: Sequence[Qubit], ctrl: Qubit,
                              range_acc: Qubit,
                              ancillas: Sequence[Qubit], leaf_fn,
                              order: Literal["inc", "dec"]) -> None:
    """Scan 256..258 on the promised modulo-259 endpoint domain."""
    if len(index_reg) != LS_WIDTH:
        raise ValueError("top decoder requires a 9-bit index")
    if len(ancillas) < 4:
        raise ValueError("top decoder requires four clean lanes")
    top = ancillas[0]
    path = list(ancillas[1:3])
    clean_temp = ancillas[3]
    qc.ccx(ctrl, index_reg[8], top)

    def wrapped(encoded: int, equality: Qubit) -> None:
        label = encoded + 256
        if order == "inc":
            leaf_fn(label, range_acc, clean_temp)
            qc.cx(equality, range_acc)
        else:
            qc.cx(equality, range_acc)
            leaf_fn(label, range_acc, clean_temp)

    # On 0..258, high=1 implies bits 2..7 are zero and bits 0..1 encode 0..2.
    unary_iteration_tight(
        qc, index_reg=index_reg[:2], labels=[0, 1, 2], ctrl=top,
        ancillas=path, leaf_fn=wrapped, order=order,
    )
    qc.ccx(ctrl, index_reg[8], top)


def _range_scan_259_nine(qc: QuantumCircuit, *,
                         boundary: Sequence[Qubit], ctrl: Qubit,
                         range_acc: Qubit, path: Sequence[Qubit],
                         leaf_fn, order: Literal["inc", "dec"]) -> None:
    """Run the inclusive 0..boundary range scan with nine clean lanes.

    The low 256 labels stop one level before materialized equality, reserving
    the eighth path lane for clean HMR.  Labels 256..258 use their exact
    promised-domain ternary decoder.  On the modulo-259 domain exactly one
    equality toggles ``range_acc``.
    """
    if len(path) < 8:
        raise ValueError("mod-259 range scan requires eight path lanes")

    if order == "inc":
        qc.cx(ctrl, range_acc)
        _low256_range_scan_conditioned_hmr(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, leaf_fn=leaf_fn, order="inc",
        )
        _top3_range_scan_valid259(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, leaf_fn=leaf_fn, order="inc",
        )
    elif order == "dec":
        _top3_range_scan_valid259(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, leaf_fn=leaf_fn, order="dec",
        )
        _low256_range_scan_conditioned_hmr(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, leaf_fn=leaf_fn, order="dec",
        )
        qc.cx(ctrl, range_acc)
    else:
        raise ValueError("bad mod-259 range-scan order")


def _upper_zero_map_midpoint_nine(qc: QuantumCircuit, *, ctrl: Qubit,
                                  boundary_B: Sequence[Qubit],
                                  bits: Sequence[Qubit],
                                  dirty_map: Sequence[Qubit],
                                  scratch: Sequence[Qubit]) -> None:
    """Apply the 259-bit upper-zero dirty map using nine clean lanes."""
    if len(bits) != 259 or len(dirty_map) != 259:
        raise ValueError("midpoint upper-zero map requires 259-bit work registers")
    if len(scratch) < 9:
        raise ValueError("midpoint upper-zero map requires nine clean lanes")
    path = list(scratch[:8])
    range_acc = scratch[8]

    def leaf_forward(j: int, boundary_control: Qubit,
                     clean_temp: Qubit) -> None:
        _apply_not_factor_with_clean(
            qc, boundary_control=boundary_control, data_bit=bits[j],
            neighbor=None if j == 258 else dirty_map[j + 1],
            target=dirty_map[j], clean_temp=clean_temp,
        )

    def leaf_reverse(j: int, boundary_control: Qubit,
                     clean_temp: Qubit) -> None:
        if j < 258:
            _apply_not_factor_with_clean(
                qc, boundary_control=boundary_control, data_bit=bits[j],
                neighbor=dirty_map[j + 1], target=dirty_map[j],
                clean_temp=clean_temp,
            )

    _range_scan_259_nine(
        qc, boundary=boundary_B, ctrl=ctrl, range_acc=range_acc,
        path=path, leaf_fn=leaf_forward, order="inc",
    )
    _range_scan_259_nine(
        qc, boundary=boundary_B, ctrl=ctrl, range_acc=range_acc,
        path=path, leaf_fn=leaf_reverse, order="dec",
    )


def _low256_range_scan_conditioned_borrowed(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    ctrl: Qubit,
    range_acc: Qubit,
    ancillas: Sequence[Qubit],
    borrowed: Qubit,
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Scan labels 0..255 with seven clean path lanes and one dirty lender."""
    if len(index_reg) != LS_WIDTH:
        raise ValueError("borrowed low decoder requires a 9-bit index")
    if len(ancillas) < 7:
        raise ValueError("borrowed low decoder requires seven clean lanes")
    path = list(ancillas[:7])
    high = index_reg[8]
    bit7 = index_reg[7]
    root = path[0]

    qc.x(high)
    qc.x(bit7)
    _borrowed_c3x(qc, ctrl, high, bit7, root, borrowed)
    qc.x(bit7)
    qc.x(high)

    def rec(labels: Sequence[int], g: Qubit, depth: int) -> None:
        labels = list(labels)
        if len(labels) == 2:
            low_label, high_label = sorted(labels)
            bit = _e._split_bit(labels)

            def toggle_equality(label: int) -> None:
                if ((label >> bit) & 1) == 0:
                    qc.x(index_reg[bit])
                qc.ccx(g, index_reg[bit], range_acc)
                if ((label >> bit) & 1) == 0:
                    qc.x(index_reg[bit])

            if order == "inc":
                leaf_fn(low_label, range_acc)
                toggle_equality(low_label)
                leaf_fn(high_label, range_acc)
                toggle_equality(high_label)
            else:
                toggle_equality(high_label)
                leaf_fn(high_label, range_acc)
                toggle_equality(low_label)
                leaf_fn(low_label, range_acc)
            return
        bit = _e._split_bit(labels)
        zero = [label for label in labels if ((label >> bit) & 1) == 0]
        one = [label for label in labels if ((label >> bit) & 1) == 1]
        h = path[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    low = list(range(0, 128))
    high_labels = list(range(128, 256))

    def toggle_root_branch() -> None:
        qc.x(high)
        qc.ccx(ctrl, high, root)
        qc.x(high)

    if order == "inc":
        rec(low, root, 1)
        toggle_root_branch()
        rec(high_labels, root, 1)
        toggle_root_branch()
    else:
        toggle_root_branch()
        rec(high_labels, root, 1)
        toggle_root_branch()
        rec(low, root, 1)

    qc.x(high)
    qc.x(bit7)
    _borrowed_c3x(qc, ctrl, high, bit7, root, borrowed)
    qc.x(bit7)
    qc.x(high)


def _top3_range_scan_valid259_borrowed(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    ctrl: Qubit,
    range_acc: Qubit,
    ancillas: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Scan labels 256..258 without reserving a clean HMR lane."""
    if len(index_reg) != LS_WIDTH:
        raise ValueError("borrowed top decoder requires a 9-bit index")
    if len(ancillas) < 3:
        raise ValueError("borrowed top decoder requires three clean lanes")
    top = ancillas[0]
    path = list(ancillas[1:3])
    qc.ccx(ctrl, index_reg[8], top)

    def wrapped(encoded: int, equality: Qubit) -> None:
        label = encoded + 256
        if order == "inc":
            leaf_fn(label, range_acc)
            qc.cx(equality, range_acc)
        else:
            qc.cx(equality, range_acc)
            leaf_fn(label, range_acc)

    unary_iteration_tight(
        qc, index_reg=index_reg[:2], labels=[0, 1, 2], ctrl=top,
        ancillas=path, leaf_fn=wrapped, order=order,
    )
    qc.ccx(ctrl, index_reg[8], top)


def _top3_range_scan_valid259_conditional_clean(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    ctrl: Qubit,
    range_acc: Qubit,
    ancillas: Sequence[Qubit],
    clean_helper: Qubit,
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Scan labels 256..258 using ctrl as a conditional-clean helper."""
    if len(index_reg) != LS_WIDTH:
        raise ValueError("conditional-clean top decoder requires a 9-bit index")
    if len(ancillas) < 3:
        raise ValueError("conditional-clean top decoder requires three clean lanes")
    top = ancillas[0]
    path = list(ancillas[1:3])
    qc.ccx(ctrl, index_reg[8], top)

    def wrapped(encoded: int, equality: Qubit) -> None:
        label = encoded + 256
        if order == "inc":
            leaf_fn(label, range_acc, clean_helper)
            qc.cx(equality, range_acc)
        else:
            qc.cx(equality, range_acc)
            leaf_fn(label, range_acc, clean_helper)

    qc.x(clean_helper)
    unary_iteration_tight(
        qc, index_reg=index_reg[:2], labels=[0, 1, 2], ctrl=top,
        ancillas=path, leaf_fn=wrapped, order=order,
    )
    qc.x(clean_helper)
    qc.ccx(ctrl, index_reg[8], top)


def _low256_range_scan_conditioned_dirty_seven(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    ctrl: Qubit,
    range_acc: Qubit,
    ancillas: Sequence[Qubit],
    dirty: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Scan 0..255 with six clean path lanes and restored dirty lenders."""
    if len(index_reg) != LS_WIDTH:
        raise ValueError("seven-lane low decoder requires a 9-bit index")
    if len(ancillas) < 6:
        raise ValueError("seven-lane low decoder requires six path lanes")
    if not dirty:
        raise ValueError("seven-lane low decoder requires dirty lenders")
    path = list(ancillas[:6])
    high = index_reg[8]
    bit7 = index_reg[7]
    root = path[0]

    qc.x(high)
    qc.x(bit7)
    _borrowed_c3x(qc, ctrl, high, bit7, root, dirty[0])
    qc.x(bit7)
    qc.x(high)

    def visit(label: int, controls: Sequence[Qubit]) -> None:
        if order == "inc":
            leaf_fn(label, range_acc)
            _toggle_raw_controls_dirty(qc, controls, range_acc, dirty)
        else:
            _toggle_raw_controls_dirty(qc, controls, range_acc, dirty)
            leaf_fn(label, range_acc)

    def direct(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            visit(sub_labels[0], controls)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

        def branch(values, bit_value: int) -> None:
            if not values:
                return
            if bit_value == 0:
                qc.x(index_reg[bit])
            direct(values, list(controls) + [index_reg[bit]])
            if bit_value == 0:
                qc.x(index_reg[bit])

        if order == "inc":
            branch(zero, 0)
            branch(one, 1)
        else:
            branch(one, 1)
            branch(zero, 0)

    def rec(sub_labels, g, depth):
        if _tight_unary_depth_for_labels(sub_labels) <= 2:
            direct(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = path[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    low = list(range(0, 128))
    high_labels = list(range(128, 256))

    def toggle_root_branch() -> None:
        qc.x(high)
        qc.ccx(ctrl, high, root)
        qc.x(high)

    if order == "inc":
        rec(low, root, 1)
        toggle_root_branch()
        rec(high_labels, root, 1)
        toggle_root_branch()
    else:
        toggle_root_branch()
        rec(high_labels, root, 1)
        toggle_root_branch()
        rec(low, root, 1)

    qc.x(high)
    qc.x(bit7)
    _borrowed_c3x(qc, ctrl, high, bit7, root, dirty[0])
    qc.x(bit7)
    qc.x(high)



def _low256_range_scan_conditioned_dirty_six(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    ctrl: Qubit,
    range_acc: Qubit,
    ancillas: Sequence[Qubit],
    dirty: Sequence[Qubit],
    clean_helper: Qubit,
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Scan 0..255 with five clean path lanes and restored dirty lenders.

    Relative to the official seven-clean-lane decoder, one additional binary
    level is left as a raw control.  At the leaves this gives at most four raw
    controls, for which the existing dirty-control toggle needs two lenders.
    """
    if len(index_reg) != LS_WIDTH:
        raise ValueError("six-lane low decoder requires a 9-bit index")
    if len(ancillas) < 5:
        raise ValueError("six-lane low decoder requires five path lanes")
    if len(dirty) < 2:
        raise ValueError("six-lane low decoder requires two dirty lenders")
    path = list(ancillas[:5])
    high = index_reg[8]
    bit7 = index_reg[7]
    root = path[0]

    qc.x(high)
    qc.x(bit7)
    _borrowed_c3x(qc, ctrl, high, bit7, root, dirty[0])
    qc.x(bit7)
    qc.x(high)

    def visit(label: int, controls: Sequence[Qubit]) -> None:
        def toggle_equality() -> None:
            _toggle_four_controls_conditional_zero(
                qc,
                controls=controls,
                target=range_acc,
                conditional_zero=clean_helper,
                borrowed=dirty[0],
            )

        if order == "inc":
            leaf_fn(label, range_acc, clean_helper)
            toggle_equality()
        else:
            toggle_equality()
            leaf_fn(label, range_acc, clean_helper)

    def direct(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            visit(sub_labels[0], controls)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

        def branch(values, bit_value: int) -> None:
            if not values:
                return
            if bit_value == 0:
                qc.x(index_reg[bit])
            direct(values, list(controls) + [index_reg[bit]])
            if bit_value == 0:
                qc.x(index_reg[bit])

        if order == "inc":
            branch(zero, 0)
            branch(one, 1)
        else:
            branch(one, 1)
            branch(zero, 0)

    def rec(sub_labels, g, depth):
        if _tight_unary_depth_for_labels(sub_labels) <= 3:
            direct(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = path[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    low = list(range(0, 128))
    high_labels = list(range(128, 256))

    def toggle_root_branch() -> None:
        qc.x(high)
        qc.ccx(ctrl, high, root)
        qc.x(high)

    def clean_rec(labels: Sequence[int]) -> None:
        # range_acc can be one only when the original ctrl is one.  Inverting
        # ctrl therefore supplies a zero HMR helper on every active leaf.  If
        # ctrl was zero, range_acc remains zero and the final-control HMR
        # ordering makes the helper value irrelevant.
        qc.x(clean_helper)
        rec(labels, root, 1)
        qc.x(clean_helper)

    if order == "inc":
        clean_rec(low)
        toggle_root_branch()
        clean_rec(high_labels)
        toggle_root_branch()
    else:
        toggle_root_branch()
        clean_rec(high_labels)
        toggle_root_branch()
        clean_rec(low)

    qc.x(high)
    qc.x(bit7)
    _borrowed_c3x(qc, ctrl, high, bit7, root, dirty[0])
    qc.x(bit7)
    qc.x(high)


def _low256_range_scan_conditioned_dirty_five(
    qc: QuantumCircuit,
    *,
    index_reg: Sequence[Qubit],
    ctrl: Qubit,
    range_acc: Qubit,
    ancillas: Sequence[Qubit],
    dirty: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Scan 0..255 with three/four clean path lanes and dirty lenders."""
    if len(index_reg) != LS_WIDTH:
        raise ValueError("five-lane low decoder requires a 9-bit index")
    if len(ancillas) < 3:
        raise ValueError("low decoder requires at least three path lanes")
    path_count = min(4, len(ancillas))
    direct_depth = 4 if path_count == 4 else 5
    if len(dirty) < direct_depth - 1:
        raise ValueError(
            f"low decoder requires {direct_depth - 1} dirty lenders"
        )
    path = list(ancillas[:path_count])
    high = index_reg[8]
    bit7 = index_reg[7]
    root = path[0]

    qc.x(high)
    qc.x(bit7)
    _borrowed_c3x(qc, ctrl, high, bit7, root, dirty[0])
    qc.x(bit7)
    qc.x(high)

    def visit(label: int, controls: Sequence[Qubit]) -> None:
        if order == "inc":
            leaf_fn(label, range_acc)
            _toggle_raw_controls_dirty(qc, controls, range_acc, dirty)
        else:
            _toggle_raw_controls_dirty(qc, controls, range_acc, dirty)
            leaf_fn(label, range_acc)

    def direct(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            visit(sub_labels[0], controls)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

        def branch(values, bit_value: int) -> None:
            if not values:
                return
            if bit_value == 0:
                qc.x(index_reg[bit])
            direct(values, list(controls) + [index_reg[bit]])
            if bit_value == 0:
                qc.x(index_reg[bit])

        if order == "inc":
            branch(zero, 0)
            branch(one, 1)
        else:
            branch(one, 1)
            branch(zero, 0)

    def rec(sub_labels, g, depth):
        if _tight_unary_depth_for_labels(sub_labels) <= direct_depth:
            direct(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = path[depth]
        _e._and_with_index_bit(qc, g, index_reg[bit], h, 0)
        if order == "inc":
            rec(zero, h, depth + 1)
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
        else:
            qc.cx(g, h)
            rec(one, h, depth + 1)
            qc.cx(g, h)
            rec(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, index_reg[bit], h, 0)

    low = list(range(0, 128))
    high_labels = list(range(128, 256))

    def toggle_root_branch() -> None:
        qc.x(high)
        qc.ccx(ctrl, high, root)
        qc.x(high)

    if order == "inc":
        rec(low, root, 1)
        toggle_root_branch()
        rec(high_labels, root, 1)
        toggle_root_branch()
    else:
        toggle_root_branch()
        rec(high_labels, root, 1)
        toggle_root_branch()
        rec(low, root, 1)

    qc.x(high)
    qc.x(bit7)
    _borrowed_c3x(qc, ctrl, high, bit7, root, dirty[0])
    qc.x(bit7)
    qc.x(high)


def _range_scan_259_five_dirty(
    qc: QuantumCircuit,
    *,
    boundary: Sequence[Qubit],
    ctrl: Qubit,
    scratch: Sequence[Qubit],
    dirty: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Inclusive modulo-259 scan with four/five clean restored lanes."""
    if len(scratch) < 4:
        raise ValueError("dirty mod-259 range scan requires four clean lanes")
    path_count = 4 if len(scratch) >= 5 else 3
    path = list(scratch[:path_count])
    range_acc = scratch[path_count]
    if order == "inc":
        qc.cx(ctrl, range_acc)
        _low256_range_scan_conditioned_dirty_five(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, dirty=dirty, leaf_fn=leaf_fn, order="inc",
        )
        _top3_range_scan_valid259_borrowed(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, leaf_fn=leaf_fn, order="inc",
        )
    elif order == "dec":
        _top3_range_scan_valid259_borrowed(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, leaf_fn=leaf_fn, order="dec",
        )
        _low256_range_scan_conditioned_dirty_five(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, dirty=dirty, leaf_fn=leaf_fn, order="dec",
        )
        qc.cx(ctrl, range_acc)
    else:
        raise ValueError("bad five-lane mod-259 scan order")


def _range_scan_259_four_conditional(
    qc: QuantumCircuit,
    *,
    boundary: Sequence[Qubit],
    ctrl: Qubit,
    scratch: Sequence[Qubit],
    dirty: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Modulo-259 scan using four clean lanes and ctrl as a live-path helper."""
    if len(scratch) < 4:
        raise ValueError("conditional mod-259 range scan needs four clean lanes")
    path = list(scratch[:3])
    range_acc = scratch[3]

    def low_scan() -> None:
        high = boundary[8]
        bit7 = boundary[7]
        root = path[0]
        qc.x(high)
        qc.x(bit7)
        _borrowed_c3x(qc, ctrl, high, bit7, root, dirty[0])
        qc.x(bit7)
        qc.x(high)

        def visit(label: int, controls: Sequence[Qubit]) -> None:
            if order == "inc":
                leaf_fn(label, range_acc, ctrl)
            qc.x(ctrl)
            _toggle_raw_controls_conditionally_clean(
                qc, controls, range_acc, dirty, ctrl,
            )
            qc.x(ctrl)
            if order == "dec":
                leaf_fn(label, range_acc, ctrl)

        def direct(sub_labels, controls) -> None:
            if len(sub_labels) == 1:
                visit(sub_labels[0], controls)
                return
            bit = _e._split_bit(sub_labels)
            zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
            one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

            def branch(values, bit_value: int) -> None:
                if not values:
                    return
                if bit_value == 0:
                    qc.x(boundary[bit])
                direct(values, list(controls) + [boundary[bit]])
                if bit_value == 0:
                    qc.x(boundary[bit])

            if order == "inc":
                branch(zero, 0)
                branch(one, 1)
            else:
                branch(one, 1)
                branch(zero, 0)

        def rec(sub_labels, g, depth) -> None:
            if _tight_unary_depth_for_labels(sub_labels) <= 5:
                direct(sub_labels, [g])
                return
            bit = _e._split_bit(sub_labels)
            zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
            one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
            h = path[depth]
            _e._and_with_index_bit(qc, g, boundary[bit], h, 0)
            if order == "inc":
                rec(zero, h, depth + 1)
                qc.cx(g, h)
                rec(one, h, depth + 1)
                qc.cx(g, h)
            else:
                qc.cx(g, h)
                rec(one, h, depth + 1)
                qc.cx(g, h)
                rec(zero, h, depth + 1)
            _e._uncompute_and_with_index_bit(qc, g, boundary[bit], h, 0)

        low = list(range(0, 128))
        high_labels = list(range(128, 256))

        def toggle_root_branch() -> None:
            qc.x(high)
            qc.ccx(ctrl, high, root)
            qc.x(high)

        if order == "inc":
            rec(low, root, 1)
            toggle_root_branch()
            rec(high_labels, root, 1)
            toggle_root_branch()
        else:
            toggle_root_branch()
            rec(high_labels, root, 1)
            toggle_root_branch()
            rec(low, root, 1)

        qc.x(high)
        qc.x(bit7)
        _borrowed_c3x(qc, ctrl, high, bit7, root, dirty[0])
        qc.x(bit7)
        qc.x(high)

    def top_scan() -> None:
        _top3_range_scan_valid259_conditional_clean(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, clean_helper=ctrl, leaf_fn=leaf_fn, order=order,
        )

    if order == "inc":
        qc.cx(ctrl, range_acc)
        low_scan()
        top_scan()
    elif order == "dec":
        top_scan()
        low_scan()
        qc.cx(ctrl, range_acc)
    else:
        raise ValueError("bad conditional mod-259 scan order")


def _upper_zero_map_midpoint_four_conditional(
    qc: QuantumCircuit,
    *,
    ctrl: Qubit,
    boundary_B: Sequence[Qubit],
    bits: Sequence[Qubit],
    dirty_map: Sequence[Qubit],
    dirty: Sequence[Qubit],
    scratch: Sequence[Qubit],
) -> None:
    """Upper-zero map with four clean lanes and a conditionally-zero ctrl."""
    if len(bits) != 259 or len(dirty_map) != 259:
        raise ValueError("conditional midpoint map requires 259-bit registers")
    if len(scratch) < 4:
        raise ValueError("conditional midpoint map needs four clean lanes")

    def leaf_forward(j: int, boundary_control: Qubit,
                     clean_helper: Qubit) -> None:
        _apply_not_factor_with_conditional_zero(
            qc, boundary_control=boundary_control, data_bit=bits[j],
            neighbor=None if j == 258 else dirty_map[j + 1],
            target=dirty_map[j], conditional_zero=clean_helper,
        )

    def leaf_reverse(j: int, boundary_control: Qubit,
                     clean_helper: Qubit) -> None:
        if j < 258:
            _apply_not_factor_with_conditional_zero(
                qc, boundary_control=boundary_control, data_bit=bits[j],
                neighbor=dirty_map[j + 1], target=dirty_map[j],
                conditional_zero=clean_helper,
            )

    _range_scan_259_four_conditional(
        qc, boundary=boundary_B, ctrl=ctrl, scratch=scratch, dirty=dirty,
        leaf_fn=leaf_forward, order="inc",
    )
    _range_scan_259_four_conditional(
        qc, boundary=boundary_B, ctrl=ctrl, scratch=scratch, dirty=dirty,
        leaf_fn=leaf_reverse, order="dec",
    )


def _upper_zero_map_midpoint_four_palindromic(
    qc: QuantumCircuit,
    *,
    ctrl: Qubit,
    boundary_B: Sequence[Qubit],
    bits: Sequence[Qubit],
    dirty_map: Sequence[Qubit],
    dirty: Sequence[Qubit],
    scratch: Sequence[Qubit],
) -> None:
    """Four-clean upper-zero map with one shared palindromic decoder walk."""
    if len(bits) != 259 or len(dirty_map) != 259:
        raise ValueError("palindromic midpoint map requires 259-bit registers")
    if len(boundary_B) != 9 or len(scratch) < 4 or not dirty:
        raise ValueError("palindromic midpoint map workspace mismatch")
    path = list(scratch[:3])
    range_acc = scratch[3]
    labels = list(range(259))

    def factor(j: int, reverse: bool) -> None:
        if reverse and j == 258:
            return
        _apply_not_factor_with_conditional_zero(
            qc, boundary_control=range_acc, data_bit=bits[j],
            neighbor=None if j == 258 else dirty_map[j + 1],
            target=dirty_map[j], conditional_zero=ctrl,
        )

    def equality_toggle(controls: Sequence[Qubit]) -> None:
        if len(controls) >= 4:
            _toggle_raw_controls_conditionally_clean(
                qc, controls, range_acc, dirty, ctrl,
            )
        else:
            _toggle_raw_controls_dirty(qc, controls, range_acc, dirty)

    def direct_forward(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            qc.x(ctrl)
            factor(sub_labels[0], False)
            equality_toggle(controls)
            qc.x(ctrl)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        qc.x(boundary_B[bit])
        direct_forward(zero, list(controls) + [boundary_B[bit]])
        qc.x(boundary_B[bit])
        direct_forward(one, list(controls) + [boundary_B[bit]])

    def direct_reverse(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            qc.x(ctrl)
            equality_toggle(controls)
            factor(sub_labels[0], True)
            qc.x(ctrl)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        direct_reverse(one, list(controls) + [boundary_B[bit]])
        qc.x(boundary_B[bit])
        direct_reverse(zero, list(controls) + [boundary_B[bit]])
        qc.x(boundary_B[bit])

    def direct_palindrome(sub_labels, controls) -> None:
        if len(sub_labels) == 1:
            qc.x(ctrl)
            factor(sub_labels[0], False)
            qc.x(ctrl)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        qc.x(boundary_B[bit])
        direct_forward(zero, list(controls) + [boundary_B[bit]])
        qc.x(boundary_B[bit])
        direct_palindrome(one, list(controls) + [boundary_B[bit]])
        qc.x(boundary_B[bit])
        direct_reverse(zero, list(controls) + [boundary_B[bit]])
        qc.x(boundary_B[bit])

    def scan_forward(sub_labels, g: Qubit, depth: int) -> None:
        if _tight_unary_depth_for_labels(sub_labels) <= 6:
            direct_forward(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = path[depth]
        _e._and_with_index_bit(qc, g, boundary_B[bit], h, 0)
        scan_forward(zero, h, depth + 1)
        qc.cx(g, h)
        scan_forward(one, h, depth + 1)
        qc.cx(g, h)
        _e._uncompute_and_with_index_bit(qc, g, boundary_B[bit], h, 0)

    def scan_reverse(sub_labels, g: Qubit, depth: int) -> None:
        if _tight_unary_depth_for_labels(sub_labels) <= 6:
            direct_reverse(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = path[depth]
        _e._and_with_index_bit(qc, g, boundary_B[bit], h, 0)
        qc.cx(g, h)
        scan_reverse(one, h, depth + 1)
        qc.cx(g, h)
        scan_reverse(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, boundary_B[bit], h, 0)

    def scan_palindrome(sub_labels, g: Qubit, depth: int) -> None:
        if _tight_unary_depth_for_labels(sub_labels) <= 6:
            direct_palindrome(sub_labels, [g])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        h = path[depth]
        _e._and_with_index_bit(qc, g, boundary_B[bit], h, 0)
        scan_forward(zero, h, depth + 1)
        qc.cx(g, h)
        scan_palindrome(one, h, depth + 1)
        qc.cx(g, h)
        scan_reverse(zero, h, depth + 1)
        _e._uncompute_and_with_index_bit(qc, g, boundary_B[bit], h, 0)

    qc.cx(ctrl, range_acc)
    scan_palindrome(labels, ctrl, 0)
    qc.cx(ctrl, range_acc)


def _range_scan_259_two_dirty(
    qc: QuantumCircuit,
    *,
    boundary: Sequence[Qubit],
    ctrl: Qubit,
    scratch: Sequence[Qubit],
    dirty: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Exact modulo-259 scan with one clean path lane and one accumulator."""
    if len(boundary) != 9 or len(scratch) < 2 or len(dirty) < 8:
        raise ValueError("two-clean modulo-259 scan workspace mismatch")
    root = scratch[0]
    range_acc = scratch[1]

    def low_scan() -> None:
        high = boundary[8]
        bit7 = boundary[7]
        qc.x(high)
        qc.x(bit7)
        _borrowed_c3x(qc, ctrl, high, bit7, root, dirty[0])
        qc.x(bit7)
        qc.x(high)

        def visit(label: int, controls: Sequence[Qubit]) -> None:
            if order == "inc":
                leaf_fn(label, range_acc)
                _toggle_raw_controls_dirty(qc, controls, range_acc, dirty)
            else:
                _toggle_raw_controls_dirty(qc, controls, range_acc, dirty)
                leaf_fn(label, range_acc)

        def direct(sub_labels, controls) -> None:
            if len(sub_labels) == 1:
                visit(sub_labels[0], controls)
                return
            bit = _e._split_bit(sub_labels)
            zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
            one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

            def branch(values, bit_value: int) -> None:
                if bit_value == 0:
                    qc.x(boundary[bit])
                direct(values, list(controls) + [boundary[bit]])
                if bit_value == 0:
                    qc.x(boundary[bit])

            if order == "inc":
                branch(zero, 0)
                branch(one, 1)
            else:
                branch(one, 1)
                branch(zero, 0)

        low = list(range(128))
        upper = list(range(128, 256))

        def toggle_root_branch() -> None:
            qc.x(high)
            qc.ccx(ctrl, high, root)
            qc.x(high)

        if order == "inc":
            direct(low, [root])
            toggle_root_branch()
            direct(upper, [root])
            toggle_root_branch()
        else:
            toggle_root_branch()
            direct(upper, [root])
            toggle_root_branch()
            direct(low, [root])

        qc.x(high)
        qc.x(bit7)
        _borrowed_c3x(qc, ctrl, high, bit7, root, dirty[0])
        qc.x(bit7)
        qc.x(high)

    def exact_top(label: int) -> None:
        inverted = []
        for bit, lane in enumerate(boundary):
            if ((label >> bit) & 1) == 0:
                qc.x(lane)
                inverted.append(lane)
        _toggle_raw_controls_dirty(
            qc, [ctrl] + list(boundary), range_acc, dirty,
        )
        for lane in reversed(inverted):
            qc.x(lane)

    def top_scan() -> None:
        endpoints = range(256, 259) if order == "inc" else range(258, 255, -1)
        for label in endpoints:
            if order == "inc":
                leaf_fn(label, range_acc)
                exact_top(label)
            else:
                exact_top(label)
                leaf_fn(label, range_acc)

    if order == "inc":
        qc.cx(ctrl, range_acc)
        low_scan()
        top_scan()
    elif order == "dec":
        top_scan()
        low_scan()
        qc.cx(ctrl, range_acc)
    else:
        raise ValueError("bad two-clean modulo-259 scan order")


def _range_scan_259_one_dirty(
    qc: QuantumCircuit,
    *,
    boundary: Sequence[Qubit],
    ctrl: Qubit,
    scratch: Sequence[Qubit],
    dirty: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Exact modulo-259 scan with a sole clean range accumulator."""
    if len(boundary) != 9 or len(scratch) < 1 or len(dirty) < 8:
        raise ValueError("one-clean modulo-259 scan workspace mismatch")
    range_acc = scratch[0]

    def toggle_exact(label: int) -> None:
        inverted = []
        for bit, lane in enumerate(boundary):
            if ((label >> bit) & 1) == 0:
                qc.x(lane)
                inverted.append(lane)
        _toggle_raw_controls_dirty(
            qc, [ctrl] + list(boundary), range_acc, dirty,
        )
        for lane in reversed(inverted):
            qc.x(lane)

    labels = range(259) if order == "inc" else range(258, -1, -1)
    if order == "inc":
        qc.cx(ctrl, range_acc)
        for label in labels:
            leaf_fn(label, range_acc)
            toggle_exact(label)
    elif order == "dec":
        for label in labels:
            toggle_exact(label)
            leaf_fn(label, range_acc)
        qc.cx(ctrl, range_acc)
    else:
        raise ValueError("bad one-clean modulo-259 scan order")


def _range_scan_259_three_dirty(
    qc: QuantumCircuit,
    *,
    boundary: Sequence[Qubit],
    ctrl: Qubit,
    scratch: Sequence[Qubit],
    dirty: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Exact modulo-259 scan with two clean path lanes and one accumulator."""
    if len(boundary) != 9 or len(scratch) < 3 or len(dirty) < 8:
        raise ValueError("three-clean modulo-259 scan workspace mismatch")
    path = list(scratch[:2])
    range_acc = scratch[2]

    def low_scan() -> None:
        high = boundary[8]
        bit7 = boundary[7]
        root = path[0]
        qc.x(high)
        qc.x(bit7)
        _borrowed_c3x(qc, ctrl, high, bit7, root, dirty[0])
        qc.x(bit7)
        qc.x(high)

        def visit(label: int, controls: Sequence[Qubit]) -> None:
            if order == "inc":
                leaf_fn(label, range_acc)
                _toggle_raw_controls_dirty(qc, controls, range_acc, dirty)
            else:
                _toggle_raw_controls_dirty(qc, controls, range_acc, dirty)
                leaf_fn(label, range_acc)

        def direct(sub_labels, controls) -> None:
            if len(sub_labels) == 1:
                visit(sub_labels[0], controls)
                return
            bit = _e._split_bit(sub_labels)
            zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
            one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

            def branch(values, bit_value: int) -> None:
                if bit_value == 0:
                    qc.x(boundary[bit])
                direct(values, list(controls) + [boundary[bit]])
                if bit_value == 0:
                    qc.x(boundary[bit])

            if order == "inc":
                branch(zero, 0)
                branch(one, 1)
            else:
                branch(one, 1)
                branch(zero, 0)

        def rec(sub_labels, g: Qubit, depth: int) -> None:
            if _tight_unary_depth_for_labels(sub_labels) <= 6:
                direct(sub_labels, [g])
                return
            bit = _e._split_bit(sub_labels)
            zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
            one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
            h = path[depth]
            _e._and_with_index_bit(qc, g, boundary[bit], h, 0)
            if order == "inc":
                rec(zero, h, depth + 1)
                qc.cx(g, h)
                rec(one, h, depth + 1)
                qc.cx(g, h)
            else:
                qc.cx(g, h)
                rec(one, h, depth + 1)
                qc.cx(g, h)
                rec(zero, h, depth + 1)
            _e._uncompute_and_with_index_bit(qc, g, boundary[bit], h, 0)

        low = list(range(128))
        upper = list(range(128, 256))

        def toggle_root_branch() -> None:
            qc.x(high)
            qc.ccx(ctrl, high, root)
            qc.x(high)

        if order == "inc":
            rec(low, root, 1)
            toggle_root_branch()
            rec(upper, root, 1)
            toggle_root_branch()
        else:
            toggle_root_branch()
            rec(upper, root, 1)
            toggle_root_branch()
            rec(low, root, 1)

        qc.x(high)
        qc.x(bit7)
        _borrowed_c3x(qc, ctrl, high, bit7, root, dirty[0])
        qc.x(bit7)
        qc.x(high)

    def exact_top(label: int) -> None:
        inverted = []
        for bit, lane in enumerate(boundary):
            if ((label >> bit) & 1) == 0:
                qc.x(lane)
                inverted.append(lane)
        _toggle_raw_controls_dirty(
            qc, [ctrl] + list(boundary), range_acc, dirty,
        )
        for lane in reversed(inverted):
            qc.x(lane)

    def top_scan() -> None:
        endpoints = range(256, 259) if order == "inc" else range(258, 255, -1)
        for label in endpoints:
            if order == "inc":
                leaf_fn(label, range_acc)
                exact_top(label)
            else:
                exact_top(label)
                leaf_fn(label, range_acc)

    if order == "inc":
        qc.cx(ctrl, range_acc)
        low_scan()
        top_scan()
    elif order == "dec":
        top_scan()
        low_scan()
        qc.cx(ctrl, range_acc)
    else:
        raise ValueError("bad three-clean modulo-259 scan order")


def _upper_zero_map_midpoint_three_dirty(
    qc: QuantumCircuit,
    *,
    ctrl: Qubit,
    boundary_B: Sequence[Qubit],
    bits: Sequence[Qubit],
    dirty_map: Sequence[Qubit],
    dirty: Sequence[Qubit],
    scratch: Sequence[Qubit],
) -> None:
    """Exact three-clean upper-zero map used with a stable copied carry."""
    if len(bits) != 259 or len(dirty_map) != 259 or len(scratch) < 3:
        raise ValueError("three-clean midpoint map workspace mismatch")

    def leaf_forward(j: int, boundary_control: Qubit) -> None:
        _apply_not_factor_with_borrowed(
            qc, boundary_control=boundary_control, data_bit=bits[j],
            neighbor=None if j == 258 else dirty_map[j + 1],
            target=dirty_map[j], borrowed=dirty[0],
        )

    def leaf_reverse(j: int, boundary_control: Qubit) -> None:
        if j < 258:
            _apply_not_factor_with_borrowed(
                qc, boundary_control=boundary_control, data_bit=bits[j],
                neighbor=dirty_map[j + 1], target=dirty_map[j],
                borrowed=dirty[0],
            )

    _range_scan_259_three_dirty(
        qc, boundary=boundary_B, ctrl=ctrl, scratch=scratch,
        dirty=dirty[1:], leaf_fn=leaf_forward, order="inc",
    )
    _range_scan_259_three_dirty(
        qc, boundary=boundary_B, ctrl=ctrl, scratch=scratch,
        dirty=dirty[1:], leaf_fn=leaf_reverse, order="dec",
    )


def _upper_zero_map_midpoint_two_dirty(
    qc: QuantumCircuit,
    *,
    ctrl: Qubit,
    boundary_B: Sequence[Qubit],
    bits: Sequence[Qubit],
    dirty_map: Sequence[Qubit],
    dirty: Sequence[Qubit],
    scratch: Sequence[Qubit],
) -> None:
    """Exact two-clean upper-zero map used with a stable copied carry."""
    if len(bits) != 259 or len(dirty_map) != 259 or len(scratch) < 2:
        raise ValueError("two-clean midpoint map workspace mismatch")

    def leaf_forward(j: int, boundary_control: Qubit) -> None:
        _apply_not_factor_with_borrowed(
            qc, boundary_control=boundary_control, data_bit=bits[j],
            neighbor=None if j == 258 else dirty_map[j + 1],
            target=dirty_map[j], borrowed=dirty[0],
        )

    def leaf_reverse(j: int, boundary_control: Qubit) -> None:
        if j < 258:
            _apply_not_factor_with_borrowed(
                qc, boundary_control=boundary_control, data_bit=bits[j],
                neighbor=dirty_map[j + 1], target=dirty_map[j],
                borrowed=dirty[0],
            )

    _range_scan_259_two_dirty(
        qc, boundary=boundary_B, ctrl=ctrl, scratch=scratch,
        dirty=dirty[1:], leaf_fn=leaf_forward, order="inc",
    )
    _range_scan_259_two_dirty(
        qc, boundary=boundary_B, ctrl=ctrl, scratch=scratch,
        dirty=dirty[1:], leaf_fn=leaf_reverse, order="dec",
    )


def _upper_zero_map_midpoint_one_dirty(
    qc: QuantumCircuit,
    *,
    ctrl: Qubit,
    boundary_B: Sequence[Qubit],
    bits: Sequence[Qubit],
    dirty_map: Sequence[Qubit],
    dirty: Sequence[Qubit],
    scratch: Sequence[Qubit],
) -> None:
    """Exact one-clean upper-zero map used with a stable copied carry."""
    if len(bits) != 259 or len(dirty_map) != 259 or len(scratch) < 1:
        raise ValueError("one-clean midpoint map workspace mismatch")

    def leaf_forward(j: int, boundary_control: Qubit) -> None:
        _apply_not_factor_with_borrowed(
            qc, boundary_control=boundary_control, data_bit=bits[j],
            neighbor=None if j == 258 else dirty_map[j + 1],
            target=dirty_map[j], borrowed=dirty[0],
        )

    def leaf_reverse(j: int, boundary_control: Qubit) -> None:
        if j < 258:
            _apply_not_factor_with_borrowed(
                qc, boundary_control=boundary_control, data_bit=bits[j],
                neighbor=dirty_map[j + 1], target=dirty_map[j],
                borrowed=dirty[0],
            )

    _range_scan_259_one_dirty(
        qc, boundary=boundary_B, ctrl=ctrl, scratch=scratch,
        dirty=dirty[1:], leaf_fn=leaf_forward, order="inc",
    )
    _range_scan_259_one_dirty(
        qc, boundary=boundary_B, ctrl=ctrl, scratch=scratch,
        dirty=dirty[1:], leaf_fn=leaf_reverse, order="dec",
    )


def _upper_zero_map_midpoint_five_dirty(
    qc: QuantumCircuit,
    *,
    ctrl: Qubit,
    boundary_B: Sequence[Qubit],
    bits: Sequence[Qubit],
    dirty_map: Sequence[Qubit],
    dirty: Sequence[Qubit],
    scratch: Sequence[Qubit],
) -> None:
    """Apply the 259-bit upper-zero map with four/five clean lanes."""
    if len(bits) != 259 or len(dirty_map) != 259:
        raise ValueError("five-lane midpoint map requires 259-bit registers")
    if len(scratch) < 4:
        raise ValueError("midpoint map requires four clean lanes")

    def leaf_forward(j: int, boundary_control: Qubit) -> None:
        _apply_not_factor_with_borrowed(
            qc, boundary_control=boundary_control, data_bit=bits[j],
            neighbor=None if j == 258 else dirty_map[j + 1],
            target=dirty_map[j], borrowed=dirty[0],
        )

    def leaf_reverse(j: int, boundary_control: Qubit) -> None:
        if j < 258:
            _apply_not_factor_with_borrowed(
                qc, boundary_control=boundary_control, data_bit=bits[j],
                neighbor=dirty_map[j + 1], target=dirty_map[j],
                borrowed=dirty[0],
            )

    _range_scan_259_five_dirty(
        qc, boundary=boundary_B, ctrl=ctrl, scratch=scratch, dirty=dirty,
        leaf_fn=leaf_forward, order="inc",
    )
    _range_scan_259_five_dirty(
        qc, boundary=boundary_B, ctrl=ctrl, scratch=scratch, dirty=dirty,
        leaf_fn=leaf_reverse, order="dec",
    )


def _range_scan_259_six_dirty(
    qc: QuantumCircuit,
    *,
    boundary: Sequence[Qubit],
    ctrl: Qubit,
    scratch: Sequence[Qubit],
    dirty: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Inclusive modulo-259 scan with six clean and restored dirty lanes."""
    if len(scratch) < 6:
        raise ValueError("dirty mod-259 range scan requires six clean lanes")
    path = list(scratch[:5])
    range_acc = scratch[5]
    if order == "inc":
        qc.cx(ctrl, range_acc)
        _low256_range_scan_conditioned_dirty_six(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, dirty=dirty, clean_helper=ctrl,
            leaf_fn=leaf_fn, order="inc",
        )
        _top3_range_scan_valid259_conditional_clean(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, clean_helper=ctrl, leaf_fn=leaf_fn, order="inc",
        )
    elif order == "dec":
        _top3_range_scan_valid259_conditional_clean(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, clean_helper=ctrl, leaf_fn=leaf_fn, order="dec",
        )
        _low256_range_scan_conditioned_dirty_six(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, dirty=dirty, clean_helper=ctrl,
            leaf_fn=leaf_fn, order="dec",
        )
        qc.cx(ctrl, range_acc)
    else:
        raise ValueError("bad six-lane mod-259 scan order")


def _upper_zero_map_midpoint_six_dirty(
    qc: QuantumCircuit,
    *,
    ctrl: Qubit,
    boundary_B: Sequence[Qubit],
    bits: Sequence[Qubit],
    dirty_map: Sequence[Qubit],
    dirty: Sequence[Qubit],
    scratch: Sequence[Qubit],
) -> None:
    """Apply the 259-bit upper-zero map with six clean lanes."""
    if len(bits) != 259 or len(dirty_map) != 259:
        raise ValueError("six-lane midpoint map requires 259-bit registers")
    if len(scratch) < 6:
        raise ValueError("six-lane midpoint map requires six clean lanes")

    def leaf_forward(j: int, boundary_control: Qubit,
                     clean_temp: Qubit) -> None:
        _apply_not_factor_with_conditional_zero(
            qc, boundary_control=boundary_control, data_bit=bits[j],
            neighbor=None if j == 258 else dirty_map[j + 1],
            target=dirty_map[j], conditional_zero=clean_temp,
        )

    def leaf_reverse(j: int, boundary_control: Qubit,
                     clean_temp: Qubit) -> None:
        if j < 258:
            _apply_not_factor_with_conditional_zero(
                qc, boundary_control=boundary_control, data_bit=bits[j],
                neighbor=dirty_map[j + 1], target=dirty_map[j],
                conditional_zero=clean_temp,
            )

    _range_scan_259_six_dirty(
        qc, boundary=boundary_B, ctrl=ctrl, scratch=scratch, dirty=dirty,
        leaf_fn=leaf_forward, order="inc",
    )
    _range_scan_259_six_dirty(
        qc, boundary=boundary_B, ctrl=ctrl, scratch=scratch, dirty=dirty,
        leaf_fn=leaf_reverse, order="dec",
    )


def _range_scan_259_seven_dirty(
    qc: QuantumCircuit,
    *,
    boundary: Sequence[Qubit],
    ctrl: Qubit,
    scratch: Sequence[Qubit],
    dirty: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Inclusive modulo-259 scan with seven clean and dirty lenders."""
    if len(scratch) < 7:
        raise ValueError("dirty mod-259 range scan requires seven clean lanes")
    path = list(scratch[:6])
    range_acc = scratch[6]
    if order == "inc":
        qc.cx(ctrl, range_acc)
        _low256_range_scan_conditioned_dirty_seven(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, dirty=dirty, leaf_fn=leaf_fn, order="inc",
        )
        _top3_range_scan_valid259_borrowed(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, leaf_fn=leaf_fn, order="inc",
        )
    elif order == "dec":
        _top3_range_scan_valid259_borrowed(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, leaf_fn=leaf_fn, order="dec",
        )
        _low256_range_scan_conditioned_dirty_seven(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, dirty=dirty, leaf_fn=leaf_fn, order="dec",
        )
        qc.cx(ctrl, range_acc)
    else:
        raise ValueError("bad seven-lane mod-259 scan order")


def _upper_zero_map_midpoint_seven_dirty(
    qc: QuantumCircuit,
    *,
    ctrl: Qubit,
    boundary_B: Sequence[Qubit],
    bits: Sequence[Qubit],
    dirty_map: Sequence[Qubit],
    dirty: Sequence[Qubit],
    scratch: Sequence[Qubit],
) -> None:
    """Apply the 259-bit upper-zero map with seven clean lanes."""
    if len(bits) != 259 or len(dirty_map) != 259:
        raise ValueError("seven-lane midpoint map requires 259-bit registers")
    if len(scratch) < 7:
        raise ValueError("seven-lane midpoint map requires seven clean lanes")

    def leaf_forward(j: int, boundary_control: Qubit) -> None:
        _apply_not_factor_with_borrowed(
            qc, boundary_control=boundary_control, data_bit=bits[j],
            neighbor=None if j == 258 else dirty_map[j + 1],
            target=dirty_map[j], borrowed=dirty[0],
        )

    def leaf_reverse(j: int, boundary_control: Qubit) -> None:
        if j < 258:
            _apply_not_factor_with_borrowed(
                qc, boundary_control=boundary_control, data_bit=bits[j],
                neighbor=dirty_map[j + 1], target=dirty_map[j],
                borrowed=dirty[0],
            )

    _range_scan_259_seven_dirty(
        qc, boundary=boundary_B, ctrl=ctrl, scratch=scratch, dirty=dirty,
        leaf_fn=leaf_forward, order="inc",
    )
    _range_scan_259_seven_dirty(
        qc, boundary=boundary_B, ctrl=ctrl, scratch=scratch, dirty=dirty,
        leaf_fn=leaf_reverse, order="dec",
    )


def _range_scan_259_eight_borrowed(
    qc: QuantumCircuit,
    *,
    boundary: Sequence[Qubit],
    ctrl: Qubit,
    scratch: Sequence[Qubit],
    borrowed: Qubit,
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Inclusive modulo-259 range scan with eight clean and one dirty lane."""
    if len(scratch) < 8:
        raise ValueError("borrowed mod-259 range scan requires eight clean lanes")
    path = list(scratch[:7])
    range_acc = scratch[7]
    if order == "inc":
        qc.cx(ctrl, range_acc)
        _low256_range_scan_conditioned_borrowed(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, borrowed=borrowed, leaf_fn=leaf_fn, order="inc",
        )
        _top3_range_scan_valid259_borrowed(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, leaf_fn=leaf_fn, order="inc",
        )
    elif order == "dec":
        _top3_range_scan_valid259_borrowed(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, leaf_fn=leaf_fn, order="dec",
        )
        _low256_range_scan_conditioned_borrowed(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, borrowed=borrowed, leaf_fn=leaf_fn, order="dec",
        )
        qc.cx(ctrl, range_acc)
    else:
        raise ValueError("bad borrowed mod-259 range-scan order")


def _upper_zero_map_midpoint_eight_borrowed(
    qc: QuantumCircuit,
    *,
    ctrl: Qubit,
    boundary_B: Sequence[Qubit],
    bits: Sequence[Qubit],
    dirty_map: Sequence[Qubit],
    borrowed: Qubit,
    scratch: Sequence[Qubit],
) -> None:
    """Apply the 259-bit upper-zero dirty map with eight clean lanes."""
    if len(bits) != 259 or len(dirty_map) != 259:
        raise ValueError("borrowed midpoint map requires 259-bit work registers")
    if len(scratch) < 8:
        raise ValueError("borrowed midpoint map requires eight clean lanes")

    def leaf_forward(j: int, boundary_control: Qubit) -> None:
        _apply_not_factor_with_borrowed(
            qc, boundary_control=boundary_control, data_bit=bits[j],
            neighbor=None if j == 258 else dirty_map[j + 1],
            target=dirty_map[j], borrowed=borrowed,
        )

    def leaf_reverse(j: int, boundary_control: Qubit) -> None:
        if j < 258:
            _apply_not_factor_with_borrowed(
                qc, boundary_control=boundary_control, data_bit=bits[j],
                neighbor=dirty_map[j + 1], target=dirty_map[j],
                borrowed=borrowed,
            )

    _range_scan_259_eight_borrowed(
        qc, boundary=boundary_B, ctrl=ctrl, scratch=scratch,
        borrowed=borrowed, leaf_fn=leaf_forward, order="inc",
    )
    _range_scan_259_eight_borrowed(
        qc, boundary=boundary_B, ctrl=ctrl, scratch=scratch,
        borrowed=borrowed, leaf_fn=leaf_reverse, order="dec",
    )


@lru_cache(maxsize=None)
def compact_prefix_add_midtail_gate(*, n: int, k: int, K: int,
                                    name: str = "T_ADD_MIDTAIL_COMPACT") -> Gate:
    """Restoring T add with exact midpoint tail/carry sign capture.

    The old exact-width stream retained the upper-zero predicate before the
    cancelling T subtraction.  That predicate is stale at the restoring-add
    carry midpoint.  This block computes the upper endpoint before the first
    arithmetic pass, captures the selected carry, applies the dirty-map
    sandwich at the midpoint, and then finishes the add.  The carry flag,
    dirty map, ten dirty passengers, endpoint registers, and all three clean
    scratch lanes are restored exactly.
    """
    if n != 256 or k != 1 or K > 257:
        raise ValueError("midpoint T add is certified for secp256k1 labels 1..257")
    if k > K:
        raise ValueError("need k <= K")
    work_size = n + 3
    Ctrl = QuantumRegister(1, "Ctrl")
    Sign = QuantumRegister(1, "Sign")
    Tail = QuantumRegister(1, "Tail")
    Work1 = QuantumRegister(work_size, "Work1")
    Work2 = QuantumRegister(work_size, "Work2")
    l_t = QuantumRegister(LT_WIDTH, "l_t")
    l_s = QuantumRegister(LS_WIDTH, "l_s")
    l_rp = QuantumRegister(LRP_WIDTH, "l_rp")
    Dirty = QuantumRegister(DIRTY_PASSENGER_SIZE, "DirtyPassenger")
    Scratch = QuantumRegister(2, "Scratch")
    qc = _e._block_circuit(
        Ctrl, Sign, Tail, Work1, Work2, l_t, l_s, l_rp,
        Dirty, Scratch, name=name,
    )

    encoded_labels = list(range(0, K - 1))
    depth = _tight_unary_depth_for_labels(encoded_labels)
    path_depth = max(0, depth - 7)
    path = list(Scratch[:path_depth])
    carry = Tail[0]
    acc = Scratch[1]

    # Prepare B = 258 - ell_s - ell_rp before the arithmetic history occupies
    # the carry lane.  First map the modulo-259 truth-minus-one shift encoding
    # to its true value.  This step is essential at ell_s=0, whose encoding is
    # 258; treating that sentinel as an ordinary 9-bit integer gives B+253.
    affine_carry = carry
    lrp_extended = list(l_rp) + [Dirty[0]]
    qc.x(affine_carry)
    inc_mod259_1ctrl_dirty(qc, affine_carry, l_s, Dirty)
    qc.x(affine_carry)
    qc.append(
        _e.cuccaro_add_mod_2n_no_z_gate(LS_WIDTH, name="ADD_lrp8_to_ls9"),
        lrp_extended + list(l_s) + [affine_carry],
    )
    qc.cx(Dirty[0], l_s[LS_WIDTH - 1])
    _const_minus_dirty(qc, l_s, n + 1, Dirty)

    def qpair(j: int) -> tuple[Qubit, Qubit]:
        idx = j - k
        return Work1[idx], Work2[idx]

    def first_leaf(encoded: int, equality: Qubit) -> None:
        j = encoded + 2
        addend, target = qpair(j)
        previous_addend, _ = qpair(j - 1)
        _apply_cell_borrowed(
            qc, "add", "first", acc, addend, target,
            previous_addend, Dirty[1],
        )
        # The direct-leaf range scan toggles its accumulator outside this leaf.

    qc.cx(Ctrl[0], acc)
    addend1, target1 = qpair(1)
    _apply_cell_borrowed(
        qc, "add", "first", Ctrl[0], addend1, target1,
        carry, Dirty[2],
    )
    if encoded_labels:
        unary_range_iteration_dirty_128raw(
            qc, index_reg=l_t, labels=encoded_labels, ctrl=Ctrl[0],
            range_acc=acc, ancillas=path, borrowed=Dirty[3:9],
            leaf_fn=first_leaf, order="inc",
            toggle_before_leaf=False,
            conditional_clean_helper=Ctrl[0],
        )

    def copy_selected_carry() -> None:
        def leaf(encoded: int, controls: Sequence[Qubit]) -> None:
            _toggle_raw_controls_dirty(
                qc, list(controls) + [Work1[encoded + 1]], acc, Dirty[3:],
            )

        unary_iteration_dirty_128raw(
            qc, index_reg=l_t, labels=encoded_labels,
            ctrl=Ctrl[0], ancillas=Scratch[:1],
            leaf_fn=leaf, order="inc",
        )

    def selected_carry_sign_toggle() -> None:
        def leaf(encoded: int, controls: Sequence[Qubit]) -> None:
            _toggle_raw_controls_dirty(
                qc, list(controls) + [Work1[encoded + 2]],
                Sign[0], Dirty[3:],
            )

        unary_iteration_dirty_128raw(
            qc, index_reg=l_t, labels=encoded_labels, ctrl=acc,
            ancillas=Scratch[:1], leaf_fn=leaf, order="inc",
        )

    if encoded_labels:
        # The range accumulator has returned to zero on the certified l_t
        # support.  Copy the dynamic carry into that fixed clean lane, then use
        # a two-map commutator.  The copied carry remains stable while Work1 is
        # the dirty upper-zero map, so two maps replace the former four-map
        # dirty-passenger sandwich.
        copy_selected_carry()
        selected_carry_sign_toggle()
        _upper_zero_map_midpoint_two_dirty(
            qc, ctrl=Ctrl[0], boundary_B=l_s, bits=Work2,
            dirty_map=Work1, dirty=Dirty, scratch=Scratch[:2],
        )
        selected_carry_sign_toggle()
        _upper_zero_map_midpoint_two_dirty(
            qc, ctrl=Ctrl[0], boundary_B=l_s, bits=Work2,
            dirty_map=Work1, dirty=Dirty, scratch=Scratch[:2],
        )
        copy_selected_carry()

    def second_leaf(encoded: int, equality: Qubit) -> None:
        j = encoded + 2
        addend, target = qpair(j)
        previous_addend, _ = qpair(j - 1)
        _apply_cell_borrowed(
            qc, "add", "second", acc, addend, target,
            previous_addend, Dirty[1],
        )

    if encoded_labels:
        unary_range_iteration_dirty_128raw(
            qc, index_reg=l_t, labels=encoded_labels, ctrl=Ctrl[0],
            range_acc=acc, ancillas=path, borrowed=Dirty[3:9],
            leaf_fn=second_leaf, order="dec",
            toggle_before_leaf=True,
            conditional_clean_helper=Ctrl[0],
        )
    _apply_cell_borrowed(
        qc, "add", "second", Ctrl[0], addend1, target1,
        carry, Dirty[2],
    )
    qc.cx(Ctrl[0], acc)

    _const_minus_dirty(qc, l_s, n + 1, Dirty)
    qc.cx(Dirty[0], l_s[LS_WIDTH - 1])
    qc.append(
        _e.cuccaro_sub_mod_2n_no_z_gate(LS_WIDTH, name="SUB_lrp8_from_ls9"),
        lrp_extended + list(l_s) + [affine_carry],
    )
    qc.x(affine_carry)
    dec_mod259_1ctrl_dirty(qc, affine_carry, l_s, Dirty)
    qc.x(affine_carry)
    return _e._finalize_block(qc)



def _range_scan_tight_dirty_octet_sentinel(
    qc: QuantumCircuit,
    *,
    leq: bool,
    boundary: Sequence[Qubit],
    k: int,
    K: int,
    ctrl: Qubit,
    scratch: Sequence[Qubit],
    borrowed: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Six-clean scan for up to 258 labels using raw endpoint sentinels."""
    labels = list(range(k, K + 1))
    if K <= 255:
        _range_scan_tight_dirty_octet(
            qc, leq=leq, boundary=boundary, k=k, K=K, ctrl=ctrl,
            scratch=scratch, borrowed=borrowed, leaf_fn=leaf_fn, order=order,
        )
        return
    if K > 259 or len(scratch) < 6 or len(borrowed) < 8:
        raise ValueError("sentinel scan supports ranges ending at most 259")
    main = [label for label in labels if label <= 255]
    sentinels = [label for label in labels if label > 255]
    if len(sentinels) > 4:
        raise ValueError("sentinel scan has more than four high endpoints")
    if main:
        main_depth = _tight_unary_depth_for_labels(main)
        range_acc = scratch[max(0, main_depth - 3)]
    else:
        range_acc = scratch[0]

    def scan_main(*, leq_mode: bool,
                      order_mode: Literal["inc", "dec"]) -> None:
        # The low tree branches only on bits 0..7.  Add !bit8 to each
        # equality toggle so boundaries 256..259 cannot alias low labels.
        # The range accumulator still carries Ctrl across the low block.
        qc.x(boundary[8])
        _range_scan_tight_dirty_octet(
            qc, leq=leq_mode, boundary=boundary,
            k=main[0], K=main[-1], ctrl=ctrl,
            scratch=scratch, borrowed=borrowed, leaf_fn=leaf_fn,
            order=order_mode, equality_guards=[boundary[8]],
        )
        qc.x(boundary[8])

    def toggle_eq(label: int) -> None:
        inverted = []
        for bit, lane in enumerate(boundary):
            if ((label >> bit) & 1) == 0:
                qc.x(lane)
                inverted.append(lane)
        _toggle_raw_controls_dirty(
            qc, [ctrl] + list(boundary), range_acc, borrowed,
        )
        for lane in reversed(inverted):
            qc.x(lane)

    if leq and order == "inc":
        if main:
            scan_main(leq_mode=True, order_mode="inc")
        else:
            qc.cx(ctrl, range_acc)
        for label in sentinels:
            leaf_fn(label, range_acc)
            toggle_eq(label)
    elif leq and order == "dec":
        for label in reversed(sentinels):
            toggle_eq(label)
            leaf_fn(label, range_acc)
        if main:
            scan_main(leq_mode=True, order_mode="dec")
        else:
            qc.cx(ctrl, range_acc)
    elif not leq and order == "dec":
        qc.cx(ctrl, range_acc)
        for label in reversed(sentinels):
            leaf_fn(label, range_acc)
            toggle_eq(label)
        if main:
            qc.cx(ctrl, range_acc)
            scan_main(leq_mode=False, order_mode="dec")
    elif not leq and order == "inc":
        if main:
            scan_main(leq_mode=False, order_mode="inc")
            qc.cx(ctrl, range_acc)
        for label in sentinels:
            toggle_eq(label)
            leaf_fn(label, range_acc)
        qc.cx(ctrl, range_acc)
    else:
        raise ValueError("bad sentinel scan mode/order")



def _terminal_aux6_decoder_alias(labels: Sequence[int], endpoint: int) -> int:
    """Classify an off-support endpoint through the pinned unary tree."""
    labels = list(sorted(set(labels)))
    if not labels:
        raise ValueError("terminal Aux6 alias needs a nonempty low support")
    while len(labels) > 1:
        bit = _e._split_bit(labels)
        branch = (endpoint >> bit) & 1
        labels = [
            label for label in labels
            if ((label >> bit) & 1) == branch
        ]
    return labels[0]


def _terminal_aux6_direct_inversion_mask(
    labels: Sequence[int], leaf: int, direct_depth: int = 4,
) -> int:
    """Return index-bit X conjugations live at a direct-leaf callback."""
    labels = list(sorted(set(labels)))
    if leaf not in labels:
        raise ValueError("terminal Aux6 leaf is outside the low support")
    while _tight_unary_depth_for_labels(labels) > direct_depth:
        bit = _e._split_bit(labels)
        branch = (leaf >> bit) & 1
        labels = [
            label for label in labels
            if ((label >> bit) & 1) == branch
        ]
    mask = 0
    while len(labels) > 1:
        bit = _e._split_bit(labels)
        branch = (leaf >> bit) & 1
        if branch == 0:
            mask |= 1 << bit
        labels = [
            label for label in labels
            if ((label >> bit) & 1) == branch
        ]
    return mask


def _range_scan_tight_dirty_hexadecet_aux6_terminal(
    qc: QuantumCircuit,
    *,
    leq: bool,
    boundary: Sequence[Qubit],
    k: int,
    K: int,
    ctrl: Qubit,
    scratch: Sequence[Qubit],
    borrowed: Sequence[Qubit],
    leaf_fn,
    order: Literal["inc", "dec"],
) -> None:
    """Exact three/four/five/six-clean terminal scan for labels through 259.

    A crossing window is split into [k,255] and labels 256..K.  The low tree
    aliases a high endpoint h to a low leaf a(h).  An exact endpoint toggle at
    that leaf cancels the false low-tree equality before the leaf can observe
    a wrong range control.  Each high label is then visited exactly once with
    an exact equality toggle.  This preserves the original leaf order and its
    nonidentity behavior when the range control is zero.
    """
    if k > K:
        raise ValueError("terminal Aux6 scan needs k <= K")
    if K > 259:
        raise ValueError("terminal Aux6 scan supports labels at most 259")
    clean_lanes = len(scratch)
    if clean_lanes == 2:
        if len(borrowed) < 8:
            raise ValueError("two-clean terminal scan needs eight dirty lenders")
        _range_scan_tight_dirty_256raw(
            qc, leq=leq, boundary=boundary, k=k, K=K, ctrl=ctrl,
            scratch=scratch, borrowed=borrowed, leaf_fn=leaf_fn, order=order,
        )
        return
    if clean_lanes < 3:
        if clean_lanes < 1 or len(borrowed) < 8:
            raise ValueError("direct terminal scan needs one clean lane and eight lenders")
        range_acc = scratch[0]

        def toggle_exact(label: int) -> None:
            inverted = []
            for bit, lane in enumerate(boundary):
                if ((label >> bit) & 1) == 0:
                    qc.x(lane)
                    inverted.append(lane)
            _toggle_raw_controls_dirty(
                qc, [ctrl] + list(boundary), range_acc, borrowed,
            )
            for lane in reversed(inverted):
                qc.x(lane)

        def toggle_values(values) -> None:
            for value in values:
                toggle_exact(value)

        # Initialize and clean the running predicate on the complete nine-bit
        # boundary domain, not just when the endpoint lies inside [k,K].
        if leq and order == "inc":
            toggle_values(range(k, 512))
            for label in range(k, K + 1):
                leaf_fn(label, range_acc)
                toggle_exact(label)
            toggle_values(range(K + 1, 512))
        elif leq and order == "dec":
            toggle_values(range(K, 512))
            for label in range(K, k - 1, -1):
                leaf_fn(label, range_acc)
                if label > k:
                    toggle_exact(label - 1)
            toggle_values(range(k, 512))
        elif not leq and order == "inc":
            toggle_values(range(0, k + 1))
            for label in range(k, K + 1):
                leaf_fn(label, range_acc)
                if label < K:
                    toggle_exact(label + 1)
            toggle_values(range(0, K + 1))
        elif not leq and order == "dec":
            toggle_values(range(0, K + 1))
            for label in range(K, k - 1, -1):
                leaf_fn(label, range_acc)
                toggle_exact(label)
            toggle_values(range(0, k))
        else:
            raise ValueError("bad direct terminal scan mode/order")
        return
    use_six_clean = clean_lanes >= 6
    use_five_clean = clean_lanes == 5
    use_four_clean = clean_lanes == 4
    if not (k <= 255 < K):
        if use_six_clean:
            scan = _range_scan_tight_dirty_octet
        elif use_five_clean:
            scan = _range_scan_tight_dirty_hexadecet
        elif use_four_clean:
            scan = _range_scan_tight_dirty_32raw
        else:
            scan = _range_scan_tight_dirty_64raw
        scan(
            qc, leq=leq, boundary=boundary, k=k, K=K, ctrl=ctrl,
            scratch=scratch, borrowed=borrowed, leaf_fn=leaf_fn, order=order,
        )
        return
    if len(boundary) != 9:
        raise ValueError("terminal Aux6 crossing scan needs a 9-bit endpoint")
    if len(scratch) < 3:
        raise ValueError("terminal crossing scan needs three clean lanes")
    if len(borrowed) < 8:
        raise ValueError("terminal Aux6 crossing scan needs eight dirty lenders")

    main = list(range(k, 256))
    depth = _tight_unary_depth_for_labels(main)
    path_reduction = (
        3 if use_six_clean else (4 if use_five_clean else (5 if use_four_clean else 6))
    )
    range_acc = scratch[max(0, depth - path_reduction)]
    high_endpoints = list(range(256, K + 1))

    def toggle_exact_endpoint(endpoint: int, current_xor_mask: int = 0) -> None:
        inverted = []
        for bit, lane in enumerate(boundary):
            current_expected = (
                ((endpoint >> bit) & 1) ^ ((current_xor_mask >> bit) & 1)
            )
            if current_expected == 0:
                qc.x(lane)
                inverted.append(lane)
        _toggle_raw_controls_dirty(
            qc, [ctrl] + list(boundary), range_acc, borrowed,
        )
        for lane in reversed(inverted):
            qc.x(lane)

    aliases = {
        endpoint: _terminal_aux6_decoder_alias(main, endpoint)
        for endpoint in high_endpoints
    }

    aliases_to_endpoints = {}
    for endpoint, alias in aliases.items():
        aliases_to_endpoints.setdefault(alias, []).append(endpoint)

    direct_masks = {
        label: _terminal_aux6_direct_inversion_mask(
            main, label, path_reduction,
        )
        for label in aliases_to_endpoints
    }

    def cancel_false_high_equality(label: int, _range_acc: Qubit) -> None:
        for endpoint in aliases_to_endpoints.get(label, ()):
            toggle_exact_endpoint(endpoint, direct_masks[label])

    def low_scan(*, toggle_before_leaf: bool) -> None:
        kwargs = dict(
            index_reg=boundary, labels=main, ctrl=ctrl,
            range_acc=range_acc,
            ancillas=scratch[:max(0, depth - path_reduction)],
            borrowed=borrowed, leaf_fn=leaf_fn, order=order,
            toggle_before_leaf=toggle_before_leaf,
            after_toggle_fn=cancel_false_high_equality,
        )
        if use_six_clean:
            unary_range_iteration_dirty_octet(qc, **kwargs)
        elif use_five_clean:
            unary_range_iteration_dirty_hexadecet(qc, **kwargs)
        elif use_four_clean:
            unary_range_iteration_dirty_32raw(qc, **kwargs)
        else:
            unary_range_iteration_dirty_64raw(qc, **kwargs)

    def high_scan(*, toggle_before_leaf: bool) -> None:
        endpoints = high_endpoints if order == "inc" else reversed(high_endpoints)
        for endpoint in endpoints:
            if toggle_before_leaf:
                toggle_exact_endpoint(endpoint)
            leaf_fn(endpoint, range_acc)
            if not toggle_before_leaf:
                toggle_exact_endpoint(endpoint)

    if leq and order == "inc":
        qc.cx(ctrl, range_acc)
        low_scan(toggle_before_leaf=False)
        high_scan(toggle_before_leaf=False)
    elif leq and order == "dec":
        high_scan(toggle_before_leaf=True)
        low_scan(toggle_before_leaf=True)
        qc.cx(ctrl, range_acc)
    elif not leq and order == "dec":
        qc.cx(ctrl, range_acc)
        high_scan(toggle_before_leaf=False)
        low_scan(toggle_before_leaf=False)
    elif not leq and order == "inc":
        low_scan(toggle_before_leaf=True)
        high_scan(toggle_before_leaf=True)
        qc.cx(ctrl, range_acc)
    else:
        raise ValueError("bad terminal Aux6 scan mode/order")


def _upper_zero_map_borrowed(qc: QuantumCircuit, *, ctrl: Qubit,
                             boundary_B: Sequence[Qubit], bits: Sequence[Qubit],
                             dirty_map: Sequence[Qubit], borrowed: Sequence[Qubit],
                             k: int, K: int, scratch: Sequence[Qubit]) -> None:
    borrowed = [borrowed] if isinstance(borrowed, Qubit) else list(borrowed)
    depth = _tight_unary_depth_for_labels(list(range(k, K + 1)))
    if len(scratch) < 1:
        raise ValueError("borrowed upper-zero map scratch shortage")

    def leaf_forward(j: int, bctrl: Qubit) -> None:
        idx = j - k
        _apply_not_factor_with_borrowed(
            qc, boundary_control=bctrl, data_bit=bits[idx],
            neighbor=None if j == K else dirty_map[idx + 1],
            target=dirty_map[idx], borrowed=borrowed[0],
        )

    def leaf_reverse(j: int, bctrl: Qubit) -> None:
        if j < K:
            idx = j - k
            _apply_not_factor_with_borrowed(
                qc, boundary_control=bctrl, data_bit=bits[idx],
                neighbor=dirty_map[idx + 1], target=dirty_map[idx],
                borrowed=borrowed[0],
            )

    _range_scan_tight_dirty_hexadecet_aux6_terminal(
        qc, leq=True, boundary=boundary_B, k=k, K=K, ctrl=ctrl,
        scratch=scratch, borrowed=borrowed, leaf_fn=leaf_forward, order="inc",
    )
    _range_scan_tight_dirty_hexadecet_aux6_terminal(
        qc, leq=True, boundary=boundary_B, k=k, K=K, ctrl=ctrl,
        scratch=scratch, borrowed=borrowed, leaf_fn=leaf_reverse, order="dec",
    )


def _lower_zero_map_borrowed(qc: QuantumCircuit, *, ctrl: Qubit,
                             boundary_A: Sequence[Qubit], bits: Sequence[Qubit],
                             dirty_map: Sequence[Qubit], borrowed: Sequence[Qubit],
                             k: int, K: int, scratch: Sequence[Qubit]) -> None:
    borrowed = [borrowed] if isinstance(borrowed, Qubit) else list(borrowed)
    depth = _tight_unary_depth_for_labels(list(range(k, K + 1)))
    if len(scratch) < 1:
        raise ValueError("borrowed lower-zero map scratch shortage")

    def leaf_forward(j: int, bctrl: Qubit) -> None:
        idx = j - k
        _apply_not_factor_with_borrowed(
            qc, boundary_control=bctrl, data_bit=bits[idx],
            neighbor=None if j == k else dirty_map[idx - 1],
            target=dirty_map[idx], borrowed=borrowed[0],
        )

    def leaf_reverse(j: int, bctrl: Qubit) -> None:
        if j > k:
            idx = j - k
            _apply_not_factor_with_borrowed(
                qc, boundary_control=bctrl, data_bit=bits[idx],
                neighbor=dirty_map[idx - 1], target=dirty_map[idx],
                borrowed=borrowed[0],
            )

    _range_scan_tight_dirty_hexadecet_aux6_terminal(
        qc, leq=False, boundary=boundary_A, k=k, K=K, ctrl=ctrl,
        scratch=scratch, borrowed=borrowed, leaf_fn=leaf_forward, order="dec",
    )
    _range_scan_tight_dirty_hexadecet_aux6_terminal(
        qc, leq=False, boundary=boundary_A, k=k, K=K, ctrl=ctrl,
        scratch=scratch, borrowed=borrowed, leaf_fn=leaf_reverse, order="inc",
    )


def _highest_position_xor_write_borrowed(qc: QuantumCircuit, *, ctrl: Qubit,
                                         boundary_B: Sequence[Qubit], bits: Sequence[Qubit],
                                         dirty_map: Sequence[Qubit], target_len: Sequence[Qubit],
                                         borrowed: Sequence[Qubit], k: int, K: int,
                                         scratch: Sequence[Qubit]) -> None:
    mask = (1 << len(target_len)) - 1

    def writes() -> None:
        for j in range(K, k, -1):
            _e.xor_const_into_reg_controls(
                qc, target_len, ((j - 1) ^ (j - 2)) & mask,
                ctrls=[ctrl, dirty_map[j - k]], scratch=scratch,
            )
        _e.xor_const_into_reg_controls(
            qc, target_len, ((k - 1) ^ mask) & mask,
            ctrls=[ctrl, dirty_map[0]], scratch=scratch,
        )

    _e.xor_const_into_reg_controls(qc, target_len, (K - 1) & mask,
                                   ctrls=[ctrl], scratch=scratch)
    writes()
    _upper_zero_map_borrowed(
        qc, ctrl=ctrl, boundary_B=boundary_B, bits=bits, dirty_map=dirty_map,
        borrowed=borrowed, k=k, K=K, scratch=scratch,
    )
    writes()
    _upper_zero_map_borrowed(
        qc, ctrl=ctrl, boundary_B=boundary_B, bits=bits, dirty_map=dirty_map,
        borrowed=borrowed, k=k, K=K, scratch=scratch,
    )


def _right_length_xor_write_borrowed(qc: QuantumCircuit, *, n: int, ctrl: Qubit,
                                     boundary_A: Sequence[Qubit], bits: Sequence[Qubit],
                                     dirty_map: Sequence[Qubit], target_len: Sequence[Qubit],
                                     borrowed: Sequence[Qubit], k: int, K: int,
                                     scratch: Sequence[Qubit]) -> None:
    mask = (1 << len(target_len)) - 1

    def val(pos: int) -> int:
        return (n + 3 - pos) & mask

    def writes() -> None:
        for j in range(k, K):
            _e.xor_const_into_reg_controls(
                qc, target_len, val(j) ^ val(j + 1),
                ctrls=[ctrl, dirty_map[j - k]], scratch=scratch,
            )
        _e.xor_const_into_reg_controls(
            qc, target_len, val(K) ^ mask,
            ctrls=[ctrl, dirty_map[K - k]], scratch=scratch,
        )

    _e.xor_const_into_reg_controls(qc, target_len, val(k),
                                   ctrls=[ctrl], scratch=scratch)
    writes()
    _lower_zero_map_borrowed(
        qc, ctrl=ctrl, boundary_A=boundary_A, bits=bits, dirty_map=dirty_map,
        borrowed=borrowed, k=k, K=K, scratch=scratch,
    )
    writes()
    _lower_zero_map_borrowed(
        qc, ctrl=ctrl, boundary_A=boundary_A, bits=bits, dirty_map=dirty_map,
        borrowed=borrowed, k=k, K=K, scratch=scratch,
    )


def _const_minus_258_tight(
    qc: QuantumCircuit,
    register: Sequence[Qubit],
    scratch: Sequence[Qubit],
) -> None:
    """Apply y -> 258-y modulo 512 with eight clean lanes."""
    register = list(register)
    if len(register) != 9 or len(scratch) < 8:
        raise ValueError("tight 258-y map requires width 9 and eight scratch")
    for lane in register:
        qc.x(lane)
    _e.inc_mod2n_uncontrolled(qc, register, scratch[:8])
    _e.inc_mod2n_uncontrolled(qc, register[1:], scratch[:7])
    qc.x(register[8])


def _add_three_tight(
    qc: QuantumCircuit,
    register: Sequence[Qubit],
    scratch: Sequence[Qubit],
) -> None:
    """Add three modulo 512 with eight clean lanes."""
    register = list(register)
    if len(register) != 9 or len(scratch) < 8:
        raise ValueError("tight +3 map requires width 9 and eight scratch")
    _e.inc_mod2n_uncontrolled(qc, register, scratch[:8])
    _e.inc_mod2n_uncontrolled(qc, register[1:], scratch[:7])


def _sub_three_tight(
    qc: QuantumCircuit,
    register: Sequence[Qubit],
    scratch: Sequence[Qubit],
) -> None:
    """Subtract three modulo 512 with eight clean lanes."""
    register = list(register)
    if len(register) != 9 or len(scratch) < 8:
        raise ValueError("tight -3 map requires width 9 and eight scratch")
    _e.dec_mod2n_uncontrolled(qc, register[1:], scratch[:7])
    _e.dec_mod2n_uncontrolled(qc, register, scratch[:8])


@lru_cache(maxsize=None)
def compact_len_update_lt_gate(*, n: int, k: int, K: int,
                               name: str = "LEN_LT_COMPACT") -> Gate:
    M = K - k + 1
    Ctrl = QuantumRegister(1, "Ctrl")
    Work1 = QuantumRegister(M, "Work1")
    Work2 = QuantumRegister(M, "Work2")
    l_t = QuantumRegister(LT_WIDTH, "l_t")
    l_rp = QuantumRegister(LRP_WIDTH, "l_rp")
    Dirty = QuantumRegister(8, "DirtyPassenger")
    Extension = QuantumRegister(1, "Extension")
    Scratch = QuantumRegister(2, "Scratch")
    qc = _e._block_circuit(
        Ctrl, Work1, Work2, l_t, l_rp, Dirty, Extension, Scratch,
        name=name,
    )
    extension = Extension[0]
    boundary = list(l_rp) + [extension]
    map_scratch = list(Scratch)
    _const_minus_dirty(qc, boundary, 258, Dirty)
    _highest_position_xor_write_borrowed(
        qc, ctrl=Ctrl[0], boundary_B=boundary, bits=Work2, dirty_map=Work1,
        target_len=l_t, borrowed=Dirty, k=k, K=K, scratch=map_scratch,
    )
    _highest_position_xor_write_borrowed(
        qc, ctrl=Ctrl[0], boundary_B=boundary, bits=Work1, dirty_map=Work2,
        target_len=l_t, borrowed=Dirty, k=k, K=K, scratch=map_scratch,
    )
    _const_minus_dirty(qc, boundary, 258, Dirty)
    return _e._finalize_block(qc)


@lru_cache(maxsize=None)
def compact_len_update_lrp_gate(*, n: int, k: int, K: int,
                                name: str = "LEN_LRP_COMPACT") -> Gate:
    M = K - k + 1
    Ctrl = QuantumRegister(1, "Ctrl")
    Work1 = QuantumRegister(M, "Work1")
    Work2 = QuantumRegister(M, "Work2")
    l_t = QuantumRegister(LT_WIDTH, "l_t")
    l_rp = QuantumRegister(LRP_WIDTH, "l_rp")
    Dirty = QuantumRegister(8, "DirtyPassenger")
    Extension = QuantumRegister(1, "Extension")
    Scratch = QuantumRegister(2, "Scratch")
    qc = _e._block_circuit(
        Ctrl, Work1, Work2, l_t, l_rp, Dirty, Extension, Scratch,
        name=name,
    )
    extension = Extension[0]
    boundary = list(l_t) + [extension]
    map_scratch = list(Scratch)
    _add_const_dirty(qc, boundary, 3, Dirty)
    _right_length_xor_write_borrowed(
        qc, n=n, ctrl=Ctrl[0], boundary_A=boundary, bits=Work1, dirty_map=Work2,
        target_len=l_rp, borrowed=Dirty, k=k, K=K, scratch=map_scratch,
    )
    _right_length_xor_write_borrowed(
        qc, n=n, ctrl=Ctrl[0], boundary_A=boundary, bits=Work2, dirty_map=Work1,
        target_len=l_rp, borrowed=Dirty, k=k, K=K, scratch=map_scratch,
    )
    _sub_const_dirty(qc, boundary, 3, Dirty)
    return _e._finalize_block(qc)


@lru_cache(maxsize=None)
def compact_swap_work_and_len_gate(*, n: int, k4: int, K4: int,
                                   k5: int, K5: int,
                                   name: str = "SWAP_AND_LEN_COMPACT") -> Gate:
    work_size = n + 3
    Ctrl = QuantumRegister(1, "Ctrl")
    Work1 = QuantumRegister(work_size, "Work1")
    Work2 = QuantumRegister(work_size, "Work2")
    l_t = QuantumRegister(LT_WIDTH, "l_t")
    l_rp = QuantumRegister(LRP_WIDTH, "l_rp")
    Dirty = QuantumRegister(8, "DirtyPassenger")
    Extension = QuantumRegister(1, "Extension")
    Scratch = QuantumRegister(2, "Scratch")
    qc = _e._block_circuit(
        Ctrl, Work1, Work2, l_t, l_rp, Dirty, Extension, Scratch,
        name=name,
    )
    for i in range(work_size):
        _e.cswap_toffoli(qc, Ctrl[0], Work1[i], Work2[i])
    gate_lt = compact_len_update_lt_gate(n=n, k=k4, K=K4)
    _e._append_with_optional_clbits(
        qc, gate_lt,
        [Ctrl[0]] + list(Work1[k4 - 1:K4]) + list(Work2[k4 - 1:K4])
        + list(l_t) + list(l_rp)
        + list(Dirty) + [Extension[0]] + list(Scratch),
    )
    gate_lrp = compact_len_update_lrp_gate(n=n, k=k5, K=K5)
    _e._append_with_optional_clbits(
        qc, gate_lrp,
        [Ctrl[0]] + list(Work1[k5 - 1:K5]) + list(Work2[k5 - 1:K5])
        + list(l_t) + list(l_rp)
        + list(Dirty) + [Extension[0]] + list(Scratch),
    )
    return _e._finalize_block(qc)


@lru_cache(maxsize=None)
def compact_tail_zero_gate(*, n: int,
                           name: str = "T_TAIL_ZERO_COMPACT") -> Gate:
    work_size = n + 3
    Ctrl = QuantumRegister(1, "Ctrl")
    Tail = QuantumRegister(1, "Tail")
    Work1 = QuantumRegister(work_size, "Work1")
    Work2 = QuantumRegister(work_size, "Work2")
    l_t = QuantumRegister(LT_WIDTH, "l_t")
    l_s = QuantumRegister(LS_WIDTH, "l_s")
    l_rp = QuantumRegister(LRP_WIDTH, "l_rp")
    Borrowed = QuantumRegister(1, "Borrowed")
    Scratch = QuantumRegister(9, "Scratch")
    qc = _e._block_circuit(Ctrl, Tail, Work1, Work2, l_t, l_s, l_rp,
                           Borrowed, Scratch, name=name)
    carry = Scratch[8]
    lrp_extended = list(l_rp) + [Borrowed[0]]
    affine_scratch = list(Scratch)
    qc.append(_e.cuccaro_add_mod_2n_no_z_gate(LS_WIDTH, name="ADD_lrp8_to_ls9"),
              lrp_extended + list(l_s) + [carry])
    # The borrowed high addend contributes exactly 256 modulo 512.  Cancel it
    # without learning or changing the borrowed value.
    qc.cx(Borrowed[0], l_s[LS_WIDTH - 1])
    _e.const_minus_inplace(qc, l_s, n, affine_scratch)

    def selected_dirty_toggle() -> None:
        labels = list(range(0, work_size - 3))
        depth = _tight_unary_depth_for_labels(labels)

        def leaf(encoded_length: int, ej: Qubit) -> None:
            qc.ccx(ej, Work1[encoded_length + 2], Tail[0])

        unary_iteration_tight(
            qc, index_reg=l_t, labels=labels, ctrl=Ctrl[0],
            ancillas=list(Scratch[:depth]), leaf_fn=leaf, order="inc",
        )

    map_scratch = list(Scratch)
    selected_dirty_toggle()
    _upper_zero_map_borrowed(
        qc, ctrl=Ctrl[0], boundary_B=l_s, bits=Work2, dirty_map=Work1,
        borrowed=Borrowed[0], k=0, K=work_size - 1, scratch=map_scratch,
    )
    selected_dirty_toggle()
    _upper_zero_map_borrowed(
        qc, ctrl=Ctrl[0], boundary_B=l_s, bits=Work2, dirty_map=Work1,
        borrowed=Borrowed[0], k=0, K=work_size - 1, scratch=map_scratch,
    )

    _e.const_minus_inplace(qc, l_s, n, affine_scratch)
    qc.cx(Borrowed[0], l_s[LS_WIDTH - 1])
    qc.append(_e.cuccaro_sub_mod_2n_no_z_gate(LS_WIDTH, name="SUB_lrp8_from_ls9"),
              lrp_extended + list(l_s) + [carry])
    return _e._finalize_block(qc)


@lru_cache(maxsize=None)
def compact_lower_borrow_gate(*, n: int,
                              name: str = "T_LOWER_BORROW_COMPACT") -> Gate:
    work_size = n + 3
    Ctrl = QuantumRegister(1, "Ctrl")
    Tail = QuantumRegister(1, "Tail")
    Neg = QuantumRegister(1, "Neg")
    Work1 = QuantumRegister(work_size, "Work1")
    Work2 = QuantumRegister(work_size, "Work2")
    l_t = QuantumRegister(LT_WIDTH, "l_t")
    Borrowed = QuantumRegister(1, "Borrowed")
    Scratch = QuantumRegister(9, "Scratch")
    qc = _e._block_circuit(Ctrl, Tail, Neg, Work1, Work2, l_t,
                           Borrowed, Scratch, name=name)
    carry, active, eq = Scratch[:3]
    eq_pool = list(Scratch[3:])
    qc.ccx(Ctrl[0], Tail[0], active)

    def first_pass_cell(idx: int) -> None:
        addend = Work1[idx]
        target = Work2[idx]
        carry_in = carry if idx == 0 else Work1[idx - 1]
        qc.cx(carry_in, target)
        qc.cx(addend, carry_in)
        qc.ccx(carry_in, target, addend)

    for idx in range(work_size):
        first_pass_cell(idx)
        physical = idx + 1
        if 2 <= physical <= 257:
            _e.compute_eq_const(qc, l_t, physical - 2, eq, eq_pool)
            _borrowed_c3x(qc, active, eq, Work1[idx], Neg[0], Borrowed[0])
            _e.compute_eq_const(qc, l_t, physical - 2, eq, eq_pool)

    for idx in range(work_size - 1, -1, -1):
        addend = Work1[idx]
        target = Work2[idx]
        carry_in = carry if idx == 0 else Work1[idx - 1]
        qc.ccx(carry_in, target, addend)
        qc.cx(addend, carry_in)
        qc.cx(carry_in, target)
    qc.ccx(Ctrl[0], Tail[0], active)
    return _e._finalize_block(qc)

@lru_cache(maxsize=None)
def swap_work_and_len_unary_shared_gate(*, n: int, len_width: int, k4: int, K4: int,
                                        k5: int, K5: int, name: str = "SWAP_AND_LEN_S835_FAST") -> Gate:
    work_size = n + 3
    depth4 = _e.unary_depth(K4 - k4 + 1)
    depth5 = _e.unary_depth(K5 - k5 + 1)
    scratch4 = max(len_width + 1, depth4 + 2)
    scratch5 = max(len_width + 1, depth5 + 2)
    scratch_size = max(scratch4, scratch5)
    Ctrl = QuantumRegister(1, "Ctrl")
    Work1 = QuantumRegister(work_size, "Work1")
    Work2 = QuantumRegister(work_size, "Work2")
    l_t = QuantumRegister(len_width, "l_t")
    l_rp = QuantumRegister(len_width, "l_rp")
    Scratch = QuantumRegister(scratch_size, "Scratch")
    qc = _e._block_circuit(Ctrl, Work1, Work2, l_t, l_rp, Scratch, name=name)
    for i in range(work_size):
        _e.cswap_toffoli(qc, Ctrl[0], Work1[i], Work2[i])
    gate_lt = len_update_lt_unary_gate(n=n, k=k4, K=K4, len_width=len_width)
    _e._append_with_optional_clbits(qc, gate_lt, [Ctrl[0]] + list(Work1[k4 - 1:K4]) + list(Work2[k4 - 1:K4])
                                    + list(l_t) + list(l_rp) + list(Scratch[:scratch4]))
    gate_lrp = len_update_lrp_unary_gate(n=n, k=k5, K=K5, len_width=len_width)
    _e._append_with_optional_clbits(qc, gate_lrp, [Ctrl[0]] + list(Work1[k5 - 1:K5]) + list(Work2[k5 - 1:K5])
                                    + list(l_t) + list(l_rp) + list(Scratch[:scratch5]))
    return _e._finalize_block(qc)


def _fastdual_interval_scratch_size(n: int, k: int, K: int, len_width: int, shift_width: int) -> int:
    """Scratch size used by ``lc_interval_addsub_unary_gate``.

    This helper mirrors the scratch layout in ``lc_interval_addsub_unary_gate``.
    It is intentionally kept next to ``qiskit_paper_aux_size`` because the
    default Aux size used by the checkpointed counter must scale with this
    value.  For n=256 the worst case is 19 scratch qubits plus the temporary
    Ctrl bit, i.e. Aux=20.  For n=512 the unary path depth increases by one
    on each of the two endpoint scans, so the worst-case scratch is 21 and
    Aux must be 22.
    """
    if k > K:
        return 0
    endpoint_width = max(len_width, shift_width)
    rel_count = K - k + 1
    labels_main = list(range(rel_count))
    if rel_count > 1 and ((rel_count - 1) & (rel_count - 2)) == 0:
        # Same top-special split as lc_interval_addsub_unary_gate.
        labels_main = list(range(rel_count - 1))
    depth = _tight_unary_depth_for_labels(labels_main) if labels_main else 0
    base = max(2 * depth, endpoint_width)
    return base + 3


def _fastdual_prefix_scratch_size(k: int, K: int, len_width: int) -> int:
    if k > K:
        return 0
    depth = _e.unary_depth(K - k + 1)
    return max(depth, len_width) + 3


def _fastdual_interval_scratch_size(label_count: int, endpoint_width: int) -> int:
    """Scratch qubits used by lc_interval_addsub_unary_gate.

    The FASTDUAL interval Add/Sub block handles a one-more-than-a-power-of-two
    interval by pulling the top label out as a special endpoint.  Its two endpoint
    unary paths therefore have depth based on ``main_count`` rather than directly
    on ``label_count``.  The scratch layout in lc_interval_addsub_unary_gate is

        base = max(2*depth, endpoint_width)
        Scratch[base], Scratch[base+1], Scratch[base+2]

    so the number of scratch qubits needed by the block is ``base + 3``.
    This is 19 for n=256 but grows to 21 for n=384/512; the previous hard-coded
    lower bound of 19 caused the n=512 qubit-arity mismatch.
    """
    depth = _tight_unary_depth_for_labels(list(range(label_count))) if label_count > 1 else 0
    return max(2 * depth, endpoint_width) + 3


def fixed_schedule_shift_width(n: int, base_width: int, T_max: int) -> int:
    """Retain every post-terminal rotation without wrapping the pointer."""
    max_padding = max(1, T_max - 4 * n)
    return max(base_width, max_padding.bit_length())


def safe_active_windows(n: int, T: int) -> dict[str, tuple[int, int]]:
    """Return universally certified windows for secp256k1's fixed schedule."""
    if n == 256:
        if not 1 <= T <= len(_CERTIFIED_WINDOW_ROWS):
            raise ValueError(f"certified secp256k1 step out of range: {T}")
        row = _CERTIFIED_WINDOW_ROWS[T - 1]

        # A null certified window means the block control is unreachable on
        # every valid secp256k1 state at this step.  A singleton keeps the
        # generic controlled gate shape while adding no semantic assumption.
        def window(name: str) -> tuple[int, int]:
            value = row[name]
            return (1, 1) if value is None else (int(value[0]), int(value[1]))

        return {
            "r_addsub": window("r_addsub"),
            "swap": window("quotient_swap"),
            "t_addsub": window("t_addsub"),
            "len_update_lt": window("len_update_lt"),
            "len_update_lrp": window("len_update_lrp"),
        }
    try:
        return _e.active_windows(n, T)
    except ValueError:
        work_size = n + 3
        return {
            "r_addsub": (1, work_size),
            "swap": (1, work_size - 1),
            "t_addsub": (1, work_size),
            "len_update_lt": (1, work_size),
            "len_update_lrp": (1, work_size),
        }


@lru_cache(maxsize=None)
def compact_pre_shift_gate(*, work_size: int,
                           name: str = "PRE_SHIFT_MOD259") -> Gate:
    Phase1 = QuantumRegister(1, "Phase1")
    Phase2 = QuantumRegister(1, "Phase2")
    Work2 = QuantumRegister(work_size, "Work2")
    l_s = QuantumRegister(LS_WIDTH, "l_s")
    Dirty = QuantumRegister(DIRTY_PASSENGER_SIZE, "DirtyPassenger")
    Scratch = QuantumRegister(1, "Scratch")
    qc = _e._block_circuit(
        Phase1, Phase2, Work2, l_s, Dirty, Scratch, name=name,
    )
    both = Scratch[0]

    qc.x(Phase1[0])
    for i in range(work_size - 1):
        _e.cswap_toffoli(qc, Phase1[0], Work2[i], Work2[i + 1])
    inc_mod259_1ctrl_dirty(qc, Phase1[0], l_s, Dirty)

    qc.ccx(Phase1[0], Phase2[0], both)
    _e.controlled_rotate_right_by_two(qc, both, list(Work2))
    dec_mod259_1ctrl_dirty(qc, both, l_s, Dirty)
    dec_mod259_1ctrl_dirty(qc, both, l_s, Dirty)
    qc.ccx(Phase1[0], Phase2[0], both)

    qc.x(Phase1[0])
    return _e._finalize_block(qc)


@lru_cache(maxsize=None)
def compact_post_shift_gate(*, work_size: int,
                            name: str = "POST_SHIFT_MOD259") -> Gate:
    Phase1 = QuantumRegister(1, "Phase1")
    Phase2 = QuantumRegister(1, "Phase2")
    Work2 = QuantumRegister(work_size, "Work2")
    l_s = QuantumRegister(LS_WIDTH, "l_s")
    Dirty = QuantumRegister(DIRTY_PASSENGER_SIZE, "DirtyPassenger")
    Scratch = QuantumRegister(1, "Scratch")
    qc = _e._block_circuit(
        Phase1, Phase2, Work2, l_s, Dirty, Scratch, name=name,
    )
    both = Scratch[0]

    for i in range(work_size - 1):
        _e.cswap_toffoli(qc, Phase1[0], Work2[i], Work2[i + 1])
    inc_mod259_1ctrl_dirty(qc, Phase1[0], l_s, Dirty)
    qc.ccx(Phase1[0], Phase2[0], both)
    _e.controlled_rotate_right_by_two(qc, both, list(Work2))
    dec_mod259_1ctrl_dirty(qc, both, l_s, Dirty)
    dec_mod259_1ctrl_dirty(qc, both, l_s, Dirty)
    qc.ccx(Phase1[0], Phase2[0], both)
    return _e._finalize_block(qc)


@lru_cache(maxsize=None)
def compact_phase_update_gate(name: str = "PHASE_UPDATE_COMPACT") -> Gate:
    Phase1 = QuantumRegister(1, "Phase1")
    Phase2 = QuantumRegister(1, "Phase2")
    Sign = QuantumRegister(1, "Sign")
    l_q = QuantumRegister(LQ_WIDTH, "l_q")
    l_rp = QuantumRegister(LRP_WIDTH, "l_rp")
    l_s = QuantumRegister(LS_WIDTH, "l_s")
    Dirty = QuantumRegister(DIRTY_PASSENGER_SIZE, "DirtyPassenger")
    Scratch = QuantumRegister(1, "Scratch")
    qc = _e._block_circuit(
        Phase1, Phase2, Sign, l_q, l_rp, l_s, Dirty, Scratch, name=name,
    )
    z_lrp = Scratch[0]

    def toggle_eq(
        register: Sequence[Qubit],
        value: int,
        target: Qubit,
        extra_controls: Sequence[Qubit] = (),
    ) -> None:
        inverted = []
        for bit, lane in enumerate(register):
            if ((value >> bit) & 1) == 0:
                qc.x(lane)
                inverted.append(lane)
        _toggle_raw_controls_dirty(
            qc, list(register) + list(extra_controls), target, Dirty,
        )
        for lane in reversed(inverted):
            qc.x(lane)

    toggle_eq(l_rp, LRP_ZERO, z_lrp)
    # A & !Z = A xor (A & Z).  This avoids storing both equality flags.
    toggle_eq(l_q, (1 << LQ_WIDTH) - 1, Phase2[0], [Sign[0]])
    toggle_eq(l_q, (1 << LQ_WIDTH) - 1, Phase2[0], [z_lrp, Sign[0]])
    toggle_eq(l_q, (1 << LQ_WIDTH) - 1, Phase2[0], [Phase1[0]])
    toggle_eq(l_q, (1 << LQ_WIDTH) - 1, Phase2[0], [z_lrp, Phase1[0]])
    toggle_eq(l_q, (1 << LQ_WIDTH) - 1, Sign[0], [Phase2[0]])
    toggle_eq(l_q, (1 << LQ_WIDTH) - 1, Sign[0], [z_lrp, Phase2[0]])
    toggle_eq(l_rp, LRP_ZERO, z_lrp)

    # Modulo-259 revisits the shift-zero sentinel during terminal padding.
    # Guard the phase transition with l_rp != 0 so padding remains frozen.
    toggle_eq(l_rp, LRP_ZERO, z_lrp)
    toggle_eq(l_s, LS_ZERO, Phase1[0])
    toggle_eq(l_s, LS_ZERO, Phase1[0], [z_lrp])
    toggle_eq(l_s, LS_ZERO, Phase2[0])
    toggle_eq(l_s, LS_ZERO, Phase2[0], [z_lrp])
    toggle_eq(l_rp, LRP_ZERO, z_lrp)
    return _e._finalize_block(qc)


def qiskit_paper_aux_size(n: int, len_width: int, shift_width: int, T_max: Optional[int] = None,
                          include_algorithm1: bool = False) -> int:
    if n != 256:
        raise ValueError("exact-width dirty12 route is certified only for secp256k1")
    return CLEAN_AUX_SIZE

def make_global_registers_noctrl(*, n: int, len_width: int, shift_width: int,
                                 T_max: Optional[int] = None, include_algorithm1: bool = False,
                                 aux_size: Optional[int] = None):
    work_size = n + 3
    Phase1 = QuantumRegister(1, "Phase1")
    Phase2 = QuantumRegister(1, "Phase2")
    Iter = QuantumRegister(1, "Iter")
    Sign = QuantumRegister(1, "Sign")
    Work1 = QuantumRegister(work_size, "Work1")
    Work2 = QuantumRegister(work_size, "Work2")
    l_t = QuantumRegister(LT_WIDTH, "l_t")
    l_q = QuantumRegister(LQ_WIDTH, "l_q")
    l_s = QuantumRegister(LS_WIDTH, "l_s")
    l_rp = QuantumRegister(LRP_WIDTH, "l_rp")
    if aux_size is None:
        aux_size = qiskit_paper_aux_size(n, len_width, shift_width, T_max, include_algorithm1)
    if aux_size != CLEAN_AUX_SIZE:
        raise ValueError(f"exact-width route requires Aux={CLEAN_AUX_SIZE}")
    Aux = QuantumRegister(aux_size, "Aux")
    Dirty = QuantumRegister(DIRTY_PASSENGER_SIZE, "DirtyPassenger")
    TAnc = QuantumRegister(TIGHT_ANC_SIZE, "TAnc")
    return Phase1, Phase2, Iter, Sign, Work1, Work2, l_t, l_q, l_s, l_rp, Aux, Dirty, TAnc


def _make_condition(qc: QuantumCircuit, conditions, out: Qubit, scratch: Sequence[Qubit]) -> None:
    _e.compute_control(qc, conditions, out, scratch)


def _toggle_phase_b_from_lq(
    qc: QuantumCircuit,
    *,
    phase1: Qubit,
    phase2: Qubit,
    l_q: Sequence[Qubit],
) -> None:
    """Toggle Phase2 exactly on phase-B states at the T-add boundary."""
    marker = l_q[LQ_WIDTH - 1]
    qc.x(phase1)
    qc.x(marker)
    qc.ccx(phase1, marker, phase2)
    qc.x(marker)
    qc.x(phase1)


def _toggle_phase_d_marker(
    qc: QuantumCircuit,
    *,
    phase1: Qubit,
    phase2: Qubit,
    l_q: Sequence[Qubit],
    dirty: Sequence[Qubit],
) -> None:
    """Toggle Phase2 on the reserved physical l_q=255 phase-D marker."""
    marker = l_q[LQ_WIDTH - 1]
    qc.x(marker)
    _toggle_raw_controls_dirty(
        qc, [phase1] + list(l_q), phase2, dirty,
    )
    qc.x(marker)


def _toggle_phase_b_sentinel(
    qc: QuantumCircuit,
    *,
    phase1: Qubit,
    phase2: Qubit,
    l_q: Sequence[Qubit],
    dirty: Sequence[Qubit],
) -> None:
    """Swap physical l_q codes 511 and 255 on phase-B states.

    The truth-minus-one encoding makes semantic l_q=0 physical code 511.
    Phase B excludes physical code 255, so that code is a reversible marker
    for the omitted endpoint while Phase2 is loaned to the R block.
    """
    marker = l_q[LQ_WIDTH - 1]
    qc.x(phase1)
    _toggle_raw_controls_dirty(
        qc, [phase1, phase2] + list(l_q[: LQ_WIDTH - 1]), marker, dirty,
    )
    qc.x(phase1)


def _borrow_phase2_for_tadd(
    qc: QuantumCircuit,
    *,
    phase1: Qubit,
    phase2: Qubit,
    l_q: Sequence[Qubit],
    dirty: Sequence[Qubit],
    inverse: bool = False,
) -> None:
    """Clear/restore Phase2 using the physical truth-minus-one l_q domain.

    At the T-add boundary the four legal domains are A=(00,511),
    B=(01,0..255), C=(10,0..254 or 511), and D=(11,511).
    D is moved to reserved code 255 and B is recoverable from Phase1=0
    with the l_q high bit clear. Phase2 is therefore clean for the complete
    T-add block and the inverse sequence restores both registers exactly.
    """
    if len(l_q) != LQ_WIDTH:
        raise ValueError("T-add Phase2 loan requires the nine-bit l_q register")
    marker = l_q[LQ_WIDTH - 1]
    if not inverse:
        qc.ccx(phase1, phase2, marker)
        _toggle_phase_d_marker(
            qc, phase1=phase1, phase2=phase2, l_q=l_q, dirty=dirty,
        )
        _toggle_phase_b_from_lq(
            qc, phase1=phase1, phase2=phase2, l_q=l_q,
        )
    else:
        _toggle_phase_b_from_lq(
            qc, phase1=phase1, phase2=phase2, l_q=l_q,
        )
        _toggle_phase_d_marker(
            qc, phase1=phase1, phase2=phase2, l_q=l_q, dirty=dirty,
        )
        qc.ccx(phase1, phase2, marker)


def _borrow_phase2_for_r(
    qc: QuantumCircuit,
    *,
    ctrl: Qubit,
    phase1: Qubit,
    phase2: Qubit,
    l_q: Sequence[Qubit],
    dirty: Sequence[Qubit],
    inverse: bool = False,
) -> None:
    """Clear/restore Phase2 on the broader R-boundary phase-B domain."""
    if not inverse:
        _toggle_phase_b_sentinel(
            qc, phase1=phase1, phase2=phase2, l_q=l_q, dirty=dirty,
        )
        _borrow_phase2_for_tadd(
            qc, phase1=phase1, phase2=phase2, l_q=l_q, dirty=dirty,
        )
        _toggle_live_r_phase2_mode(
            qc, ctrl=ctrl, mode=phase1, phase2=phase2,
            l_q=l_q, dirty=dirty,
        )
    else:
        _toggle_live_r_phase2_mode(
            qc, ctrl=ctrl, mode=phase1, phase2=phase2,
            l_q=l_q, dirty=dirty, inverse=True,
        )
        _borrow_phase2_for_tadd(
            qc, phase1=phase1, phase2=phase2, l_q=l_q, dirty=dirty,
            inverse=True,
        )
        _toggle_phase_b_sentinel(
            qc, phase1=phase1, phase2=phase2, l_q=l_q, dirty=dirty,
        )


def _canonicalize_lq_for_iter_loan(
    qc: QuantumCircuit,
    *,
    phase1: Qubit,
    l_q: Sequence[Qubit],
    dirty: Sequence[Qubit],
) -> None:
    """Map the weight-at-most-255 T-add domain to l_q=0..255.

    After the Phase2 loan, Phase1=0 uses codes 0..254 and 511, while
    Phase1=1 uses 0..253, 255, and 511.  The two missing weight-256 endpoints
    would be B:255 and C:254.  Excluding only those endpoints leaves exactly
    256 codes per Phase1 value, so this involution moves the sentinel 511 to
    the missing low code in each branch.
    """
    if len(l_q) != LQ_WIDTH:
        raise ValueError("T-add Iter loan requires the nine-bit l_q register")

    # Phase1=0: swap 511 and 255 (they differ only in the high bit).
    qc.x(phase1)
    _toggle_raw_controls_dirty(
        qc, [phase1] + list(l_q[:8]), l_q[8], dirty,
    )
    qc.x(phase1)

    # Phase1=1: swap 511 and 254 along the Gray path 511 -> 510 -> 254.
    gray_controls = [phase1, l_q[8]] + list(l_q[1:8])
    _toggle_raw_controls_dirty(qc, gray_controls, l_q[0], dirty)
    qc.x(l_q[0])
    _toggle_raw_controls_dirty(
        qc, [phase1] + list(l_q[:8]), l_q[8], dirty,
    )
    qc.x(l_q[0])
    _toggle_raw_controls_dirty(qc, gray_controls, l_q[0], dirty)


def _borrow_iter_for_tadd(
    qc: QuantumCircuit,
    *,
    phase1: Qubit,
    iteration: Qubit,
    l_q: Sequence[Qubit],
    dirty: Sequence[Qubit],
    inverse: bool = False,
) -> None:
    """Clear/restore Iter by packing it into canonical l_q bit 8."""
    marker = l_q[LQ_WIDTH - 1]
    if not inverse:
        _canonicalize_lq_for_iter_loan(
            qc, phase1=phase1, l_q=l_q, dirty=dirty,
        )
        qc.cx(iteration, marker)
        qc.cx(marker, iteration)
    else:
        qc.cx(marker, iteration)
        qc.cx(iteration, marker)
        _canonicalize_lq_for_iter_loan(
            qc, phase1=phase1, l_q=l_q, dirty=dirty,
        )


def _toggle_live_r_phase(qc: QuantumCircuit, *, phase1: Qubit,
                         l_rp: Sequence[Qubit], out: Qubit,
                         dirty: Sequence[Qubit]) -> None:
    """Toggle ``out`` by ``l_rp != 0 and phase1 == 0`` on valid EEA states.

    Length zero is encoded as all ones.  The Algorithm-3 terminal transition
    produces Phase1=Phase2=Sign=0, and padding preserves those controls.  Thus
    terminal and Phase1=1 are mutually exclusive on the block domain, making

        1 xor Phase1 xor [l_rp == 0]

    equal to ``[l_rp != 0] and not Phase1``.  Every operation targets ``out``,
    so a second invocation cleans it exactly.
    """
    qc.x(out)
    qc.cx(phase1, out)
    _toggle_raw_controls_dirty(qc, l_rp, out, dirty)


def _toggle_tsub_condition(
    qc: QuantumCircuit,
    *,
    phase1: Qubit,
    phase2: Qubit,
    sign: Qubit,
    out: Qubit,
    dirty: Sequence[Qubit],
) -> None:
    """Toggle ``phase1 and (phase2 or not sign)`` without clean scratch."""
    qc.x(sign)
    qc.ccx(phase1, phase2, out)
    qc.ccx(phase1, sign, out)
    _borrowed_c3x(qc, phase1, phase2, sign, out, dirty[0])
    qc.x(sign)


def _toggle_terminal_endpoint_raw(
    qc: QuantumCircuit,
    *,
    l_q: Sequence[Qubit],
    l_s: Sequence[Qubit],
    out: Qubit,
    dirty: Sequence[Qubit],
    scratch: Sequence[Qubit],
    extra_lenders: Sequence[Qubit] = (),
) -> None:
    """Toggle the exact l_q=0,l_s=0 terminal predicate without flags."""
    if len(l_q) != LQ_WIDTH or len(l_s) != LS_WIDTH:
        raise ValueError("terminal endpoint widths do not match")
    lenders = list(dirty) + list(scratch[:5]) + list(extra_lenders)
    controls = list(l_q) + list(l_s)
    if len(lenders) < len(controls) - 2:
        raise ValueError("terminal endpoint raw MCX needs sixteen lenders")
    for bit, lane in enumerate(l_s):
        if ((LS_ZERO >> bit) & 1) == 0:
            qc.x(lane)
    _toggle_raw_controls_dirty(qc, controls, out, lenders)
    for bit, lane in enumerate(l_s):
        if ((LS_ZERO >> bit) & 1) == 0:
            qc.x(lane)


def append_one_step_T(qc: QuantumCircuit, *, T: int, n: int, len_width: int, shift_width: int,
                      Phase1, Phase2, Iter, Sign, Work1, Work2, l_t, l_q, l_s, l_rp,
                      Aux, Dirty, TAnc=None) -> None:
    work_size = n + 3
    windows = safe_active_windows(n, T)
    k1, K1 = windows["r_addsub"]
    # The certified secp256k1 table already includes the live carry/sign lane.
    # Small-width fallback tests retain the historical one-lane repair.
    if n != 256:
        k1 = max(1, k1 - 1)
    k2, K2 = windows["swap"]
    k3, K3 = windows["t_addsub"]
    # A null t_addsub certificate row proves that neither T arithmetic block
    # can be live on any valid secp256k1 state at this fixed-schedule step.
    # Retain the surrounding phase/control bookkeeping, but omit the two large
    # controlled arithmetic gates entirely instead of instantiating singleton
    # placeholder windows whose controls are known to be unreachable.
    t_addsub_reachable = (
        n != 256 or _CERTIFIED_WINDOW_ROWS[T - 1]["t_addsub"] is not None
    )
    k4, K4 = windows["len_update_lt"]
    k5, K5 = windows["len_update_lrp"]
    ctrl = Aux[0]
    scratch = list(Aux[1:])
    pool = scratch
    # Pre-shift
    pre = compact_pre_shift_gate(work_size=work_size)
    _e._append_with_optional_clbits(
        qc,
        pre,
        [Phase1[0], Phase2[0]]
        + list(Work2)
        + list(l_s)
        + list(Dirty)
        + [ctrl],
    )
    # Terminal padding must only rotate Work2.  Fold l_rp!=0 and Phase1=0 into
    # the existing control and retain it across the complete R sequence.
    _toggle_live_r_phase(qc, phase1=Phase1[0], l_rp=l_rp, out=ctrl, dirty=Dirty)
    # Pack Phase2 into the exact R-boundary phase/l_q domain.  R itself
    # temporarily encodes its transformed boundary modulo 256, stores Iter in
    # the freed ninth bit, and therefore receives a genuinely clean carry.
    _borrow_phase2_for_r(
        qc, ctrl=ctrl, phase1=Phase1[0], phase2=Phase2[0], l_q=l_q,
        dirty=Dirty,
    )
    rfused = compact_r_subrestore_fused_gate(n=n, k=k1, K=K1)
    _e._append_with_optional_clbits(
        qc, rfused,
        [ctrl, Phase2[0], Phase1[0], Sign[0]]
        + list(Work1[k1 - 1:K1]) + list(Work2[k1 - 1:K1])
        + list(l_t) + list(l_q) + list(l_s) + list(Dirty) + [Iter[0]] + list(TAnc),
    )
    _borrow_phase2_for_r(
        qc, ctrl=ctrl, phase1=Phase1[0], phase2=Phase2[0], l_q=l_q,
        dirty=Dirty, inverse=True,
    )
    _toggle_live_r_phase(qc, phase1=Phase1[0], l_rp=l_rp, out=ctrl, dirty=Dirty)
    # Swap: ctrl = Phase1 xor Phase2
    qc.cx(Phase1[0], ctrl); qc.cx(Phase2[0], ctrl)
    # At this point ctrl = Phase1 xor Phase2, so Phase2 can be cleared,
    # borrowed as the eighth swap scratch lane, and restored exactly.
    qc.cx(ctrl, Phase2[0]); qc.cx(Phase1[0], Phase2[0])
    lc_swap_window = (
        _CERTIFIED_WINDOW_ROWS[T - 1]["quotient_swap"] if n == 256
        else (k2, K2)
    )
    if lc_swap_window is not None:
        lcs = compact_lc_swap_gate(k=k2, K=K2)
        _e._append_with_optional_clbits(
            qc, lcs,
            [ctrl, Phase1[0], Sign[0]]
            + list(Work1[k2 - 1:K2 + 1]) + list(l_t) + list(l_q)
            + list(Dirty[2:8]) + [Dirty[8]]
            + [Phase2[0]],
        )
    qc.cx(Phase1[0], Phase2[0]); qc.cx(ctrl, Phase2[0])
    qc.cx(Phase2[0], ctrl); qc.cx(Phase1[0], ctrl)
    # l_q +/- updates.
    _make_condition(qc, [(Phase1[0], 1), (Phase2[0], 0)], ctrl, scratch)
    _decrement_by_dirty_carry(qc, l_q, Dirty, ctrl, clean_prefix=scratch)
    _make_condition(qc, [(Phase1[0], 1), (Phase2[0], 0)], ctrl, scratch)
    _make_condition(qc, [(Phase1[0], 0), (Phase2[0], 1)], ctrl, scratch)
    _increment_by_dirty_carry(qc, l_q, Dirty, ctrl, clean_prefix=scratch)
    _make_condition(qc, [(Phase1[0], 0), (Phase2[0], 1)], ctrl, scratch)
    # T sub condition: Phase1=1 and (Phase2=1 or Sign=0)
    _toggle_tsub_condition(
        qc, phase1=Phase1[0], phase2=Phase2[0], sign=Sign[0],
        out=ctrl, dirty=Dirty,
    )
    _borrow_phase2_for_tadd(
        qc, phase1=Phase1[0], phase2=Phase2[0], l_q=l_q,
        dirty=Dirty,
    )
    _borrow_iter_for_tadd(
        qc, phase1=Phase1[0], iteration=Iter[0], l_q=l_q,
        dirty=Dirty,
    )
    if t_addsub_reachable:
        tsub = compact_prefix_addsub_gate(k=k3, K=K3,
                                          mode="sub", sign_update=False,
                                          capture_borrow_sign=False,
                                          target="work2", name="T_SUB_COMPACT")
        _e._append_with_optional_clbits(qc, tsub, [ctrl, Sign[0]] + list(Work1[k3-1:K3]) + list(Work2[k3-1:K3])
                                        + list(l_t) + [Dirty[3], Dirty[6], Dirty[0], Dirty[1], Dirty[2]]
                                        + (scratch + [Phase2[0], Iter[0]] + list(TAnc))[:tsub.num_qubits-(2+2*(K3-k3+1)+LT_WIDTH+5)])
    _borrow_iter_for_tadd(
        qc, phase1=Phase1[0], iteration=Iter[0], l_q=l_q,
        dirty=Dirty, inverse=True,
    )
    _borrow_phase2_for_tadd(
        qc, phase1=Phase1[0], phase2=Phase2[0], l_q=l_q,
        dirty=Dirty, inverse=True,
    )
    _toggle_tsub_condition(
        qc, phase1=Phase1[0], phase2=Phase2[0], sign=Sign[0],
        out=ctrl, dirty=Dirty,
    )
    qc.cx(Phase1[0], Sign[0])
    _borrow_phase2_for_tadd(
        qc, phase1=Phase1[0], phase2=Phase2[0], l_q=l_q,
        dirty=Dirty,
    )
    _borrow_iter_for_tadd(
        qc, phase1=Phase1[0], iteration=Iter[0], l_q=l_q,
        dirty=Dirty,
    )
    if t_addsub_reachable:
        tadd = compact_prefix_add_midtail_gate(n=n, k=k3, K=K3)
        _e._append_with_optional_clbits(
            qc, tadd,
            [Phase1[0], Sign[0], ctrl]
            + list(Work1) + list(Work2)
            + list(l_t) + list(l_s) + list(l_rp)
            + list(Dirty) + scratch + [Phase2[0], Iter[0]],
        )
    _borrow_iter_for_tadd(
        qc, phase1=Phase1[0], iteration=Iter[0], l_q=l_q,
        dirty=Dirty, inverse=True,
    )
    _borrow_phase2_for_tadd(
        qc, phase1=Phase1[0], phase2=Phase2[0], l_q=l_q,
        dirty=Dirty, inverse=True,
    )
    # Post-shift
    post = compact_post_shift_gate(work_size=work_size)
    _e._append_with_optional_clbits(
        qc,
        post,
        [Phase1[0], Phase2[0]]
        + list(Work2)
        + list(l_s)
        + list(Dirty)
        + [ctrl],
    )
    # Phase update
    pupdate = compact_phase_update_gate()
    _e._append_with_optional_clbits(
        qc, pupdate,
        [Phase1[0], Phase2[0], Sign[0]]
        + list(l_q) + list(l_rp) + list(l_s)
        + list(Dirty) + [ctrl],
    )
    # End iteration every four steps.
    if T % 4 == 0:
        # Termination is aligned to a four-step boundary.  During terminal
        # padding l_s returns to its modulo-259 zero sentinel only at offsets
        # 259 and 518; neither is divisible by four, and the certified horizon
        # is shorter than the 1036-step joint recurrence.  Therefore the
        # original two-flag end trigger remains exact without an l_rp guard.
        _toggle_terminal_endpoint_raw(
            qc, l_q=l_q, l_s=l_s, out=ctrl,
            dirty=Dirty, scratch=scratch,
            extra_lenders=[
                Iter[0], Sign[0], Phase1[0], Phase2[0], l_t[0], l_t[1],
            ],
        )
        # The post-update state has the same exact phase/l_q domain as the
        # next T-add boundary.  The length-swap gate touches neither Phase2
        # nor l_q, so Phase2 can supply its fifth clean path lane here too.
        _borrow_phase2_for_tadd(
            qc, phase1=Phase1[0], phase2=Phase2[0], l_q=l_q,
            dirty=Dirty,
        )
        _borrow_iter_for_tadd(
            qc, phase1=Phase1[0], iteration=Iter[0], l_q=l_q,
            dirty=Dirty,
        )
        # The original Section 4.5 bounds are unsafe.  These ranges come from
        # the pinned continuant certificate above; small-width tests still use
        # full scans because the certificate is specific to secp256k1.
        if n != 256:
            k4, K4, k5, K5 = 1, work_size, 1, work_size
        swlen = compact_swap_work_and_len_gate(
            n=n, k4=k4, K4=K4, k5=k5, K5=K5,
        )
        _e._append_with_optional_clbits(qc, swlen, [ctrl] + list(Work1) + list(Work2)
                                        + list(l_t) + list(l_rp)
                                        + list(Dirty[:8]) + [Phase1[0]]
                                        + scratch + [Phase2[0], Iter[0]])
        _borrow_iter_for_tadd(
            qc, phase1=Phase1[0], iteration=Iter[0], l_q=l_q,
            dirty=Dirty, inverse=True,
        )
        _borrow_phase2_for_tadd(
            qc, phase1=Phase1[0], phase2=Phase2[0], l_q=l_q,
            dirty=Dirty, inverse=True,
        )
        qc.cx(ctrl, Iter[0])
        _toggle_terminal_endpoint_raw(
            qc, l_q=l_q, l_s=l_s, out=ctrl,
            dirty=Dirty, scratch=scratch,
            extra_lenders=[
                Iter[0], Sign[0], Phase1[0], Phase2[0], l_t[0], l_t[1],
            ],
        )


def build_step_circuit(n:int, T:int, *, T_max:Optional[int]=None, aux_size:Optional[int]=None, measurement_uncompute:bool=True):
    cfg=get_n_config(n); lw=int(cfg['len_width']); T_max=int(T_max or cfg['T_max'])
    sw=LS_WIDTH
    if aux_size is None: aux_size=qiskit_paper_aux_size(n,lw,sw,T_max)
    set_measurement_uncompute(measurement_uncompute)
    regs=make_global_registers_noctrl(n=n,len_width=lw,shift_width=sw,T_max=T_max,aux_size=aux_size)
    qc=QuantumCircuit(*regs, name=f"S835_FASTDUAL_STEP_T{T}_{n}")
    Phase1,Phase2,Iter,Sign,Work1,Work2,l_t,l_q,l_s,l_rp,Aux,Dirty,TAnc=regs
    append_one_step_T(qc,T=T,n=n,len_width=lw,shift_width=sw,Phase1=Phase1,Phase2=Phase2,Iter=Iter,Sign=Sign,Work1=Work1,Work2=Work2,l_t=l_t,l_q=l_q,l_s=l_s,l_rp=l_rp,Aux=Aux,Dirty=Dirty,TAnc=TAnc)
    return qc

if __name__ == '__main__':
    import argparse,json
    ap=argparse.ArgumentParser(); ap.add_argument('--n',type=int,default=256); ap.add_argument('--T',type=int,default=1); ap.add_argument('--count',action='store_true'); args=ap.parse_args()
    cfg=get_n_config(args.n); lw=int(cfg['len_width']); Tm=int(cfg['T_max'])
    sw=LS_WIDTH
    out={'n':args.n,'l_t_width':LT_WIDTH,'l_q_width':LQ_WIDTH,'l_s_width':LS_WIDTH,
         'l_rp_width':LRP_WIDTH,'T_max':Tm,'aux_size':qiskit_paper_aux_size(args.n,lw,sw,Tm),
         'dirty_passenger_size':DIRTY_PASSENGER_SIZE}
    qc=build_step_circuit(args.n,args.T,T_max=Tm)
    out['step_qubits']=qc.num_qubits; out['top_ops']={str(k):int(v) for k,v in qc.count_ops().items()}
    if args.count:
        out['ops']={str(k):int(v) for k,v in _e.count_circuit_ops_recursive(qc).items()}
    print(json.dumps(out,indent=2,sort_keys=True))
