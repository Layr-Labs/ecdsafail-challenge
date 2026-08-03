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
if hashlib.sha256(_certified_window_bytes).hexdigest() != _CERTIFIED_WINDOW_SHA256:
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
CLEAN_AUX_SIZE = 6
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
            _toggle_raw_controls_dirty(qc, controls, range_acc, borrowed)
        if toggle_before_leaf:
            toggle()
            leaf_fn(label, range_acc)
        else:
            leaf_fn(label, range_acc)
            toggle()

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


def unary_range_iteration_dirty_two_to_five(
    qc: QuantumCircuit,
    *,
    index_reg,
    labels,
    ctrl,
    range_acc,
    ancillas,
    borrowed,
    leaf_fn,
    order,
    toggle_before_leaf: bool,
    before_toggle_fn=None,
    after_toggle_fn=None,
) -> None:
    """Job-218696 final-five decoder with terminal callbacks.

    Relative to the pinned final-four-level decoder, this consumes one fewer
    clean path lane and one additional restored dirty lender.
    """
    labels = sorted(set(labels))
    if not labels:
        return
    need = max(0, _tight_unary_depth_for_labels(labels) - 5)
    if len(ancillas) < need:
        raise ValueError(f"final-five decoder needs {need} clean path lanes")
    if len(borrowed) < 4:
        raise ValueError("final-five decoder needs four restored dirty lenders")

    def visit(label, controls):
        def toggle():
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

    def direct(sub_labels, controls):
        if len(sub_labels) == 1:
            visit(sub_labels[0], controls)
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]

        def branch(values, bit_value):
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
        elif order == "dec":
            branch(one, 1)
            branch(zero, 0)
        else:
            raise ValueError(order)

    def rec(sub_labels, control, depth):
        if _tight_unary_depth_for_labels(sub_labels) <= 5:
            direct(sub_labels, [control])
            return
        bit = _e._split_bit(sub_labels)
        zero = [value for value in sub_labels if ((value >> bit) & 1) == 0]
        one = [value for value in sub_labels if ((value >> bit) & 1) == 1]
        child = ancillas[depth]
        _e._and_with_index_bit(qc, control, index_reg[bit], child, 0)
        if order == "inc":
            rec(zero, child, depth + 1)
            qc.cx(control, child)
            rec(one, child, depth + 1)
            qc.cx(control, child)
        elif order == "dec":
            qc.cx(control, child)
            rec(one, child, depth + 1)
            qc.cx(control, child)
            rec(zero, child, depth + 1)
        else:
            raise ValueError(order)
        _e._uncompute_and_with_index_bit(
            qc, control, index_reg[bit], child, 0,
        )

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
) -> None:
    """Swap 0 and 259 using restored dirty lenders instead of clean scratch."""
    if len(reg) != LS_WIDTH:
        raise ValueError("dirty 0/259 transposition requires a 9-bit register")
    qc.cx(reg[8], reg[0])
    qc.cx(reg[8], reg[1])
    for lane in reg[:8]:
        qc.x(lane)
    _toggle_raw_controls_dirty(
        qc,
        [ctrl] + [reg[bit] for bit in range(LS_WIDTH) if bit != 8],
        reg[8],
        dirty,
    )
    for lane in reversed(reg[:8]):
        qc.x(lane)
    qc.cx(reg[8], reg[1])
    qc.cx(reg[8], reg[0])


def inc_mod259_1ctrl_dirty(
    qc: QuantumCircuit,
    ctrl: Qubit,
    reg: Sequence[Qubit],
    dirty: Sequence[Qubit],
) -> None:
    """Controlled +1 modulo 259 with arbitrary restored dirty lenders."""
    _increment_by_dirty_carry(qc, reg, dirty, ctrl)
    _controlled_zero_259_swap_dirty(qc, ctrl=ctrl, reg=reg, dirty=dirty)


def dec_mod259_1ctrl_dirty(
    qc: QuantumCircuit,
    ctrl: Qubit,
    reg: Sequence[Qubit],
    dirty: Sequence[Qubit],
) -> None:
    """Exact inverse of inc_mod259_1ctrl_dirty."""
    _controlled_zero_259_swap_dirty(qc, ctrl=ctrl, reg=reg, dirty=dirty)
    _decrement_by_dirty_carry(qc, reg, dirty, ctrl)


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
) -> None:
    """Uncontrolled 0/259 transposition using a restored constant-one lane."""
    qc.x(one)
    _controlled_zero_259_swap_dirty(qc, ctrl=one, reg=reg, dirty=dirty)
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
) -> None:
    """Swap two lanes under raw controls using restored dirty lenders."""
    controls = list(controls)
    qc.cx(right, left)
    _toggle_raw_controls_dirty(qc, controls + [left], right, dirty)
    qc.cx(right, left)


_ONE_CLEAN_MCX_CONTEXTS = {}


def _bind_one_clean_mcx_context(qc: QuantumCircuit, clean: Qubit) -> None:
    """Bind a source-certified clean lane to one cached block circuit."""
    key = id(qc)
    previous = _ONE_CLEAN_MCX_CONTEXTS.get(key)
    if previous is not None and (previous[0] is not qc or previous[1] != clean):
        raise RuntimeError("conflicting one-clean MCX context")
    _ONE_CLEAN_MCX_CONTEXTS[key] = (qc, clean)


def _bound_one_clean_mcx_lane(
    qc: QuantumCircuit, explicit: Optional[Qubit],
) -> Optional[Qubit]:
    if explicit is not None:
        return explicit
    entry = _ONE_CLEAN_MCX_CONTEXTS.get(id(qc))
    if entry is None:
        return None
    if entry[0] is not qc:
        raise RuntimeError("stale one-clean MCX circuit identity")
    return entry[1]


def _mcx_one_clean(
    qc: QuantumCircuit,
    controls: Sequence[Qubit],
    target: Qubit,
    clean: Qubit,
) -> None:
    """Exact phase-free C^kX using one zero-initialized restored lane.

    For k >= 3 this is the regular-CCX Khattar-Gidney linear ladder:
    2*k-3 CCX and 2*k-6 X gates.  ``clean`` is a semantic precondition.
    """
    controls = list(controls)
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
    lanes = [clean] + controls
    if len(set(controls + [target, clean])) != k + 2:
        raise ValueError("one-clean MCX lanes must be distinct")

    up_ccx = []
    up_x = []
    for index in range(0, len(lanes) - 2, 2):
        up_ccx.append(("ccx", lanes[index + 1], lanes[index + 2], lanes[index]))
        if index:
            up_x.append(("x", lanes[index], None, None))

    down_ccx = []
    down_x = []
    if len(lanes) & 1:
        x_index, y_index, target_index = len(lanes) - 3, len(lanes) - 5, len(lanes) - 6
    else:
        x_index, y_index, target_index = len(lanes) - 1, len(lanes) - 4, len(lanes) - 5
    if target_index > 0:
        down_ccx.append(("ccx", lanes[x_index], lanes[y_index], lanes[target_index]))
        down_x.append(("x", lanes[target_index], None, None))
    for index in range(target_index, 2, -2):
        down_ccx.append(("ccx", lanes[index], lanes[index - 1], lanes[index - 2]))
        down_x.append(("x", lanes[index - 2], None, None))
    ladder = up_ccx + up_x + down_x + down_ccx

    def emit(operation) -> None:
        kind, left, right, out = operation
        if kind == "x":
            qc.x(left)
        else:
            qc.ccx(left, right, out)

    for operation in ladder:
        emit(operation)
    middle_second = 1 + max(0, 6 - len(lanes))
    qc.ccx(lanes[0], lanes[middle_second], target)
    for operation in reversed(ladder):
        emit(operation)


def _mcx_dirty_ladder(qc: QuantumCircuit, controls: Sequence[Qubit],
                      target: Qubit, dirty: Sequence[Qubit], *,
                      clean: Optional[Qubit] = None) -> None:
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
    clean = _bound_one_clean_mcx_lane(qc, clean)
    if clean is not None and clean not in controls and clean != target:
        _mcx_one_clean(qc, controls, target, clean)
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



def _cca_layer_id(position: int) -> int:
    layer_id, covered = 0, 0
    while covered <= position:
        covered += (1 << layer_id) + 1
        layer_id += 1
    return layer_id - 1


def _cca_start_layer(layer_id: int) -> int:
    return sum((1 << index) + 1 for index in range(layer_id))


def _cca_prefix_layers(
    q: Sequence[Qubit], clean: Sequence[Qubit]
) -> list[tuple[list[Qubit], list[tuple[str, tuple[Qubit, ...]]]]]:
    """Khattar--Gidney prefix controls with ordinary reversible cleanup."""
    q = list(q)
    clean = list(clean)
    if not q:
        return [([], [])]
    if not clean:
        raise ValueError("prefix increment requires clean scratch")

    ret = [([], [])]
    targets: list[Qubit] = []
    n_layers = _cca_layer_id(len(q) - 1)
    anc = [clean[0]]
    for layer_id in range(n_layers + 1):
        start = _cca_start_layer(layer_id)
        end = min(len(q), _cca_start_layer(layer_id + 1))
        ret.append((targets + q[start:start + 1], []))
        for index in range(start + 1, end):
            if index == start + 1:
                q0, q1, target = q[index], q[index - 1], anc[start - index]
            else:
                q0, q1, target = q[index], anc[start - index + 1], anc[start - index]
            operations = [("ccx", (q0, q1, target))]
            if target != clean[0]:
                operations.insert(0, ("x", (target,)))
            ret.append((targets + [target], operations))
        targets.append(anc[start - end + 1])
        anc = anc[start - end + 2:] + q[start:end]

    if len(targets) <= 2:
        return ret
    if len(clean) < 3:
        raise ValueError("recursive prefix increment requires three clean lanes")

    ret.append(([], []))
    recursive = _cca_prefix_layers(targets, clean[2:])
    for layer_id in range(1, n_layers + 1):
        start = _cca_start_layer(layer_id)
        end = min(len(q), _cca_start_layer(layer_id + 1))
        recursive_targets, recursive_ops = recursive[layer_id]
        ret[start + 1][1].extend(recursive_ops)
        if len(recursive_targets) == 1:
            temporary = recursive_targets[0]
        elif len(recursive_targets) == 2:
            temporary = clean[1]
            ret[start + 1][1].append(
                ("ccx", (recursive_targets[0], recursive_targets[1], temporary))
            )
        else:
            raise AssertionError("recursive prefix did not lower to two controls")
        for index in range(start, end):
            ret[index + 1] = (
                [temporary, ret[index + 1][0][-1]], ret[index + 1][1]
            )
        if len(recursive_targets) == 2:
            ret[end + 1][1].append(
                ("ccx", (recursive_targets[0], recursive_targets[1], temporary))
            )
    return ret


def _cca_increment_schedule(
    register: Sequence[Qubit], clean: Sequence[Qubit]
) -> list[tuple[str, tuple[Qubit, ...]]]:
    register = list(register)
    clean = list(clean)
    if not register:
        return []
    if len(set(register + clean)) != len(register) + len(clean):
        raise ValueError("prefix increment lanes must be distinct")
    layers = _cca_prefix_layers(register[:-1], clean)
    operations: list[tuple[str, tuple[Qubit, ...]]] = []
    for _, transition in layers:
        for operation in transition:
            target = operation[1][-1]
            if not (target in clean and clean.index(target) & 1):
                operations.append(operation)
    for index in range(len(layers) - 1, -1, -1):
        controls, transition = layers[index]
        if index < len(register):
            if not controls:
                operations.append(("x", (register[index],)))
            elif len(controls) == 1:
                operations.append(("cx", (controls[0], register[index])))
            elif len(controls) == 2:
                operations.append(
                    ("ccx", (controls[0], controls[1], register[index]))
                )
            else:
                raise AssertionError("prefix controls were not fully lowered")
        operations.extend(reversed(transition))
    return operations


def _cca_emit(
    qc: QuantumCircuit,
    operations: Sequence[tuple[str, tuple[Qubit, ...]]],
    *,
    inverse: bool = False,
) -> None:
    iterable = reversed(operations) if inverse else operations
    for kind, wires in iterable:
        if kind == "x":
            qc.x(wires[0])
        elif kind == "cx":
            qc.cx(wires[0], wires[1])
        elif kind == "ccx":
            qc.ccx(wires[0], wires[1], wires[2])
        else:
            raise AssertionError(f"unsupported prefix operation {kind}")


def _increment_prefix_clean(
    qc: QuantumCircuit, register: Sequence[Qubit], clean: Sequence[Qubit]
) -> None:
    _cca_emit(qc, _cca_increment_schedule(register, clean))


def _decrement_prefix_clean(
    qc: QuantumCircuit, register: Sequence[Qubit], clean: Sequence[Qubit]
) -> None:
    _cca_emit(qc, _cca_increment_schedule(register, clean), inverse=True)


def _increment_by_prefix_clean(
    qc: QuantumCircuit,
    register: Sequence[Qubit],
    clean: Sequence[Qubit],
    control: Qubit,
) -> None:
    operations = _cca_increment_schedule([control] + list(register), clean)
    if not operations or operations[-1] != ("x", (control,)):
        raise AssertionError("controlled prefix schedule tail mismatch")
    _cca_emit(qc, operations[:-1])


def _decrement_by_prefix_clean(
    qc: QuantumCircuit,
    register: Sequence[Qubit],
    clean: Sequence[Qubit],
    control: Qubit,
) -> None:
    operations = _cca_increment_schedule([control] + list(register), clean)
    if not operations or operations[-1] != ("x", (control,)):
        raise AssertionError("controlled prefix schedule tail mismatch")
    _cca_emit(qc, operations[:-1], inverse=True)


def _add_three_prefix_clean(
    qc: QuantumCircuit, register: Sequence[Qubit], clean: Sequence[Qubit]
) -> None:
    register = list(register)
    _increment_prefix_clean(qc, register, clean)
    _increment_prefix_clean(qc, register[1:], clean)


def _sub_three_prefix_clean(
    qc: QuantumCircuit, register: Sequence[Qubit], clean: Sequence[Qubit]
) -> None:
    register = list(register)
    _decrement_prefix_clean(qc, register[1:], clean)
    _decrement_prefix_clean(qc, register, clean)


def _const_minus_258_prefix_clean(
    qc: QuantumCircuit, register: Sequence[Qubit], clean: Sequence[Qubit]
) -> None:
    register = list(register)
    if len(register) != 9:
        raise ValueError("258-y prefix map requires width 9")
    for lane in register:
        qc.x(lane)
    _increment_prefix_clean(qc, register, clean)
    _increment_prefix_clean(qc, register[1:], clean)
    qc.x(register[8])


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
    clean: Optional[Qubit] = None,
) -> None:
    target = list(target)
    for bit in range(len(target) - 1, -1, -1):
        for lane in target[:bit]:
            qc.x(lane)
        _mcx_dirty_ladder(
            qc, [carry] + target[:bit], target[bit], lenders, clean=clean
        )
        for lane in reversed(target[:bit]):
            qc.x(lane)


def _increment_by_dirty_carry(
    qc: QuantumCircuit,
    target: Sequence[Qubit],
    lenders: Sequence[Qubit],
    carry: Qubit,
    clean: Optional[Qubit] = None,
) -> None:
    target = list(target)
    for bit in range(len(target) - 1, -1, -1):
        _mcx_dirty_ladder(
            qc, [carry] + target[:bit], target[bit], lenders, clean=clean
        )


def _add_dirty_carry(
    qc: QuantumCircuit,
    target: Sequence[Qubit],
    addend: Sequence[Qubit],
    carry: Qubit,
) -> None:
    _dirty_carry_add_raw(qc, target, addend, carry)
    _decrement_by_dirty_carry(qc, target, addend, carry)


def _sub_dirty_carry(
    qc: QuantumCircuit,
    target: Sequence[Qubit],
    addend: Sequence[Qubit],
    carry: Qubit,
) -> None:
    for lane in target:
        qc.x(lane)
    _dirty_carry_add_raw(qc, target, addend, carry)
    for lane in target:
        qc.x(lane)
    _increment_by_dirty_carry(qc, target, addend, carry)


def _increment_dirty(
    qc: QuantumCircuit,
    register: Sequence[Qubit],
    dirty: Sequence[Qubit],
) -> None:
    register = list(register)
    for bit in range(len(register) - 1, 0, -1):
        _mcx_dirty_ladder(qc, register[:bit], register[bit], dirty)
    qc.x(register[0])


def _decrement_dirty(
    qc: QuantumCircuit,
    register: Sequence[Qubit],
    dirty: Sequence[Qubit],
) -> None:
    register = list(register)
    qc.x(register[0])
    for bit in range(1, len(register)):
        _mcx_dirty_ladder(qc, register[:bit], register[bit], dirty)


def _add_const_dirty(
    qc: QuantumCircuit,
    register: Sequence[Qubit],
    constant: int,
    dirty: Sequence[Qubit],
) -> None:
    register = list(register)
    for bit in range(len(register)):
        if (constant >> bit) & 1:
            _increment_dirty(qc, register[bit:], dirty)


def _sub_const_dirty(
    qc: QuantumCircuit,
    register: Sequence[Qubit],
    constant: int,
    dirty: Sequence[Qubit],
) -> None:
    register = list(register)
    for bit in range(len(register) - 1, -1, -1):
        if (constant >> bit) & 1:
            _decrement_dirty(qc, register[bit:], dirty)


def _const_minus_dirty(
    qc: QuantumCircuit,
    register: Sequence[Qubit],
    constant: int,
    dirty: Sequence[Qubit],
) -> None:
    """Apply y -> constant-y modulo 2**len(register), exactly involutively."""
    for lane in register:
        qc.x(lane)
    _add_const_dirty(qc, register, constant + 1, dirty)


def _toggle_raw_controls_dirty(qc: QuantumCircuit, controls: Sequence[Qubit],
                               target: Qubit, dirty: Sequence[Qubit], *,
                               clean: Optional[Qubit] = None) -> None:
    """Toggle a target by raw controls, restoring arbitrary dirty lenders."""
    controls = list(controls)
    if target in controls:
        raise ValueError("raw-control target aliases a control")
    if len(controls) == 1:
        qc.cx(controls[0], target)
    elif len(controls) == 2:
        qc.ccx(controls[0], controls[1], target)
    elif len(controls) == 3:
        if not dirty:
            raise ValueError("raw C3X needs one dirty lender")
        _borrowed_c3x(
            qc, controls[0], controls[1], controls[2], target, dirty[0],
        )
    else:
        _mcx_dirty_ladder(qc, controls, target, dirty, clean=clean)


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
) -> None:
    """Arithmetic cell under an unmaterialized equality product."""
    controls = list(controls)

    def toggle(extra: Sequence[Qubit], out: Qubit) -> None:
        _toggle_raw_controls_dirty(qc, controls + list(extra), out, dirty)

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
) -> None:
    """Raw-control form of the fused R second-scan cell."""
    controls = list(controls)
    _toggle_raw_controls_dirty(
        qc, controls + [carry, target], addend, dirty
    )
    _toggle_raw_controls_dirty(qc, controls + [addend], carry, dirty)
    _e.cswap_toffoli(qc, mode, addend, carry)
    _toggle_raw_controls_dirty(qc, controls + [addend], target, dirty)
    _e.cswap_toffoli(qc, mode, addend, carry)


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
    Dirty = QuantumRegister(4, "DirtyPassenger")
    depth = _tight_unary_depth_for_labels(list(range(k, K + 1)))
    Scratch = QuantumRegister(6, "Scratch")
    qc = _e._block_circuit(
        Ctrl, Direction, Sign, Work1, l_t, l_q, Dirty, Scratch, name=name,
    )
    path_depth = max(0, depth - 3)
    path = list(Scratch[:path_depth])
    extension = Dirty[0]
    carry = Scratch[5]
    qc.append(_e.cuccaro_add_mod_2n_no_z_gate(LQ_WIDTH, name="ADD_lt8_to_lq9"),
              list(l_t) + [extension] + list(l_q) + [carry])
    _bind_one_clean_mcx_context(qc, carry)
    qc.cx(extension, l_q[LQ_WIDTH - 1])
    _add_three_prefix_clean(qc, l_q, Scratch)

    def leaf(j: int, controls: Sequence[Qubit]) -> None:
        qc.x(Direction[0])
        _dirty_mcswap(
            qc,
            list(controls) + [Direction[0]],
            Sign[0],
            Work1[j - k + 1],
            Dirty,
        )
        qc.x(Direction[0])
        _dirty_mcswap(
            qc,
            list(controls) + [Direction[0]],
            Sign[0],
            Work1[j - k],
            Dirty,
        )

    unary_iteration_dirty_octet_raw(
        qc, index_reg=l_q, labels=list(range(k, K + 1)), ctrl=Ctrl[0],
        ancillas=path, leaf_fn=leaf, order="inc",
    )
    _sub_three_prefix_clean(qc, l_q, Scratch)
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
    """Two-scan exact R subtract/conditional-restore block."""
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
    Scratch = QuantumRegister(2, "Scratch")
    Clean = QuantumRegister(1, "OneCleanMCX")
    qc = _e._block_circuit(
        Ctrl, Phase2, Mode, Sign, Work1, Work2, l_t, l_q, l_s,
        Dirty, Scratch, Clean, name=name,
    )
    _bind_one_clean_mcx_context(qc, Clean[0])
    carry = Scratch[0]
    acc = Scratch[1]
    # Ctrl is the folded live-R predicate, so Ctrl=1 implies Mode=Phase1=0.
    # On inactive branches the affine setup is exactly reversed without
    # touching the work registers.  Mode can therefore hold the temporary
    # zero extension during setup/first scan and teardown.  The second scan
    # uses a restored dirty passenger while Mode holds the restore predicate.
    extension = Mode[0]
    affine_addend = list(l_t) + [extension]
    _add_dirty_carry(qc, l_q, affine_addend, Dirty[9])
    _add_const_dirty(qc, l_q, 4, Dirty)
    _const_minus_dirty(qc, l_s, n + 2, Dirty)
    _swap_zero_259_uncontrolled_dirty(qc, l_s, extension, Dirty)

    def qpair(j: int) -> tuple[Qubit, Qubit]:
        idx = j - k
        return Work2[idx], Work1[idx]

    def leaf_first(
        j: int,
        s_controls: Sequence[Qubit],
        q_controls: Sequence[Qubit],
    ) -> None:
        addend, target = qpair(j)
        if j < K:
            next_addend, _ = qpair(j + 1)
            _apply_cell_borrowed(
                qc, "sub", "first", acc, addend, target,
                next_addend, Dirty[0],
            )
        _apply_cell_raw(
            qc, "sub", "first", s_controls, addend, target, carry, Dirty,
        )
        _toggle_raw_controls_dirty(qc, s_controls, acc, Dirty)
        _toggle_raw_controls_dirty(qc, q_controls, acc, Dirty)
        _toggle_raw_controls_dirty(
            qc, list(q_controls) + [addend], Sign[0], Dirty,
        )

    dual_unary_iteration_direct_raw_ab(
        qc, index_a=l_s, index_b=l_q, labels=list(range(k, K + 1)),
        common_ctrl=Ctrl[0],
        leaf_fn=leaf_first, order="dec",
    )

    # On live-R states Mode enters as Phase1=0.  Convert it to
    # 1 xor (Phase2 & Sign), the old conditional-restoration predicate.
    qc.ccx(Ctrl[0], Phase2[0], Sign[0])
    qc.x(Mode[0])
    qc.ccx(Phase2[0], Sign[0], Mode[0])

    def leaf_second(
        j: int,
        s_controls: Sequence[Qubit],
        q_controls: Sequence[Qubit],
    ) -> None:
        addend, target = qpair(j)
        _toggle_raw_controls_dirty(qc, q_controls, acc, Dirty)
        _toggle_raw_controls_dirty(qc, s_controls, acc, Dirty)
        if j < K:
            next_addend, _ = qpair(j + 1)
            _apply_r_fused_second_cell_borrowed(
                qc, mode=Mode[0], ctrl=acc, addend=addend,
                target=target, carry=next_addend, borrowed=Dirty[0],
            )
        _apply_r_fused_second_cell_raw(
            qc, mode=Mode[0], controls=s_controls, addend=addend,
            target=target, carry=carry, dirty=Dirty,
        )

    dual_unary_iteration_direct_raw_ab(
        qc, index_a=l_s, index_b=l_q, labels=list(range(k, K + 1)),
        common_ctrl=Ctrl[0],
        leaf_fn=leaf_second, order="inc",
    )

    qc.ccx(Phase2[0], Sign[0], Mode[0])
    qc.x(Mode[0])
    _swap_zero_259_uncontrolled_dirty(qc, l_s, extension, Dirty)
    _const_minus_dirty(qc, l_s, n + 2, Dirty)
    _sub_const_dirty(qc, l_q, 4, Dirty)
    _sub_dirty_carry(qc, l_q, affine_addend, Dirty[9])
    return _e._finalize_block(qc)


def _compact_prefix_addsub_scratch_count(*, k: int, K: int) -> int:
    encoded_labels = list(range(0, K - 1))
    depth = _tight_unary_depth_for_labels(encoded_labels)
    path_depth = max(0, depth - 6)
    return max(path_depth, 1) + 2

@lru_cache(maxsize=None)
def compact_prefix_addsub_gate(*, k: int, K: int,
                               mode: Literal["add", "sub"], sign_update: bool,
                               capture_borrow_sign: bool,
                               target: Literal["work1", "work2"], name: str,
                               use_one_clean_mcx: bool = False) -> Gate:
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
    path_depth = max(0, depth - 6)
    base = max(path_depth, 1)
    Scratch = QuantumRegister(base + 2, "Scratch")
    registers = [Ctrl, Sign, Work1, Work2, l_t, Borrowed, Scratch]
    Clean = None
    if use_one_clean_mcx:
        Clean = QuantumRegister(1, "OneCleanMCX")
        registers.append(Clean)
    qc = _e._block_circuit(*registers, name=name)
    if Clean is not None:
        _bind_one_clean_mcx_context(qc, Clean[0])
    path = list(Scratch[:path_depth])
    carry = Scratch[base]
    acc = Scratch[base + 1]

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
    # Scratch[0] is clean outside the unary tree, so the boundary cell uses
    # the clean MBU C3X lowering and returns it to zero before the tree starts.
    _apply_cell_dirty(
        qc, mode, "first", Ctrl[0], addend1, tgt1, carry, Scratch[0],
    )
    if encoded_labels:
        unary_range_iteration_dirty_64raw(
            qc, index_reg=l_t, labels=encoded_labels, ctrl=Ctrl[0],
            range_acc=acc, ancillas=path, borrowed=Borrowed,
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
        unary_range_iteration_dirty_64raw(
            qc, index_reg=l_t, labels=encoded_labels, ctrl=Ctrl[0],
            range_acc=acc, ancillas=path, borrowed=Borrowed,
            leaf_fn=leaf_second, order="dec",
            toggle_before_leaf=True,
        )
    _apply_cell_dirty(
        qc, mode, "second", Ctrl[0], addend1, tgt1, carry, Scratch[0],
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


def _range_scan_tight_dirty_two_to_five(
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
            f"final-five tight range scan needs {required} lanes, "
            f"got {len(scratch)}"
        )
    if len(borrowed) < 4:
        raise ValueError("final-five tight range scan needs four dirty lenders")
    path = list(scratch[:path_depth])
    range_acc = scratch[path_depth]

    def scan(*, toggle_before_leaf: bool) -> None:
        unary_range_iteration_dirty_two_to_five(
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
        raise ValueError("bad final-five tight range-scan order")

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
        _low256_range_scan_conditioned_dirty_six(
            qc, index_reg=boundary, ctrl=ctrl, range_acc=range_acc,
            ancillas=path, dirty=dirty, leaf_fn=leaf_fn, order="dec",
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
    dirty map, ten dirty passengers, endpoint registers, and all six clean
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
    Scratch = QuantumRegister(6, "Scratch")
    qc = _e._block_circuit(
        Ctrl, Sign, Tail, Work1, Work2, l_t, l_s, l_rp,
        Dirty, Scratch, name=name,
    )

    encoded_labels = list(range(0, K - 1))
    depth = _tight_unary_depth_for_labels(encoded_labels)
    path_depth = max(0, depth - 3)
    path = list(Scratch[:path_depth])
    carry = Tail[0]
    acc = Scratch[5]
    selected_carry = Dirty[9]

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

    def selected_carry_toggle(encoded: int, range_control: Qubit) -> None:
        addend, _ = qpair(encoded + 2)
        qc.ccx(range_control, addend, selected_carry)

    qc.cx(Ctrl[0], acc)
    addend1, target1 = qpair(1)
    _apply_cell_dirty(
        qc, "add", "first", Ctrl[0], addend1, target1,
        carry, Scratch[0],
    )
    if encoded_labels:
        unary_range_iteration_dirty_octet(
            qc, index_reg=l_t, labels=encoded_labels, ctrl=Ctrl[0],
            range_acc=acc, ancillas=path, borrowed=Dirty[4:6],
            leaf_fn=first_leaf, order="inc",
            toggle_before_leaf=False,
            before_toggle_fn=selected_carry_toggle,
            after_toggle_fn=selected_carry_toggle,
        )

    midpoint_scratch = list(Scratch)

    def selected_dirty_sign_toggle() -> None:
        def leaf(encoded: int, controls: Sequence[Qubit]) -> None:
            _toggle_raw_controls_dirty(
                qc, list(controls) + [Work1[encoded + 2]], Sign[0], Dirty[4:],
            )

        unary_iteration_dirty_quartet_raw(
            qc, index_reg=l_t, labels=encoded_labels,
            ctrl=selected_carry, ancillas=midpoint_scratch,
            leaf_fn=leaf, order="inc",
        )

    def clear_selected_carry_passenger() -> None:
        def leaf(encoded: int, controls: Sequence[Qubit]) -> None:
            _toggle_raw_controls_dirty(
                qc,
                list(controls) + [Work1[encoded + 1]],
                selected_carry,
                Dirty[4:9],
            )

        unary_iteration_dirty_quartet_raw(
            qc, index_reg=l_t, labels=encoded_labels, ctrl=Ctrl[0],
            ancillas=midpoint_scratch, leaf_fn=leaf, order="inc",
        )

    # If selected_carry enters as D and the first scan adds C, each four-gate
    # sandwich contributes (D xor C)Z.  Clearing C after the first sandwich
    # and repeating contributes DZ, leaving exactly CZ and restoring D.
    selected_dirty_sign_toggle()
    _upper_zero_map_midpoint_six_dirty(
        qc, ctrl=Ctrl[0], boundary_B=l_s, bits=Work2,
        dirty_map=Work1, dirty=Dirty, scratch=midpoint_scratch,
    )
    selected_dirty_sign_toggle()
    _upper_zero_map_midpoint_six_dirty(
        qc, ctrl=Ctrl[0], boundary_B=l_s, bits=Work2,
        dirty_map=Work1, dirty=Dirty, scratch=midpoint_scratch,
    )
    clear_selected_carry_passenger()
    selected_dirty_sign_toggle()
    _upper_zero_map_midpoint_six_dirty(
        qc, ctrl=Ctrl[0], boundary_B=l_s, bits=Work2,
        dirty_map=Work1, dirty=Dirty, scratch=midpoint_scratch,
    )
    selected_dirty_sign_toggle()
    _upper_zero_map_midpoint_six_dirty(
        qc, ctrl=Ctrl[0], boundary_B=l_s, bits=Work2,
        dirty_map=Work1, dirty=Dirty, scratch=midpoint_scratch,
    )

    def second_leaf(encoded: int, equality: Qubit) -> None:
        j = encoded + 2
        addend, target = qpair(j)
        previous_addend, _ = qpair(j - 1)
        _apply_cell_borrowed(
            qc, "add", "second", acc, addend, target,
            previous_addend, Dirty[1],
        )

    if encoded_labels:
        unary_range_iteration_dirty_octet(
            qc, index_reg=l_t, labels=encoded_labels, ctrl=Ctrl[0],
            range_acc=acc, ancillas=path, borrowed=Dirty[4:6],
            leaf_fn=second_leaf, order="dec",
            toggle_before_leaf=True,
        )
    _apply_cell_dirty(
        qc, "add", "second", Ctrl[0], addend1, target1,
        carry, Scratch[0],
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
    labels: Sequence[int], leaf: int,
) -> int:
    """Return index-bit X conjugations live at a final-five leaf callback."""
    labels = list(sorted(set(labels)))
    if leaf not in labels:
        raise ValueError("terminal Aux6 leaf is outside the low support")
    while _tight_unary_depth_for_labels(labels) > 5:
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

def _range_scan_tight_dirty_two_to_five_aux6_terminal(
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
    """Exact four-scan-lane Aux6 terminal scan for labels through 259.

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
    if not (k <= 255 < K):
        _range_scan_tight_dirty_two_to_five(
            qc, leq=leq, boundary=boundary, k=k, K=K, ctrl=ctrl,
            scratch=scratch, borrowed=borrowed, leaf_fn=leaf_fn, order=order,
        )
        return
    if len(boundary) != 9:
        raise ValueError("terminal Aux6 crossing scan needs a 9-bit endpoint")
    if len(scratch) < 4:
        raise ValueError("terminal Aux6 crossing scan needs four scan lanes")
    if len(borrowed) < 8:
        raise ValueError("terminal Aux6 crossing scan needs eight dirty lenders")

    main = list(range(k, 256))
    depth = _tight_unary_depth_for_labels(main)
    range_acc = scratch[max(0, depth - 5)]
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
        label: _terminal_aux6_direct_inversion_mask(main, label)
        for label in aliases_to_endpoints
    }

    def cancel_false_high_equality(label: int, _range_acc: Qubit) -> None:
        for endpoint in aliases_to_endpoints.get(label, ()):
            toggle_exact_endpoint(endpoint, direct_masks[label])

    def low_scan(*, toggle_before_leaf: bool) -> None:
        unary_range_iteration_dirty_two_to_five(
            qc, index_reg=boundary, labels=main, ctrl=ctrl,
            range_acc=range_acc, ancillas=scratch[:max(0, depth - 5)],
            borrowed=borrowed, leaf_fn=leaf_fn, order=order,
            toggle_before_leaf=toggle_before_leaf,
            after_toggle_fn=cancel_false_high_equality,
        )

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
    if len(scratch) < min(4, max(1, depth - 4)):
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

    _range_scan_tight_dirty_two_to_five_aux6_terminal(
        qc, leq=True, boundary=boundary_B, k=k, K=K, ctrl=ctrl,
        scratch=scratch, borrowed=borrowed, leaf_fn=leaf_forward, order="inc",
    )
    _range_scan_tight_dirty_two_to_five_aux6_terminal(
        qc, leq=True, boundary=boundary_B, k=k, K=K, ctrl=ctrl,
        scratch=scratch, borrowed=borrowed, leaf_fn=leaf_reverse, order="dec",
    )

def _lower_zero_map_borrowed(qc: QuantumCircuit, *, ctrl: Qubit,
                             boundary_A: Sequence[Qubit], bits: Sequence[Qubit],
                             dirty_map: Sequence[Qubit], borrowed: Sequence[Qubit],
                             k: int, K: int, scratch: Sequence[Qubit]) -> None:
    borrowed = [borrowed] if isinstance(borrowed, Qubit) else list(borrowed)
    depth = _tight_unary_depth_for_labels(list(range(k, K + 1)))
    if len(scratch) < min(4, max(1, depth - 4)):
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

    _range_scan_tight_dirty_two_to_five_aux6_terminal(
        qc, leq=False, boundary=boundary_A, k=k, K=K, ctrl=ctrl,
        scratch=scratch, borrowed=borrowed, leaf_fn=leaf_forward, order="dec",
    )
    _range_scan_tight_dirty_two_to_five_aux6_terminal(
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
    Scratch = QuantumRegister(5, "Scratch")
    qc = _e._block_circuit(
        Ctrl, Work1, Work2, l_t, l_rp, Dirty, Extension, Scratch,
        name=name,
    )
    extension = Extension[0]
    boundary = list(l_rp) + [extension]
    map_scratch = list(Scratch)
    _const_minus_258_prefix_clean(qc, boundary, Scratch)
    _highest_position_xor_write_borrowed(
        qc, ctrl=Ctrl[0], boundary_B=boundary, bits=Work2, dirty_map=Work1,
        target_len=l_t, borrowed=Dirty, k=k, K=K, scratch=map_scratch,
    )
    _highest_position_xor_write_borrowed(
        qc, ctrl=Ctrl[0], boundary_B=boundary, bits=Work1, dirty_map=Work2,
        target_len=l_t, borrowed=Dirty, k=k, K=K, scratch=map_scratch,
    )
    _const_minus_258_prefix_clean(qc, boundary, Scratch)
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
    Scratch = QuantumRegister(5, "Scratch")
    qc = _e._block_circuit(
        Ctrl, Work1, Work2, l_t, l_rp, Dirty, Extension, Scratch,
        name=name,
    )
    extension = Extension[0]
    boundary = list(l_t) + [extension]
    map_scratch = list(Scratch)
    _add_three_prefix_clean(qc, boundary, Scratch)
    _right_length_xor_write_borrowed(
        qc, n=n, ctrl=Ctrl[0], boundary_A=boundary, bits=Work1, dirty_map=Work2,
        target_len=l_rp, borrowed=Dirty, k=k, K=K, scratch=map_scratch,
    )
    _right_length_xor_write_borrowed(
        qc, n=n, ctrl=Ctrl[0], boundary_A=boundary, bits=Work2, dirty_map=Work1,
        target_len=l_rp, borrowed=Dirty, k=k, K=K, scratch=map_scratch,
    )
    _sub_three_prefix_clean(qc, boundary, Scratch)
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
    Scratch = QuantumRegister(5, "Scratch")
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
    Clean = QuantumRegister(1, "OneCleanMCX")
    qc = _e._block_circuit(
        Phase1, Phase2, Work2, l_s, Dirty, Scratch, Clean, name=name,
    )
    _bind_one_clean_mcx_context(qc, Clean[0])
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
    Clean = QuantumRegister(1, "OneCleanMCX")
    qc = _e._block_circuit(
        Phase1, Phase2, Work2, l_s, Dirty, Scratch, Clean, name=name,
    )
    _bind_one_clean_mcx_context(qc, Clean[0])
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
    Scratch = QuantumRegister(2, "Scratch")
    Clean = QuantumRegister(1, "OneCleanMCX")
    qc = _e._block_circuit(
        Phase1, Phase2, Sign, l_q, l_rp, l_s, Dirty, Scratch, Clean, name=name,
    )
    _bind_one_clean_mcx_context(qc, Clean[0])
    z_lq, z_lrp = Scratch[:2]

    def toggle_eq(register: Sequence[Qubit], value: int, target: Qubit) -> None:
        inverted = []
        for bit, lane in enumerate(register):
            if ((value >> bit) & 1) == 0:
                qc.x(lane)
                inverted.append(lane)
        _toggle_raw_controls_dirty(qc, register, target, Dirty)
        for lane in reversed(inverted):
            qc.x(lane)

    toggle_eq(l_q, (1 << LQ_WIDTH) - 1, z_lq)
    toggle_eq(l_rp, LRP_ZERO, z_lrp)
    qc.x(z_lrp)
    _borrowed_c3x(qc, z_lq, z_lrp, Sign[0], Phase2[0], Dirty[0])
    _borrowed_c3x(qc, z_lq, z_lrp, Phase1[0], Phase2[0], Dirty[0])
    _borrowed_c3x(qc, z_lq, z_lrp, Phase2[0], Sign[0], Dirty[0])
    qc.x(z_lrp)
    toggle_eq(l_rp, LRP_ZERO, z_lrp)
    toggle_eq(l_q, (1 << LQ_WIDTH) - 1, z_lq)

    # Modulo-259 revisits the shift-zero sentinel during terminal padding.
    # Guard the phase transition with l_rp != 0 so padding remains frozen.
    toggle_eq(l_s, LS_ZERO, z_lq)
    toggle_eq(l_rp, LRP_ZERO, z_lrp)
    qc.x(z_lrp)
    qc.ccx(z_lq, z_lrp, Phase1[0])
    qc.ccx(z_lq, z_lrp, Phase2[0])
    qc.x(z_lrp)
    toggle_eq(l_rp, LRP_ZERO, z_lrp)
    toggle_eq(l_s, LS_ZERO, z_lq)
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
    return Phase1, Phase2, Iter, Sign, Work1, Work2, l_t, l_q, l_s, l_rp, Aux, Dirty


def _make_condition(qc: QuantumCircuit, conditions, out: Qubit, scratch: Sequence[Qubit]) -> None:
    _e.compute_control(qc, conditions, out, scratch)


def _toggle_phase_b_from_lq(
    qc: QuantumCircuit,
    *,
    phase1: Qubit,
    phase2: Qubit,
    l_q: Sequence[Qubit],
) -> None:
    """Toggle Phase2 exactly on phase-B states at the T-add boundary.

    ``l_q`` is truth-minus-one encoded.  Phase A therefore has the 511 zero
    sentinel while phase B lies in 0..255.  With Phase1=0, the high bit alone
    distinguishes those domains exactly.
    """
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

def _borrow_phase2_for_tadd(
    qc: QuantumCircuit,
    *,
    phase1: Qubit,
    phase2: Qubit,
    l_q: Sequence[Qubit],
    dirty: Sequence[Qubit],
    inverse: bool = False,
) -> None:
    """Clear/restore Phase2 using the exact Algorithm-3 phase/l_q domain.

    Immediately before T-add the reachable states are:

      A: (Phase1,Phase2)=(0,0), physical l_q=511
      B: (0,1), physical l_q in 0..w-1
      C: (1,0), physical l_q in 0..w-2 or 511
      D: (1,1), physical l_q=511

    with ``w <= 256``.  Phase D is first moved from the 511 sentinel to the
    otherwise-unused physical code 255; phase B is recoverable from
    ``Phase1=0`` and the high bit being clear.  This makes Phase2 clean for
    the complete T-add block without losing information.  The inverse sequence
    reconstructs both phases and removes the reserved marker exactly.
    """
    if len(l_q) != LQ_WIDTH:
        raise ValueError("T-add Phase2 loan requires the nine-bit l_q register")
    marker = l_q[LQ_WIDTH - 1]
    if not inverse:
        # D: (1,1,l_q=511) -> (1,0,l_q=255).
        qc.ccx(phase1, phase2, marker)
        _toggle_phase_d_marker(
            qc, phase1=phase1, phase2=phase2, l_q=l_q, dirty=dirty,
        )
        # B is the remaining Phase2=1 state and has high(l_q)=0, Phase1=0.
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

def _toggle_terminal_endpoint_raw(
    qc: QuantumCircuit,
    *,
    l_q: Sequence[Qubit],
    l_s: Sequence[Qubit],
    out: Qubit,
    dirty: Sequence[Qubit],
    scratch: Sequence[Qubit],
    clean: Optional[Qubit] = None,
) -> None:
    """Toggle the exact l_q=0,l_s=0 terminal predicate without flags."""
    if len(l_q) != LQ_WIDTH or len(l_s) != LS_WIDTH:
        raise ValueError("terminal endpoint widths do not match")
    lenders = list(dirty) + list(scratch[:5])
    controls = list(l_q) + list(l_s)
    if clean is None and len(lenders) < len(controls) - 2:
        raise ValueError("terminal endpoint raw MCX needs sixteen lenders")
    for bit, lane in enumerate(l_s):
        if ((LS_ZERO >> bit) & 1) == 0:
            qc.x(lane)
    _toggle_raw_controls_dirty(qc, controls, out, lenders, clean=clean)
    for bit, lane in enumerate(l_s):
        if ((LS_ZERO >> bit) & 1) == 0:
            qc.x(lane)

def append_one_step_T(qc: QuantumCircuit, *, T: int, n: int, len_width: int, shift_width: int,
                      Phase1, Phase2, Iter, Sign, Work1, Work2, l_t, l_q, l_s, l_rp,
                      Aux, Dirty) -> None:
    work_size = n + 3
    windows = safe_active_windows(n, T)
    k1, K1 = windows["r_addsub"]
    # The certified secp256k1 table already includes the live carry/sign lane.
    # Small-width fallback tests retain the historical one-lane repair.
    if n != 256:
        k1 = max(1, k1 - 1)
    k2, K2 = windows["swap"]
    k3, K3 = windows["t_addsub"]
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
        + [ctrl, scratch[0]],
    )
    # Terminal padding must only rotate Work2.  Fold l_rp!=0 and Phase1=0 into
    # the existing control and retain it across the complete R sequence.
    _toggle_live_r_phase(qc, phase1=Phase1[0], l_rp=l_rp, out=ctrl, dirty=Dirty)
    rfused = compact_r_subrestore_fused_gate(n=n, k=k1, K=K1)
    _e._append_with_optional_clbits(
        qc, rfused,
        [ctrl, Phase2[0], Phase1[0], Sign[0]]
        + list(Work1[k1 - 1:K1]) + list(Work2[k1 - 1:K1])
        + list(l_t) + list(l_q) + list(l_s) + list(Dirty)
        + scratch[:2] + [scratch[2]],
    )
    _toggle_live_r_phase(qc, phase1=Phase1[0], l_rp=l_rp, out=ctrl, dirty=Dirty)
    # Swap: ctrl = Phase1 xor Phase2
    qc.cx(Phase1[0], ctrl); qc.cx(Phase2[0], ctrl)
    # At this point ctrl = Phase1 xor Phase2, so Phase2 can be cleared,
    # borrowed as the sixth LC scratch lane, and restored exactly.
    qc.cx(ctrl, Phase2[0]); qc.cx(Phase1[0], Phase2[0])
    lcs = compact_lc_swap_gate(k=k2, K=K2)
    _e._append_with_optional_clbits(
        qc, lcs,
        [ctrl, Phase1[0], Sign[0]]
        + list(Work1[k2 - 1:K2 + 1]) + list(l_t) + list(l_q)
        + list(Dirty[2:6])
        + (scratch + [Phase2[0]])[:6],
    )
    qc.cx(Phase1[0], Phase2[0]); qc.cx(ctrl, Phase2[0])
    qc.cx(Phase2[0], ctrl); qc.cx(Phase1[0], ctrl)
    # l_q +/- updates.
    _make_condition(qc, [(Phase1[0], 1), (Phase2[0], 0)], ctrl, scratch)
    _decrement_by_prefix_clean(qc, l_q, scratch[:3], ctrl)
    _make_condition(qc, [(Phase1[0], 1), (Phase2[0], 0)], ctrl, scratch)
    _make_condition(qc, [(Phase1[0], 0), (Phase2[0], 1)], ctrl, scratch)
    _increment_by_prefix_clean(qc, l_q, scratch[:3], ctrl)
    _make_condition(qc, [(Phase1[0], 0), (Phase2[0], 1)], ctrl, scratch)
    # The restoring add computes its tail predicate at the exact selected-carry
    # midpoint.  Phase1 is already the add control, so the global control lane
    # can hold that temporary while five global scratch lanes plus the reversible Phase2 loan remain
    # available to the unchanged six-scratch T-add.
    # T sub condition: Phase1=1 and (Phase2=1 or Sign=0)
    tmp = scratch[0]
    _make_condition(qc, [(Phase2[0], 0), (Sign[0], 1)], tmp, scratch[1:])
    _make_condition(qc, [(Phase1[0], 1), (tmp, 0)], ctrl, scratch[1:])
    _make_condition(qc, [(Phase2[0], 0), (Sign[0], 1)], tmp, scratch[1:])
    tsub_scratch_count = _compact_prefix_addsub_scratch_count(k=k3, K=K3)
    if tsub_scratch_count > len(scratch):
        raise ValueError("T_SUB_COMPACT exceeds the global clean-scratch budget")
    tsub_uses_clean = tsub_scratch_count < len(scratch)
    tsub = compact_prefix_addsub_gate(k=k3, K=K3,
                                      mode="sub", sign_update=False,
                                      capture_borrow_sign=False,
                                      target="work2", name="T_SUB_COMPACT",
                                      use_one_clean_mcx=tsub_uses_clean)
    tsub_lanes = ([ctrl, Sign[0]]
                  + list(Work1[k3-1:K3]) + list(Work2[k3-1:K3])
                  + list(l_t) + [Dirty[3], Dirty[6], Dirty[0], Dirty[1], Dirty[2]]
                  + scratch[:tsub_scratch_count])
    if tsub_uses_clean:
        tsub_lanes.append(scratch[tsub_scratch_count])
    _e._append_with_optional_clbits(qc, tsub, tsub_lanes)
    _make_condition(qc, [(Phase2[0], 0), (Sign[0], 1)], tmp, scratch[1:])
    _make_condition(qc, [(Phase1[0], 1), (tmp, 0)], ctrl, scratch[1:])
    _make_condition(qc, [(Phase2[0], 0), (Sign[0], 1)], tmp, scratch[1:])
    qc.cx(Phase1[0], Sign[0])
    # Source-bound Phase2 loan: D uses physical l_q=255, not logical 256.
    _borrow_phase2_for_tadd(
        qc, phase1=Phase1[0], phase2=Phase2[0], l_q=l_q,
        dirty=Dirty,
    )
    tadd = compact_prefix_add_midtail_gate(n=n, k=k3, K=K3)
    _e._append_with_optional_clbits(
        qc, tadd,
        [Phase1[0], Sign[0], ctrl]
        + list(Work1) + list(Work2)
        + list(l_t) + list(l_s) + list(l_rp)
        + list(Dirty) + scratch + [Phase2[0]],
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
        + [ctrl, scratch[0]],
    )
    # Phase update
    pupdate = compact_phase_update_gate()
    _e._append_with_optional_clbits(
        qc, pupdate,
        [Phase1[0], Phase2[0], Sign[0]]
        + list(l_q) + list(l_rp) + list(l_s)
        + list(Dirty) + [ctrl, scratch[0], scratch[1]],
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
            dirty=Dirty, scratch=scratch, clean=scratch[0],
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
                                        + scratch)
        qc.cx(ctrl, Iter[0])
        _toggle_terminal_endpoint_raw(
            qc, l_q=l_q, l_s=l_s, out=ctrl,
            dirty=Dirty, scratch=scratch, clean=scratch[0],
        )

def build_step_circuit(n:int, T:int, *, T_max:Optional[int]=None, aux_size:Optional[int]=None, measurement_uncompute:bool=True):
    cfg=get_n_config(n); lw=int(cfg['len_width']); T_max=int(T_max or cfg['T_max'])
    sw=LS_WIDTH
    if aux_size is None: aux_size=qiskit_paper_aux_size(n,lw,sw,T_max)
    set_measurement_uncompute(measurement_uncompute)
    regs=make_global_registers_noctrl(n=n,len_width=lw,shift_width=sw,T_max=T_max,aux_size=aux_size)
    qc=QuantumCircuit(*regs, name=f"S835_FASTDUAL_STEP_T{T}_{n}")
    Phase1,Phase2,Iter,Sign,Work1,Work2,l_t,l_q,l_s,l_rp,Aux,Dirty=regs
    append_one_step_T(qc,T=T,n=n,len_width=lw,shift_width=sw,Phase1=Phase1,Phase2=Phase2,Iter=Iter,Sign=Sign,Work1=Work1,Work2=Work2,l_t=l_t,l_q=l_q,l_s=l_s,l_rp=l_rp,Aux=Aux,Dirty=Dirty)
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
