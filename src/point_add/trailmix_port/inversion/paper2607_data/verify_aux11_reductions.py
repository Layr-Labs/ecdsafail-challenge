#!/usr/bin/env python3
"""Differential basis-state checks for the paper2607 11-clean-aux route."""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
import random
import sys


PRIMITIVES = {"x", "cx", "ccx", "z", "cz", "swap", "clean_c3x_mbu"}
LOGICAL_REGISTERS = (
    "Phase1",
    "Phase2",
    "Iter",
    "Sign",
    "Work1",
    "Work2",
    "l_t",
    "l_q",
    "l_s",
    "l_rp",
    "DirtyPassenger",
)


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def as_circuit(obj):
    if hasattr(obj, "data"):
        return obj
    definition = getattr(obj, "definition", None)
    if definition is None:
        raise TypeError(f"{obj!r} has no circuit definition")
    return definition


def qindex(circuit, qubit) -> int:
    circuit = as_circuit(circuit)
    return circuit.find_bit(qubit).index


def qreg(circuit, name: str):
    circuit = as_circuit(circuit)
    matches = [register for register in circuit.qregs if register.name == name]
    if len(matches) != 1:
        raise AssertionError(f"{circuit.name}: register {name!r}: {len(matches)} matches")
    return matches[0]


def flatten(circuit, qmap=None):
    circuit = as_circuit(circuit)
    if qmap is None:
        qmap = {qubit: index for index, qubit in enumerate(circuit.qubits)}
    for item in circuit.data:
        operation = item.operation
        qargs = [qmap[qubit] for qubit in item.qubits]
        name = operation.name.lower()
        if name in PRIMITIVES:
            yield name, qargs
            continue
        definition = operation.definition
        if definition is None:
            raise ValueError(f"opaque operation {operation.name!r}")
        child_map = {
            qubit: qargs[index] for index, qubit in enumerate(definition.qubits)
        }
        yield from flatten(definition, child_map)


def apply(circuit, state: list[int], case_mask: int, *, inverse: bool = False) -> None:
    operations = list(flatten(circuit))
    if inverse:
        operations.reverse()
    for name, qargs in operations:
        if name == "x":
            state[qargs[0]] ^= case_mask
        elif name == "cx":
            state[qargs[1]] ^= state[qargs[0]]
        elif name == "ccx":
            state[qargs[2]] ^= state[qargs[0]] & state[qargs[1]]
        elif name == "swap":
            state[qargs[0]], state[qargs[1]] = state[qargs[1]], state[qargs[0]]
        elif name == "clean_c3x_mbu":
            if state[qargs[4]] != 0:
                raise AssertionError("clean-C3X temporary is not clean")
            state[qargs[3]] ^= (
                state[qargs[0]] & state[qargs[1]] & state[qargs[2]]
            )
        elif name in {"z", "cz"}:
            continue
        else:
            raise AssertionError(name)


def random_words(width: int, cases: int, rng: random.Random) -> list[int]:
    lanes = [0] * width
    for case in range(cases):
        value = rng.getrandbits(width)
        for bit in range(width):
            if (value >> bit) & 1:
                lanes[bit] |= 1 << case
    return lanes


def constant_word(value: int, width: int, case_mask: int) -> list[int]:
    return [case_mask if (value >> bit) & 1 else 0 for bit in range(width)]


def positional_layout(fields: list[tuple[str, int]]) -> dict[str, range]:
    offset = 0
    layout = {}
    for name, width in fields:
        layout[name] = range(offset, offset + width)
        offset += width
    return layout


def set_positional(
    state: list[int], layout: dict[str, range], name: str, values: list[int]
) -> None:
    positions = layout[name]
    if len(positions) != len(values):
        raise AssertionError(f"{name}: width {len(positions)} != {len(values)}")
    for position, value in zip(positions, values):
        state[position] = value


def get_positional(
    state: list[int], layout: dict[str, range], name: str
) -> list[int]:
    return [state[position] for position in layout[name]]


def initialize_positional(
    old,
    new,
    old_layout: dict[str, range],
    new_layout: dict[str, range],
    values: dict[str, list[int]],
) -> tuple[list[int], list[int]]:
    old_state = [0] * old.num_qubits
    new_state = [0] * new.num_qubits
    for name, lanes in values.items():
        set_positional(old_state, old_layout, name, lanes)
        set_positional(new_state, new_layout, name, lanes)
    return old_state, new_state


def set_register(circuit, state: list[int], name: str, values: list[int]) -> None:
    register = qreg(circuit, name)
    if len(register) != len(values):
        raise AssertionError(f"{name}: width {len(register)} != {len(values)}")
    for qubit, value in zip(register, values):
        state[qindex(circuit, qubit)] = value


def get_register(circuit, state: list[int], name: str) -> list[int]:
    return [state[qindex(circuit, qubit)] for qubit in qreg(circuit, name)]


def compare_outputs(label: str, old, old_state, new, new_state) -> None:
    for name in LOGICAL_REGISTERS:
        if get_register(old, old_state, name) != get_register(new, new_state, name):
            raise AssertionError(f"{label}: {name} differs")
    if any(get_register(old, old_state, "Aux")):
        raise AssertionError(f"{label}: old Aux not clean")
    if any(get_register(new, new_state, "Aux")):
        raise AssertionError(f"{label}: new Aux not clean")


def initialize_common(old, new, values: dict[str, list[int]]) -> tuple[list[int], list[int]]:
    old_state = [0] * old.num_qubits
    new_state = [0] * new.num_qubits
    for name, lanes in values.items():
        set_register(old, old_state, name, lanes)
        set_register(new, new_state, name, lanes)
    return old_state, new_state


def check_full_steps(original, candidate, *, cases: int, quick: bool) -> None:
    rng = random.Random(0x823F011)
    # Arbitrary metadata is not a supported input to later microsteps: even the
    # aux12 reference can leave its scratch live there.  Step 1 remains useful
    # as a whole-caller differential check; later reachable trajectories are
    # covered by the serialized-stream and official endpoint replays.
    steps = [1]
    case_mask = (1 << cases) - 1
    for step in steps:
        old = original.build_step_circuit(
            256, step, T_max=1616, aux_size=12, measurement_uncompute=False,
        )
        new = candidate.build_step_circuit(
            256, step, T_max=1616, aux_size=11, measurement_uncompute=False,
        )
        if (old.num_qubits, new.num_qubits) != (578, 577):
            raise AssertionError(f"step {step}: widths {old.num_qubits}/{new.num_qubits}")

        values = {
            "Phase1": [0],
            "Phase2": [0],
            "Iter": [rng.getrandbits(cases)],
            "Sign": [0],
            "Work1": random_words(259, cases, rng),
            "Work2": random_words(259, cases, rng),
            "l_t": constant_word(0, 8, case_mask),
            "l_q": constant_word((1 << 9) - 1, 9, case_mask),
            "l_s": constant_word(258, 9, case_mask),
            "l_rp": constant_word(254, 8, case_mask),
            "DirtyPassenger": random_words(10, cases, rng),
        }
        old_state, new_state = initialize_common(old, new, values)
        old_initial, new_initial = old_state.copy(), new_state.copy()
        apply(old, old_state, case_mask)
        apply(new, new_state, case_mask)
        compare_outputs(f"step {step}", old, old_state, new, new_state)
        apply(old, old_state, case_mask, inverse=True)
        apply(new, new_state, case_mask, inverse=True)
        if old_state != old_initial or new_state != new_initial:
            raise AssertionError(f"step {step}: reverse mismatch")
        print(f"PASS full-step differential step={step} cases={cases}", flush=True)


def check_r_blocks(original, candidate, *, cases: int, quick: bool) -> None:
    rng = random.Random(0x823A11)
    steps = [1, 1470] if quick else [1, 257, 800, 1200, 1470, 1600]
    case_mask = (1 << cases) - 1
    for step in steps:
        k, upper = candidate.safe_active_windows(256, step)["r_addsub"]
        old = original.compact_r_subrestore_fused_gate(n=256, k=k, K=upper)
        new = candidate.compact_r_subrestore_fused_gate(n=256, k=k, K=upper)
        work_width = upper - k + 1
        common_fields = [
            ("Ctrl", 1),
            ("Phase2", 1),
            ("Mode", 1),
            ("Sign", 1),
            ("Work1", work_width),
            ("Work2", work_width),
            ("l_t", 8),
            ("l_q", 9),
            ("l_s", 9),
            ("DirtyPassenger", 10),
        ]
        old_layout = positional_layout(common_fields + [("Scratch", 11)])
        new_layout = positional_layout(common_fields + [("Scratch", 10)])
        ctrl = rng.getrandbits(cases)
        mode = rng.getrandbits(cases) & (case_mask ^ ctrl)
        values = {
            "Ctrl": [ctrl],
            "Phase2": [rng.getrandbits(cases)],
            "Mode": [mode],
            "Sign": [rng.getrandbits(cases)],
            "Work1": random_words(upper - k + 1, cases, rng),
            "Work2": random_words(upper - k + 1, cases, rng),
            # Choose a certified in-window dynamic interval:
            # lower=ell_t+ell_q+1=k and upper=259-ell_s=upper.
            "l_t": constant_word(k - 2, 8, case_mask),
            "l_q": constant_word((1 << 9) - 1, 9, case_mask),
            "l_s": constant_word((258 - upper) % 259, 9, case_mask),
            "DirtyPassenger": random_words(10, cases, rng),
        }
        old_state, new_state = initialize_positional(
            old, new, old_layout, new_layout, values
        )
        old_initial, new_initial = old_state.copy(), new_state.copy()
        apply(old, old_state, case_mask)
        apply(new, new_state, case_mask)
        for name in values:
            if get_positional(old_state, old_layout, name) != get_positional(
                new_state, new_layout, name
            ):
                raise AssertionError(f"R step {step}: {name} differs")
        if any(get_positional(old_state, old_layout, "Scratch")):
            raise AssertionError(f"R step {step}: old Scratch not clean")
        if any(get_positional(new_state, new_layout, "Scratch")):
            raise AssertionError(f"R step {step}: new Scratch not clean")
        apply(old, old_state, case_mask, inverse=True)
        apply(new, new_state, case_mask, inverse=True)
        if old_state != old_initial or new_state != new_initial:
            raise AssertionError(f"R step {step}: reverse mismatch")
        print(f"PASS R differential step={step} window={k}:{upper}", flush=True)


def check_phase_update(original, candidate, *, cases: int) -> None:
    rng = random.Random(0x823FACE)
    case_mask = (1 << cases) - 1
    old = original.compact_phase_update_gate()
    new = candidate.compact_phase_update_gate()
    common_fields = [
        ("Phase1", 1),
        ("Phase2", 1),
        ("Sign", 1),
        ("l_q", 9),
        ("l_rp", 8),
        ("l_s", 9),
    ]
    old_layout = positional_layout(common_fields + [("Scratch", 11)])
    new_layout = positional_layout(common_fields + [("Scratch", 10)])
    values = {
        "Phase1": [rng.getrandbits(cases)],
        "Phase2": [rng.getrandbits(cases)],
        "Sign": [rng.getrandbits(cases)],
        "l_q": random_words(9, cases, rng),
        "l_rp": random_words(8, cases, rng),
        "l_s": random_words(9, cases, rng),
    }
    old_state, new_state = initialize_positional(
        old, new, old_layout, new_layout, values
    )
    old_initial, new_initial = old_state.copy(), new_state.copy()
    apply(old, old_state, case_mask)
    apply(new, new_state, case_mask)
    for name in values:
        if get_positional(old_state, old_layout, name) != get_positional(
            new_state, new_layout, name
        ):
            raise AssertionError(f"phase update: {name} differs")
    if any(get_positional(old_state, old_layout, "Scratch")):
        raise AssertionError("phase update: old Scratch not clean")
    if any(get_positional(new_state, new_layout, "Scratch")):
        raise AssertionError("phase update: new Scratch not clean")
    apply(old, old_state, case_mask, inverse=True)
    apply(new, new_state, case_mask, inverse=True)
    if old_state != old_initial or new_state != new_initial:
        raise AssertionError("phase update: reverse mismatch")
    print(f"PASS phase-update differential cases={cases}", flush=True)


def check_terminal_blocks(original, candidate, *, cases: int, quick: bool) -> None:
    rng = random.Random(0x8237E2)
    # The end trigger is unreachable before the 1024-step lower horizon.
    steps = [1524, 1600] if quick else [1024, 1200, 1400, 1524, 1600]
    case_mask = (1 << cases) - 1
    for step in steps:
        windows = candidate.safe_active_windows(256, step)
        k4, upper4 = windows["len_update_lt"]
        k5, upper5 = windows["len_update_lrp"]
        old = original.compact_swap_work_and_len_gate(
            n=256, k4=k4, K4=upper4, k5=k5, K5=upper5,
        )
        new = candidate.compact_swap_work_and_len_gate(
            n=256, k4=k4, K4=upper4, k5=k5, K5=upper5,
        )
        common_fields = [
            ("Ctrl", 1),
            ("Work1", 259),
            ("Work2", 259),
            ("l_t", 8),
            ("l_rp", 8),
            ("Borrowed", 1),
        ]
        old_layout = positional_layout(common_fields + [("Scratch", 11)])
        new_layout = positional_layout(
            common_fields + [("Extension", 1), ("Scratch", 10)]
        )
        ctrl = rng.getrandbits(cases)
        extension = rng.getrandbits(cases) & (case_mask ^ ctrl)
        boundary_b = max(3, k4)
        if boundary_b > upper4:
            raise AssertionError(
                f"terminal step {step}: no valid l_rp boundary in {k4}:{upper4}"
            )
        boundary_a = max(3, k5)
        if boundary_a > upper5:
            raise AssertionError(
                f"terminal step {step}: no valid l_t boundary in {k5}:{upper5}"
            )
        values = {
            "Ctrl": [ctrl],
            "Work1": random_words(259, cases, rng),
            "Work2": random_words(259, cases, rng),
            # LEN_LT scans B=258-enc(l_rp); LEN_LRP scans
            # A=enc(l_t)+3.  Keep both boundaries in their certificates.
            "l_t": constant_word(boundary_a - 3, 8, case_mask),
            "l_rp": constant_word(258 - boundary_b, 8, case_mask),
            "Borrowed": [rng.getrandbits(cases)],
        }
        old_state, new_state = initialize_positional(
            old, new, old_layout, new_layout, values
        )
        set_positional(new_state, new_layout, "Extension", [extension])
        old_initial, new_initial = old_state.copy(), new_state.copy()
        apply(old, old_state, case_mask)
        apply(new, new_state, case_mask)
        for name in values:
            if get_positional(old_state, old_layout, name) != get_positional(
                new_state, new_layout, name
            ):
                raise AssertionError(f"terminal step {step}: {name} differs")
        if get_positional(new_state, new_layout, "Extension") != [extension]:
            raise AssertionError(f"terminal step {step}: Extension not restored")
        if any(get_positional(old_state, old_layout, "Scratch")):
            raise AssertionError(f"terminal step {step}: old Scratch not clean")
        if any(get_positional(new_state, new_layout, "Scratch")):
            raise AssertionError(f"terminal step {step}: new Scratch not clean")
        apply(old, old_state, case_mask, inverse=True)
        apply(new, new_state, case_mask, inverse=True)
        if old_state != old_initial or new_state != new_initial:
            raise AssertionError(f"terminal step {step}: reverse mismatch")
        print(f"PASS terminal differential step={step} cases={cases}", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--original", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--cases", type=int, default=32)
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args()
    if not 1 <= args.cases <= 128:
        raise SystemExit("--cases must be in 1..128")
    original = load_module("paper2607_original", args.original.resolve())
    candidate = load_module("paper2607_candidate", args.candidate.resolve())
    check_phase_update(original, candidate, cases=args.cases)
    check_r_blocks(original, candidate, cases=args.cases, quick=args.quick)
    check_terminal_blocks(original, candidate, cases=args.cases, quick=args.quick)
    check_full_steps(original, candidate, cases=args.cases, quick=args.quick)
    print("PASS aux11 differential suite", flush=True)


if __name__ == "__main__":
    main()
