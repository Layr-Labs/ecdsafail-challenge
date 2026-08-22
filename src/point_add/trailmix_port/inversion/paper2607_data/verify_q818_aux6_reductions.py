#!/usr/bin/env python3
"""Differential basis-state checks for the Q817 five-clean-aux route."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import verify_aux11_reductions as diff


LOGICAL_STEP_REGISTERS = (
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


def check_tadd_null_schedule(candidate) -> None:
    null_steps = [
        step
        for step, row in enumerate(candidate._CERTIFIED_WINDOW_ROWS, start=1)
        if row["t_addsub"] is None
    ]
    if null_steps != [1, 2, 3, 4]:
        raise AssertionError(f"unexpected t_addsub null steps: {null_steps}")
    print("PASS certified t_addsub null steps=1,2,3,4", flush=True)


def random_register(circuit, name: str, cases: int, rng: random.Random) -> list[int]:
    return diff.random_words(len(diff.qreg(circuit, name)), cases, rng)


def compare_gate(
    label: str,
    old,
    new,
    *,
    common: dict[str, list[int]],
    old_private: dict[str, list[int]] | None = None,
    new_private: dict[str, list[int]] | None = None,
) -> None:
    old_private = old_private or {}
    new_private = new_private or {}
    old_state = [0] * old.num_qubits
    new_state = [0] * new.num_qubits
    for name, values in common.items():
        diff.set_register(old, old_state, name, values)
        diff.set_register(new, new_state, name, values)
    for name, values in old_private.items():
        diff.set_register(old, old_state, name, values)
    for name, values in new_private.items():
        diff.set_register(new, new_state, name, values)
    old_initial = old_state.copy()
    new_initial = new_state.copy()
    case_mask = 0
    for values in list(common.values()) + list(old_private.values()) + list(new_private.values()):
        for value in values:
            case_mask |= value
    case_mask = (1 << max(1, case_mask.bit_length())) - 1

    diff.apply(old, old_state, case_mask)
    diff.apply(new, new_state, case_mask)
    for name in common:
        got = diff.get_register(new, new_state, name)
        want = diff.get_register(old, old_state, name)
        if got != want:
            raise AssertionError(f"{label}: {name} differs")
    for name in old_private:
        if diff.get_register(old, old_state, name) != diff.get_register(
            old, old_initial, name
        ):
            raise AssertionError(f"{label}: old {name} not restored")
    for name in new_private:
        if diff.get_register(new, new_state, name) != diff.get_register(
            new, new_initial, name
        ):
            raise AssertionError(f"{label}: new {name} not restored")
    if any(diff.get_register(old, old_state, "Scratch")):
        raise AssertionError(f"{label}: old Scratch not clean")
    if any(diff.get_register(new, new_state, "Scratch")):
        raise AssertionError(f"{label}: new Scratch not clean")

    diff.apply(old, old_state, case_mask, inverse=True)
    diff.apply(new, new_state, case_mask, inverse=True)
    if old_state != old_initial:
        raise AssertionError(f"{label}: old reverse mismatch")
    if new_state != new_initial:
        raise AssertionError(f"{label}: new reverse mismatch")
    print(f"PASS {label} reverse=exact", flush=True)


def compare_gate_positional(
    label: str,
    old,
    new,
    *,
    cases: int,
    common_fields: list[tuple[str, int]],
    common: dict[str, list[int]],
    old_private_fields: list[tuple[str, int]] | None = None,
    new_private_fields: list[tuple[str, int]] | None = None,
    old_private: dict[str, list[int]] | None = None,
    new_private: dict[str, list[int]] | None = None,
) -> None:
    old_private_fields = old_private_fields or []
    new_private_fields = new_private_fields or []
    old_private = old_private or {}
    new_private = new_private or {}
    old_prefix = common_fields + old_private_fields
    new_prefix = common_fields + new_private_fields
    old_scratch = old.num_qubits - sum(width for _, width in old_prefix)
    new_scratch = new.num_qubits - sum(width for _, width in new_prefix)
    if old_scratch < 0 or new_scratch < 0:
        raise AssertionError(f"{label}: invalid positional layout")
    old_layout = diff.positional_layout(old_prefix + [("Scratch", old_scratch)])
    new_layout = diff.positional_layout(new_prefix + [("Scratch", new_scratch)])
    old_state = [0] * old.num_qubits
    new_state = [0] * new.num_qubits
    for name, values in common.items():
        diff.set_positional(old_state, old_layout, name, values)
        diff.set_positional(new_state, new_layout, name, values)
    for name, values in old_private.items():
        diff.set_positional(old_state, old_layout, name, values)
    for name, values in new_private.items():
        diff.set_positional(new_state, new_layout, name, values)
    old_initial, new_initial = old_state.copy(), new_state.copy()
    case_mask = (1 << cases) - 1
    diff.apply(old, old_state, case_mask)
    diff.apply(new, new_state, case_mask)
    for name in common:
        if diff.get_positional(old_state, old_layout, name) != diff.get_positional(
            new_state, new_layout, name
        ):
            raise AssertionError(f"{label}: {name} differs")
    for name in old_private:
        if diff.get_positional(old_state, old_layout, name) != diff.get_positional(
            old_initial, old_layout, name
        ):
            raise AssertionError(f"{label}: old {name} not restored")
    for name in new_private:
        if diff.get_positional(new_state, new_layout, name) != diff.get_positional(
            new_initial, new_layout, name
        ):
            raise AssertionError(f"{label}: new {name} not restored")
    if any(diff.get_positional(old_state, old_layout, "Scratch")):
        raise AssertionError(f"{label}: old Scratch not clean")
    if any(diff.get_positional(new_state, new_layout, "Scratch")):
        raise AssertionError(f"{label}: new Scratch not clean")
    diff.apply(old, old_state, case_mask, inverse=True)
    diff.apply(new, new_state, case_mask, inverse=True)
    if old_state != old_initial or new_state != new_initial:
        raise AssertionError(f"{label}: reverse mismatch")
    print(
        f"PASS {label} scratch={old_scratch}->{new_scratch} reverse=exact",
        flush=True,
    )


def random_field_values(
    fields: list[tuple[str, int]], cases: int, rng: random.Random
) -> dict[str, list[int]]:
    return {
        name: diff.random_words(width, cases, rng)
        for name, width in fields
    }


def check_live_predicate(original, candidate) -> None:
    from qiskit import QuantumCircuit, QuantumRegister

    phase_o = QuantumRegister(1, "Phase1")
    lrp_o = QuantumRegister(8, "l_rp")
    out_o = QuantumRegister(1, "Out")
    scratch_o = QuantumRegister(6, "Scratch")
    old = QuantumCircuit(phase_o, lrp_o, out_o, scratch_o)
    original._toggle_live_r_phase(
        old, phase1=phase_o[0], l_rp=lrp_o, out=out_o[0], scratch=scratch_o,
    )

    phase_n = QuantumRegister(1, "Phase1")
    lrp_n = QuantumRegister(8, "l_rp")
    out_n = QuantumRegister(1, "Out")
    dirty_n = QuantumRegister(10, "DirtyPassenger")
    scratch_n = QuantumRegister(1, "Scratch")
    new = QuantumCircuit(phase_n, lrp_n, out_n, dirty_n, scratch_n)
    candidate._toggle_live_r_phase(
        new, phase1=phase_n[0], l_rp=lrp_n, out=out_n[0], dirty=dirty_n,
    )

    cases = 1024
    case_mask = (1 << cases) - 1
    phase = [0]
    lrp = [0] * 8
    out = [0]
    for case in range(cases):
        value = case & 0xFF
        if (case >> 8) & 1:
            phase[0] |= 1 << case
        if (case >> 9) & 1:
            out[0] |= 1 << case
        for bit in range(8):
            if (value >> bit) & 1:
                lrp[bit] |= 1 << case
    rng = random.Random(0x81811E)
    common = {"Phase1": phase, "l_rp": lrp, "Out": out}
    old_state = [0] * old.num_qubits
    new_state = [0] * new.num_qubits
    for name, values in common.items():
        diff.set_register(old, old_state, name, values)
        diff.set_register(new, new_state, name, values)
    dirty = diff.random_words(10, cases, rng)
    diff.set_register(new, new_state, "DirtyPassenger", dirty)
    old_initial, new_initial = old_state.copy(), new_state.copy()
    diff.apply(old, old_state, case_mask)
    diff.apply(new, new_state, case_mask)
    for name in common:
        if diff.get_register(old, old_state, name) != diff.get_register(new, new_state, name):
            raise AssertionError(f"live predicate: {name} differs")
    if diff.get_register(new, new_state, "DirtyPassenger") != dirty:
        raise AssertionError("live predicate: dirty lenders not restored")
    if any(diff.get_register(old, old_state, "Scratch")):
        raise AssertionError("live predicate: old Scratch not clean")
    diff.apply(old, old_state, case_mask, inverse=True)
    diff.apply(new, new_state, case_mask, inverse=True)
    if old_state != old_initial or new_state != new_initial:
        raise AssertionError("live predicate: reverse mismatch")
    print("PASS live-predicate cases=1024 dirty=restored reverse=exact", flush=True)


def endpoint_cases() -> tuple[list[int], list[int]]:
    pairs = []
    pairs.extend((lq, 258) for lq in range(512))
    pairs.extend((0, ls) for ls in range(512))
    rng = random.Random(0x818E0D)
    pairs.extend((rng.randrange(512), rng.randrange(512)) for _ in range(1024))
    lq_words = [0] * 9
    ls_words = [0] * 9
    for case, (lq, ls) in enumerate(pairs):
        for bit in range(9):
            if (lq >> bit) & 1:
                lq_words[bit] |= 1 << case
            if (ls >> bit) & 1:
                ls_words[bit] |= 1 << case
    return lq_words, ls_words


def check_terminal_endpoint(original, candidate) -> None:
    from qiskit import QuantumCircuit, QuantumRegister

    lq_o = QuantumRegister(9, "l_q")
    ls_o = QuantumRegister(9, "l_s")
    out_o = QuantumRegister(1, "Out")
    dirty_o = QuantumRegister(10, "DirtyPassenger")
    scratch_o = QuantumRegister(5, "Scratch")
    iteration_o = QuantumRegister(1, "Iter")
    old = QuantumCircuit(lq_o, ls_o, out_o, dirty_o, scratch_o, iteration_o)
    original._toggle_terminal_endpoint_raw(
        old, l_q=lq_o, l_s=ls_o, out=out_o[0], dirty=dirty_o,
        scratch=scratch_o, extra_lenders=iteration_o,
    )

    lq_n = QuantumRegister(9, "l_q")
    ls_n = QuantumRegister(9, "l_s")
    out_n = QuantumRegister(1, "Out")
    dirty_n = QuantumRegister(10, "DirtyPassenger")
    scratch_n = QuantumRegister(4, "Scratch")
    iteration_n = QuantumRegister(1, "Iter")
    sign_n = QuantumRegister(1, "Sign")
    new = QuantumCircuit(
        lq_n, ls_n, out_n, dirty_n, scratch_n, iteration_n, sign_n,
    )
    candidate._toggle_terminal_endpoint_raw(
        new, l_q=lq_n, l_s=ls_n, out=out_n[0], dirty=dirty_n,
        scratch=scratch_n, extra_lenders=[iteration_n[0], sign_n[0]],
    )

    lq, ls = endpoint_cases()
    cases = 2048
    case_mask = (1 << cases) - 1
    rng = random.Random(0x818E11)
    common = {
        "l_q": lq,
        "l_s": ls,
        "Out": diff.random_words(1, cases, rng),
        "DirtyPassenger": diff.random_words(10, cases, rng),
    }
    old_state = [0] * old.num_qubits
    new_state = [0] * new.num_qubits
    for name, values in common.items():
        diff.set_register(old, old_state, name, values)
        diff.set_register(new, new_state, name, values)
    iteration = diff.random_words(1, cases, rng)
    sign = diff.random_words(1, cases, rng)
    diff.set_register(old, old_state, "Iter", iteration)
    diff.set_register(new, new_state, "Iter", iteration)
    diff.set_register(new, new_state, "Sign", sign)
    old_initial, new_initial = old_state.copy(), new_state.copy()
    diff.apply(old, old_state, case_mask)
    diff.apply(new, new_state, case_mask)
    for name in common:
        if diff.get_register(old, old_state, name) != diff.get_register(new, new_state, name):
            raise AssertionError(f"terminal endpoint: {name} differs")
    if diff.get_register(new, new_state, "Iter") != diff.get_register(
        new, new_initial, "Iter"
    ):
        raise AssertionError("terminal endpoint: Iter lender not restored")
    if diff.get_register(new, new_state, "Sign") != sign:
        raise AssertionError("terminal endpoint: Sign lender not restored")
    if any(diff.get_register(old, old_state, "Scratch")) or any(
        diff.get_register(new, new_state, "Scratch")
    ):
        raise AssertionError("terminal endpoint: Scratch not clean")
    diff.apply(old, old_state, case_mask, inverse=True)
    diff.apply(new, new_state, case_mask, inverse=True)
    if old_state != old_initial or new_state != new_initial:
        raise AssertionError("terminal endpoint: reverse mismatch")
    print("PASS terminal-endpoint cases=2048 lenders=restored reverse=exact", flush=True)


def check_lc(original, candidate, cases: int) -> None:
    rng = random.Random(0x8181C)
    for step in (4, 519, 800, 1200, 1616):
        k, upper = candidate.safe_active_windows(256, step)["swap"]
        old = original.compact_lc_swap_gate(k=k, K=upper)
        new = candidate.compact_lc_swap_gate(k=k, K=upper)
        fields = [
            ("Ctrl", 1), ("Direction", 1), ("Sign", 1),
            ("Work1", upper - k + 2), ("l_t", 8), ("l_q", 9),
        ]
        old_dirty = diff.random_words(4, cases, rng)
        new_dirty = old_dirty + diff.random_words(1, cases, rng)
        compare_gate_positional(
            f"lc-swap step={step} window={k}:{upper} cases={cases}",
            old, new, cases=cases, common_fields=fields,
            common=random_field_values(fields, cases, rng),
            old_private_fields=[("DirtyPassenger", 4)],
            new_private_fields=[("DirtyPassenger", 5)],
            old_private={"DirtyPassenger": old_dirty},
            new_private={"DirtyPassenger": new_dirty},
        )


def check_tsub(original, candidate, cases: int) -> None:
    rng = random.Random(0x81875B)
    for upper in (1, 130, 200, 257):
        kwargs = dict(
            k=1, K=upper, mode="sub", sign_update=False,
            capture_borrow_sign=False, target="work2", name=f"T_SUB_{upper}",
        )
        old = original.compact_prefix_addsub_gate(**kwargs)
        new = candidate.compact_prefix_addsub_gate(**kwargs)
        fields = [
            ("Ctrl", 1), ("Sign", 1), ("Work1", upper),
            ("Work2", upper), ("l_t", 8),
        ]
        first_three = diff.random_words(3, cases, rng)
        compare_gate_positional(
            f"t-sub upper={upper} cases={cases}", old, new, cases=cases,
            common_fields=fields, common=random_field_values(fields, cases, rng),
            old_private_fields=[("Borrowed", 3)],
            new_private_fields=[("Borrowed", 4)],
            old_private={"Borrowed": first_three},
            new_private={
                "Borrowed": first_three + diff.random_words(1, cases, rng)
            },
        )


def check_tadd(original, candidate, cases: int) -> None:
    rng = random.Random(0x818ADD)
    for upper in (1, 130, 200, 257):
        old = original.compact_prefix_add_midtail_gate(n=256, k=1, K=upper)
        new = candidate.compact_prefix_add_midtail_gate(n=256, k=1, K=upper)
        fields = [
            ("Ctrl", 1), ("Sign", 1), ("Tail", 1),
            ("Work1", 259), ("Work2", 259), ("l_t", 8),
            ("l_s", 9), ("l_rp", 8), ("DirtyPassenger", 10),
        ]
        compare_gate_positional(
            f"t-add upper={upper} cases={cases}", old, new, cases=cases,
            common_fields=fields, common=random_field_values(fields, cases, rng),
        )


def check_terminal_lengths(original, candidate, cases: int) -> None:
    rng = random.Random(0x8187E2)
    for step in (1024, 1200, 1400, 1524, 1600):
        windows = candidate.safe_active_windows(256, step)
        k4, upper4 = windows["len_update_lt"]
        k5, upper5 = windows["len_update_lrp"]
        old = original.compact_swap_work_and_len_gate(
            n=256, k4=k4, K4=upper4, k5=k5, K5=upper5,
        )
        new = candidate.compact_swap_work_and_len_gate(
            n=256, k4=k4, K4=upper4, k5=k5, K5=upper5,
        )
        fields = [
            ("Ctrl", 1), ("Work1", 259), ("Work2", 259),
            ("l_t", 8), ("l_rp", 8), ("DirtyPassenger", 8),
            ("Extension", 1),
        ]
        compare_gate_positional(
            f"terminal-lengths step={step} windows={k4}:{upper4}/{k5}:{upper5} cases={cases}",
            old, new, cases=cases, common_fields=fields,
            common=random_field_values(fields, cases, rng),
        )


def check_step_one(original, candidate, cases: int) -> None:
    rng = random.Random(0x81757E9)
    case_mask = (1 << cases) - 1
    old = original.build_step_circuit(
        256, 1, T_max=1616, aux_size=6, measurement_uncompute=False,
    )
    new = candidate.build_step_circuit(
        256, 1, T_max=1616, aux_size=5, measurement_uncompute=False,
    )
    values = {
        "Phase1": [0],
        "Phase2": [0],
        "Iter": diff.random_words(1, cases, rng),
        "Sign": [0],
        "Work1": diff.random_words(259, cases, rng),
        "Work2": diff.random_words(259, cases, rng),
        "l_t": diff.constant_word(0, 8, case_mask),
        "l_q": diff.constant_word((1 << 9) - 1, 9, case_mask),
        "l_s": diff.constant_word(258, 9, case_mask),
        "l_rp": diff.constant_word(254, 8, case_mask),
        "DirtyPassenger": diff.random_words(10, cases, rng),
    }
    old_state = [0] * old.num_qubits
    new_state = [0] * new.num_qubits
    for name, lanes in values.items():
        diff.set_register(old, old_state, name, lanes)
        diff.set_register(new, new_state, name, lanes)
    old_initial, new_initial = old_state.copy(), new_state.copy()
    diff.apply(old, old_state, case_mask)
    diff.apply(new, new_state, case_mask)
    for name in LOGICAL_STEP_REGISTERS:
        if diff.get_register(old, old_state, name) != diff.get_register(new, new_state, name):
            raise AssertionError(f"step 1: {name} differs")
    if any(diff.get_register(old, old_state, "Aux")) or any(
        diff.get_register(new, new_state, "Aux")
    ):
        raise AssertionError("step 1: Aux not clean")
    diff.apply(old, old_state, case_mask, inverse=True)
    diff.apply(new, new_state, case_mask, inverse=True)
    if old_state != old_initial or new_state != new_initial:
        raise AssertionError("step 1: reverse mismatch")
    print(f"PASS full-step step=1 cases={cases} reverse=exact", flush=True)


def check_all_construct(candidate) -> None:
    started = time.monotonic()
    widths: dict[int, int] = {}
    counts: Counter[str] = Counter()
    for step in range(1, 1617):
        circuit = candidate.build_step_circuit(
            256, step, T_max=1616, aux_size=5, measurement_uncompute=False,
        )
        widths[circuit.num_qubits] = widths.get(circuit.num_qubits, 0) + 1
        counts.update(candidate.count_circuit_ops_recursive(circuit))
        if step % 100 == 0:
            print(
                f"COUNT step={step} elapsed={time.monotonic() - started:.1f}s",
                flush=True,
            )
    if widths != {571: 1616}:
        raise AssertionError(f"schedule widths: {widths}")
    records = sum(counts.values())
    executed_toffoli = counts["ccx"] + 2 * counts["clean_c3x_mbu"]
    source_path = Path(candidate.__file__).resolve()
    receipt = {
        "schema": "paper2607-q817-aux5-schedule-count-v1",
        "source": str(source_path),
        "source_sha256": hashlib.sha256(source_path.read_bytes()).hexdigest(),
        "steps": 1616,
        "local_width": 571,
        "clean_aux": 5,
        "primitive_counts_per_traversal": dict(sorted(counts.items())),
        "records_per_traversal": records,
        "executed_toffoli_per_traversal": executed_toffoli,
        "four_traversal_records": 4 * records,
        "four_traversal_executed_toffoli": 4 * executed_toffoli,
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    print(json.dumps(receipt, indent=2, sort_keys=True), flush=True)
    print("PASS all-steps constructed=1616 local_width=571 clean_aux=5", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--original", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--cases", type=int, default=32)
    parser.add_argument("--construct-all", action="store_true")
    args = parser.parse_args()
    if not 1 <= args.cases <= 128:
        raise SystemExit("--cases must be in 1..128")
    original = diff.load_module("paper2607_q818_reference", args.original.resolve())
    candidate = diff.load_module("paper2607_q817_candidate", args.candidate.resolve())
    check_tadd_null_schedule(candidate)
    check_terminal_endpoint(original, candidate)
    check_lc(original, candidate, args.cases)
    check_tsub(original, candidate, args.cases)
    check_tadd(original, candidate, args.cases)
    check_terminal_lengths(original, candidate, args.cases)
    check_step_one(original, candidate, args.cases)
    if args.construct_all:
        check_all_construct(candidate)
    print("PASS Q817 Aux5 differential suite", flush=True)


if __name__ == "__main__":
    main()
