#!/usr/bin/env python3
"""Differential and reversibility checks for the complete Aux10 prototype."""

from __future__ import annotations

import argparse
from pathlib import Path
import random

import verify_aux11_reductions as v
import verify_aux10_stage1 as stage1


def words_from_values(values, width):
    lanes = [0] * width
    for case, value in enumerate(values):
        if not 0 <= value < (1 << width):
            raise ValueError((value, width))
        for bit in range(width):
            if (value >> bit) & 1:
                lanes[bit] |= 1 << case
    return lanes


def compare_positional(label, old_state, old_layout, new_state, new_layout, names):
    for name in names:
        if v.get_positional(old_state, old_layout, name) != v.get_positional(
            new_state, new_layout, name
        ):
            raise AssertionError(f"{label}: {name} differs")
    if any(v.get_positional(old_state, old_layout, "Scratch")):
        raise AssertionError(f"{label}: old Scratch not clean")
    if any(v.get_positional(new_state, new_layout, "Scratch")):
        raise AssertionError(f"{label}: new Scratch not clean")


def run_pair(label, old, new, old_layout, new_layout, values, extra_new, cases):
    old_state, new_state = v.initialize_positional(
        old, new, old_layout, new_layout, values
    )
    for name, lanes in extra_new.items():
        v.set_positional(new_state, new_layout, name, lanes)
    old_initial, new_initial = old_state.copy(), new_state.copy()
    mask = (1 << cases) - 1
    v.apply(old, old_state, mask)
    v.apply(new, new_state, mask)
    compare_positional(
        label, old_state, old_layout, new_state, new_layout, values.keys()
    )
    for name, lanes in extra_new.items():
        if v.get_positional(new_state, new_layout, name) != lanes:
            raise AssertionError(f"{label}: {name} not restored")
    v.apply(old, old_state, mask, inverse=True)
    v.apply(new, new_state, mask, inverse=True)
    if old_state != old_initial or new_state != new_initial:
        raise AssertionError(f"{label}: inverse mismatch")


def check_r(old_mod, new_mod, cases):
    rng = random.Random(0xA10B0001)
    mask = (1 << cases) - 1
    for step in [1, 257, 800, 1200, 1470, 1600]:
        k, upper = new_mod.safe_active_windows(256, step)["r_addsub"]
        old = old_mod.compact_r_subrestore_fused_gate(n=256, k=k, K=upper)
        new = new_mod.compact_r_subrestore_fused_gate(n=256, k=k, K=upper)
        width = upper - k + 1
        common = [
            ("Ctrl", 1),
            ("Phase2", 1),
            ("Mode", 1),
            ("Sign", 1),
            ("Work1", width),
            ("Work2", width),
            ("l_t", 8),
            ("l_q", 9),
            ("l_s", 9),
            ("DirtyPassenger", 10),
        ]
        old_layout = v.positional_layout(common + [("Scratch", 10)])
        new_layout = v.positional_layout(common + [("Scratch", 9)])
        ctrl = rng.getrandbits(cases)
        mode = rng.getrandbits(cases) & (mask ^ ctrl)
        values = {
            "Ctrl": [ctrl],
            "Phase2": [rng.getrandbits(cases)],
            "Mode": [mode],
            "Sign": [rng.getrandbits(cases)],
            "Work1": v.random_words(width, cases, rng),
            "Work2": v.random_words(width, cases, rng),
            "l_t": v.constant_word(k - 2, 8, mask),
            "l_q": v.constant_word((1 << 9) - 1, 9, mask),
            "l_s": v.constant_word((258 - upper) % 259, 9, mask),
            "DirtyPassenger": v.random_words(10, cases, rng),
        }
        run_pair(
            f"R step {step}", old, new, old_layout, new_layout, values, {}, cases
        )
        print(f"PASS R step={step} window={k}:{upper}", flush=True)


def check_t_sub(old_mod, new_mod, cases):
    rng = random.Random(0xA10B0002)
    mask = (1 << cases) - 1
    for step in [1, 257, 800, 1200, 1470, 1600]:
        k, upper = new_mod.safe_active_windows(256, step)["t_addsub"]
        old = old_mod.compact_prefix_addsub_gate(
            k=k, K=upper, mode="sub", sign_update=False,
            capture_borrow_sign=False, target="work2", name="T_SUB_OLD",
        )
        new = new_mod.compact_prefix_addsub_gate(
            k=k, K=upper, mode="sub", sign_update=False,
            capture_borrow_sign=False, target="work2", name="T_SUB_NEW",
        )
        width = upper - k + 1
        old_scratch = old.num_qubits - (2 + 2 * width + 8 + 1)
        new_scratch = new.num_qubits - (2 + 2 * width + 8 + 1)
        common = [
            ("Ctrl", 1),
            ("Sign", 1),
            ("Work1", width),
            ("Work2", width),
            ("l_t", 8),
            ("Borrowed", 1),
        ]
        old_layout = v.positional_layout(common + [("Scratch", old_scratch)])
        new_layout = v.positional_layout(common + [("Scratch", new_scratch)])
        encoded_values = [
            rng.randrange(0, max(1, upper - 1)) for _ in range(cases)
        ]
        values = {
            "Ctrl": [rng.getrandbits(cases)],
            "Sign": [rng.getrandbits(cases)],
            "Work1": v.random_words(width, cases, rng),
            "Work2": v.random_words(width, cases, rng),
            "l_t": words_from_values(encoded_values, 8),
            "Borrowed": [rng.getrandbits(cases)],
        }
        run_pair(
            f"T-sub step {step}", old, new, old_layout, new_layout,
            values, {}, cases,
        )
        print(
            f"PASS T-sub step={step} window={k}:{upper} "
            f"scratch={old_scratch}->{new_scratch}",
            flush=True,
        )


def check_t_add(old_mod, new_mod, cases):
    rng = random.Random(0xA10B0003)
    mask = (1 << cases) - 1
    for step in [1, 800, 1470, 1600]:
        k, upper = new_mod.safe_active_windows(256, step)["t_addsub"]
        old = old_mod.compact_prefix_add_midtail_gate(n=256, k=k, K=upper)
        new = new_mod.compact_prefix_add_midtail_gate(n=256, k=k, K=upper)
        common = [
            ("Ctrl", 1),
            ("Sign", 1),
            ("Tail", 1),
            ("Work1", 259),
            ("Work2", 259),
            ("l_t", 8),
            ("l_s", 9),
            ("l_rp", 8),
            ("Borrowed", 1),
        ]
        old_layout = v.positional_layout(common + [("Scratch", 10)])
        new_layout = v.positional_layout(common + [("Scratch", 9)])
        encoded_values = [
            rng.randrange(0, max(1, upper - 1)) for _ in range(cases)
        ]
        ls_values = [rng.randrange(0, 259) for _ in range(cases)]
        lrp_values = [rng.randrange(0, 256) for _ in range(cases)]
        values = {
            "Ctrl": [rng.getrandbits(cases)],
            "Sign": [rng.getrandbits(cases)],
            "Tail": [0],
            "Work1": v.random_words(259, cases, rng),
            "Work2": v.random_words(259, cases, rng),
            "l_t": words_from_values(encoded_values, 8),
            "l_s": words_from_values(ls_values, 9),
            "l_rp": words_from_values(lrp_values, 8),
            "Borrowed": [rng.getrandbits(cases)],
        }
        run_pair(
            f"T-add step {step}", old, new, old_layout, new_layout,
            values, {}, cases,
        )
        print(f"PASS T-add step={step} window={k}:{upper}", flush=True)


def check_terminal(old_mod, new_mod, cases):
    rng = random.Random(0xA10B0004)
    mask = (1 << cases) - 1
    for step in [1024, 1200, 1400, 1524, 1600]:
        windows = new_mod.safe_active_windows(256, step)
        k4, upper4 = windows["len_update_lt"]
        k5, upper5 = windows["len_update_lrp"]
        old = old_mod.compact_swap_work_and_len_gate(
            n=256, k4=k4, K4=upper4, k5=k5, K5=upper5
        )
        new = new_mod.compact_swap_work_and_len_gate(
            n=256, k4=k4, K4=upper4, k5=k5, K5=upper5
        )
        common = [
            ("Ctrl", 1),
            ("Work1", 259),
            ("Work2", 259),
            ("l_t", 8),
            ("l_rp", 8),
            ("Borrowed", 1),
        ]
        old_layout = v.positional_layout(
            common + [("Extension", 1), ("Scratch", 10)]
        )
        new_layout = v.positional_layout(
            common + [("Extension", 1), ("Extra", 1), ("Scratch", 9)]
        )
        ctrl = rng.getrandbits(cases)
        extension = rng.getrandbits(cases) & (mask ^ ctrl)
        extra = rng.getrandbits(cases) & (mask ^ ctrl)
        # These boundary registers are derived from 8-bit length lanes:
        # boundary_b = 258 - l_rp and boundary_a = l_t + 3.  The certified
        # physical window can include label 259, but that label has no
        # representable pre-affine 8-bit endpoint for this block.
        boundary_b = [
            rng.randrange(max(3, k4), min(258, upper4) + 1)
            for _ in range(cases)
        ]
        boundary_a = [
            rng.randrange(max(3, k5), min(258, upper5) + 1)
            for _ in range(cases)
        ]
        values = {
            "Ctrl": [ctrl],
            "Work1": v.random_words(259, cases, rng),
            "Work2": v.random_words(259, cases, rng),
            "l_t": words_from_values([value - 3 for value in boundary_a], 8),
            "l_rp": words_from_values([258 - value for value in boundary_b], 8),
            "Borrowed": [rng.getrandbits(cases)],
            "Extension": [extension],
        }
        run_pair(
            f"terminal step {step}", old, new, old_layout, new_layout,
            values, {"Extra": [extra]}, cases,
        )
        print(
            f"PASS terminal step={step} windows={k4}:{upper4},{k5}:{upper5}",
            flush=True,
        )


def check_full_step(old_mod, new_mod, cases):
    rng = random.Random(0xA10B0005)
    mask = (1 << cases) - 1
    old = old_mod.build_step_circuit(
        256, 1, T_max=1616, aux_size=11, measurement_uncompute=False
    )
    new = new_mod.build_step_circuit(
        256, 1, T_max=1616, aux_size=10, measurement_uncompute=False
    )
    if (old.num_qubits, new.num_qubits) != (577, 576):
        raise AssertionError(f"full-step widths {old.num_qubits}/{new.num_qubits}")
    values = {
        "Phase1": [0],
        "Phase2": [0],
        "Iter": [rng.getrandbits(cases)],
        "Sign": [0],
        "Work1": v.random_words(259, cases, rng),
        "Work2": v.random_words(259, cases, rng),
        "l_t": v.constant_word(0, 8, mask),
        "l_q": v.constant_word((1 << 9) - 1, 9, mask),
        "l_s": v.constant_word(258, 9, mask),
        "l_rp": v.constant_word(254, 8, mask),
        "DirtyPassenger": v.random_words(10, cases, rng),
    }
    old_state, new_state = v.initialize_common(old, new, values)
    old_initial, new_initial = old_state.copy(), new_state.copy()
    v.apply(old, old_state, mask)
    v.apply(new, new_state, mask)
    v.compare_outputs("full step 1", old, old_state, new, new_state)
    v.apply(old, old_state, mask, inverse=True)
    v.apply(new, new_state, mask, inverse=True)
    if old_state != old_initial or new_state != new_initial:
        raise AssertionError("full step 1 inverse mismatch")
    print("PASS full-step differential Qiskit width=577->576", flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--old", type=Path, required=True)
    parser.add_argument("--new", type=Path, required=True)
    parser.add_argument("--cases", type=int, default=32)
    args = parser.parse_args()
    old_mod = v.load_module("aux10_candidate_old", args.old.resolve())
    new_mod = v.load_module("aux10_candidate_new", args.new.resolve())
    stage1.check_pre_shift(old_mod, new_mod, args.cases)
    stage1.check_phase_update(old_mod, new_mod, args.cases)
    stage1.check_lc_swap(old_mod, new_mod, args.cases)
    check_r(old_mod, new_mod, args.cases)
    check_t_sub(old_mod, new_mod, args.cases)
    check_t_add(old_mod, new_mod, args.cases)
    check_terminal(old_mod, new_mod, args.cases)
    check_full_step(old_mod, new_mod, args.cases)
    print("PASS complete Aux10 differential suite", flush=True)


if __name__ == "__main__":
    main()
