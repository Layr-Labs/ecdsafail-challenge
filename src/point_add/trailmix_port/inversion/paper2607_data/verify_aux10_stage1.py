#!/usr/bin/env python3
"""Differential checks for the first Aux10 kernel reductions."""

from __future__ import annotations

import argparse
from pathlib import Path
import random

from verify_aux11_reductions import (
    apply,
    constant_word,
    get_positional,
    initialize_positional,
    load_module,
    positional_layout,
    random_words,
    set_positional,
)


def assert_clean(label, state, layout, name):
    if any(get_positional(state, layout, name)):
        raise AssertionError(f"{label}: {name} not clean")


def check_pre_shift(old_mod, new_mod, cases):
    rng = random.Random(0xA10A0001)
    mask = (1 << cases) - 1
    old = old_mod.compact_pre_shift_gate(work_size=259)
    new = new_mod.compact_pre_shift_gate(work_size=259)
    common = [
        ("Phase1", 1),
        ("Phase2", 1),
        ("Work2", 259),
        ("l_s", 9),
    ]
    old_layout = positional_layout(common + [("Scratch", 10)])
    new_layout = positional_layout(common + [("Scratch", 9)])
    values = {
        "Phase1": [rng.getrandbits(cases)],
        "Phase2": [rng.getrandbits(cases)],
        "Work2": random_words(259, cases, rng),
        "l_s": constant_word(258, 9, mask),
    }
    old_state, new_state = initialize_positional(
        old, new, old_layout, new_layout, values
    )
    old_initial, new_initial = old_state.copy(), new_state.copy()
    apply(old, old_state, mask)
    apply(new, new_state, mask)
    for name in values:
        if get_positional(old_state, old_layout, name) != get_positional(
            new_state, new_layout, name
        ):
            raise AssertionError(f"pre-shift: {name} differs")
    assert_clean("pre-shift old", old_state, old_layout, "Scratch")
    assert_clean("pre-shift new", new_state, new_layout, "Scratch")
    apply(old, old_state, mask, inverse=True)
    apply(new, new_state, mask, inverse=True)
    if old_state != old_initial or new_state != new_initial:
        raise AssertionError("pre-shift inverse mismatch")
    print(f"PASS pre-shift cases={cases}", flush=True)


def check_phase_update(old_mod, new_mod, cases):
    rng = random.Random(0xA10A0002)
    mask = (1 << cases) - 1
    old = old_mod.compact_phase_update_gate()
    new = new_mod.compact_phase_update_gate()
    common = [
        ("Phase1", 1),
        ("Phase2", 1),
        ("Sign", 1),
        ("l_q", 9),
        ("l_rp", 8),
        ("l_s", 9),
    ]
    old_layout = positional_layout(common + [("Scratch", 10)])
    new_layout = positional_layout(
        common + [("DirtyPassenger", 1), ("Scratch", 9)]
    )
    dirty = [rng.getrandbits(cases)]
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
    set_positional(new_state, new_layout, "DirtyPassenger", dirty)
    old_initial, new_initial = old_state.copy(), new_state.copy()
    apply(old, old_state, mask)
    apply(new, new_state, mask)
    for name in values:
        if get_positional(old_state, old_layout, name) != get_positional(
            new_state, new_layout, name
        ):
            raise AssertionError(f"phase-update: {name} differs")
    if get_positional(new_state, new_layout, "DirtyPassenger") != dirty:
        raise AssertionError("phase-update: dirty lender not restored")
    assert_clean("phase-update old", old_state, old_layout, "Scratch")
    assert_clean("phase-update new", new_state, new_layout, "Scratch")
    apply(old, old_state, mask, inverse=True)
    apply(new, new_state, mask, inverse=True)
    if old_state != old_initial or new_state != new_initial:
        raise AssertionError("phase-update inverse mismatch")
    print(f"PASS phase-update cases={cases}", flush=True)


def check_lc_swap(old_mod, new_mod, cases):
    rng = random.Random(0xA10A0003)
    mask = (1 << cases) - 1
    for step in [1, 257, 800, 1200, 1470, 1600]:
        k, upper = new_mod.safe_active_windows(256, step)["swap"]
        old = old_mod.compact_lc_swap_gate(k=k, K=upper)
        new = new_mod.compact_lc_swap_gate(k=k, K=upper)
        width = upper - k + 2
        old_scratch = old.num_qubits - (3 + width + 8 + 9)
        new_scratch = new.num_qubits - (3 + width + 8 + 9 + 1)
        common = [
            ("Ctrl", 1),
            ("Direction", 1),
            ("Sign", 1),
            ("Work1", width),
            ("l_t", 8),
            ("l_q", 9),
        ]
        old_layout = positional_layout(common + [("Scratch", old_scratch)])
        new_layout = positional_layout(
            common + [("DirtyPassenger", 1), ("Scratch", new_scratch)]
        )
        dirty = [rng.getrandbits(cases)]
        values = {
            "Ctrl": [rng.getrandbits(cases)],
            "Direction": [rng.getrandbits(cases)],
            "Sign": [rng.getrandbits(cases)],
            "Work1": random_words(width, cases, rng),
            "l_t": random_words(8, cases, rng),
            "l_q": random_words(9, cases, rng),
        }
        old_state, new_state = initialize_positional(
            old, new, old_layout, new_layout, values
        )
        set_positional(new_state, new_layout, "DirtyPassenger", dirty)
        old_initial, new_initial = old_state.copy(), new_state.copy()
        apply(old, old_state, mask)
        apply(new, new_state, mask)
        for name in values:
            if get_positional(old_state, old_layout, name) != get_positional(
                new_state, new_layout, name
            ):
                raise AssertionError(f"LC step {step}: {name} differs")
        if get_positional(new_state, new_layout, "DirtyPassenger") != dirty:
            raise AssertionError(f"LC step {step}: dirty lender not restored")
        assert_clean(f"LC step {step} old", old_state, old_layout, "Scratch")
        assert_clean(f"LC step {step} new", new_state, new_layout, "Scratch")
        apply(old, old_state, mask, inverse=True)
        apply(new, new_state, mask, inverse=True)
        if old_state != old_initial or new_state != new_initial:
            raise AssertionError(f"LC step {step}: inverse mismatch")
        print(
            f"PASS LC step={step} window={k}:{upper} "
            f"scratch={old_scratch}->{new_scratch}",
            flush=True,
        )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--old", type=Path, required=True)
    parser.add_argument("--new", type=Path, required=True)
    parser.add_argument("--cases", type=int, default=64)
    args = parser.parse_args()
    old_mod = load_module("aux10_stage1_old", args.old.resolve())
    new_mod = load_module("aux10_stage1_new", args.new.resolve())
    check_pre_shift(old_mod, new_mod, args.cases)
    check_phase_update(old_mod, new_mod, args.cases)
    check_lc_swap(old_mod, new_mod, args.cases)
    print("PASS Aux10 stage-1 differential suite", flush=True)


if __name__ == "__main__":
    main()
