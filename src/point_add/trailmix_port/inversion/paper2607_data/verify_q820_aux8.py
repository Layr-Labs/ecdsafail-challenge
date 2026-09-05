#!/usr/bin/env python3
"""Differential checks for the Q820 Aux8 dirty-lender prototype."""

from __future__ import annotations

import argparse
from pathlib import Path
import random

import verify_aux11_reductions as verify


def words_from_values(values, width):
    lanes = [0] * width
    for case, value in enumerate(values):
        if not 0 <= value < (1 << width):
            raise ValueError((value, width))
        for bit in range(width):
            if (value >> bit) & 1:
                lanes[bit] |= 1 << case
    return lanes


def compare_pair(
    *,
    label,
    old_gate,
    new_gate,
    old_fields,
    new_fields,
    common_values,
    old_clean,
    new_clean,
    new_dirty=None,
    cases=64,
):
    mask = (1 << cases) - 1
    old_layout = verify.positional_layout(old_fields)
    new_layout = verify.positional_layout(new_fields)
    old_state, new_state = verify.initialize_positional(
        old_gate, new_gate, old_layout, new_layout, common_values
    )
    rng = random.Random(0x820000 + sum(ord(c) for c in label))
    dirty_initial = {}
    for name in new_dirty or ():
        values = verify.random_words(len(new_layout[name]), cases, rng)
        verify.set_positional(new_state, new_layout, name, values)
        dirty_initial[name] = values
    old_initial = old_state.copy()
    new_initial = new_state.copy()

    verify.apply(old_gate, old_state, mask)
    verify.apply(new_gate, new_state, mask)
    for name in common_values:
        if verify.get_positional(old_state, old_layout, name) != verify.get_positional(
            new_state, new_layout, name
        ):
            raise AssertionError(f"{label}: differing {name}")
    for name in old_clean:
        if any(verify.get_positional(old_state, old_layout, name)):
            raise AssertionError(f"{label}: old {name} not clean")
    for name in new_clean:
        if any(verify.get_positional(new_state, new_layout, name)):
            raise AssertionError(f"{label}: new {name} not clean")
    for name, values in dirty_initial.items():
        if verify.get_positional(new_state, new_layout, name) != values:
            raise AssertionError(f"{label}: new {name} not restored")

    verify.apply(old_gate, old_state, mask, inverse=True)
    verify.apply(new_gate, new_state, mask, inverse=True)
    if old_state != old_initial:
        raise AssertionError(f"{label}: old inverse mismatch")
    if new_state != new_initial:
        raise AssertionError(f"{label}: new inverse mismatch")
    print(
        f"PASS {label} old_qubits={old_gate.num_qubits} "
        f"new_qubits={new_gate.num_qubits}",
        flush=True,
    )


def mod259_gate(module, *, dirty):
    ctrl = module.QuantumRegister(1, "Ctrl")
    reg = module.QuantumRegister(9, "Reg")
    if dirty:
        lenders = module.QuantumRegister(10, "Dirty")
        circuit = module.QuantumCircuit(ctrl, reg, lenders)
        module.inc_mod259_1ctrl_dirty(circuit, ctrl[0], reg, lenders)
    else:
        scratch = module.QuantumRegister(8, "Scratch")
        circuit = module.QuantumCircuit(ctrl, reg, scratch)
        module.inc_mod259_1ctrl(circuit, ctrl[0], reg, scratch)
    return module._e._finalize_block(circuit)


def check_mod259(old, new):
    cases = 1024
    mask = (1 << cases) - 1
    old_gate = mod259_gate(old, dirty=False)
    new_gate = mod259_gate(new, dirty=True)
    old_layout = verify.positional_layout(
        [("Ctrl", 1), ("Reg", 9), ("Scratch", 8)]
    )
    new_layout = verify.positional_layout(
        [("Ctrl", 1), ("Reg", 9), ("Dirty", 10)]
    )
    controls = [0] * 512 + [1] * 512
    values = list(range(512)) + list(range(512))
    old_state = [0] * old_gate.num_qubits
    new_state = [0] * new_gate.num_qubits
    verify.set_positional(old_state, old_layout, "Ctrl", words_from_values(controls, 1))
    verify.set_positional(new_state, new_layout, "Ctrl", words_from_values(controls, 1))
    reg_words = words_from_values(values, 9)
    verify.set_positional(old_state, old_layout, "Reg", reg_words)
    verify.set_positional(new_state, new_layout, "Reg", reg_words)
    rng = random.Random(0x820259)
    dirty = verify.random_words(10, cases, rng)
    verify.set_positional(new_state, new_layout, "Dirty", dirty)
    old_initial = old_state.copy()
    new_initial = new_state.copy()
    verify.apply(old_gate, old_state, mask)
    verify.apply(new_gate, new_state, mask)
    if verify.get_positional(old_state, old_layout, "Reg") != verify.get_positional(
        new_state, new_layout, "Reg"
    ):
        raise AssertionError("mod259 dirty permutation mismatch")
    if any(verify.get_positional(old_state, old_layout, "Scratch")):
        raise AssertionError("mod259 old scratch not clean")
    if verify.get_positional(new_state, new_layout, "Dirty") != dirty:
        raise AssertionError("mod259 dirty lenders not restored")
    verify.apply(old_gate, old_state, mask, inverse=True)
    verify.apply(new_gate, new_state, mask, inverse=True)
    if old_state != old_initial or new_state != new_initial:
        raise AssertionError("mod259 inverse mismatch")
    print("PASS mod259 exhaustive words=512 controls=2 dirty_patterns=1024", flush=True)


def random_common(fields, cases, rng):
    return {
        name: verify.random_words(width, cases, rng)
        for name, width in fields
    }


def check_shift_and_phase(old, new, cases):
    rng = random.Random(0x8205A17)
    shift_common = [
        ("Phase1", 1),
        ("Phase2", 1),
        ("Work2", 259),
        ("l_s", 9),
    ]
    values = random_common(shift_common, cases, rng)
    for label, old_gate, new_gate in (
        ("pre-shift", old.compact_pre_shift_gate(work_size=259),
         new.compact_pre_shift_gate(work_size=259)),
        ("post-shift", old.compact_post_shift_gate(work_size=259),
         new.compact_post_shift_gate(work_size=259)),
    ):
        compare_pair(
            label=label,
            old_gate=old_gate,
            new_gate=new_gate,
            old_fields=shift_common + [("OldScratch", 9)],
            new_fields=shift_common + [("NewDirty", 10), ("NewScratch", 1)],
            common_values=values,
            old_clean=["OldScratch"],
            new_clean=["NewScratch"],
            new_dirty=["NewDirty"],
            cases=cases,
        )

    phase_common = [
        ("Phase1", 1),
        ("Phase2", 1),
        ("Sign", 1),
        ("l_q", 9),
        ("l_rp", 8),
        ("l_s", 9),
        ("Dirty0", 1),
    ]
    values = random_common(phase_common, cases, rng)
    compare_pair(
        label="phase-update",
        old_gate=old.compact_phase_update_gate(),
        new_gate=new.compact_phase_update_gate(),
        old_fields=phase_common + [("OldScratch", 9)],
        new_fields=phase_common + [("DirtyExtra", 9), ("NewScratch", 2)],
        common_values=values,
        old_clean=["OldScratch"],
        new_clean=["NewScratch"],
        new_dirty=["DirtyExtra"],
        cases=cases,
    )


def check_arithmetic_blocks(old, new, cases):
    rng = random.Random(0x820A817)
    k, upper = 1, 17
    width = upper - k + 1

    r_common = [
        ("Ctrl", 1), ("Phase2", 1), ("Mode", 1), ("Sign", 1),
        ("Work1", width), ("Work2", width), ("l_t", 8), ("l_q", 9),
        ("l_s", 9), ("Dirty", 10),
    ]
    compare_pair(
        label="R-window-1-17",
        old_gate=old.compact_r_subrestore_fused_gate(n=256, k=k, K=upper),
        new_gate=new.compact_r_subrestore_fused_gate(n=256, k=k, K=upper),
        old_fields=r_common + [("OldScratch", 8)],
        new_fields=r_common + [("NewScratch", 2)],
        common_values=random_common(r_common, cases, rng),
        old_clean=["OldScratch"],
        new_clean=["NewScratch"],
        cases=cases,
    )

    lc_base = [
        ("Ctrl", 1), ("Direction", 1), ("Sign", 1), ("Work1", width + 1),
        ("l_t", 8), ("l_q", 9), ("Dirty0", 1),
    ]
    compare_pair(
        label="LC-window-1-17",
        old_gate=old.compact_lc_swap_gate(k=k, K=upper),
        new_gate=new.compact_lc_swap_gate(k=k, K=upper),
        old_fields=lc_base + [("OldScratch", 9)],
        new_fields=lc_base + [("DirtyExtra", 3), ("NewScratch", 8)],
        common_values=random_common(lc_base, cases, rng),
        old_clean=["OldScratch"],
        new_clean=["NewScratch"],
        new_dirty=["DirtyExtra"],
        cases=cases,
    )

    tsub_base = [
        ("Ctrl", 1), ("Sign", 1), ("Work1", width), ("Work2", width),
        ("l_t", 8), ("Borrowed0", 1),
    ]
    old_tsub = old.compact_prefix_addsub_gate(
        k=k, K=upper, mode="sub", sign_update=False,
        capture_borrow_sign=False, target="work2", name="OLD_TSUB",
    )
    new_tsub = new.compact_prefix_addsub_gate(
        k=k, K=upper, mode="sub", sign_update=False,
        capture_borrow_sign=False, target="work2", name="NEW_TSUB",
    )
    old_scratch = old_tsub.num_qubits - sum(width for _, width in tsub_base)
    new_scratch = (
        new_tsub.num_qubits - sum(width for _, width in tsub_base) - 1
    )
    compare_pair(
        label="T-sub-window-1-17",
        old_gate=old_tsub,
        new_gate=new_tsub,
        old_fields=tsub_base + [("OldScratch", old_scratch)],
        new_fields=tsub_base + [("BorrowedExtra", 1), ("NewScratch", new_scratch)],
        common_values=random_common(tsub_base, cases, rng),
        old_clean=["OldScratch"],
        new_clean=["NewScratch"],
        new_dirty=["BorrowedExtra"],
        cases=cases,
    )

    tadd_common = [
        ("Ctrl", 1), ("Sign", 1), ("Tail", 1), ("Work1", 259),
        ("Work2", 259), ("l_t", 8), ("l_s", 9), ("l_rp", 8), ("Dirty", 10),
    ]
    tadd_values = random_common(tadd_common, cases, rng)
    tadd_values["l_s"] = words_from_values(
        [rng.randrange(259) for _ in range(cases)], 9
    )
    compare_pair(
        label="T-add-window-1-17",
        old_gate=old.compact_prefix_add_midtail_gate(n=256, k=k, K=upper),
        new_gate=new.compact_prefix_add_midtail_gate(n=256, k=k, K=upper),
        old_fields=tadd_common + [("OldScratch", 8)],
        new_fields=tadd_common + [("NewScratch", 7)],
        common_values=tadd_values,
        old_clean=["OldScratch"],
        new_clean=["NewScratch"],
        cases=cases,
    )


def check_terminal(old, new, cases):
    rng = random.Random(0x8207E21)
    k4, K4, k5, K5 = 1, 17, 1, 17
    prefix = [
        ("Ctrl", 1), ("Work1", 259), ("Work2", 259), ("l_t", 8),
        ("l_rp", 8),
    ]
    common_values = random_common(prefix + [("Dirty0", 1)], cases, rng)
    common_values["Ctrl"] = [(1 << cases) - 1]
    common_values["Extension"] = [0]
    common_values["l_t"] = words_from_values(
        [case % 15 for case in range(cases)], 8
    )
    common_values["l_rp"] = words_from_values(
        [255 - (case % 15) for case in range(cases)], 8
    )
    compare_pair(
        label="terminal-length-window-1-17",
        old_gate=old.compact_swap_work_and_len_gate(
            n=256, k4=k4, K4=K4, k5=k5, K5=K5
        ),
        new_gate=new.compact_swap_work_and_len_gate(
            n=256, k4=k4, K4=K4, k5=k5, K5=K5
        ),
        old_fields=prefix
        + [("Dirty0", 1), ("Extension", 1), ("OldScratch", 8)],
        new_fields=prefix
        + [
            ("Dirty0", 1),
            ("DirtyExtra", 7),
            ("Extension", 1),
            ("NewScratch", 7),
        ],
        common_values=common_values,
        old_clean=["OldScratch"],
        new_clean=["NewScratch"],
        new_dirty=["DirtyExtra"],
        cases=cases,
    )


def check_construction(new):
    if new.CLEAN_AUX_SIZE != 8:
        raise AssertionError(f"candidate Aux={new.CLEAN_AUX_SIZE}, expected 8")
    for step in (1, 4, 800, 1616):
        circuit = new.build_step_circuit(
            n=256, T=step, aux_size=8, measurement_uncompute=True
        )
        if circuit.num_qubits != 574:
            raise AssertionError(
                f"step {step}: local width {circuit.num_qubits}, expected 574"
            )
        print(
            f"PASS construct step={step} local_qubits={circuit.num_qubits} "
            f"top_ops={sum(circuit.count_ops().values())}",
            flush=True,
        )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--old", type=Path, required=True)
    parser.add_argument("--new", type=Path, required=True)
    parser.add_argument("--cases", type=int, default=64)
    args = parser.parse_args()
    old = verify.load_module("q821_aux9_reference", args.old.resolve())
    new = verify.load_module("q820_aux8_candidate", args.new.resolve())
    check_mod259(old, new)
    check_shift_and_phase(old, new, args.cases)
    check_arithmetic_blocks(old, new, args.cases)
    check_terminal(old, new, args.cases)
    check_construction(new)
    print("PASS Q820 Aux8 differential suite", flush=True)


if __name__ == "__main__":
    main()
