#!/usr/bin/env python3
"""Differential basis-state checks for the Q818 T-add Phase2 loan."""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
import random
import sys

from qiskit import QuantumCircuit, QuantumRegister


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import verify_aux11_reductions as diff


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def build_wrapper(module, *, upper: int, loan: bool) -> QuantumCircuit:
    Phase1 = QuantumRegister(1, "Phase1")
    Phase2 = QuantumRegister(1, "Phase2")
    Sign = QuantumRegister(1, "Sign")
    Tail = QuantumRegister(1, "Tail")
    Work1 = QuantumRegister(259, "Work1")
    Work2 = QuantumRegister(259, "Work2")
    l_t = QuantumRegister(8, "l_t")
    l_q = QuantumRegister(9, "l_q")
    l_s = QuantumRegister(9, "l_s")
    l_rp = QuantumRegister(8, "l_rp")
    Dirty = QuantumRegister(10, "DirtyPassenger")
    Scratch = QuantumRegister(5, "Scratch")
    qc = QuantumCircuit(
        Phase1, Phase2, Sign, Tail, Work1, Work2, l_t, l_q, l_s,
        l_rp, Dirty, Scratch, name=f"TADD_Q818_{'LOAN' if loan else 'OLD'}",
    )
    if loan:
        module._borrow_phase2_for_tadd(
            qc, phase1=Phase1[0], phase2=Phase2[0], l_q=l_q, dirty=Dirty,
        )
    gate = module.compact_prefix_add_midtail_gate(n=256, k=1, K=upper)
    qargs = (
        [Phase1[0], Sign[0], Tail[0]]
        + list(Work1) + list(Work2) + list(l_t) + list(l_s) + list(l_rp)
        + list(Dirty) + list(Scratch)
    )
    if loan:
        qargs.append(Phase2[0])
    module._e._append_with_optional_clbits(qc, gate, qargs)
    if loan:
        module._borrow_phase2_for_tadd(
            qc, phase1=Phase1[0], phase2=Phase2[0], l_q=l_q,
            dirty=Dirty, inverse=True,
        )
    return qc


def words_from_values(values: list[int], width: int) -> list[int]:
    lanes = [0] * width
    for case, value in enumerate(values):
        for bit in range(width):
            if (value >> bit) & 1:
                lanes[bit] |= 1 << case
    return lanes


def phase_cases(cases: int, rng: random.Random) -> tuple[list[int], list[int], list[int]]:
    phase1 = 0
    phase2 = 0
    lq_values = []
    for case in range(cases):
        weight = rng.randrange(1, 257)
        phase = case % 4
        if phase == 0:
            p1, p2, lq = 0, 0, 511
        elif phase == 1:
            p1, p2, lq = 0, 1, rng.randrange(0, weight)
        elif phase == 2:
            p1, p2 = 1, 0
            lq = (rng.randrange(0, weight) - 1) & 511
        else:
            p1, p2, lq = 1, 1, 511
        phase1 |= p1 << case
        phase2 |= p2 << case
        lq_values.append(lq)
    return [phase1], [phase2], words_from_values(lq_values, 9)


def check_pair(original, candidate, *, upper: int, cases: int, seed: int) -> None:
    rng = random.Random(seed)
    mask = (1 << cases) - 1
    old = build_wrapper(original, upper=upper, loan=False)
    new = build_wrapper(candidate, upper=upper, loan=True)
    p1, p2, lq = phase_cases(cases, rng)
    labels = [rng.randrange(0, max(1, upper - 1)) for _ in range(cases)]
    values = {
        "Phase1": p1,
        "Phase2": p2,
        "Sign": [rng.getrandbits(cases)],
        "Tail": [0],
        "Work1": diff.random_words(259, cases, rng),
        "Work2": diff.random_words(259, cases, rng),
        "l_t": words_from_values(labels, 8),
        "l_q": lq,
        "l_s": words_from_values([rng.randrange(259) for _ in range(cases)], 9),
        "l_rp": diff.random_words(8, cases, rng),
        "DirtyPassenger": diff.random_words(10, cases, rng),
        "Scratch": [0] * 5,
    }
    old_state, new_state = diff.initialize_common(old, new, values)
    old_initial, new_initial = old_state.copy(), new_state.copy()
    diff.apply(old, old_state, mask)
    diff.apply(new, new_state, mask)
    for name in values:
        if diff.get_register(old, old_state, name) != diff.get_register(new, new_state, name):
            raise AssertionError(f"upper={upper}: {name} differs")
    if any(diff.get_register(new, new_state, "Scratch")):
        raise AssertionError(f"upper={upper}: scratch not clean")
    diff.apply(old, old_state, mask, inverse=True)
    diff.apply(new, new_state, mask, inverse=True)
    if old_state != old_initial or new_state != new_initial:
        raise AssertionError(f"upper={upper}: inverse mismatch")
    print(
        f"PASS q818_tadd_phase2_loan upper={upper} cases={cases} "
        "forward=equivalent phase2=restored inverse=exact",
        flush=True,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--old-generator", type=Path, required=True)
    parser.add_argument("--cases", type=int, default=128)
    args = parser.parse_args()
    old = load_module("q818_tadd_old", args.old_generator.resolve())
    candidate = load_module(
        "q818_tadd_candidate", HERE / "eea_circuit_s835_exactwidth_dirty12.py"
    )
    for index, upper in enumerate((2, 17, 128, 256, 257)):
        check_pair(old, candidate, upper=upper, cases=args.cases, seed=0x8187AD00 + index)


if __name__ == "__main__":
    main()
