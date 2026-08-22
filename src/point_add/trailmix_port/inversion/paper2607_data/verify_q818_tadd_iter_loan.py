#!/usr/bin/env python3
"""Basis-state verification of the concrete Q818 Phase2+Iter loan circuit."""

from __future__ import annotations

import random

from qiskit import QuantumCircuit, QuantumRegister

import check_q818_tadd_iter_loan as model
import eea_circuit_s835_exactwidth_dirty12 as candidate
import verify_aux11_reductions as diff


def words(values: list[int], width: int) -> list[int]:
    lanes = [0] * width
    for case, value in enumerate(values):
        for bit in range(width):
            lanes[bit] |= ((value >> bit) & 1) << case
    return lanes


def build(*, roundtrip: bool) -> QuantumCircuit:
    phase1 = QuantumRegister(1, "Phase1")
    phase2 = QuantumRegister(1, "Phase2")
    iteration = QuantumRegister(1, "Iter")
    l_q = QuantumRegister(9, "l_q")
    dirty = QuantumRegister(10, "DirtyPassenger")
    qc = QuantumCircuit(phase1, phase2, iteration, l_q, dirty)
    candidate._borrow_phase2_for_tadd(
        qc, phase1=phase1[0], phase2=phase2[0], l_q=l_q, dirty=dirty,
    )
    candidate._borrow_iter_for_tadd(
        qc, phase1=phase1[0], iteration=iteration[0], l_q=l_q, dirty=dirty,
    )
    if roundtrip:
        candidate._borrow_iter_for_tadd(
            qc, phase1=phase1[0], iteration=iteration[0], l_q=l_q,
            dirty=dirty, inverse=True,
        )
        candidate._borrow_phase2_for_tadd(
            qc, phase1=phase1[0], phase2=phase2[0], l_q=l_q,
            dirty=dirty, inverse=True,
        )
    return qc


def main() -> None:
    logical = [(0, 0, 511)]
    logical += [(0, 1, l_q) for l_q in range(255)]
    logical += [(1, 0, l_q) for l_q in list(range(254)) + [511]]
    logical += [(1, 1, 511)]
    cases = [(p1, p2, iteration, l_q) for p1, p2, l_q in logical for iteration in (0, 1)]
    mask = (1 << len(cases)) - 1
    rng = random.Random(0x81817E12)
    dirty = diff.random_words(10, len(cases), rng)
    values = {
        "Phase1": words([row[0] for row in cases], 1),
        "Phase2": words([row[1] for row in cases], 1),
        "Iter": words([row[2] for row in cases], 1),
        "l_q": words([row[3] for row in cases], 9),
        "DirtyPassenger": dirty,
    }

    forward = build(roundtrip=False)
    state = [0] * forward.num_qubits
    for name, lanes in values.items():
        diff.set_register(forward, state, name, lanes)
    diff.apply(forward, state, mask)
    if diff.get_register(forward, state, "Phase2") != [0]:
        raise AssertionError("concrete Phase2 not clean")
    if diff.get_register(forward, state, "Iter") != [0]:
        raise AssertionError("concrete Iter not clean")
    if diff.get_register(forward, state, "DirtyPassenger") != dirty:
        raise AssertionError("concrete dirty lenders not restored")
    expected_lq = [model.forward(*row)[2] for row in cases]
    if diff.get_register(forward, state, "l_q") != words(expected_lq, 9):
        raise AssertionError("concrete l_q differs from model")

    roundtrip = build(roundtrip=True)
    state = [0] * roundtrip.num_qubits
    for name, lanes in values.items():
        diff.set_register(roundtrip, state, name, lanes)
    initial = state.copy()
    diff.apply(roundtrip, state, mask)
    if state != initial:
        raise AssertionError("concrete loan roundtrip mismatch")
    print(
        f"PASS concrete-q818-tadd-iter-loan cases={len(cases)} "
        "phase2=clean iter=clean dirty=restored model=exact roundtrip=exact"
    )


if __name__ == "__main__":
    main()
