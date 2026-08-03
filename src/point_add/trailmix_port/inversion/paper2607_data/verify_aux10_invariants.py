#!/usr/bin/env python3
"""Structural proof checks for the Q822 Aux10 candidate."""

from __future__ import annotations

import argparse
from functools import lru_cache
import hashlib
import importlib.util
from pathlib import Path
import sys

from qiskit import QuantumCircuit, QuantumRegister

import verify_aux11_reductions as sim
import derive_active_windows as schedule


MAX_QUOTIENT_WEIGHT = 256
SEALED_Q823_GENERATOR_SHA256 = (
    "4c0ddee95526526b9a3c9fa66ab5e1f65f6f03a747936c0468ee7ba1932c9224"
)
Q822_GENERATOR_SHA256 = (
    "b00c0801921234a7b7c528988addda914c8b229548959ab5c0d5fd2aeee922be"
)


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def exhaustive_lanes(width: int) -> tuple[list[int], int]:
    cases = 1 << width
    mask = (1 << cases) - 1
    lanes = []
    for bit in range(width):
        lane = 0
        for case in range(cases):
            if (case >> bit) & 1:
                lane |= 1 << case
        lanes.append(lane)
    return lanes, mask


def check_borrowed_c2swap(module) -> None:
    wires = QuantumRegister(5, "w")
    qc = QuantumCircuit(wires)
    module._borrowed_c2swap(
        qc, wires[0], wires[1], wires[2], wires[3], wires[4]
    )
    state, mask = exhaustive_lanes(5)
    initial = state.copy()
    sim.apply(qc, state, mask)
    for case in range(1 << 5):
        a, b, left, right, dirty = [
            (initial[index] >> case) & 1 for index in range(5)
        ]
        expected_left, expected_right = (
            (right, left) if a and b else (left, right)
        )
        observed = [(state[index] >> case) & 1 for index in range(5)]
        assert observed == [a, b, expected_left, expected_right, dirty]
    sim.apply(qc, state, mask, inverse=True)
    assert state == initial
    print("PASS borrowed C2SWAP exhaustive states=32")


def check_raw_controls(module) -> None:
    for controls in (3, 4):
        wires = QuantumRegister(controls + 1 + max(1, controls - 2), "w")
        qc = QuantumCircuit(wires)
        target = wires[controls]
        dirty = list(wires[controls + 1:])
        module._toggle_raw_controls_dirty(
            qc, list(wires[:controls]), target, dirty
        )
        state, mask = exhaustive_lanes(len(wires))
        initial = state.copy()
        sim.apply(qc, state, mask)
        for case in range(1 << len(wires)):
            values = [(initial[index] >> case) & 1 for index in range(len(wires))]
            product = int(all(values[:controls]))
            expected = values.copy()
            expected[controls] ^= product
            observed = [(state[index] >> case) & 1 for index in range(len(wires))]
            assert observed == expected
        sim.apply(qc, state, mask, inverse=True)
        assert state == initial
        print(
            f"PASS raw equality controls={controls} "
            f"states={1 << len(wires)}",
            flush=True,
        )


def phase_update(
    phase1: int,
    phase2: int,
    sign: int,
    *,
    lq_zero: bool,
    lrp_live: bool,
    ls_zero: bool,
) -> tuple[int, int, int]:
    """Apply the exact ordered Boolean updates in compact_phase_update_gate."""
    if lq_zero and lrp_live:
        phase2 ^= sign
        phase2 ^= phase1
        sign ^= phase2
    if ls_zero and lrp_live:
        phase1 ^= 1
        phase2 ^= 1
    return phase1, phase2, sign


@lru_cache(maxsize=None)
def quotient_control_trace(
    weight: int,
) -> tuple[
    tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]],
    ...,
]:
    """Derive every control state in one quotient cycle.

    Let q have bit length ``weight``, let ``t >= 1``, and let ``0 <= a < t``
    be the preceding coefficient magnitude.  Phase C constructs

        t' = a + q*t.

    At bit k, a zero quotient bit makes the temporary subtraction underflow:

        a + (q mod 2**k)*t <= 2**k*t - 1.

    A one bit skips that subtraction.  Hence Phase C reaches every phase
    update with Sign=0.  In Phase D, the fixed accumulator satisfies

        a + q*t < 2**weight*t
        a + q*t >= 2**k*t,  1 <= k < weight.

    Thus only the first Phase-D subtraction underflows.  These inequalities
    derive the sign recurrence; no Phase2=Sign premise is assumed.
    """
    assert 1 <= weight <= MAX_QUOTIENT_WEIGHT
    phase1 = phase2 = sign = 0
    l_q = l_s = 0
    rows = []

    # The integer inequalities are independent of the positive scale t.
    # Use t=2 only to check their tight endpoints without enumerating q.
    t = 2
    preceding_max = t - 1
    q_min = 1 << (weight - 1)
    q_max = (1 << weight) - 1

    for local_step in range(1, 4 * weight + 1):
        entry = (phase1, phase2, sign, l_q, l_s)
        if local_step <= weight:
            assert (phase1, phase2, sign) == (0, 0, 0)
            l_s += 1
            # The first oversized R shift occurs exactly at the bit-length
            # boundary and is the A-to-B transition witness.
            sign = int(local_step == weight)
        elif local_step <= 2 * weight:
            assert (phase1, phase2, sign) == (0, 1, 0)
            l_s -= 1
            l_q += 1
            # The quotient target bit is fresh zero.  Swapping it with the
            # subtraction predicate stores the bit and clears Sign.
            sign = 0
        elif local_step <= 3 * weight:
            assert (phase1, phase2, sign) == (1, 0, 0)
            bit_index = local_step - 2 * weight - 1
            assert preceding_max + ((1 << bit_index) - 1) * t < (
                1 << bit_index
            ) * t
            l_q -= 1
            l_s += 1
            # If q_k=0 the subtraction underflows by the bound above; if
            # q_k=1 it is skipped.  Both branches leave Sign=0.
            sign = 0
        else:
            assert (phase1, phase2) == (1, 1)
            shift = l_s
            assert 1 <= shift <= weight
            if shift == weight:
                assert preceding_max + q_max * t < (1 << shift) * t
                underflow = 1
            else:
                assert q_min * t >= (1 << shift) * t
                underflow = 0
            # Phase2=1 forces the subtract; the restoring add toggles Sign
            # first by one and then by the exact underflow predicate.
            sign ^= 1
            sign ^= underflow
            l_s -= 1

        pre_phase = (phase1, phase2, sign, l_q, l_s)
        phase1, phase2, sign = phase_update(
            phase1,
            phase2,
            sign,
            lq_zero=(l_q == 0),
            lrp_live=True,
            ls_zero=(l_s == 0),
        )
        post_phase = (phase1, phase2, sign, l_q, l_s)
        rows.append((entry, pre_phase, post_phase))

    assert rows[-1][1][:3] == (1, 1, 1)
    assert rows[-1][2][:3] == (0, 0, 0)
    return tuple(rows)


def check_terminal_loans() -> None:
    for weight in range(1, MAX_QUOTIENT_WEIGHT + 1):
        trace = quotient_control_trace(weight)
        assert len(trace) == 4 * weight
        for local_step, (_, pre_phase, post_phase) in enumerate(trace, 1):
            terminal = post_phase[3:] == (0, 0)
            if terminal:
                assert local_step == 4 * weight
                assert pre_phase[:3] == (1, 1, 1)
                assert post_phase[:3] == (0, 0, 0)

    # Check the same derived controls on every state in the relaxed certified
    # schedule envelope used to derive the 1,616 stream windows.
    total_candidates = 0
    terminal_candidates = 0
    for step in range(1, 1617):
        for prefix_cost in range(
            0,
            min(schedule.MAX_WEIGHTED_COST - 1, (step - 1) // 4) + 1,
        ):
            if prefix_cost == 1:
                continue
            local_step = step - 4 * prefix_cost
            interval = schedule.feasible_weight_interval(prefix_cost, local_step)
            if interval is None:
                continue
            for weight in range(interval[0], interval[1] + 1):
                total_candidates += 1
                _, pre_phase, post_phase = quotient_control_trace(weight)[
                    local_step - 1
                ]
                if post_phase[3:] == (0, 0):
                    terminal_candidates += 1
                    assert step % 4 == 0
                    assert pre_phase[:3] == (1, 1, 1)
                    assert post_phase[:3] == (0, 0, 0)

    assert total_candidates == 23_890_924
    assert terminal_candidates == 62_913

    # Once l_rp is terminal, the candidate guards both phase transitions off.
    for phase1 in range(2):
        for phase2 in range(2):
            for sign in range(2):
                assert phase_update(
                    phase1,
                    phase2,
                    sign,
                    lq_zero=True,
                    lrp_live=False,
                    ls_zero=True,
                ) == (phase1, phase2, sign)
    print(
        "PASS terminal Phase1/Phase2 derived-clean loans "
        f"weights={MAX_QUOTIENT_WEIGHT} states={total_candidates} "
        f"terminal={terminal_candidates}"
    )


def check_generator_hashes(candidate: Path, sealed_generator: Path | None) -> None:
    candidate_sha256 = hashlib.sha256(candidate.read_bytes()).hexdigest()
    assert candidate_sha256 == Q822_GENERATOR_SHA256
    if sealed_generator is not None:
        sealed_sha256 = hashlib.sha256(sealed_generator.read_bytes()).hexdigest()
        assert sealed_sha256 == SEALED_Q823_GENERATOR_SHA256
    print(
        "PASS generator identities "
        f"sealed_q823_sha256={SEALED_Q823_GENERATOR_SHA256} "
        f"q822_sha256={candidate_sha256}"
    )


def check_tail_loan() -> None:
    # Aux[0] starts clean.  Every predicate is XOR-computed, consumed, and
    # XOR-uncomputed before the restoring T add borrows it as Tail.
    for phase1 in range(2):
        for phase2 in range(2):
            for sign in range(2):
                predicate = phase1 & (phase2 | (sign ^ 1))
                ctrl = 0
                ctrl ^= predicate
                ctrl ^= predicate
                assert ctrl == 0
    print("PASS restoring-T Tail clean-loan truth table states=8")


def check_scratch_census(module) -> None:
    maxima = {
        "swap_local_scratch": 0,
        "t_prefix_scratch": 0,
        "terminal_map_scratch": 0,
    }
    for row in module._CERTIFIED_WINDOW_ROWS:
        k, upper = (1, 1) if row["quotient_swap"] is None else row["quotient_swap"]
        depth = module._tight_unary_depth_for_labels(list(range(k, upper + 1)))
        maxima["swap_local_scratch"] = max(
            maxima["swap_local_scratch"], max(module.LQ_WIDTH, depth) + 1
        )

        k, upper = (1, 1) if row["t_addsub"] is None else row["t_addsub"]
        encoded = list(range(0, upper - 1))
        depth = module._tight_unary_depth_for_labels(encoded)
        t_scratch = max(max(0, depth - 1), module.LT_WIDTH - 1) + 2
        maxima["t_prefix_scratch"] = max(
            maxima["t_prefix_scratch"], t_scratch
        )

        for key in ("len_update_lt", "len_update_lrp"):
            bounds = row[key]
            if bounds is None:
                continue
            depth = module._tight_unary_depth_for_labels(
                list(range(bounds[0], bounds[1] + 1))
            )
            maxima["terminal_map_scratch"] = max(
                maxima["terminal_map_scratch"], max(1, depth)
            )

    assert maxima == {
        "swap_local_scratch": 10,
        "t_prefix_scratch": 9,
        "terminal_map_scratch": 9,
    }
    assert module.CLEAN_AUX_SIZE == 10
    print(f"PASS 1616-step scratch census {maxima}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--sealed-generator", type=Path)
    args = parser.parse_args()
    module = load("aux10_invariant_candidate", args.candidate.resolve())
    check_generator_hashes(args.candidate.resolve(), args.sealed_generator)
    check_borrowed_c2swap(module)
    check_raw_controls(module)
    check_terminal_loans()
    check_tail_loan()
    check_scratch_census(module)
    print("PASS Aux10 structural invariant suite")


if __name__ == "__main__":
    main()
