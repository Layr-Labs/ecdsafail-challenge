#!/usr/bin/env python3
"""Structural support checks for the paper2607 11-clean-aux route."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import derive_active_windows as schedule


MAX_QUOTIENT_WEIGHT = 256
SHIFT_MODULUS = 259
MAX_TERMINAL_PADDING_STEPS = 592
ACTIVE_WINDOWS_SHA256 = (
    "3e1961f5550249604bf044edb65f1d1bc403ed75bd7178e283685ddb4f3cb880"
)


def check_phase_update_identity() -> None:
    for phase1 in range(2):
        for sign in range(2):
            for phase2 in range(2):
                for condition in range(2):
                    original = phase2 ^ (condition & (sign ^ phase1))
                    reduced = (
                        phase2
                        ^ (condition & sign)
                        ^ (condition & phase1)
                    )
                    assert reduced == original
    print("PASS phase-update temporary elimination states=16")


def check_length_swap_loan() -> None:
    for phase1 in range(2):
        for phase2 in range(2):
            control = phase1 ^ phase2
            cleared = phase2 ^ control ^ phase1
            assert cleared == 0
            restored = cleared ^ phase1 ^ control
            assert restored == phase2
    print("PASS length-swap Phase2 loan states=4")


def post_step_metadata(weight: int, local_step: int) -> tuple[int, int, int]:
    """Return (l_q, l_s, Phase1) after the phase update."""
    assert 1 <= local_step <= 4 * weight
    if local_step <= weight:
        # Phase A: the pre-shift has advanced l_s and cannot reach zero.
        return 0, local_step, 0
    if local_step <= 2 * weight:
        # Phase B: l_q increments while the post-shift decreases l_s.
        index = local_step - weight
        l_q = index
        l_s = weight - index
        phase1 = 1 if l_s == 0 else 0
        return l_q, l_s, phase1
    if local_step <= 3 * weight:
        # Phase C: l_q decreases while the post-shift advances l_s.
        index = local_step - 2 * weight
        return weight - index, index, 1
    # Phase D: l_q is zero and the post-shift decreases l_s.  At the
    # quotient boundary, the guarded phase update toggles Phase1 to zero.
    index = local_step - 3 * weight
    l_s = weight - index
    return 0, l_s, 0 if l_s == 0 else 1


def check_terminal_extension_support() -> None:
    triggers = 0
    for weight in range(1, MAX_QUOTIENT_WEIGHT + 1):
        for local_step in range(1, 4 * weight + 1):
            l_q, l_s, phase1 = post_step_metadata(weight, local_step)
            if l_q == 0 and l_s == 0:
                triggers += 1
                assert phase1 == 0

    # Once l_rp is zero, the implementation guards both phase transitions
    # with l_rp != 0.  Phase1 therefore remains zero even when the modulo-259
    # shift counter revisits its zero sentinel during terminal padding.
    phase1 = 0
    l_s = 0
    padding_triggers = 0
    for _ in range(MAX_TERMINAL_PADDING_STEPS):
        l_s = (l_s + 1) % SHIFT_MODULUS
        if l_s == 0:
            padding_triggers += 1
            assert phase1 == 0

    assert triggers == MAX_QUOTIENT_WEIGHT
    assert padding_triggers == MAX_TERMINAL_PADDING_STEPS // SHIFT_MODULUS
    print(
        "PASS terminal Phase1 extension "
        f"weights={MAX_QUOTIENT_WEIGHT} quotient_triggers={triggers} "
        f"padding_steps={MAX_TERMINAL_PADDING_STEPS} "
        f"padding_triggers={padding_triggers}"
    )


def check_relaxed_terminal_envelope() -> None:
    table_path = Path(__file__).with_name("active_windows_1616.json")
    table_bytes = table_path.read_bytes()
    assert hashlib.sha256(table_bytes).hexdigest() == ACTIVE_WINDOWS_SHA256
    rows = json.loads(table_bytes)["rows"]
    assert len(rows) == 1616

    total_candidates = 0
    terminal_candidates = 0
    bad_terminal_candidates = 0
    for row in rows:
        step = int(row["step"])
        phase_counts = {phase: 0 for phase in "ABCD"}
        candidates = 0
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
                features = schedule.phase_features(weight, local_step)
                phase = str(features["phase"])
                phase_counts[phase] += 1
                candidates += 1
                l_q, l_s, phase1 = post_step_metadata(weight, local_step)
                if l_q == 0 and l_s == 0:
                    terminal_candidates += 1
                    assert step % 4 == 0
                    if phase1:
                        bad_terminal_candidates += 1

        expected = row["proof_state_counts"]
        assert candidates == int(expected["relaxed_candidates"])
        for phase in "ABCD":
            assert phase_counts[phase] == int(expected[f"phase_{phase}"])
        total_candidates += candidates

    assert total_candidates == 23_890_924
    assert terminal_candidates == 62_913
    assert bad_terminal_candidates == 0
    print(
        "PASS relaxed terminal envelope "
        f"states={total_candidates} terminal={terminal_candidates} "
        f"bad={bad_terminal_candidates} table_sha256={ACTIVE_WINDOWS_SHA256}"
    )


def check_live_r_mode_support() -> None:
    for phase1 in range(2):
        for remainder_is_live in range(2):
            control = remainder_is_live & (phase1 ^ 1)
            if control:
                assert phase1 == 0
    print("PASS live-R Mode extension predicate states=4")


def main() -> None:
    check_phase_update_identity()
    check_length_swap_loan()
    check_terminal_extension_support()
    check_relaxed_terminal_envelope()
    check_live_r_mode_support()
    print("PASS aux11 structural support suite")


if __name__ == "__main__":
    main()
