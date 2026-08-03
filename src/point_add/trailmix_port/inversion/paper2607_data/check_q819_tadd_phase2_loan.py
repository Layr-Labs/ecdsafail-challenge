#!/usr/bin/env python3
"""Exhaustive phase-domain proof for the Q819 T-add Phase2 loan.

The proof enumerates every quotient weight and every Algorithm-3 microstep,
which is a superset of the certified secp256k1 schedule.  It evaluates the
physical truth-minus-one l_q value immediately before T-add, applies the reversible
phase encoding, checks that Phase2 is clean, and applies the inverse encoding.
"""

from __future__ import annotations


MAX_WEIGHT = 256


def tadd_boundary_state(weight: int, local_step: int) -> tuple[str, int, int, int]:
    if not 1 <= local_step <= 4 * weight:
        raise ValueError("microstep outside quotient")
    if local_step <= weight:
        return "A", 0, 0, 511
    if local_step <= 2 * weight:
        # Phase B increments l_q before T-add.
        return "B", 0, 1, local_step - weight - 1
    if local_step <= 3 * weight:
        # Phase C decrements l_q before T-add.
        j = local_step - 2 * weight
        return "C", 1, 0, (weight - j - 1) & 511
    return "D", 1, 1, 511


def forward(phase1: int, phase2: int, l_q: int) -> tuple[int, int]:
    marker = (l_q >> 8) & 1
    marker ^= phase1 & phase2
    l_q = (l_q & 0xFF) | (marker << 8)
    phase2 ^= phase1 & int(l_q == 255)
    phase2 ^= (1 ^ phase1) & (1 ^ ((l_q >> 8) & 1))
    return phase2, l_q


def inverse(phase1: int, phase2: int, l_q: int) -> tuple[int, int]:
    phase2 ^= (1 ^ phase1) & (1 ^ ((l_q >> 8) & 1))
    phase2 ^= phase1 & int(l_q == 255)
    marker = (l_q >> 8) & 1
    marker ^= phase1 & phase2
    l_q = (l_q & 0xFF) | (marker << 8)
    return phase2, l_q


def main() -> None:
    checked = 0
    counts = {phase: 0 for phase in "ABCD"}
    for weight in range(1, MAX_WEIGHT + 1):
        for local_step in range(1, 4 * weight + 1):
            phase, phase1, phase2, l_q = tadd_boundary_state(weight, local_step)
            counts[phase] += 1
            checked += 1
            encoded_phase2, encoded_l_q = forward(phase1, phase2, l_q)
            if encoded_phase2 != 0:
                raise AssertionError((weight, local_step, phase, l_q, "not clean"))
            restored_phase2, restored_l_q = inverse(
                phase1, encoded_phase2, encoded_l_q
            )
            if (restored_phase2, restored_l_q) != (phase2, l_q):
                raise AssertionError((weight, local_step, phase, l_q, "restore"))
    print(
        "PASS q819_tadd_phase2_loan "
        f"weights=1..{MAX_WEIGHT} states={checked} phase_counts={counts} "
        "phase2_clean=yes inverse=exact"
    )


if __name__ == "__main__":
    main()
