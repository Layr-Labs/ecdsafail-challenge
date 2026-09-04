#!/usr/bin/env python3
"""Exhaustive domain proof for the benchmark-qualified Q818 Iter loan."""

from __future__ import annotations

from check_q818_tadd_phase2_loan import inverse as phase2_inverse
from check_q818_tadd_phase2_loan import forward as phase2_forward
from check_q818_tadd_phase2_loan import tadd_boundary_state


def canonicalize(phase1: int, l_q: int) -> int:
    if phase1 == 0 and l_q in (255, 511):
        return 766 - l_q
    if phase1 == 1 and l_q in (254, 511):
        return 765 - l_q
    return l_q


def forward(
    phase1: int, phase2: int, iteration: int, l_q: int
) -> tuple[int, int, int]:
    phase2, l_q = phase2_forward(phase1, phase2, l_q)
    l_q = canonicalize(phase1, l_q)
    high = ((l_q >> 8) & 1) ^ iteration
    l_q = (l_q & 0xFF) | (high << 8)
    iteration ^= high
    return phase2, iteration, l_q


def inverse(
    phase1: int, phase2: int, iteration: int, l_q: int
) -> tuple[int, int, int]:
    iteration ^= (l_q >> 8) & 1
    high = ((l_q >> 8) & 1) ^ iteration
    l_q = (l_q & 0xFF) | (high << 8)
    l_q = canonicalize(phase1, l_q)
    phase2, l_q = phase2_inverse(phase1, phase2, l_q)
    return phase2, iteration, l_q


def main() -> None:
    checked = 0
    codes: set[tuple[int, int]] = set()
    for weight in range(1, 256):
        for local_step in range(1, 4 * weight + 1):
            _, phase1, phase2, l_q = tadd_boundary_state(weight, local_step)
            for iteration in (0, 1):
                encoded = forward(phase1, phase2, iteration, l_q)
                if encoded[0] != 0 or encoded[1] != 0:
                    raise AssertionError((weight, local_step, iteration, encoded))
                codes.add((phase1, encoded[2]))
                restored = inverse(phase1, *encoded)
                if restored != (phase2, iteration, l_q):
                    raise AssertionError((weight, local_step, iteration, restored))
                checked += 1

    excluded = []
    weight = 256
    for local_step in range(1, 4 * weight + 1):
        phase, phase1, phase2, l_q = tadd_boundary_state(weight, local_step)
        for iteration in (0, 1):
            encoded = forward(phase1, phase2, iteration, l_q)
            if encoded[0] != 0 or encoded[1] != 0:
                excluded.append((phase, l_q, iteration))
            if inverse(phase1, *encoded) != (phase2, iteration, l_q):
                raise AssertionError(("weight256 reverse", local_step, iteration))

    if set(excluded) != {
        ("B", 255, 0), ("B", 255, 1),
        ("C", 254, 0), ("C", 254, 1),
    }:
        raise AssertionError(excluded)
    print(
        "PASS q818-tadd-iter-loan "
        f"weights=1..255 states={checked} packed_codes={len(codes)} "
        "phase2_clean=yes iter_clean=yes inverse=exact "
        f"excluded_weight256={excluded}"
    )


if __name__ == "__main__":
    main()
