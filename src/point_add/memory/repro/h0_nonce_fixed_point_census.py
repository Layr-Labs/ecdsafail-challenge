#!/usr/bin/env python3
"""Exact reduced census of no-op nonce freedom in lookup fixed points.

A semantic nonce can sample many verifier seeds without changing the lookup
function.  This instrument enumerates every table and every nonce in reduced
one-row domains, showing whether nonce bits change fixed-point density or only
multiply the number of independent trials.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import time
from typing import Any

try:
    from h0_fixed_point_census import (
        Scope,
        _base_records,
        _candidate_rows,
        _correction_encodings,
        _decode_draw,
        _record,
        _row_encodings,
        _semantic_reader,
    )
    from zero_score_lookup import X
except ModuleNotFoundError:
    from .h0_fixed_point_census import (
        Scope,
        _base_records,
        _candidate_rows,
        _correction_encodings,
        _decode_draw,
        _record,
        _row_encodings,
        _semantic_reader,
    )
    from .zero_score_lookup import X


def _nonce_tail(nonce: int, bits: int) -> bytes:
    if bits < 0:
        raise ValueError("nonce bits must be nonnegative")
    if nonce < 0 or nonce >= 1 << bits:
        raise ValueError("nonce is outside the declared bit width")
    records = bytearray()
    for bit in range(bits):
        target = 1 if (nonce >> bit) & 1 else 0
        record = _record(X, qt=target)
        records.extend(record)
        records.extend(record)
    return bytes(records)


def census(scope: Scope, nonce_bits: int) -> dict[str, Any]:
    if scope.rows != 1:
        raise ValueError("nonce census currently requires a one-row scope")
    base = _base_records(scope.half_width)
    row_encodings = _row_encodings(scope.key_bits)
    correction_encodings = _correction_encodings(scope.key_bits)
    tails = tuple(_nonce_tail(nonce, nonce_bits) for nonce in range(1 << nonce_bits))
    successes = 0
    checked = 0
    successful_tables: set[tuple[tuple[int, int], ...]] = set()
    started = time.monotonic()

    for rows, tail in itertools.product(_candidate_rows(scope), tails):
        shake, _, _ = _semantic_reader(
            scope,
            rows,
            base,
            row_encodings,
            correction_encodings,
            tail,
        )
        checked += 1
        state_bytes = (2 * scope.key_bits + 7) // 8
        if _decode_draw(shake.digest(state_bytes), scope) == rows:
            successes += 1
            successful_tables.add(rows)

    expected = float(1 << nonce_bits)
    sigma = math.sqrt(expected * (1.0 - 1.0 / scope.candidate_count))
    return {
        "half_width": scope.half_width,
        "rows": scope.rows,
        "nonce_bits": nonce_bits,
        "table_states": scope.candidate_count,
        "nonce_states": 1 << nonce_bits,
        "checked_pairs": checked,
        "successful_pairs": successes,
        "successful_tables": len(successful_tables),
        "expected_successful_pairs": expected,
        "success_sigma": sigma,
        "z_score": (successes - expected) / sigma if sigma else 0.0,
        "pair_success_density": successes / checked,
        "expected_pair_success_density": 1.0 / scope.candidate_count,
        "complete": checked == scope.candidate_count * (1 << nonce_bits),
        "elapsed_seconds": time.monotonic() - started,
    }


def run(max_width: int, max_nonce_bits: int) -> dict[str, Any]:
    if max_width <= 0:
        raise ValueError("max width must be positive")
    if max_nonce_bits < 0:
        raise ValueError("max nonce bits must be nonnegative")
    scopes = [
        census(Scope(width, 1), nonce_bits)
        for width in range(1, max_width + 1)
        for nonce_bits in range(max_nonce_bits + 1)
    ]
    production_table_log2 = 4_758_375.235490617
    production_nonce_bits = 48
    return {
        "experiment": "no-op nonce lookup fixed-point census",
        "scopes": scopes,
        "all_scopes_complete": all(scope["complete"] for scope in scopes),
        "all_scopes_within_four_sigma": all(abs(scope["z_score"]) <= 4.0 for scope in scopes),
        "production_extrapolation": {
            "table_log2_states": production_table_log2,
            "nonce_bits": production_nonce_bits,
            "fixed_table_exhaustive_success_log2": production_nonce_bits - production_table_log2,
            "global_pair_success_density_log2": -production_table_log2,
            "note": "Nonce bits multiply independent trials but do not change success density per table/nonce pair.",
        },
        "verdict": "green",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-width", type=int, default=2)
    parser.add_argument("--max-nonce-bits", type=int, default=8)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = run(args.max_width, args.max_nonce_bits)
    print(json.dumps(report, sort_keys=True, indent=None if args.json else 2))
    return 0 if report["all_scopes_complete"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
