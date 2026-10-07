#!/usr/bin/env python3
"""Exact reduced census of DebugPrint no-op payload freedom.

The trusted parser accepts DebugPrint records without enforcing per-kind field
shape, while resource analysis still observes every field and the simulator does
nothing for the operation. This instrument enumerates only payload values that
stay inside already declared resource ranges (plus each sentinel), so each
record changes the Fiat-Shamir seed without changing the reduced lookup's
function or resource counts.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import time
from typing import Any, Iterator

try:
    from h0_fixed_point_census import (
        Scope,
        _base_records,
        _candidate_rows,
        _correction_encodings,
        _decode_draw,
        _row_encodings,
        _semantic_reader,
    )
    from zero_score_lookup import NO_FIELD, _record
except ModuleNotFoundError:
    from .h0_fixed_point_census import (
        Scope,
        _base_records,
        _candidate_rows,
        _correction_encodings,
        _decode_draw,
        _row_encodings,
        _semantic_reader,
    )
    from .zero_score_lookup import NO_FIELD, _record

DEBUG_PRINT = 17


def _payload_records(half_width: int) -> Iterator[bytes]:
    resource_ids = (*range(2 * half_width), NO_FIELD)
    register_ids = (0, 1, 2, 3, NO_FIELD)
    for q2, q1, qt, ct, cc, rt in itertools.product(
        resource_ids,
        resource_ids,
        resource_ids,
        resource_ids,
        resource_ids,
        register_ids,
    ):
        yield _record(DEBUG_PRINT, q2=q2, q1=q1, qt=qt, ct=ct, cc=cc, rt=rt)


def payload_state_count(half_width: int) -> int:
    if half_width <= 0:
        raise ValueError("half_width must be positive")
    return (2 * half_width + 1) ** 5 * 5


def census(scope: Scope) -> dict[str, Any]:
    if scope.rows != 1:
        raise ValueError("DebugPrint payload census currently requires one row")
    base = _base_records(scope.half_width)
    row_encodings = _row_encodings(scope.key_bits)
    correction_encodings = _correction_encodings(scope.key_bits)
    payloads = tuple(_payload_records(scope.half_width))
    successful_pairs = 0
    successful_tables: set[tuple[tuple[int, int], ...]] = set()
    checked = 0
    started = time.monotonic()

    for rows, payload in itertools.product(_candidate_rows(scope), payloads):
        shake, _, _ = _semantic_reader(
            scope,
            rows,
            base,
            row_encodings,
            correction_encodings,
            payload,
        )
        checked += 1
        state_bytes = (2 * scope.key_bits + 7) // 8
        if _decode_draw(shake.digest(state_bytes), scope) == rows:
            successful_pairs += 1
            successful_tables.add(rows)

    payload_states = payload_state_count(scope.half_width)
    expected = float(payload_states)
    sigma = math.sqrt(expected * (1.0 - 1.0 / scope.candidate_count))
    return {
        "half_width": scope.half_width,
        "rows": scope.rows,
        "table_states": scope.candidate_count,
        "payload_states": payload_states,
        "checked_pairs": checked,
        "successful_pairs": successful_pairs,
        "successful_tables": len(successful_tables),
        "expected_successful_pairs": expected,
        "success_sigma": sigma,
        "z_score": (successful_pairs - expected) / sigma if sigma else 0.0,
        "pair_success_density": successful_pairs / checked,
        "expected_pair_success_density": 1.0 / scope.candidate_count,
        "complete": checked == scope.candidate_count * payload_states,
        "elapsed_seconds": time.monotonic() - started,
    }


def run(max_width: int) -> dict[str, Any]:
    if max_width <= 0:
        raise ValueError("max_width must be positive")
    scopes = [census(Scope(width, 1)) for width in range(1, max_width + 1)]
    minimum_production_payload_states = 513**5 * 5
    return {
        "experiment": "DebugPrint no-op payload fixed-point census",
        "scopes": scopes,
        "all_scopes_complete": all(scope["complete"] for scope in scopes),
        "all_scopes_within_four_sigma": all(
            abs(scope["z_score"]) <= 4.0 for scope in scopes
        ),
        "production_extrapolation": {
            "minimum_qubit_field_states": 513,
            "minimum_bit_field_states": 513,
            "register_field_states": 5,
            "payload_states_per_record": minimum_production_payload_states,
            "payload_entropy_bits_per_record": math.log2(
                minimum_production_payload_states
            ),
            "note": "Payload freedom multiplies independent seed trials but does not change fixed-point density per table/payload pair.",
        },
        "verdict": "green",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-width", type=int, default=2)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = run(args.max_width)
    print(json.dumps(report, sort_keys=True, indent=None if args.json else 2))
    return 0 if report["all_scopes_complete"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
