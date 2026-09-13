#!/usr/bin/env python3
"""Census semantic-order freedom in reduced zero-Toffoli lookup fixed points.

The zero-score lookup has far more seed freedom than an appended nonce: condition
pushes, classical inversions, correction X gates, and complete lookup rows can be
reordered without changing the circuit function. This program enumerates every
such stream in finite reduced scopes and measures whether the extra streams
change fixed-point density or merely multiply random-map trials.

A green report certifies only the declared reduced censuses and the ordering
entropy of the supplied frozen dataset. It is not a production fixed point.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import struct
import time
from collections.abc import Iterator
from pathlib import Path
from typing import Any

try:
    from h0_fixed_point_census import (
        Scope,
        _base_records,
        _candidate_rows,
        _decode_draw,
    )
    from zero_score_lookup import (
        BIT_INVERT,
        DOMAIN,
        POP_CONDITION,
        PUSH_CONDITION,
        X,
        _artifact_seed,
        _draw_dataset,
        _fixed_base_table,
        _lookup_rows,
        _minimum_unique_prefix,
        _record,
    )
except ModuleNotFoundError:
    from .h0_fixed_point_census import (
        Scope,
        _base_records,
        _candidate_rows,
        _decode_draw,
    )
    from .zero_score_lookup import (
        BIT_INVERT,
        DOMAIN,
        POP_CONDITION,
        PUSH_CONDITION,
        X,
        _artifact_seed,
        _draw_dataset,
        _fixed_base_table,
        _lookup_rows,
        _minimum_unique_prefix,
        _record,
    )


def _records(kind: int, values: tuple[int, ...], field: str) -> bytes:
    output = bytearray()
    for value in values:
        if field == "ct":
            output.extend(_record(kind, ct=value))
        elif field == "cc":
            output.extend(_record(kind, cc=value))
        elif field == "qt":
            output.extend(_record(kind, qt=value))
        else:
            raise ValueError(f"unknown operation field {field}")
    return bytes(output)


def _row_variants(key: int, correction: int, key_bits: int) -> Iterator[bytes]:
    zeros = tuple(bit for bit in range(key_bits) if not (key >> bit) & 1)
    ones = tuple(bit for bit in range(key_bits) if (correction >> bit) & 1)
    pops = b"".join(_record(POP_CONDITION) for _ in range(key_bits))
    for before_order in itertools.permutations(zeros):
        before = _records(BIT_INVERT, before_order, "ct")
        for push_order in itertools.permutations(range(key_bits)):
            pushes = _records(PUSH_CONDITION, push_order, "cc")
            for correction_order in itertools.permutations(ones):
                corrections = _records(X, correction_order, "qt")
                for after_order in itertools.permutations(zeros):
                    after = _records(BIT_INVERT, after_order, "ct")
                    yield before + pushes + corrections + pops + after


def _row_variant_count(key: int, correction: int, key_bits: int) -> int:
    zeros = key_bits - key.bit_count()
    ones = correction.bit_count()
    return (
        math.factorial(zeros)
        * math.factorial(key_bits)
        * math.factorial(ones)
        * math.factorial(zeros)
    )


def _table_body_variants(
    rows: tuple[tuple[int, int], ...], key_bits: int
) -> Iterator[bytes]:
    if not rows:
        yield b""
        return
    key, correction = rows[0]
    for first in _row_variants(key, correction, key_bits):
        for remainder in _table_body_variants(rows[1:], key_bits):
            yield first + remainder


def _operation_count(scope: Scope, rows: tuple[tuple[int, int], ...]) -> int:
    count = 4 + 4 * scope.half_width
    for key, correction in rows:
        zeros = scope.key_bits - key.bit_count()
        count += 2 * zeros + 2 * scope.key_bits + correction.bit_count()
    return count


def census(scope: Scope) -> dict[str, Any]:
    """Enumerate all declared semantic orderings for one reduced scope."""
    base = _base_records(scope.half_width)
    state_bytes = (2 * scope.key_bits + 7) // 8
    total = 0
    successes = 0
    successful_tables: set[tuple[tuple[int, int], ...]] = set()
    semantic_hashes: set[bytes] = set()
    semantic_collisions = 0
    declared = 0
    started = time.monotonic()

    for table in _candidate_rows(scope):
        row_orders = (table,) if scope.rows == 1 else (table, tuple(reversed(table)))
        table_declared = math.factorial(scope.rows)
        for key, correction in table:
            table_declared *= _row_variant_count(key, correction, scope.key_bits)
        declared += table_declared
        count = _operation_count(scope, table)
        shake_prefix = DOMAIN + struct.pack("<Q", count)
        semantic_prefix = struct.pack("<Q", count)
        for ordered_rows in row_orders:
            for row_body in _table_body_variants(ordered_rows, scope.key_bits):
                body = base + row_body
                shake = hashlib.shake_256(shake_prefix + body)
                draw = _decode_draw(shake.digest(state_bytes * scope.rows), scope)
                if draw == table:
                    successes += 1
                    successful_tables.add(table)
                semantic_hash = hashlib.sha256(semantic_prefix + body).digest()
                if semantic_hash in semantic_hashes:
                    semantic_collisions += 1
                else:
                    semantic_hashes.add(semantic_hash)
                total += 1

    outcome_states = (scope.key_states * scope.correction_states) ** scope.rows
    exact_draw_orders = math.factorial(scope.rows)
    success_probability = exact_draw_orders / outcome_states
    expected = total * success_probability
    variance = total * success_probability * (1.0 - success_probability)
    return {
        "half_width": scope.half_width,
        "rows": scope.rows,
        "candidate_tables": scope.candidate_count,
        "declared_semantic_variants": declared,
        "checked_semantic_variants": total,
        "unique_semantic_sha256": len(semantic_hashes),
        "semantic_sha256_collisions": semantic_collisions,
        "fixed_variants": successes,
        "expected_fixed_variants_random_map": expected,
        "standard_deviation_random_map": math.sqrt(variance),
        "z_score": (successes - expected) / math.sqrt(variance),
        "tables_with_fixed_variant": len(successful_tables),
        "success_density": successes / total,
        "elapsed_seconds": time.monotonic() - started,
    }


def production_order_entropy(ops_path: Path, shots: int) -> dict[str, Any]:
    """Count a conservative subset of distinct streams for one frozen draw."""
    shake, semantic_sha, emitted_ops = _artifact_seed(ops_path)
    dataset = _draw_dataset(shake, shots, _fixed_base_table())
    prefix_width = _minimum_unique_prefix(dataset)
    table = _lookup_rows(dataset, prefix_width)

    # Complete rows commute. Within each row, condition pushes, pre/post
    # inversions, and correction X gates independently commute.
    log2_variants = math.lgamma(shots + 1) / math.log(2)
    correction_weights: list[int] = []
    for key, (mask_x, mask_y) in table.items():
        zeros = prefix_width - key.bit_count()
        weight = mask_x.bit_count() + mask_y.bit_count()
        correction_weights.append(weight)
        log2_variants += (
            math.lgamma(prefix_width + 1)
            + 2 * math.lgamma(zeros + 1)
            + math.lgamma(weight + 1)
        ) / math.log(2)

    return {
        "source_ops_semantic_sha256": semantic_sha,
        "source_emitted_ops": emitted_ops,
        "shots": shots,
        "prefix_width": prefix_width,
        "table_entries": len(table),
        "minimum_correction_weight": min(correction_weights),
        "maximum_correction_weight": max(correction_weights),
        "mean_correction_weight": sum(correction_weights) / len(correction_weights),
        "log2_distinct_semantics_preserving_streams_lower_bound": log2_variants,
    }


def run(ops_path: Path, shots: int) -> dict[str, Any]:
    scopes = (Scope(1, 1), Scope(1, 2), Scope(2, 1))
    reports = [census(scope) for scope in scopes]
    production = production_order_entropy(ops_path, shots)
    green = all(
        report["declared_semantic_variants"]
        == report["checked_semantic_variants"]
        and report["semantic_sha256_collisions"] == 0
        and abs(report["z_score"]) <= 4.0
        for report in reports
    )
    return {
        "experiment": "semantics-preserving zero-score lookup permutation census",
        "verdict": "green" if green else "red",
        "scopes": reports,
        "production_entropy": production,
        "conclusion": (
            "Permutation freedom creates many distinct streams and fixed variants in reduced "
            "models, but per-stream fixed-point density remains random-map scale. Entropy is "
            "abundant; no efficient production search follows."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ops", type=Path, default=Path("ops.bin"))
    parser.add_argument("--shots", type=int, default=9_024)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    if args.shots <= 0:
        parser.error("--shots must be positive")
    report = run(args.ops, args.shots)
    print(json.dumps(report, sort_keys=True, indent=None if args.json else 2))
    return 0 if report["verdict"] == "green" else 1


if __name__ == "__main__":
    raise SystemExit(main())
