#!/usr/bin/env python3
"""Exact reduced-domain census for self-seeded zero-Toffoli lookup tables.

The production lookup route is a fixed-point problem: the table determines the
semantic operation stream, the stream determines the verifier SHAKE256 draw,
and that draw must reproduce the same table.  The production state is too large
to enumerate, so this program preserves the verifier's domain separator, field
serialization, condition-stack construction, and SHAKE256 coupling while
reducing register widths and table rows to finite exhaustive models.

A green report means every declared reduced state was enumerated exactly.  It is
mechanism evidence, not a production circuit certificate.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import struct
import time
from dataclasses import dataclass
from typing import Any, Iterable, Iterator

try:
    from zero_score_lookup import (
        APPEND_TO_REGISTER,
        BIT_INVERT,
        CANONICAL_RECORD_BYTES,
        DOMAIN,
        NO_FIELD,
        POP_CONDITION,
        PUSH_CONDITION,
        REGISTER,
        X,
        _record,
    )
except ModuleNotFoundError:
    from .zero_score_lookup import (
        APPEND_TO_REGISTER,
        BIT_INVERT,
        CANONICAL_RECORD_BYTES,
        DOMAIN,
        NO_FIELD,
        POP_CONDITION,
        PUSH_CONDITION,
        REGISTER,
        X,
        _record,
    )


@dataclass(frozen=True, slots=True)
class RowEncoding:
    key: int
    before: bytes
    after: bytes
    fixed_op_count: int


@dataclass(frozen=True, slots=True)
class Scope:
    half_width: int
    rows: int

    def __post_init__(self) -> None:
        if self.half_width <= 0:
            raise ValueError("half_width must be positive")
        if self.rows not in (1, 2):
            raise ValueError("only one-row and two-row exact scopes are supported")

    @property
    def key_bits(self) -> int:
        return 2 * self.half_width

    @property
    def key_states(self) -> int:
        return 1 << self.key_bits

    @property
    def correction_states(self) -> int:
        return 1 << self.key_bits

    @property
    def candidate_count(self) -> int:
        return (
            math.comb(self.key_states, self.rows)
            * self.correction_states**self.rows
        )

    @property
    def valid_draw_probability(self) -> float:
        numerator = math.prod(self.key_states - index for index in range(self.rows))
        return numerator / self.key_states**self.rows


def _base_records(half_width: int) -> bytes:
    records = bytearray()
    for register in range(4):
        records.extend(_record(REGISTER, rt=register))
    for qubit in range(half_width):
        records.extend(_record(APPEND_TO_REGISTER, qt=qubit, rt=0))
    for qubit in range(half_width, 2 * half_width):
        records.extend(_record(APPEND_TO_REGISTER, qt=qubit, rt=1))
    for bit in range(half_width):
        records.extend(_record(APPEND_TO_REGISTER, ct=bit, rt=2))
    for bit in range(half_width, 2 * half_width):
        records.extend(_record(APPEND_TO_REGISTER, ct=bit, rt=3))
    return bytes(records)


def _row_encodings(key_bits: int) -> tuple[RowEncoding, ...]:
    encodings: list[RowEncoding] = []
    for key in range(1 << key_bits):
        zero_positions = [bit for bit in range(key_bits) if not (key >> bit) & 1]
        before = bytearray()
        after = bytearray()
        for bit in zero_positions:
            before.extend(_record(BIT_INVERT, ct=bit))
        for bit in range(key_bits):
            before.extend(_record(PUSH_CONDITION, cc=bit))
        for _ in range(key_bits):
            after.extend(_record(POP_CONDITION))
        for bit in zero_positions:
            after.extend(_record(BIT_INVERT, ct=bit))
        encodings.append(
            RowEncoding(
                key=key,
                before=bytes(before),
                after=bytes(after),
                fixed_op_count=2 * len(zero_positions) + 2 * key_bits,
            )
        )
    return tuple(encodings)


def _correction_encodings(key_bits: int) -> tuple[tuple[bytes, int], ...]:
    encodings: list[tuple[bytes, int]] = []
    for correction in range(1 << key_bits):
        records = bytearray()
        for bit in range(key_bits):
            if (correction >> bit) & 1:
                records.extend(_record(X, qt=bit))
        encodings.append((bytes(records), correction.bit_count()))
    return tuple(encodings)


def _decode_draw(payload: bytes, scope: Scope) -> tuple[tuple[int, int], ...] | None:
    state_bits = 2 * scope.key_bits
    state_bytes = (state_bits + 7) // 8
    expected_bytes = state_bytes * scope.rows
    if len(payload) != expected_bytes:
        raise ValueError(f"draw has {len(payload)} bytes, expected {expected_bytes}")
    mask = (1 << scope.key_bits) - 1
    rows: list[tuple[int, int]] = []
    for index in range(scope.rows):
        start = index * state_bytes
        value = int.from_bytes(payload[start : start + state_bytes], "little")
        value &= (1 << state_bits) - 1
        rows.append((value & mask, (value >> scope.key_bits) & mask))
    rows.sort()
    if len({key for key, _ in rows}) != scope.rows:
        return None
    return tuple(rows)


def _candidate_rows(scope: Scope) -> Iterator[tuple[tuple[int, int], ...]]:
    corrections = range(scope.correction_states)
    for keys in itertools.combinations(range(scope.key_states), scope.rows):
        for values in itertools.product(corrections, repeat=scope.rows):
            yield tuple(zip(keys, values, strict=True))


def _semantic_reader(
    scope: Scope,
    rows: tuple[tuple[int, int], ...],
    base: bytes,
    row_encodings: tuple[RowEncoding, ...],
    correction_encodings: tuple[tuple[bytes, int], ...],
    tail: bytes = b"",
) -> tuple[Any, int, str]:
    base_count = 4 + 4 * scope.half_width
    op_count = base_count
    for key, correction in rows:
        op_count += row_encodings[key].fixed_op_count
        op_count += correction_encodings[correction][1]
    if len(tail) % CANONICAL_RECORD_BYTES:
        raise ValueError("tail must contain complete canonical operation records")
    op_count += len(tail) // CANONICAL_RECORD_BYTES

    shake = hashlib.shake_256()
    semantic = hashlib.sha256()
    prefix = DOMAIN + struct.pack("<Q", op_count)
    shake.update(prefix)
    semantic.update(struct.pack("<Q", op_count))
    shake.update(base)
    semantic.update(base)
    for key, correction in rows:
        row = row_encodings[key]
        correction_bytes = correction_encodings[correction][0]
        for chunk in (row.before, correction_bytes, row.after):
            shake.update(chunk)
            semantic.update(chunk)
    shake.update(tail)
    semantic.update(tail)
    return shake, op_count, semantic.hexdigest()


def census(scope: Scope, *, keep_fixed: int = 16) -> dict[str, Any]:
    base = _base_records(scope.half_width)
    row_encodings = _row_encodings(scope.key_bits)
    correction_encodings = _correction_encodings(scope.key_bits)
    fixed_points = 0
    fixed_samples: list[dict[str, Any]] = []
    minimum_ops: int | None = None
    maximum_ops = 0
    checked = 0
    started = time.monotonic()

    for rows in _candidate_rows(scope):
        shake, op_count, semantic_sha = _semantic_reader(
            scope,
            rows,
            base,
            row_encodings,
            correction_encodings,
        )
        checked += 1
        minimum_ops = op_count if minimum_ops is None else min(minimum_ops, op_count)
        maximum_ops = max(maximum_ops, op_count)
        state_bytes = (2 * scope.key_bits + 7) // 8
        draw = shake.digest(state_bytes * scope.rows)
        if _decode_draw(draw, scope) == rows:
            fixed_points += 1
            if len(fixed_samples) < keep_fixed:
                fixed_samples.append(
                    {
                        "rows": [[key, correction] for key, correction in rows],
                        "emitted_ops": op_count,
                        "semantic_sha256": semantic_sha,
                    }
                )

    elapsed = time.monotonic() - started
    expected = scope.valid_draw_probability
    return {
        "half_width": scope.half_width,
        "rows": scope.rows,
        "key_bits": scope.key_bits,
        "candidate_count": scope.candidate_count,
        "checked": checked,
        "fixed_points": fixed_points,
        "fixed_point_density": fixed_points / checked,
        "random_map_expected_fixed_points": expected,
        "expected_density": expected / checked,
        "minimum_emitted_ops": minimum_ops,
        "maximum_emitted_ops": maximum_ops,
        "fixed_samples": fixed_samples,
        "elapsed_seconds": elapsed,
        "complete": checked == scope.candidate_count,
    }


def default_scopes(max_one_row_width: int, max_two_row_width: int) -> tuple[Scope, ...]:
    if max_one_row_width <= 0 or max_two_row_width <= 0:
        raise ValueError("maximum widths must be positive")
    return tuple(
        [Scope(width, 1) for width in range(1, max_one_row_width + 1)]
        + [Scope(width, 2) for width in range(1, max_two_row_width + 1)]
    )


def _log2_candidate_states(key_bits: int, correction_bits: int, rows: int) -> float:
    key_states = 1 << key_bits
    key_term = sum(
        math.log2(key_states - index) - math.log2(index + 1)
        for index in range(rows)
    )
    return key_term + correction_bits * rows


def run(max_one_row_width: int = 5, max_two_row_width: int = 2) -> dict[str, Any]:
    reports = [
        census(scope)
        for scope in default_scopes(max_one_row_width, max_two_row_width)
    ]
    complete = all(report["complete"] for report in reports)
    total_candidates = sum(report["candidate_count"] for report in reports)
    total_fixed_points = sum(report["fixed_points"] for report in reports)
    production_rows = 9_024
    production_key_bits = 27
    production_correction_bits = 512
    production_log2_states = _log2_candidate_states(
        production_key_bits,
        production_correction_bits,
        production_rows,
    )
    return {
        "experiment": "reduced self-seeded lookup fixed-point census",
        "verdict": "green" if complete else "red",
        "scopes": reports,
        "total_candidates": total_candidates,
        "total_fixed_points": total_fixed_points,
        "all_scopes_complete": complete,
        "production_extrapolation": {
            "rows": production_rows,
            "key_bits": production_key_bits,
            "correction_bits_per_row": production_correction_bits,
            "state_bits_before_key_order_quotient": (
                production_rows
                * (production_key_bits + production_correction_bits)
            ),
            "log2_candidate_states": production_log2_states,
            "random_map_expected_fixed_points": 1.0,
            "random_map_fixed_point_density_log2": -production_log2_states,
            "note": (
                "The production family has one random-map fixed point in expectation, "
                "but an inverse-density search scale. Toy fixed points do not provide "
                "a scalable preimage method."
            ),
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-one-row-width", type=int, default=5)
    parser.add_argument("--max-two-row-width", type=int, default=2)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = run(args.max_one_row_width, args.max_two_row_width)
    print(json.dumps(report, sort_keys=True, indent=None if args.json else 2))
    return 0 if report["verdict"] == "green" else 1


if __name__ == "__main__":
    raise SystemExit(main())
