#!/usr/bin/env python3
"""Exact functional-graph census for canonical self-seeded lookup tables."""

from __future__ import annotations

import hashlib
import json
import math
import struct
import time
from array import array

try:
    from h0_fixed_point_census import (
        DOMAIN,
        Scope,
        _base_records,
        _correction_encodings,
        _decode_draw,
        _row_encodings,
    )
except ModuleNotFoundError:
    from .h0_fixed_point_census import (
        DOMAIN,
        Scope,
        _base_records,
        _correction_encodings,
        _decode_draw,
        _row_encodings,
    )


def successor_map(half_width: int) -> array:
    scope = Scope(half_width=half_width, rows=1)
    states = scope.key_states * scope.correction_states
    base = _base_records(half_width)
    rows = _row_encodings(scope.key_bits)
    corrections = _correction_encodings(scope.key_bits)
    base_count = 4 + 4 * half_width
    state_bytes = (2 * scope.key_bits + 7) // 8
    successors = array("I")
    for key in range(scope.key_states):
        row = rows[key]
        for correction in range(scope.correction_states):
            correction_bytes, correction_ops = corrections[correction]
            op_count = base_count + row.fixed_op_count + correction_ops
            shake = hashlib.shake_256()
            shake.update(DOMAIN)
            shake.update(struct.pack("<Q", op_count))
            shake.update(base)
            shake.update(row.before)
            shake.update(correction_bytes)
            shake.update(row.after)
            draw = _decode_draw(shake.digest(state_bytes), scope)
            assert draw is not None
            next_key, next_correction = draw[0]
            successors.append(
                next_key * scope.correction_states + next_correction
            )
    assert len(successors) == states
    return successors


def graph_report(half_width: int) -> dict[str, object]:
    started = time.monotonic()
    successors = successor_map(half_width)
    states = len(successors)
    unresolved = -2
    nonfixed_cycle = -1
    attractor = array("i", [unresolved]) * states
    fixed = [index for index, target in enumerate(successors) if index == target]
    basin_sizes = {index: 1 for index in fixed}
    for index in fixed:
        attractor[index] = index

    cycle_lengths: list[int] = []
    max_tail = 0
    for start in range(states):
        if attractor[start] != unresolved:
            continue
        path: list[int] = []
        positions: dict[int, int] = {}
        node = start
        while attractor[node] == unresolved and node not in positions:
            positions[node] = len(path)
            path.append(node)
            node = successors[node]
        if attractor[node] != unresolved:
            destination = attractor[node]
            prefix = path
        else:
            cycle_start = positions[node]
            cycle = path[cycle_start:]
            cycle_lengths.append(len(cycle))
            for member in cycle:
                attractor[member] = nonfixed_cycle
            destination = nonfixed_cycle
            prefix = path[:cycle_start]
        max_tail = max(max_tail, len(prefix))
        for member in reversed(prefix):
            attractor[member] = destination
        if destination >= 0:
            basin_sizes[destination] += len(prefix)

    fixed_basin_sizes = sorted(basin_sizes.values(), reverse=True)
    fixed_basin_total = sum(fixed_basin_sizes)
    basin_bound = math.ceil(8.0 * math.sqrt(states))
    return {
        "half_width": half_width,
        "states": states,
        "fixed_points": len(fixed),
        "fixed_point_basin_sizes": fixed_basin_sizes,
        "fixed_point_basin_total": fixed_basin_total,
        "fixed_point_basin_fraction": fixed_basin_total / states,
        "predicted_basin_bound": basin_bound,
        "basin_bound_pass": not fixed_basin_sizes
        or max(fixed_basin_sizes) <= basin_bound,
        "nonfixed_cycles": len(cycle_lengths),
        "maximum_nonfixed_cycle_length": max(cycle_lengths, default=0),
        "maximum_tail_length": max_tail,
        "elapsed_seconds": time.monotonic() - started,
        "complete": all(value != unresolved for value in attractor),
    }


def run(max_half_width: int = 5) -> dict[str, object]:
    if max_half_width < 1:
        raise ValueError("max_half_width must be positive")
    scopes = [graph_report(width) for width in range(1, max_half_width + 1)]
    return {
        "experiment": "one-row self-seeded lookup functional graph",
        "scopes": scopes,
        "all_complete": all(scope["complete"] for scope in scopes),
        "all_basin_bounds_pass": all(
            scope["basin_bound_pass"] for scope in scopes
        ),
    }


def main() -> int:
    report = run()
    print(json.dumps(report, sort_keys=True))
    return 0 if report["all_complete"] and report["all_basin_bounds_pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
