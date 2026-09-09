#!/usr/bin/env python3
"""Exhaustive affine-quotient lower bound for the pair25 normalizer domain."""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from pathlib import Path
from typing import Iterable

import y5_normalizer_synth as synth

RESEARCH_DIR = Path(__file__).resolve().parent
REPO_ROOT = RESEARCH_DIR.parents[3]
DEFAULT_OUTPUT = REPO_ROOT / ".autoresearch/measurements/y5-pair25-quotient-v1/report.json"
VALID_SYMBOLS = (0b001, 0b011, 0b100, 0b101, 0b111)
WIDTH = 5


def compress_pair(first: int, second: int) -> int:
    """Classically replay compress_2sym_fast through its proven clear_and."""
    value = first | (second << 3)

    def bit(index: int) -> int:
        return (value >> index) & 1

    value ^= 1 << 3
    value ^= bit(5) << 1
    value ^= bit(4)
    value ^= 1 << 2
    value ^= (bit(1) & bit(3)) << 5
    value ^= bit(3) << 5
    value ^= bit(3)
    value ^= bit(1) << 5
    value ^= bit(5) << 3
    value ^= (bit(5) & bit(0)) << 4
    if bit(5) != (bit(3) & bit(4)):
        raise AssertionError("compress_2sym_fast clear_and precondition failed")
    value &= ~(1 << 5)
    return value & ((1 << WIDTH) - 1)


def canonical_span(vectors: Iterable[int]) -> tuple[int, ...]:
    """Canonical reduced XOR basis of sample-column bit vectors."""
    basis: dict[int, int] = {}
    for raw in vectors:
        value = int(raw)
        for pivot in sorted(basis, reverse=True):
            if (value >> pivot) & 1:
                value ^= basis[pivot]
        if value == 0:
            continue
        pivot = value.bit_length() - 1
        for other, row in list(basis.items()):
            if (row >> pivot) & 1:
                basis[other] = row ^ value
        basis[pivot] = value
    return tuple(basis[pivot] for pivot in sorted(basis, reverse=True))


def coordinate_masks(key: tuple[int, ...], constant: int) -> list[int]:
    chosen = [constant]
    rank = 1
    for row in key:
        candidate = canonical_span([*chosen, row])
        if len(candidate) > rank:
            chosen.append(row)
            rank += 1
        if rank == WIDTH + 1:
            break
    if rank != WIDTH + 1:
        raise ValueError(f"expected affine rank {WIDTH + 1}, found {rank}")
    return chosen[1:]


def neighbor_spans(key: tuple[int, ...], constant: int) -> set[tuple[int, ...]]:
    """Enumerate one affine-conjugated CCX move modulo free affine output."""
    coordinates = coordinate_masks(key, constant)
    linear = [0] * (1 << WIDTH)
    for form in range(1, 1 << WIDTH):
        value = 0
        for bit_index, coordinate in enumerate(coordinates):
            if (form >> bit_index) & 1:
                value ^= coordinate
        linear[form] = value

    neighbors: set[tuple[int, ...]] = set()
    for direction in range(1, 1 << WIDTH):
        invariant_forms = [
            form
            for form in range(1, 1 << WIDTH)
            if (form & direction).bit_count() % 2 == 0
        ]
        hyperplane_basis: list[int] = []
        for form in invariant_forms:
            if synth.matrix_rank([*hyperplane_basis, form], WIDTH) > len(hyperplane_basis):
                hyperplane_basis.append(form)
            if len(hyperplane_basis) == WIDTH - 1:
                break
        transverse = next(
            form
            for form in range(1, 1 << WIDTH)
            if (form & direction).bit_count() % 2 == 1
        )

        products: set[int] = set()
        for left_index, left in enumerate(invariant_forms):
            for right in invariant_forms[left_index + 1 :]:
                for left_constant in (0, 1):
                    left_mask = linear[left] ^ (constant if left_constant else 0)
                    for right_constant in (0, 1):
                        right_mask = linear[right] ^ (constant if right_constant else 0)
                        products.add(left_mask & right_mask)

        fixed = [constant, *[linear[form] for form in hyperplane_basis]]
        transverse_mask = linear[transverse]
        for product in products:
            neighbors.add(canonical_span([*fixed, transverse_mask ^ product]))
    return neighbors


def pack_key(key: tuple[int, ...]) -> bytes:
    if len(key) != WIDTH + 1 or any(value >= 1 << 32 for value in key):
        raise ValueError("pair25 span key does not fit six u32 words")
    return b"".join(value.to_bytes(4, "little") for value in key)


def frontier_sha256(frontier: set[bytes]) -> str:
    digest = hashlib.sha256()
    for key in sorted(frontier):
        digest.update(key)
    return digest.hexdigest()


def write_frontier(path: Path, frontier: set[bytes]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("wb") as output:
        for key in sorted(frontier):
            output.write(key)


def run(output: Path, frontier_dir: Path | None = None) -> dict[str, object]:
    started_ns = time.time_ns()
    started = time.monotonic()
    pair_states = [
        compress_pair(first, second)
        for first in VALID_SYMBOLS
        for second in VALID_SYMBOLS
    ]
    if len(set(pair_states)) != 25:
        raise RuntimeError("valid symbol pairs did not produce 25 distinct normalizer inputs")
    if tuple(sorted(pair_states)) != synth.PAIR25_INPUTS:
        raise RuntimeError("derived pair25 domain disagrees with the synthesis contract")

    table = synth.reference_table()
    pair_outputs = [table[value] for value in pair_states]
    if sorted(pair_outputs) != list(range(25)):
        raise RuntimeError("pair25 normalizer outputs are not canonical values 0..24")

    sample_count = len(pair_states)
    constant = (1 << sample_count) - 1
    input_masks = [
        sum(((value >> bit_index) & 1) << sample for sample, value in enumerate(pair_states))
        for bit_index in range(WIDTH)
    ]
    output_masks = [
        sum(((value >> bit_index) & 1) << sample for sample, value in enumerate(pair_outputs))
        for bit_index in range(WIDTH)
    ]
    input_key = canonical_span([constant, *input_masks])
    output_key = canonical_span([constant, *output_masks])
    if len(input_key) != WIDTH + 1 or len(output_key) != WIDTH + 1:
        raise RuntimeError("input or output affine embedding is rank-deficient")

    input_depth1 = neighbor_spans(input_key, constant)
    output_depth1 = neighbor_spans(output_key, constant)
    shortest_path: int | None = 0 if input_key == output_key else None
    if shortest_path is None and output_key in input_depth1:
        shortest_path = 1
    if shortest_path is None and input_depth1.intersection(output_depth1):
        shortest_path = 2

    input_depth2: set[bytes] = set()
    reverse_edge_failures = 0
    if shortest_path is None:
        for middle in input_depth1:
            neighbors = neighbor_spans(middle, constant)
            if input_key not in neighbors:
                reverse_edge_failures += 1
            for neighbor in neighbors:
                input_depth2.add(pack_key(neighbor))
                if neighbor == output_key or neighbor in output_depth1:
                    shortest_path = 3
                    break
            if shortest_path is not None:
                break

    output_depth2_edges_checked = 0
    output_depth2: set[bytes] = set()
    output_reverse_edge_failures = 0
    if shortest_path is None:
        for middle in output_depth1:
            neighbors = neighbor_spans(middle, constant)
            if output_key not in neighbors:
                output_reverse_edge_failures += 1
            for neighbor in neighbors:
                output_depth2_edges_checked += 1
                packed = pack_key(neighbor)
                output_depth2.add(packed)
                if packed in input_depth2:
                    shortest_path = 4

    frontier_dir = output.parent if frontier_dir is None else frontier_dir
    input_depth2_path = frontier_dir / "x-depth2.bin"
    output_depth2_path = frontier_dir / "y-depth2.bin"
    write_frontier(input_depth2_path, input_depth2)
    write_frontier(output_depth2_path, output_depth2)

    report: dict[str, object] = {
        "schema_version": 2,
        "scope": "exact pair25 affine-output quotient under arbitrary affine-conjugated CCX gates",
        "pair_inputs": pair_states,
        "sorted_pair_inputs": sorted(pair_states),
        "pair_outputs": pair_outputs,
        "sorted_pair_outputs": sorted(pair_outputs),
        "input_affine_rank": len(input_key),
        "output_affine_rank": len(output_key),
        "input_depth1_states": len(input_depth1),
        "output_depth1_states": len(output_depth1),
        "input_depth2_states": len(input_depth2),
        "input_depth2_sha256": frontier_sha256(input_depth2),
        "output_depth2_edges_checked": output_depth2_edges_checked,
        "output_depth2_states": len(output_depth2),
        "output_depth2_sha256": frontier_sha256(output_depth2),
        "frontier_artifacts": {
            "input_depth2": str(input_depth2_path.relative_to(REPO_ROOT)),
            "output_depth2": str(output_depth2_path.relative_to(REPO_ROOT)),
        },
        "reverse_edge_failures": reverse_edge_failures + output_reverse_edge_failures,
        "shortest_path_at_most_four": shortest_path,
        "minimum_ccx_lower_bound": 5 if shortest_path is None else shortest_path,
        "completeness_contract": {
            "state": "the six-dimensional affine function span of a labeled 25-point embedding",
            "edge": "every nonzero direction, every unordered pair of independent invariant linear controls, and all four affine control constants",
            "quotient": "two embeddings are identified iff related by an invertible affine output map",
            "symmetry": "each generalized shear is an involution; every enumerated edge must be observed in reverse",
        },
        "started_unix_ns": started_ns,
        "recorded_unix_ns": time.time_ns(),
        "wall_seconds": time.monotonic() - started,
        "verdict": "green" if shortest_path is None and reverse_edge_failures == 0 and output_reverse_edge_failures == 0 else "red",
    }
    encoded = json.dumps(report, sort_keys=True, separators=(",", ":")).encode()
    report["report_sha256"] = hashlib.sha256(encoded).hexdigest()
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--frontier-dir", type=Path)
    args = parser.parse_args()
    report = run(
        args.output.resolve(),
        None if args.frontier_dir is None else args.frontier_dir.resolve(),
    )
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0 if report["verdict"] == "green" else 1


if __name__ == "__main__":
    raise SystemExit(main())
