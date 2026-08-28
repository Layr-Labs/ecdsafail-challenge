#!/usr/bin/env python3
"""Exact GF(2) rank test for zero-Toffoli affine point-add output bits.

For a pinned verifier operation stream, the first 9,024 SHAKE256-derived point
pairs are the complete correctness domain.  This instrument asks whether each
of the 512 required output-correction bits lies in the affine span of the 1,024
input bits.  A positive result is only finite-seed evidence because changing
the circuit changes the verifier seed; a negative result closes the direct
Clifford/affine shell on that pinned draw.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

try:
    from world_model import FULL_VERIFICATION_SHOTS
    from zero_score_lookup import _artifact_seed, _draw_dataset, _fixed_base_table
except ModuleNotFoundError:
    from .world_model import FULL_VERIFICATION_SHOTS
    from .zero_score_lookup import _artifact_seed, _draw_dataset, _fixed_base_table

COORDINATE_BITS = 256
FEATURE_BITS = 1 + 4 * COORDINATE_BITS
OUTPUT_BITS = 2 * COORDINATE_BITS
FEATURE_MASK = (1 << FEATURE_BITS) - 1


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb", buffering=0) as stream:
        while chunk := stream.read(8 * 1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def _packed_row(row: tuple[int, int, int, int, int, int]) -> int:
    target_x, target_y, offset_x, offset_y, result_x, result_y = row
    features = 1
    features |= target_x << 1
    features |= target_y << (1 + COORDINATE_BITS)
    features |= offset_x << (1 + 2 * COORDINATE_BITS)
    features |= offset_y << (1 + 3 * COORDINATE_BITS)
    correction = (result_x ^ target_x) | ((result_y ^ target_y) << COORDINATE_BITS)
    return features | (correction << FEATURE_BITS)


def reduce_dataset(
    dataset: list[tuple[int, int, int, int, int, int]],
) -> dict[str, Any]:
    basis: list[int | None] = [None] * FEATURE_BITS
    feature_rank = 0
    inconsistent_outputs = 0
    dependency_rows = 0

    for dataset_row in dataset:
        packed = _packed_row(dataset_row)
        while True:
            features = packed & FEATURE_MASK
            if features == 0:
                dependency_rows += 1
                inconsistent_outputs |= packed >> FEATURE_BITS
                break
            pivot = features.bit_length() - 1
            basis_row = basis[pivot]
            if basis_row is None:
                basis[pivot] = packed
                feature_rank += 1
                break
            packed ^= basis_row

    inconsistent_indices = [
        index for index in range(OUTPUT_BITS) if (inconsistent_outputs >> index) & 1
    ]
    exact_indices = [
        index for index in range(OUTPUT_BITS) if not (inconsistent_outputs >> index) & 1
    ]
    return {
        "rows": len(dataset),
        "feature_columns": FEATURE_BITS,
        "feature_rank": feature_rank,
        "dependency_rows": dependency_rows,
        "inconsistent_output_bits": len(inconsistent_indices),
        "exact_affine_output_bits": len(exact_indices),
        "exact_affine_output_indices": exact_indices,
    }


def inspect_artifact(path: Path, shots: int, powers: tuple[tuple[int, int], ...]) -> dict[str, Any]:
    shake, semantic_sha256, emitted_ops = _artifact_seed(path)
    dataset = _draw_dataset(shake, shots, powers)
    report = reduce_dataset(dataset)
    report.update(
        {
            "path": str(path),
            "artifact_sha256": _sha256(path),
            "canonical_semantic_sha256": semantic_sha256,
            "emitted_ops": emitted_ops,
        }
    )
    return report


def run(paths: list[Path], shots: int) -> dict[str, Any]:
    if shots <= 0:
        raise ValueError("shots must be positive")
    if not paths:
        raise ValueError("at least one ops artifact is required")
    powers = _fixed_base_table()
    artifacts = [inspect_artifact(path, shots, powers) for path in paths]
    return {
        "experiment": "affine output-correction rank",
        "shots_per_artifact": shots,
        "artifacts": artifacts,
        "all_output_bits_non_affine": all(
            artifact["exact_affine_output_bits"] == 0 for artifact in artifacts
        ),
        "verdict": "green",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ops", type=Path, action="append", required=True)
    parser.add_argument("--shots", type=int, default=FULL_VERIFICATION_SHOTS)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = run(args.ops, args.shots)
    print(json.dumps(report, sort_keys=True, indent=None if args.json else 2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
