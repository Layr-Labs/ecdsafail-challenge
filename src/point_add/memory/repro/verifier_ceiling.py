#!/usr/bin/env python3
"""Machine-check the absolute score floor implied by the trusted verifier.

The scorer has a numeric floor of zero. That floor becomes the exact attainable
minimum only when an official passing artifact scores zero; until then this
program reports an open lower/upper interval instead of inventing a circuit
lower bound that the verifier does not establish.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

try:
    from exact_scorer import score, score_from_totals
    from world_model import CURRENT_FRONTIER, FULL_VERIFICATION_SHOTS
except ModuleNotFoundError:
    from .exact_scorer import score, score_from_totals
    from .world_model import CURRENT_FRONTIER, FULL_VERIFICATION_SHOTS

PINNED_TRUSTED_SHA256 = {
    "src/bin/eval_circuit.rs": "b35314bc47a5f8eecbf60459e6c76c9b43aa034eeb9b7ec3421655d74f9e890b",
    "src/sim.rs": "f0c72f2a280cd68acee1dbf8282098f72d6b3bf4311e0abf96d122fe002256d7",
    "src/circuit.rs": "ac2255f6bcb6895c9da2dfe21c3a051a0ef8fc4e0af9598634fec0035dbf35c6",
    "src/point_add/memory/repro/exact_scorer.py": "03895414b4b5c8fc8951747593a260292e8ba75a46a298c097d24d781e6f0b8a",
    "benchmark.sh": "1f963341bfbe3d052d904c7cc5ff9d67ca9df5c98ef623092635971e18f4f941",
    "benchmark.json": "8e7cd12214e6ed93932ef1a01e89f92836905d4f1ebc708a217dd7fe7f87ba0c",
}
INTENDED_OUTPUT_QUBITS = 2 * 256
ABSOLUTE_SCORE_FLOOR = 0
ZERO_SCORE_MAX_TOTAL_TOFFOLI = (FULL_VERIFICATION_SHOTS - 1) // 2


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _check(name: str, condition: bool, detail: str) -> dict[str, Any]:
    return {"name": name, "green": condition, "detail": detail}


def verify_bounds(repo: Path, score_path: Path | None = None) -> dict[str, Any]:
    checks: list[dict[str, Any]] = []
    observed_hashes: dict[str, str] = {}
    for relative, expected in PINNED_TRUSTED_SHA256.items():
        actual = _sha256(repo / relative)
        observed_hashes[relative] = actual
        checks.append(
            _check(
                f"trusted_hash:{relative}",
                actual == expected,
                f"expected={expected}:actual={actual}",
            )
        )

    score_at_zero = score_from_totals(0, FULL_VERIFICATION_SHOTS, INTENDED_OUTPUT_QUBITS)
    score_at_zero_boundary = score_from_totals(
        ZERO_SCORE_MAX_TOTAL_TOFFOLI,
        FULL_VERIFICATION_SHOTS,
        INTENDED_OUTPUT_QUBITS,
    )
    score_after_boundary = score_from_totals(
        ZERO_SCORE_MAX_TOTAL_TOFFOLI + 1,
        FULL_VERIFICATION_SHOTS,
        INTENDED_OUTPUT_QUBITS,
    )
    checks.extend(
        (
            _check(
                "nonnegative_product_floor",
                score_at_zero == ABSOLUTE_SCORE_FLOOR,
                f"score(total=0)={score_at_zero}",
            ),
            _check(
                "rounding_zero_boundary",
                score_at_zero_boundary == ABSOLUTE_SCORE_FLOOR,
                (
                    f"total={ZERO_SCORE_MAX_TOTAL_TOFFOLI}:"
                    f"score={score_at_zero_boundary}"
                ),
            ),
            _check(
                "rounding_positive_after_boundary",
                score_after_boundary == INTENDED_OUTPUT_QUBITS,
                (
                    f"total={ZERO_SCORE_MAX_TOTAL_TOFFOLI + 1}:"
                    f"score={score_after_boundary}"
                ),
            ),
            _check(
                "current_frontier_score",
                score(
                    float(CURRENT_FRONTIER.rounded_toffoli),
                    CURRENT_FRONTIER.qubits,
                )
                == CURRENT_FRONTIER.score,
                f"score={CURRENT_FRONTIER.score}",
            ),
        )
    )

    candidate_score: int | None = None
    if score_path is not None and score_path.exists():
        score_payload = json.loads(score_path.read_text(encoding="utf-8"))
        candidate_score = score_payload.get("score")
        checks.append(
            _check(
                "candidate_score_is_nonnegative_integer",
                type(candidate_score) is int and candidate_score >= 0,
                f"candidate_score={candidate_score}",
            )
        )

    mechanics_green = all(check["green"] for check in checks)
    attained = mechanics_green and candidate_score == ABSOLUTE_SCORE_FLOOR
    upper_bound = (
        candidate_score
        if type(candidate_score) is int and candidate_score >= 0
        else CURRENT_FRONTIER.score
    )
    return {
        "model": "eval_circuit.rs::write_score absolute floor",
        "verdict": "green" if mechanics_green else "red",
        "achievability_status": "attained_by_supplied_score" if attained else "lower_bound_only",
        "absolute_score_lower_bound": ABSOLUTE_SCORE_FLOOR,
        "best_witness_upper_bound": upper_bound,
        "open_score_gap": upper_bound - ABSOLUTE_SCORE_FLOOR,
        "full_verification_shots": FULL_VERIFICATION_SHOTS,
        "zero_score_condition": {
            "maximum_total_executed_toffoli": ZERO_SCORE_MAX_TOTAL_TOFFOLI,
            "strict_average_upper_bound": 0.5,
        },
        "intended_distinct_output_qubits": INTENDED_OUTPUT_QUBITS,
        "attained": attained,
        "trusted_sha256": observed_hashes,
        "checks": checks,
        "scope_warning": (
            "The trusted verifier supplies no nontrivial global Toffoli lower bound. "
            "Zero is a proved scorer floor, not an attained circuit bound without an official witness."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true", help="exit nonzero if a pinned premise fails")
    parser.add_argument("--json", action="store_true", help="emit compact JSON")
    parser.add_argument(
        "--score-json",
        type=Path,
        help="optional trusted score.json witness; defaults to the repository score.json",
    )
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[4]
    score_path = args.score_json if args.score_json is not None else repo / "score.json"
    report = verify_bounds(repo, score_path)
    print(json.dumps(report, sort_keys=True, indent=None if args.json else 2))
    return int(args.verify and report["verdict"] != "green")


if __name__ == "__main__":
    raise SystemExit(main())
