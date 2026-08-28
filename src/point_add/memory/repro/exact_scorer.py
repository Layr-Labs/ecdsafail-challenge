#!/usr/bin/env python3
"""Exact model of eval_circuit.rs::write_score; not a replacement verifier."""

from __future__ import annotations

import argparse
import csv
import json
import math
from decimal import Decimal, ROUND_FLOOR
from pathlib import Path
from typing import Any

U64_MAX = (1 << 64) - 1
_U64_LIMIT_AS_FLOAT = float(1 << 64)
_LIVE_FRONTIER = {
    "average_toffoli": 1_291_859.302,
    "total_toffoli": 11_657_738_337,
    "shots": 9_024,
    "qubits": 1_154,
    "score": 1_490_805_286,
}


def _require_u64(name: str, value: int) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an int")
    if value < 0 or value > U64_MAX:
        raise ValueError(f"{name} must be in [0, 2**64 - 1]")
    return value


def _require_verifier_float(name: str, value: float) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise TypeError(f"{name} must be a real number")
    result = float(value)
    if not math.isfinite(result) or result < 0.0 or result >= _U64_LIMIT_AS_FLOAT:
        raise ValueError(f"{name} must be finite and in [0, 2**64 - 1]")
    return result


def score(avg_toffoli: float, qubits: int) -> int:
    """Return Rust's rounded-Toffoli × qubits score with u64 saturation."""
    average = _require_verifier_float("avg_toffoli", avg_toffoli)
    width = _require_u64("qubits", qubits)
    rounded_toffoli = math.floor(average + 0.5)
    return min(rounded_toffoli * width, U64_MAX)


def score_from_totals(total_toffoli: int, shots: int, qubits: int) -> int:
    """Compute the score after the verifier's IEEE-754 totals/shots division."""
    total = _require_u64("total_toffoli", total_toffoli)
    sample_count = _require_u64("shots", shots)
    width = _require_u64("qubits", qubits)
    if sample_count == 0:
        raise ValueError("shots must be greater than zero")
    average = float(total) / float(sample_count)
    return score(average, width)


def backtest_results(path: Path) -> dict[str, Any]:
    """Replay every accepted results.tsv row against a decimal-text oracle."""
    checked: list[dict[str, Any]] = []
    failures: list[dict[str, Any]] = []
    with path.open(newline="", encoding="utf-8") as source:
        for line_number, row in enumerate(csv.DictReader(source, delimiter="\t"), start=2):
            if row["correct"] != "OK":
                continue
            average_text = row["toffoli"]
            qubits = int(row["qubits"])
            decimal_rounded = int(
                (Decimal(average_text) + Decimal("0.5")).to_integral_value(rounding=ROUND_FLOOR)
            )
            expected = min(decimal_rounded * qubits, U64_MAX)
            actual = score(float(average_text), qubits)
            result = {
                "line": line_number,
                "commit": row["commit"],
                "average_toffoli": average_text,
                "qubits": qubits,
                "expected": expected,
                "actual": actual,
            }
            checked.append(result)
            if actual != expected:
                failures.append(result)

    live_average_score = score(
        _LIVE_FRONTIER["average_toffoli"], _LIVE_FRONTIER["qubits"]
    )
    live_totals_score = score_from_totals(
        _LIVE_FRONTIER["total_toffoli"],
        _LIVE_FRONTIER["shots"],
        _LIVE_FRONTIER["qubits"],
    )
    if live_average_score != _LIVE_FRONTIER["score"] or live_totals_score != _LIVE_FRONTIER["score"]:
        failures.append(
            {
                "case": "live-frontier",
                "expected": _LIVE_FRONTIER["score"],
                "from_average": live_average_score,
                "from_totals": live_totals_score,
            }
        )

    return {
        "model": "eval_circuit.rs::write_score",
        "results_path": str(path),
        "ok_rows_checked": len(checked),
        "live_frontier": {
            **_LIVE_FRONTIER,
            "score_from_average": live_average_score,
            "score_from_totals": live_totals_score,
        },
        "failures": failures,
        "rows": checked,
        "verdict": "green" if not failures else "red",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--backtest", type=Path, required=True, metavar="RESULTS_TSV")
    parser.add_argument("--json", action="store_true", help="emit compact JSON")
    args = parser.parse_args()
    report = backtest_results(args.backtest)
    print(json.dumps(report, sort_keys=True, indent=None if args.json else 2))
    return 0 if report["verdict"] == "green" else 1


if __name__ == "__main__":
    raise SystemExit(main())
