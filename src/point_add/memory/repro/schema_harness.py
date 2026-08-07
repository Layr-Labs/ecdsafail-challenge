#!/usr/bin/env python3
"""Content-addressed predict/observe loop for ECDSA Fail research.

The harness records reality; it does not edit source or certify circuits. Every
research iteration starts with one preregistered prediction and must receive an
observation before another iteration can begin. Hash-chain backtesting, niche
portfolio selection, mismatch reframing, and ten-iteration checkpoints keep the
loop auditable without installing a second controller.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from collections import Counter
from collections.abc import Mapping
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    from artifact_io import fingerprint
    from exact_scorer import score
    from world_model import (
        CURRENT_FRONTIER,
        ActionKind,
        EvidenceKind,
        InstrumentSet,
        action_impact,
    )
except ModuleNotFoundError:
    from .artifact_io import fingerprint
    from .exact_scorer import score
    from .world_model import (
        CURRENT_FRONTIER,
        ActionKind,
        EvidenceKind,
        InstrumentSet,
        action_impact,
    )

SCHEMA_VERSION = 1
MAX_ITERATIONS = 500
ZERO_HASH = "0" * 64
NICHES = {
    "H0-zero-rounding": "verifier-specific construction crossing the zero-score rounding boundary",
    "H1-gcd-apply": "GCD/apply traversal and controlled arithmetic",
    "H2-square": "reversible modular square",
    "H3-coordinate-shell": "classical-offset coordinate shell and source invariants",
    "H4-postpasses": "exact postpasses, strip provenance, and calibration",
    "H5-width": "peak-qubit schedule, cap, or complete alternative representation",
}
_RECORD_TYPES = {
    "frontier",
    "prediction",
    "observation",
    "candidate",
    "reframe",
    "submission",
    "checkpoint",
}
_OBSERVATION_VERDICTS = {"pass", "fail", "no_effect", "inconclusive", "error"}
_CANDIDATE_STATUSES = {"live", "promoted", "retired"}


def _canonical_json(value: Mapping[str, Any]) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")


def _hash_record(record: Mapping[str, Any]) -> str:
    material = {key: value for key, value in record.items() if key != "record_sha256"}
    return hashlib.sha256(_canonical_json(material)).hexdigest()


def _require_text(row: Mapping[str, Any], key: str) -> str:
    value = row.get(key)
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{key} must be a non-empty string")
    return value


def _require_int(row: Mapping[str, Any], key: str, *, minimum: int = 0) -> int:
    value = row.get(key)
    if type(value) is not int or value < minimum:
        raise ValueError(f"{key} must be an integer >= {minimum}")
    return value


def _require_number(row: Mapping[str, Any], key: str, *, nonnegative: bool = False) -> float:
    value = row.get(key)
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"{key} must be a finite number")
    result = float(value)
    if not math.isfinite(result) or (nonnegative and result < 0.0):
        raise ValueError(f"{key} must be {'non-negative and ' if nonnegative else ''}finite")
    return result


def _require_sha256(row: Mapping[str, Any], key: str, *, optional: bool = False) -> str | None:
    value = row.get(key)
    if value is None and optional:
        return None
    if not isinstance(value, str) or len(value) != 64:
        raise ValueError(f"{key} must be a SHA-256 digest")
    try:
        bytes.fromhex(value)
    except ValueError as error:
        raise ValueError(f"{key} must be hexadecimal") from error
    return value.lower()


def _payload(record: Mapping[str, Any]) -> dict[str, Any]:
    metadata = {
        "schema_version",
        "sequence",
        "recorded_at",
        "previous_sha256",
        "record_sha256",
    }
    return {key: value for key, value in record.items() if key not in metadata}


def load_ledger(path: Path) -> tuple[dict[str, Any], ...]:
    if not path.exists():
        return ()
    records: list[dict[str, Any]] = []
    previous = ZERO_HASH
    with path.open(encoding="utf-8") as source:
        for line_number, line in enumerate(source, start=1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"line {line_number}: record must be an object")
            if row.get("schema_version") != SCHEMA_VERSION:
                raise ValueError(f"line {line_number}: unsupported schema version")
            if row.get("sequence") != len(records):
                raise ValueError(f"line {line_number}: non-contiguous sequence")
            if row.get("previous_sha256") != previous:
                raise ValueError(f"line {line_number}: broken previous hash")
            actual = _hash_record(row)
            if row.get("record_sha256") != actual:
                raise ValueError(f"line {line_number}: record hash mismatch")
            records.append(row)
            previous = actual
    return tuple(records)


def _predictions(records: tuple[dict[str, Any], ...]) -> list[dict[str, Any]]:
    return [record for record in records if record.get("type") == "prediction"]


def _observations_for(records: tuple[dict[str, Any], ...], iteration: int) -> list[dict[str, Any]]:
    return [
        record
        for record in records
        if record.get("type") == "observation" and record.get("iteration") == iteration
    ]


def _last_mismatch_is_reframed(records: tuple[dict[str, Any], ...]) -> bool:
    mismatch_sequence = max(
        (
            record["sequence"]
            for record in records
            if record.get("type") == "observation" and record.get("prediction_match") is False
        ),
        default=-1,
    )
    if mismatch_sequence < 0:
        return True
    return any(
        record.get("type") == "reframe" and record["sequence"] > mismatch_sequence
        for record in records
    )


def _validate_frontier(payload: Mapping[str, Any], records: tuple[dict[str, Any], ...]) -> None:
    if records:
        raise ValueError("frontier can only initialize an empty ledger")
    if _require_int(payload, "iteration") != 0:
        raise ValueError("frontier iteration must be zero")
    _require_text(payload, "submission_id")
    _require_text(payload, "source_ref")
    _require_sha256(payload, "ops_sha256")
    _require_sha256(payload, "canonical_ops_sha256")
    _require_int(payload, "score")
    qubits = _require_int(payload, "qubits")
    rounded_toffoli = _require_int(payload, "rounded_toffoli")
    if score(float(rounded_toffoli), qubits) != payload["score"]:
        raise ValueError("frontier metrics do not reproduce its score")
    if _require_int(payload, "ceiling_score") != 0:
        raise ValueError("pinned verifier ceiling must be zero")
    if _require_int(payload, "max_iterations", minimum=1) != MAX_ITERATIONS:
        raise ValueError(f"max_iterations must be {MAX_ITERATIONS}")
    instruments = payload.get("instruments")
    if not isinstance(instruments, Mapping):
        raise ValueError("frontier requires instrument hashes")
    for key in ("verifier_sha256", "simulator_sha256", "scorer_sha256", "identity_sha256"):
        _require_sha256(instruments, key)


def _validate_prediction(payload: Mapping[str, Any], records: tuple[dict[str, Any], ...]) -> None:
    predictions = _predictions(records)
    iteration = _require_int(payload, "iteration", minimum=1)
    expected_iteration = len(predictions) + 1
    if iteration != expected_iteration:
        raise ValueError(f"prediction iteration must be {expected_iteration}")
    if iteration > MAX_ITERATIONS:
        raise ValueError(f"iteration cap {MAX_ITERATIONS} reached")
    if predictions and not _observations_for(records, iteration - 1):
        raise ValueError("previous prediction has no observation")
    if not _last_mismatch_is_reframed(records):
        raise ValueError("prediction mismatch requires a reframe before continuing")
    if iteration > 10 and (iteration - 1) // 10 > 0:
        checkpoint_iteration = ((iteration - 1) // 10) * 10
        if not any(
            record.get("type") == "checkpoint"
            and record.get("iteration") == checkpoint_iteration
            for record in records
        ):
            raise ValueError(f"missing checkpoint at iteration {checkpoint_iteration}")
    niche = _require_text(payload, "niche")
    if niche not in NICHES:
        raise ValueError(f"unknown niche {niche}")
    action_kind = ActionKind(_require_text(payload, "action_kind"))
    if action_kind is ActionKind.PROMOTION:
        raise ValueError("promotion cannot be a research prediction")
    _require_text(payload, "candidate_id")
    _require_text(payload, "parent_candidate_id")
    _require_sha256(payload, "parent_ops_sha256")
    _require_text(payload, "mechanism")
    delta_qubits = payload.get("delta_qubits")
    if type(delta_qubits) is not int:
        raise ValueError("delta_qubits must be an integer")
    delta_toffoli = _require_number(payload, "delta_toffoli_mean")
    _require_number(payload, "delta_toffoli_standard_deviation", nonnegative=True)
    _require_text(payload, "correctness_risk")
    full_verification_budget = _require_int(payload, "full_verification_budget")
    if action_kind is ActionKind.NO_EFFECT and (
        delta_qubits != 0 or delta_toffoli != 0.0 or full_verification_budget != 0
    ):
        raise ValueError("measurement-only predictions require zero deltas and zero full-run budget")
    expected_invalidations = payload.get("expected_invalidations")
    if not isinstance(expected_invalidations, list) or any(
        not isinstance(value, str) for value in expected_invalidations
    ):
        raise ValueError("expected_invalidations must be a string list")
    canonical = sorted(dependency.value for dependency in action_impact(action_kind).invalidated)
    if sorted(expected_invalidations) != canonical:
        raise ValueError(
            "prediction invalidations differ from the world model: "
            f"expected={canonical}:actual={sorted(expected_invalidations)}"
        )


def _prediction_for(
    records: tuple[dict[str, Any], ...], iteration: int
) -> dict[str, Any] | None:
    return next(
        (
            record
            for record in records
            if record.get("type") == "prediction" and record.get("iteration") == iteration
        ),
        None,
    )


def _validate_observation(payload: Mapping[str, Any], records: tuple[dict[str, Any], ...]) -> None:
    iteration = _require_int(payload, "iteration", minimum=1)
    prediction = _prediction_for(records, iteration)
    if prediction is None:
        raise ValueError(f"observation has no prediction for iteration {iteration}")
    observation_id = _require_text(payload, "observation_id")
    if any(
        record.get("type") == "observation" and record.get("observation_id") == observation_id
        for record in records
    ):
        raise ValueError(f"duplicate observation_id {observation_id}")
    stage = _require_text(payload, "stage")
    if stage not in {"hash", "proxy", "proof", "full", "submission"}:
        raise ValueError(f"unknown observation stage {stage}")
    EvidenceKind(_require_text(payload, "evidence_kind"))
    verdict = _require_text(payload, "verdict")
    if verdict not in _OBSERVATION_VERDICTS:
        raise ValueError(f"unknown observation verdict {verdict}")
    _require_text(payload, "conclusion")
    artifact_hash = _require_sha256(payload, "artifact_ops_sha256", optional=True)
    prediction_match = payload.get("prediction_match")
    if prediction_match is not None and type(prediction_match) is not bool:
        raise ValueError("prediction_match must be boolean or null")
    measurement = payload.get("measurement")
    if measurement is not None and not isinstance(measurement, Mapping):
        raise ValueError("measurement must be an object or null")
    if stage == "full":
        if artifact_hash is None:
            raise ValueError("full observation requires exact artifact hash")
        if payload["evidence_kind"] != EvidenceKind.TRUSTED_FULL.value:
            raise ValueError("full observation requires trusted full evidence")
        if not isinstance(measurement, Mapping):
            raise ValueError("full observation requires measurement")
        if _require_int(measurement, "shots") != 9_024:
            raise ValueError("full observation must contain 9,024 shots")
        for key in (
            "classical_failures",
            "phase_garbage_batches",
            "ancilla_garbage_batches",
        ):
            _require_int(measurement, key)
        _require_int(measurement, "qubits")
        _require_number(measurement, "average_toffoli", nonnegative=True)
        _require_int(measurement, "score")
        if artifact_hash == prediction["parent_ops_sha256"]:
            raise ValueError("full verification denied for byte-identical parent artifact")


def _validate_candidate(payload: Mapping[str, Any]) -> None:
    _require_int(payload, "iteration")
    _require_text(payload, "candidate_id")
    niche = _require_text(payload, "niche")
    if niche not in NICHES:
        raise ValueError(f"unknown niche {niche}")
    status = _require_text(payload, "status")
    if status not in _CANDIDATE_STATUSES:
        raise ValueError(f"unknown candidate status {status}")
    _require_text(payload, "parent_candidate_id")
    _require_text(payload, "evidence")
    _require_sha256(payload, "artifact_ops_sha256", optional=True)


def _validate_reframe(payload: Mapping[str, Any], records: tuple[dict[str, Any], ...]) -> None:
    iteration = _require_int(payload, "iteration", minimum=1)
    if _prediction_for(records, iteration) is None:
        raise ValueError("reframe requires an existing iteration")
    _require_text(payload, "claim")
    _require_text(payload, "compression")
    _require_text(payload, "forward_prediction")


def _validate_submission(payload: Mapping[str, Any]) -> None:
    _require_int(payload, "iteration", minimum=1)
    _require_text(payload, "submission_id")
    _require_text(payload, "source_ref")
    _require_sha256(payload, "artifact_ops_sha256")
    _require_text(payload, "status")
    _require_int(payload, "official_score")
    _require_text(payload, "outcome")


def _validate_checkpoint(payload: Mapping[str, Any], records: tuple[dict[str, Any], ...]) -> None:
    iteration = _require_int(payload, "iteration", minimum=10)
    if iteration % 10:
        raise ValueError("checkpoint iteration must be divisible by ten")
    _require_sha256(payload, "segment_tail_sha256")
    _require_sha256(payload, "summary_sha256")
    _require_text(payload, "summary_path")
    if not records or payload["segment_tail_sha256"] != records[-1]["record_sha256"]:
        raise ValueError("checkpoint tail hash does not match the ledger")


def validate_payload(payload: Mapping[str, Any], records: tuple[dict[str, Any], ...]) -> None:
    record_type = _require_text(payload, "type")
    if record_type not in _RECORD_TYPES:
        raise ValueError(f"unknown record type {record_type}")
    if record_type == "frontier":
        _validate_frontier(payload, records)
    elif not records or records[0].get("type") != "frontier":
        raise ValueError("ledger must start with a frontier record")
    elif record_type == "prediction":
        _validate_prediction(payload, records)
    elif record_type == "observation":
        _validate_observation(payload, records)
    elif record_type == "candidate":
        _validate_candidate(payload)
    elif record_type == "reframe":
        _validate_reframe(payload, records)
    elif record_type == "submission":
        _validate_submission(payload)
    elif record_type == "checkpoint":
        _validate_checkpoint(payload, records)


def append_payload(
    path: Path,
    payload: Mapping[str, Any],
    *,
    recorded_at: str | None = None,
) -> dict[str, Any]:
    records = load_ledger(path)
    validate_payload(payload, records)
    record = {
        "schema_version": SCHEMA_VERSION,
        "sequence": len(records),
        "recorded_at": recorded_at
        or datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z"),
        "previous_sha256": records[-1]["record_sha256"] if records else ZERO_HASH,
        **payload,
    }
    record["record_sha256"] = _hash_record(record)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as destination:
        destination.write(_canonical_json(record).decode("utf-8"))
        destination.write("\n")
        destination.flush()
        os.fsync(destination.fileno())
    return record


def initialize_ledger(path: Path, repo: Path) -> dict[str, Any]:
    if path.exists() and path.stat().st_size:
        raise ValueError(f"ledger already initialized: {path}")
    instruments = InstrumentSet.from_files(
        repo / "src/bin/eval_circuit.rs",
        repo / "src/sim.rs",
        repo / "src/point_add/memory/repro/exact_scorer.py",
    )
    artifact = fingerprint(repo / "ops.bin")
    if artifact["compressed_ops_sha256"] != CURRENT_FRONTIER.ops_sha256:
        raise ValueError("current ops.bin does not match the pinned frontier")
    return append_payload(
        path,
        {
            "type": "frontier",
            "iteration": 0,
            "submission_id": CURRENT_FRONTIER.submission_id,
            "source_ref": CURRENT_FRONTIER.source_ref,
            "ops_sha256": CURRENT_FRONTIER.ops_sha256,
            "canonical_ops_sha256": CURRENT_FRONTIER.canonical_ops_sha256,
            "score": CURRENT_FRONTIER.score,
            "qubits": CURRENT_FRONTIER.qubits,
            "rounded_toffoli": CURRENT_FRONTIER.rounded_toffoli,
            "ceiling_score": 0,
            "max_iterations": MAX_ITERATIONS,
            "instruments": {
                "verifier_sha256": instruments.verifier_sha256,
                "simulator_sha256": instruments.simulator_sha256,
                "scorer_sha256": instruments.scorer_sha256,
                "identity_sha256": instruments.identity_sha256,
            },
        },
    )


def select_niche(records: tuple[dict[str, Any], ...]) -> dict[str, Any]:
    counts = Counter(
        record["niche"] for record in records if record.get("type") == "prediction"
    )
    last_sequence = {
        niche: max(
            (
                record["sequence"]
                for record in records
                if record.get("type") == "prediction" and record.get("niche") == niche
            ),
            default=-1,
        )
        for niche in NICHES
    }
    selected = min(NICHES, key=lambda niche: (counts[niche], last_sequence[niche], niche))
    return {
        "selected_niche": selected,
        "description": NICHES[selected],
        "prediction_counts": dict(sorted((niche, counts[niche]) for niche in NICHES)),
    }


def backtest(records: tuple[dict[str, Any], ...]) -> dict[str, Any]:
    failures: list[str] = []
    if not records:
        failures.append("empty_ledger")
    elif records[0].get("type") != "frontier":
        failures.append("missing_initial_frontier")
    predictions = _predictions(records)
    for expected, prediction in enumerate(predictions, start=1):
        if prediction.get("iteration") != expected:
            failures.append(f"noncontiguous_prediction:{prediction.get('iteration')}")
        try:
            action_kind = ActionKind(prediction["action_kind"])
            canonical = sorted(
                dependency.value for dependency in action_impact(action_kind).invalidated
            )
            if sorted(prediction.get("expected_invalidations", [])) != canonical:
                failures.append(f"invalidation_mismatch:{expected}")
        except (KeyError, ValueError):
            failures.append(f"invalid_action_kind:{expected}")
        observations = _observations_for(records, expected)
        if expected < len(predictions) and not observations:
            failures.append(f"missing_observation:{expected}")
    completed = max(
        (iteration for iteration in range(1, len(predictions) + 1) if _observations_for(records, iteration)),
        default=0,
    )
    for checkpoint_iteration in range(10, completed + 1, 10):
        if not any(
            record.get("type") == "checkpoint"
            and record.get("iteration") == checkpoint_iteration
            for record in records
        ):
            failures.append(f"missing_checkpoint:{checkpoint_iteration}")
    if len(predictions) > MAX_ITERATIONS:
        failures.append("iteration_cap_exceeded")
    for record in records:
        if record.get("type") == "candidate" and record.get("niche") not in NICHES:
            failures.append(f"unknown_candidate_niche:{record.get('candidate_id')}")
    return {
        "model": "ECDSA Schema evidence loop",
        "verdict": "green" if not failures else "red",
        "records": len(records),
        "iterations_started": len(predictions),
        "iterations_completed": completed,
        "remaining_iterations": MAX_ITERATIONS - len(predictions),
        "tail_sha256": records[-1]["record_sha256"] if records else ZERO_HASH,
        "pending_iteration": (
            predictions[-1]["iteration"]
            if predictions and not _observations_for(records, predictions[-1]["iteration"])
            else None
        ),
        "failures": failures,
        "portfolio": select_niche(records),
    }


def checkpoint(path: Path, checkpoint_dir: Path, iteration: int) -> dict[str, Any]:
    records = load_ledger(path)
    if iteration % 10 or iteration < 10:
        raise ValueError("checkpoint iteration must be a positive multiple of ten")
    if any(
        record.get("type") == "checkpoint" and record.get("iteration") == iteration
        for record in records
    ):
        raise ValueError(f"checkpoint {iteration} already exists")
    completed = {
        record["iteration"]
        for record in records
        if record.get("type") == "observation"
    }
    if any(value not in completed for value in range(1, iteration + 1)):
        raise ValueError(f"cannot checkpoint before iterations 1..{iteration} are observed")
    verdicts = Counter(
        record["verdict"] for record in records if record.get("type") == "observation"
    )
    niches = Counter(
        record["niche"] for record in records if record.get("type") == "prediction"
    )
    live_candidates: dict[str, str] = {}
    for record in records:
        if record.get("type") != "candidate":
            continue
        if record["status"] == "live":
            live_candidates[record["candidate_id"]] = record["niche"]
        else:
            live_candidates.pop(record["candidate_id"], None)
    summary = {
        "schema_version": SCHEMA_VERSION,
        "iteration": iteration,
        "segment_tail_sha256": records[-1]["record_sha256"],
        "established": verdicts["pass"],
        "refuted": verdicts["fail"] + verdicts["no_effect"],
        "unresolved": verdicts["inconclusive"] + verdicts["error"],
        "niche_attempts": dict(sorted(niches.items())),
        "live_candidates": dict(sorted(live_candidates.items())),
        "next_portfolio": select_niche(records),
    }
    summary_bytes = _canonical_json(summary)
    summary_sha = hashlib.sha256(summary_bytes).hexdigest()
    checkpoint_dir.mkdir(parents=True, exist_ok=True)
    summary_path = checkpoint_dir / f"iteration-{iteration:04d}-{summary_sha[:12]}.json"
    if summary_path.exists():
        raise ValueError(f"checkpoint file already exists: {summary_path}")
    summary_path.write_bytes(summary_bytes + b"\n")
    record = append_payload(
        path,
        {
            "type": "checkpoint",
            "iteration": iteration,
            "segment_tail_sha256": summary["segment_tail_sha256"],
            "summary_sha256": summary_sha,
            "summary_path": str(summary_path),
        },
    )
    return {"record": record, "summary": summary}


def _read_payload(path: Path) -> Mapping[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, Mapping):
        raise ValueError("record JSON must be an object")
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--ledger",
        type=Path,
        default=Path(".autoresearch/measurements.jsonl"),
    )
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("init")
    append_parser = subparsers.add_parser("append")
    append_parser.add_argument("record_json", type=Path)
    subparsers.add_parser("backtest")
    subparsers.add_parser("status")
    subparsers.add_parser("select")
    checkpoint_parser = subparsers.add_parser("checkpoint")
    checkpoint_parser.add_argument("iteration", type=int)
    checkpoint_parser.add_argument(
        "--checkpoint-dir",
        type=Path,
        default=Path(".autoresearch/checkpoints"),
    )
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[4]

    try:
        if args.command == "init":
            output = initialize_ledger(args.ledger, repo)
        elif args.command == "append":
            output = append_payload(args.ledger, _read_payload(args.record_json))
        elif args.command == "backtest":
            output = backtest(load_ledger(args.ledger))
        elif args.command == "status":
            output = backtest(load_ledger(args.ledger))
        elif args.command == "select":
            output = select_niche(load_ledger(args.ledger))
        else:
            output = checkpoint(args.ledger, args.checkpoint_dir, args.iteration)
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as error:
        print(json.dumps({"verdict": "red", "error": str(error)}, sort_keys=True))
        return 1

    print(json.dumps(output, sort_keys=True))
    if args.command in {"backtest", "status"}:
        return 0 if output["verdict"] == "green" else 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
