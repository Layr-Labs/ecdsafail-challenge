#!/usr/bin/env python3
"""DGM-inspired, verifier-first search over the ECDSA Fail ledger.

This module deliberately does not embed the upstream Darwin Gödel Machine
runner.  It ports the two useful search mechanisms--an archive of stepping
stones and quality/underexploration parent selection--onto the existing
content-addressed Schema ledger and Git commits.

The ledger remains the evidence authority.  This file derives an archive,
selects a parent deterministically, preregisters a structured prediction, and
confines Codex mutations to a disposable worktree.  Only trusted verification
can promote a candidate.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import os
import random
import re
import shutil
import signal
import subprocess
import tempfile
from contextlib import contextmanager
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

import fcntl

try:
    from artifact_io import fingerprint
    from exact_scorer import score
    from schema_harness import (
        MAX_ITERATIONS,
        NICHES,
        append_payload,
        backtest,
        load_ledger,
        select_niche,
    )
    from world_model import (
        Action,
        ActionKind,
        Dependency,
        EvidenceKind,
        Frontier,
        InstrumentSet,
        Prediction,
        Candidate,
        Verification,
        action_impact,
        full_verification_gate,
        promotion_gate,
    )
except ModuleNotFoundError:
    from .artifact_io import fingerprint
    from .exact_scorer import score
    from .schema_harness import (
        MAX_ITERATIONS,
        NICHES,
        append_payload,
        backtest,
        load_ledger,
        select_niche,
    )
    from .world_model import (
        Action,
        ActionKind,
        Dependency,
        EvidenceKind,
        Frontier,
        InstrumentSet,
        Prediction,
        Candidate,
        Verification,
        action_impact,
        full_verification_gate,
        promotion_gate,
    )


DGM_UPSTREAM_URL = "https://github.com/jennyzzt/dgm.git"
DGM_UPSTREAM_REVISION = "a565fd2d1dca504ef5104a7cc0f3bdc4ab9b4fd2"
CANDIDATE_REF_PREFIX = "refs/autoresearch/candidates"
DEFAULT_LEDGER = Path(".autoresearch/measurements.jsonl")
DEFAULT_ARCHIVE = Path(".autoresearch/index/dgm_archive.json")
DEFAULT_ATTEMPTS = Path(".autoresearch/attempts")
DEFAULT_WORKTREES = Path(".autoresearch/worktrees")
SHOT_LADDER = (512, 2_048, 8_192, 9_024)
FULL_SHOTS = SHOT_LADDER[-1]
WORST_SCORE = float((1 << 64) - 1)
ALLOWED_MUTATION_ROOT = Path("src/point_add")
ALLOWED_MUTATION_SUFFIXES = {".rs"}
EMITTERS = ("refiner", "recombiner", "literature", "cold-start", "abductor")
_FRONTIER_NICHE = "__frontier__"
_CANDIDATE_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,95}$")
_SECRET_MARKERS = (
    "API_KEY",
    "AUTH",
    "BEARER",
    "COOKIE",
    "CREDENTIAL",
    "PASSWORD",
    "PRIVATE_KEY",
    "SECRET",
    "SESSION",
    "TOKEN",
)
_DANGEROUS_ENV = {
    "BASH_ENV",
    "CDPATH",
    "DYLD_INSERT_LIBRARIES",
    "ENV",
    "GIT_CONFIG_COUNT",
    "GIT_CONFIG_GLOBAL",
    "GIT_CONFIG_SYSTEM",
    "LD_PRELOAD",
    "NODE_OPTIONS",
    "PYTHONPATH",
    "PYTHONSTARTUP",
    "RUSTC_WRAPPER",
}
_PROXY_ENV = {
    "ALL_PROXY",
    "FTP_PROXY",
    "HTTPS_PROXY",
    "HTTP_PROXY",
    "NO_PROXY",
}

LITERATURE_TRANSFERS = (
    {
        "paper": "arXiv:2607.13816",
        "use": (
            "Exact reversible EEA, register sharing, length/location controls, "
            "active windows, and measurement-based uncomputation are mechanism "
            "donors for H1/H5. Re-prove every specialized block in this ABI."
        ),
        "boundary": (
            "Its ECDLP/Shor point-add stack is not this classical-offset map. "
            "Only operations expressible by this verifier's Hmr and classical "
            "condition stack are candidates; no unsupported feed-forward."
        ),
    },
    {
        "paper": "arXiv:2606.02235",
        "use": (
            "Qarton supplies secp256k1 pseudo-Mersenne reduction structure and "
            "CDKM/Gidney scheduling ideas for H1/H2/H5."
        ),
        "boundary": (
            "Published approximate, MSB-only, probabilistic, or classical-block "
            "shortcuts are hypotheses only. This benchmark requires exact "
            "gate-level 9,024/9,024 verification."
        ),
    },
)

_PROPOSAL_SCHEMA: dict[str, Any] = {
    "type": "object",
    "additionalProperties": False,
    "required": [
        "candidate_id",
        "action_kind",
        "mechanism",
        "delta_qubits",
        "delta_toffoli_mean",
        "delta_toffoli_standard_deviation",
        "correctness_risk",
        "full_verification_budget",
        "mutation_instructions",
        "falsifier",
    ],
    "properties": {
        "candidate_id": {"type": "string", "minLength": 1, "maxLength": 96},
        "action_kind": {
            "type": "string",
            "enum": [
                ActionKind.NONCE_ONLY.value,
                ActionKind.EXACT_REWRITE.value,
                ActionKind.GEOMETRY.value,
                ActionKind.RISK_OR_STRIP_BUDGET.value,
                ActionKind.REPRESENTATION.value,
            ],
        },
        "mechanism": {"type": "string", "minLength": 1},
        "delta_qubits": {"type": "integer"},
        "delta_toffoli_mean": {"type": "number"},
        "delta_toffoli_standard_deviation": {
            "type": "number",
            "minimum": 0,
        },
        "correctness_risk": {"type": "string", "minLength": 1},
        "full_verification_budget": {"type": "integer", "minimum": 0, "maximum": 1},
        "mutation_instructions": {"type": "string", "minLength": 1},
        "falsifier": {"type": "string", "minLength": 1},
    },
}

_REFRAME_SCHEMA: dict[str, Any] = {
    "type": "object",
    "additionalProperties": False,
    "required": ["claim", "compression", "forward_prediction"],
    "properties": {
        "claim": {"type": "string", "minLength": 1},
        "compression": {"type": "string", "minLength": 1},
        "forward_prediction": {"type": "string", "minLength": 1},
    },
}

_PATCH_SCHEMA: dict[str, Any] = {
    "type": "object",
    "additionalProperties": False,
    "required": ["patch", "summary"],
    "properties": {
        "patch": {"type": "string", "minLength": 1},
        "summary": {"type": "string", "minLength": 1},
    },
}


@dataclass(frozen=True, slots=True)
class Metrics:
    average_toffoli: float
    qubits: int

    @property
    def score(self) -> int:
        return score(self.average_toffoli, self.qubits)


@dataclass(frozen=True, slots=True)
class ArchiveNode:
    candidate_id: str
    parent_candidate_id: str | None
    niche: str
    iteration: int
    status: str
    frontier_submission_id: str
    source_ref: str | None
    artifact_ops_sha256: str | None
    canonical_artifact_sha256: str | None
    actual_score: int | None
    average_toffoli: float | None
    qubits: int | None
    emitted_ops: int | None
    predicted_score: float
    prediction_standard_deviation: float
    conservative_score: float
    functioning: bool
    reproducible: bool
    functioning_children: int = 0
    emitter: str | None = None
    evidence: str | None = None

    def to_mapping(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True, slots=True)
class ParentChoice:
    node: ArchiveNode
    niche: str
    iteration: int
    ledger_tail_sha256: str
    seed: int
    rank_percentile: float
    quality: float
    weight: float
    probability: float

    def to_mapping(self) -> dict[str, Any]:
        result = asdict(self)
        result["node"] = self.node.to_mapping()
        return result


@dataclass(frozen=True, slots=True)
class StageResult:
    stage: str
    passed: bool
    conclusion: str
    evidence_kind: str
    artifact_ops_sha256: str | None
    canonical_artifact_sha256: str | None
    measurement: dict[str, Any] | None


@dataclass(frozen=True, slots=True)
class PublicFrontier:
    submission_id: str
    source_ref: str
    score: int
    qubits: int
    rounded_toffoli: int


_ANSI_ESCAPE = re.compile(r"\x1b\[[0-9;]*m")
_PUBLIC_ROW = re.compile(
    r"^([0-9a-f]{7})\s+.*?\s+promoted\s+([0-9]+)\s+"
    r'\{"qubits":([0-9]+),"toffoli":([0-9]+)\}.*?\s+'
    r"([0-9a-f]{7,40})\s+[0-9]+/[0-9]+/[0-9]+",
)


def repo_root() -> Path:
    return Path(__file__).resolve().parents[4]


def _records_of_type(
    records: Sequence[Mapping[str, Any]], record_type: str
) -> list[Mapping[str, Any]]:
    return [record for record in records if record.get("type") == record_type]


def _latest_by(
    records: Iterable[Mapping[str, Any]], key: str
) -> dict[Any, Mapping[str, Any]]:
    latest: dict[Any, Mapping[str, Any]] = {}
    for record in records:
        value = record.get(key)
        if value is not None:
            latest[value] = record
    return latest


def _frontier_id(frontier: Mapping[str, Any]) -> str:
    return f"{str(frontier['source_ref'])[:7]}-frontier"


def _clean_full_observation(record: Mapping[str, Any]) -> bool:
    if (
        record.get("type") != "observation"
        or record.get("stage") != "full"
        or record.get("verdict") != "pass"
    ):
        return False
    measurement = record.get("measurement")
    if not isinstance(measurement, Mapping):
        return False
    try:
        exact_score = score(
            float(measurement["average_toffoli"]),
            int(measurement["qubits"]),
        )
    except (KeyError, TypeError, ValueError):
        return False
    return (
        measurement.get("shots") == FULL_SHOTS
        and measurement.get("score") == exact_score
        and all(
            measurement.get(key) == 0
            for key in (
                "classical_failures",
                "phase_garbage_batches",
                "ancilla_garbage_batches",
            )
        )
    )


def _full_observations(
    records: Sequence[Mapping[str, Any]],
) -> dict[int, Mapping[str, Any]]:
    result: dict[int, Mapping[str, Any]] = {}
    for record in records:
        if record.get("type") == "observation" and record.get("stage") == "full":
            result[int(record["iteration"])] = record
    return result


def _submission_by_iteration(
    records: Sequence[Mapping[str, Any]],
) -> dict[int, Mapping[str, Any]]:
    result: dict[int, Mapping[str, Any]] = {}
    for record in _records_of_type(records, "submission"):
        if record.get("status") == "promoted":
            result[int(record["iteration"])] = record
    return result


def build_archive(
    records: Sequence[Mapping[str, Any]],
    *,
    repo: Path | None = None,
) -> tuple[ArchiveNode, ...]:
    """Rebuild the complete stepping-stone archive from ledger records."""
    if not records or records[0].get("type") != "frontier":
        raise ValueError("archive requires a ledger beginning with frontier")
    frontier = records[0]
    root_id = _frontier_id(frontier)
    root_metrics = Metrics(
        average_toffoli=float(frontier["rounded_toffoli"]),
        qubits=int(frontier["qubits"]),
    )
    latest_candidates = _latest_by(
        _records_of_type(records, "candidate"), "candidate_id"
    )
    predictions = _latest_by(
        _records_of_type(records, "prediction"), "candidate_id"
    )
    predictions_by_iteration = {
        int(record["iteration"]): record
        for record in _records_of_type(records, "prediction")
    }
    candidate_ids_by_iteration: dict[int, set[str]] = {}
    for candidate_id, candidate in latest_candidates.items():
        candidate_ids_by_iteration.setdefault(int(candidate["iteration"]), set()).add(
            str(candidate_id)
        )
    observations = _full_observations(records)
    submissions = _submission_by_iteration(records)

    candidate_ids = set(predictions) | set(latest_candidates)
    parent_ids = {
        str(record.get("parent_candidate_id"))
        for record in (*predictions.values(), *latest_candidates.values())
        if record.get("parent_candidate_id")
    }
    unresolved_parent_ids = sorted(parent_ids - candidate_ids - {root_id})
    root = ArchiveNode(
            candidate_id=root_id,
            parent_candidate_id=None,
            niche=_FRONTIER_NICHE,
            iteration=0,
            status="promoted",
            frontier_submission_id=str(frontier["submission_id"]),
            source_ref=str(frontier["source_ref"]),
            artifact_ops_sha256=str(frontier["ops_sha256"]),
            canonical_artifact_sha256=str(frontier["canonical_ops_sha256"]),
            actual_score=int(frontier["score"]),
            average_toffoli=root_metrics.average_toffoli,
            qubits=root_metrics.qubits,
            emitted_ops=None,
            predicted_score=float(frontier["score"]),
            prediction_standard_deviation=0.0,
            conservative_score=float(frontier["score"]),
            functioning=True,
            reproducible=(
                repo is None or _ref_commit(repo, str(frontier["source_ref"])) is not None
            ),
            evidence="initial trusted frontier",
        )
    metrics: dict[str, Metrics] = {root_id: root_metrics}
    nodes: dict[str, ArchiveNode] = {root_id: root}
    for alias in unresolved_parent_ids:
        nodes[alias] = ArchiveNode(
            candidate_id=alias,
            parent_candidate_id=None,
            niche=_FRONTIER_NICHE,
            iteration=0,
            status="retired",
            frontier_submission_id=str(frontier["submission_id"]),
            source_ref=None,
            artifact_ops_sha256=None,
            canonical_artifact_sha256=None,
            actual_score=None,
            average_toffoli=None,
            qubits=None,
            emitted_ops=None,
            predicted_score=WORST_SCORE,
            prediction_standard_deviation=WORST_SCORE,
            conservative_score=WORST_SCORE,
            functioning=False,
            reproducible=False,
            evidence="unresolved external parent placeholder",
        )

    unresolved = set(candidate_ids)
    while unresolved:
        progressed = False
        for candidate_id in sorted(unresolved):
            prediction = predictions.get(candidate_id)
            candidate = latest_candidates.get(candidate_id)
            inherited_prediction = (
                predictions_by_iteration.get(int(candidate["iteration"]))
                if candidate is not None
                else None
            )
            model_prediction = prediction or inherited_prediction
            source = candidate or prediction
            if source is None:
                unresolved.remove(candidate_id)
                progressed = True
                continue
            parent_id = str(source.get("parent_candidate_id") or root_id)
            parent_metrics = metrics.get(parent_id)
            if parent_metrics is None and parent_id in unresolved:
                continue
            if parent_metrics is None:
                parent_metrics = root_metrics

            iteration = int(
                source.get(
                    "iteration",
                    model_prediction.get("iteration", 0) if model_prediction else 0,
                )
            )
            retained_ids = candidate_ids_by_iteration.get(iteration, set())
            owns_iteration_evidence = candidate is not None or not retained_ids
            full = observations.get(iteration) if owns_iteration_evidence else None
            submission = submissions.get(iteration) if owns_iteration_evidence else None
            actual_metrics: Metrics | None = None
            actual_score: int | None = None
            if full is not None and isinstance(full.get("measurement"), Mapping):
                measurement = full["measurement"]
                if "average_toffoli" in measurement and "qubits" in measurement:
                    actual_metrics = Metrics(
                        float(measurement["average_toffoli"]),
                        int(measurement["qubits"]),
                    )
                    actual_score = int(measurement.get("score", actual_metrics.score))
            if candidate is not None and all(
                key in candidate
                for key in ("actual_average_toffoli", "actual_qubits", "actual_score")
            ):
                actual_metrics = Metrics(
                    float(candidate["actual_average_toffoli"]),
                    int(candidate["actual_qubits"]),
                )
                actual_score = int(candidate["actual_score"])
            if submission is not None:
                actual_score = int(submission["official_score"])

            predicted_metrics = parent_metrics
            conservative = float(parent_metrics.score)
            predicted_score = float(parent_metrics.score)
            predicted_sigma = 0.0
            if model_prediction is not None:
                predicted_metrics = Metrics(
                    max(
                        0.0,
                        parent_metrics.average_toffoli
                        + float(model_prediction["delta_toffoli_mean"]),
                    ),
                    max(
                        0,
                        parent_metrics.qubits
                        + int(model_prediction["delta_qubits"]),
                    ),
                )
                upper_metrics = Metrics(
                    max(
                        0.0,
                        predicted_metrics.average_toffoli
                        + 2.0
                        * float(
                            model_prediction["delta_toffoli_standard_deviation"]
                        ),
                    ),
                    predicted_metrics.qubits,
                )
                predicted_score = float(predicted_metrics.score)
                conservative = float(upper_metrics.score)
                predicted_sigma = max(0.0, (conservative - predicted_score) / 2.0)
            if actual_metrics is not None:
                metrics[candidate_id] = actual_metrics
                predicted_score = float(actual_score if actual_score is not None else actual_metrics.score)
                conservative = predicted_score
                predicted_sigma = 0.0
            else:
                metrics[candidate_id] = predicted_metrics

            status = str(candidate.get("status", "retired") if candidate else "retired")
            functioning = (
                status == "promoted"
                or (full is not None and _clean_full_observation(full))
                or submission is not None
            )
            source_ref = None
            if candidate is not None and candidate.get("source_ref"):
                source_ref = str(candidate["source_ref"])
            elif submission is not None and submission.get("source_ref"):
                source_ref = str(submission["source_ref"])
            archived_ref = candidate_ref(str(candidate_id))
            reproducible = bool(
                repo is not None
                and (
                    _ref_commit(repo, archived_ref)
                    or (source_ref and _ref_commit(repo, source_ref))
                )
            )
            if repo is None:
                reproducible = bool(source_ref)
            node = ArchiveNode(
                candidate_id=str(candidate_id),
                parent_candidate_id=parent_id,
                niche=str(source.get("niche", _FRONTIER_NICHE)),
                iteration=iteration,
                status=status,
                frontier_submission_id=(
                    str(submission["submission_id"])
                    if submission is not None
                    else (
                        str(candidate["official_submission_id"])
                        if candidate is not None
                        and candidate.get("official_submission_id")
                        else (
                            str(candidate["parent_frontier_submission_id"])
                            if candidate is not None
                            and candidate.get("parent_frontier_submission_id")
                            else nodes.get(parent_id, root).frontier_submission_id
                        )
                    )
                ),
                source_ref=source_ref,
                artifact_ops_sha256=(
                    str(candidate["artifact_ops_sha256"])
                    if candidate is not None and candidate.get("artifact_ops_sha256")
                    else (
                        str(full["artifact_ops_sha256"])
                        if full is not None and full.get("artifact_ops_sha256")
                        else None
                    )
                ),
                canonical_artifact_sha256=(
                    str(candidate["canonical_artifact_sha256"])
                    if candidate is not None
                    and candidate.get("canonical_artifact_sha256")
                    else None
                ),
                actual_score=actual_score,
                average_toffoli=metrics[candidate_id].average_toffoli,
                qubits=metrics[candidate_id].qubits,
                emitted_ops=(
                    int(candidate["emitted_ops"])
                    if candidate is not None and candidate.get("emitted_ops") is not None
                    else None
                ),
                predicted_score=predicted_score,
                prediction_standard_deviation=predicted_sigma,
                conservative_score=conservative,
                functioning=functioning,
                reproducible=reproducible,
                emitter=(
                    str(candidate["emitter"])
                    if candidate is not None and candidate.get("emitter")
                    else None
                ),
                evidence=(
                    str(candidate["evidence"])
                    if candidate is not None and candidate.get("evidence")
                    else None
                ),
            )
            nodes[candidate_id] = node
            unresolved.remove(candidate_id)
            progressed = True
        if not progressed:
            # A malformed lineage must remain inspectable rather than hanging.
            for candidate_id in sorted(unresolved):
                prediction = predictions.get(candidate_id)
                candidate = latest_candidates.get(candidate_id)
                source = candidate or prediction or {}
                nodes[candidate_id] = ArchiveNode(
                    candidate_id=str(candidate_id),
                    parent_candidate_id=(
                        str(source["parent_candidate_id"])
                        if source.get("parent_candidate_id")
                        else root_id
                    ),
                    niche=str(source.get("niche", _FRONTIER_NICHE)),
                    iteration=int(source.get("iteration", 0)),
                    status=str(source.get("status", "retired")),
                    frontier_submission_id=root.frontier_submission_id,
                    source_ref=None,
                    artifact_ops_sha256=None,
                    canonical_artifact_sha256=None,
                    actual_score=None,
                    average_toffoli=None,
                    qubits=None,
                    emitted_ops=None,
                    predicted_score=float(frontier["score"]),
                    prediction_standard_deviation=0.0,
                    conservative_score=float(frontier["score"]),
                    functioning=False,
                    reproducible=False,
                    evidence="unresolved lineage",
                )
            break

    child_counts: dict[str, int] = {}
    for node in nodes.values():
        if node.functioning and node.reproducible and node.parent_candidate_id is not None:
            child_counts[node.parent_candidate_id] = (
                child_counts.get(node.parent_candidate_id, 0) + 1
            )
    return tuple(
        replace(node, functioning_children=child_counts.get(node.candidate_id, 0))
        for node in sorted(nodes.values(), key=lambda item: (item.iteration, item.candidate_id))
    )


def selection_seed(iteration: int, ledger_tail_sha256: str) -> int:
    material = f"dgm-search-v1:{iteration}:{ledger_tail_sha256}".encode()
    return int.from_bytes(hashlib.sha256(material).digest()[:16], "big")


def select_emitter(
    records: Sequence[Mapping[str, Any]],
    *,
    iteration: int,
    ledger_tail_sha256: str,
) -> dict[str, Any]:
    if iteration == 63:
        return {"emitter": "literature", "reason": "first post-62 transfer"}
    last_observation = next(
        (
            record
            for record in reversed(records)
            if record.get("type") == "observation"
        ),
        None,
    )
    if last_observation is not None and last_observation.get("prediction_match") is False:
        return {"emitter": "abductor", "reason": "latest result mismatched prediction"}
    attempts = {emitter: 0 for emitter in EMITTERS}
    contributions = {emitter: 0 for emitter in EMITTERS}
    for record in _records_of_type(records, "candidate"):
        emitter = record.get("emitter")
        if emitter not in attempts:
            continue
        attempts[str(emitter)] += 1
        contributions[str(emitter)] += int(
            record.get("archive_contribution") is True
        )
    total = sum(attempts.values())
    scores: dict[str, float] = {}
    for emitter in EMITTERS:
        count = attempts[emitter]
        scores[emitter] = (
            math.inf
            if count == 0
            else contributions[emitter] / count
            + math.sqrt(2.0 * math.log(total + 1.0) / count)
        )
    best = max(scores.values())
    tied = sorted(emitter for emitter, value in scores.items() if value == best)
    index = selection_seed(iteration, ledger_tail_sha256) % len(tied)
    return {
        "emitter": tied[index],
        "reason": "UCB on archive-cell contribution",
        "attempts": attempts,
        "contributions": contributions,
        "ucb": {
            emitter: (None if math.isinf(value) else value)
            for emitter, value in scores.items()
        },
    }


def parent_distribution(
    nodes: Sequence[ArchiveNode],
    niche: str,
) -> tuple[tuple[ArchiveNode, float, float, float, float], ...]:
    """Return node, rank percentile, quality, weight, probability."""
    if niche not in NICHES:
        raise ValueError(f"unknown niche {niche}")
    # The portfolio chooses the problem niche; it does not erase useful
    # stepping stones from other cells. This also permits recombination from a
    # distant lineage while keeping the proposed mechanism targeted at `niche`.
    eligible = [
        node for node in nodes if node.functioning and node.reproducible
    ]
    if not eligible:
        raise ValueError(f"no functioning parent for niche {niche}")
    ranked = sorted(eligible, key=lambda node: (node.conservative_score, node.candidate_id))
    weighted: list[tuple[ArchiveNode, float, float, float]] = []
    denominator = max(1, len(ranked) - 1)
    for rank, node in enumerate(ranked):
        percentile = rank / denominator if len(ranked) > 1 else 0.0
        quality = math.exp(-2.0 * percentile)
        weight = (0.05 + quality) / (1.0 + node.functioning_children)
        weighted.append((node, percentile, quality, weight))
    total = sum(item[3] for item in weighted)
    return tuple((*item, item[3] / total) for item in weighted)


def choose_parent(
    nodes: Sequence[ArchiveNode],
    *,
    niche: str,
    iteration: int,
    ledger_tail_sha256: str,
) -> ParentChoice:
    distribution = parent_distribution(nodes, niche)
    seed = selection_seed(iteration, ledger_tail_sha256)
    draw = random.Random(seed).random()
    cumulative = 0.0
    selected = distribution[-1]
    for item in distribution:
        cumulative += item[4]
        if draw < cumulative:
            selected = item
            break
    node, percentile, quality, weight, probability = selected
    return ParentChoice(
        node=node,
        niche=niche,
        iteration=iteration,
        ledger_tail_sha256=ledger_tail_sha256,
        seed=seed,
        rank_percentile=percentile,
        quality=quality,
        weight=weight,
        probability=probability,
    )


def candidate_ref(candidate_id: str) -> str:
    if not _CANDIDATE_ID.fullmatch(candidate_id) or ".." in candidate_id:
        raise ValueError(f"candidate id is not safe for a Git ref: {candidate_id!r}")
    reference = f"{CANDIDATE_REF_PREFIX}/{candidate_id}"
    if subprocess.run(
        ["git", "check-ref-format", reference],
        capture_output=True,
    ).returncode:
        raise ValueError(f"candidate id is not a valid Git ref: {candidate_id!r}")
    return reference


def sanitized_environment(
    source: Mapping[str, str] | None = None,
) -> dict[str, str]:
    """Strip credentials and process-injection variables from child agents."""
    environment = dict(os.environ if source is None else source)
    for key in tuple(environment):
        upper = key.upper()
        if (
            key in _DANGEROUS_ENV
            or upper in _PROXY_ENV
            or any(marker in upper for marker in _SECRET_MARKERS)
        ):
            environment.pop(key, None)
    environment["CARGO_NET_OFFLINE"] = "true"
    return environment


def validate_mutation_paths(paths: Iterable[str]) -> tuple[str, ...]:
    """Reject every mutation outside Rust implementation files in point_add."""
    accepted: list[str] = []
    for raw in paths:
        path = Path(raw)
        if path.is_absolute() or ".." in path.parts:
            raise ValueError(f"unsafe mutation path: {raw}")
        if (
            not path.is_relative_to(ALLOWED_MUTATION_ROOT)
            or path.suffix not in ALLOWED_MUTATION_SUFFIXES
            or "memory" in path.parts
        ):
            raise ValueError(f"mutation escaped editable Rust surface: {raw}")
        accepted.append(path.as_posix())
    if not accepted:
        raise ValueError("mutation produced no editable Rust changes")
    return tuple(sorted(set(accepted)))


def validate_mutation_tree(worktree: Path, paths: Iterable[str]) -> tuple[str, ...]:
    accepted = validate_mutation_paths(paths)
    for raw in accepted:
        path = worktree / raw
        if path.is_symlink():
            raise ValueError(f"mutation created a symlink: {raw}")
        if path.exists() and not path.is_file():
            raise ValueError(f"mutation created a non-file path: {raw}")
    summary = _git_output(worktree, "diff", "--summary")
    if any(
        marker in summary
        for marker in ("mode change", "create mode 120000", "Subproject commit")
    ):
        raise ValueError(f"mutation changed file type or mode: {summary}")
    return accepted


def semantic_noop(
    artifact: Mapping[str, Any],
    *,
    parent_compressed_sha256: str,
    parent_canonical_sha256: str | None,
) -> bool:
    if parent_canonical_sha256:
        return artifact.get("canonical_semantic_sha256") == parent_canonical_sha256
    return artifact.get("compressed_ops_sha256") == parent_compressed_sha256


def validate_and_apply_patch(worktree: Path, patch: str) -> tuple[str, ...]:
    if len(patch.encode("utf-8")) > 2 * 1024 * 1024:
        raise ValueError("mutation patch exceeds 2 MiB")
    forbidden = (
        "GIT binary patch",
        "Binary files ",
        "old mode ",
        "new mode ",
        "similarity index ",
        "rename from ",
        "rename to ",
        "Subproject commit ",
    )
    if any(marker in patch for marker in forbidden):
        raise ValueError("mutation patch contains binary, mode, rename, or submodule data")
    headers = re.findall(r"^diff --git a/(\S+) b/(\S+)$", patch, flags=re.MULTILINE)
    if not headers:
        raise ValueError("mutation output is not a Git unified diff")
    header_paths: list[str] = []
    for before, after in headers:
        if before != after:
            raise ValueError("mutation patch may not rename files")
        header_paths.append(after)
    validate_mutation_paths(header_paths)
    for arguments in (("--check", "--whitespace=error-all"), ()):
        completed = subprocess.run(
            ["git", "-C", str(worktree), "apply", *arguments, "-"],
            input=patch,
            capture_output=True,
            text=True,
        )
        if completed.returncode:
            raise ValueError(f"git apply failed: {completed.stderr.strip()}")
    changed = _changed_paths(worktree)
    return validate_mutation_tree(worktree, changed)


def verify_upstream_clone(repo: Path) -> dict[str, Any]:
    clone = repo / ".autoresearch/upstream/dgm"
    if not clone.is_dir():
        raise ValueError(f"missing pinned DGM clone: {clone}")
    head = _git_output(clone, "rev-parse", "HEAD")
    origin = _git_output(clone, "remote", "get-url", "origin")
    if head != DGM_UPSTREAM_REVISION:
        raise ValueError(f"DGM revision mismatch: {head}")
    if origin.rstrip("/") != DGM_UPSTREAM_URL.rstrip("/"):
        raise ValueError(f"DGM origin mismatch: {origin}")
    return {"path": str(clone), "origin": origin, "revision": head, "verdict": "green"}


def _git_output(repo: Path, *arguments: str) -> str:
    completed = subprocess.run(
        ["git", "-C", str(repo), *arguments],
        check=True,
        capture_output=True,
        text=True,
    )
    return completed.stdout.strip()


def _ref_commit(repo: Path, reference: str) -> str | None:
    completed = subprocess.run(
        ["git", "-C", str(repo), "rev-parse", "--verify", "--quiet", f"{reference}^{{commit}}"],
        capture_output=True,
        text=True,
    )
    return completed.stdout.strip() or None


def resolve_parent_ref(repo: Path, node: ArchiveNode) -> str:
    archived = candidate_ref(node.candidate_id)
    if _ref_commit(repo, archived):
        return archived
    if node.source_ref and _ref_commit(repo, node.source_ref):
        return node.source_ref
    raise ValueError(
        f"parent {node.candidate_id} has no local candidate ref or resolvable source ref"
    )


def _best_score(records: Sequence[Mapping[str, Any]]) -> int:
    scores = [int(records[0]["score"])]
    scores.extend(
        int(record["official_score"])
        for record in _records_of_type(records, "submission")
        if record.get("status") == "promoted"
    )
    scores.extend(
        int(record["actual_score"])
        for record in _records_of_type(records, "candidate")
        if record.get("status") == "promoted"
        and record.get("official_submission_id")
        and record.get("actual_score") is not None
    )
    for record in records:
        if _clean_full_observation(record):
            measurement = record.get("measurement")
            if isinstance(measurement, Mapping) and "score" in measurement:
                scores.append(int(measurement["score"]))
    return min(scores)


def parse_public_frontier_table(output: str) -> PublicFrontier:
    rows: list[PublicFrontier] = []
    for raw in output.splitlines():
        line = _ANSI_ESCAPE.sub("", raw)
        match = _PUBLIC_ROW.match(line)
        if match is None:
            continue
        submission, raw_score, raw_qubits, raw_toffoli, source = match.groups()
        rows.append(
            PublicFrontier(
                submission_id=submission,
                source_ref=source,
                score=int(raw_score),
                qubits=int(raw_qubits),
                rounded_toffoli=int(raw_toffoli),
            )
        )
    if not rows:
        raise ValueError("could not parse any promoted public frontier rows")
    return min(rows, key=lambda row: (row.score, row.submission_id))


def refresh_public_frontier(repo: Path, *, timeout: int = 120) -> PublicFrontier:
    completed = _run_with_timeout(
        ["ecdsafail", "submissions", "--all"],
        cwd=repo,
        environment=sanitized_environment(),
        timeout=timeout,
    )
    if completed.returncode:
        raise RuntimeError(f"public frontier refresh failed: {completed.stderr[-1000:]}")
    short = parse_public_frontier_table(completed.stdout)
    main_rows = _git_ls_remote(repo, "refs/heads/main")
    if len(main_rows) != 1 or not main_rows[0][0].startswith(short.source_ref):
        raise RuntimeError("public table and origin/main advanced inconsistently; retry")
    submission_rows = _git_ls_remote(
        repo, f"refs/heads/submissions/{short.submission_id}*"
    )
    if len(submission_rows) != 1:
        raise RuntimeError(
            f"could not resolve public submission {short.submission_id} to one full id"
        )
    full_submission_id = submission_rows[0][1].rsplit("/", 1)[-1]
    return replace(
        short,
        submission_id=full_submission_id,
        source_ref=main_rows[0][0],
    )


def _git_ls_remote(repo: Path, pattern: str) -> list[tuple[str, str]]:
    completed = subprocess.run(
        ["git", "-C", str(repo), "ls-remote", "origin", pattern],
        check=True,
        capture_output=True,
        text=True,
    )
    rows: list[tuple[str, str]] = []
    for line in completed.stdout.splitlines():
        if not line.strip():
            continue
        commit, reference = line.split("\t", 1)
        rows.append((commit, reference))
    return rows


def ensure_ready(records: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    report = backtest(tuple(dict(record) for record in records))
    if report["verdict"] != "green":
        raise ValueError(f"schema harness is red: {report['failures']}")
    if report["pending_iteration"] is not None:
        raise ValueError(f"iteration {report['pending_iteration']} is still pending")
    if report["iterations_started"] >= MAX_ITERATIONS:
        raise ValueError(f"iteration cap {MAX_ITERATIONS} reached")
    if _best_score(records) == 0:
        raise ValueError("certified score-zero stop condition reached")
    return report


def pending_dgm_prediction(
    records: Sequence[Mapping[str, Any]],
) -> Mapping[str, Any] | None:
    report = backtest(tuple(dict(record) for record in records))
    pending = report.get("pending_iteration")
    if pending is None:
        return None
    for record in reversed(records):
        if (
            record.get("type") == "prediction"
            and record.get("iteration") == pending
            and str(record.get("candidate_id", "")).startswith("dgm-i")
        ):
            return record
    return None


def recover_pending_infrastructure_error(
    ledger: Path,
    *,
    conclusion: str,
) -> dict[str, Any]:
    """Close only a DGM-owned pending iteration after an infrastructure crash."""
    records = load_ledger(ledger)
    prediction = pending_dgm_prediction(records)
    if prediction is None:
        raise ValueError("there is no pending DGM iteration to recover")
    observation = {
        "type": "observation",
        "iteration": int(prediction["iteration"]),
        "observation_id": f"{prediction['candidate_id']}-infrastructure-error",
        "stage": "hash",
        "evidence_kind": EvidenceKind.NARRATIVE.value,
        "verdict": "error",
        "artifact_ops_sha256": None,
        "prediction_match": None,
        "measurement": None,
        "conclusion": conclusion,
    }
    return append_payload(ledger, observation)


def archive_report(
    records: Sequence[Mapping[str, Any]],
    *,
    repo: Path | None = None,
) -> dict[str, Any]:
    report = backtest(tuple(dict(record) for record in records))
    nodes = build_archive(records, repo=repo)
    next_iteration = int(report["iterations_started"]) + 1
    niche = str(report["portfolio"]["selected_niche"])
    choice = choose_parent(
        nodes,
        niche=niche,
        iteration=next_iteration,
        ledger_tail_sha256=str(report["tail_sha256"]),
    )
    mapping: dict[str, Any] = {
        "schema_version": 1,
        "derived_from_tail_sha256": report["tail_sha256"],
        "iterations_started": report["iterations_started"],
        "best_score": _best_score(records),
        "next_niche": niche,
        "next_emitter": select_emitter(
            records,
            iteration=next_iteration,
            ledger_tail_sha256=str(report["tail_sha256"]),
        ),
        "nodes": [node.to_mapping() for node in nodes],
        "next_parent": choice.to_mapping(),
    }
    if repo is not None:
        mapping["next_parent"]["resolvable_ref"] = (
            resolve_parent_ref(repo, choice.node)
            if (
                _ref_commit(repo, candidate_ref(choice.node.candidate_id))
                or (choice.node.source_ref and _ref_commit(repo, choice.node.source_ref))
            )
            else None
        )
    return mapping


def _atomic_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(value, sort_keys=True, indent=2) + "\n"
    with tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", dir=path.parent, delete=False
    ) as destination:
        destination.write(encoded)
        temporary = Path(destination.name)
    os.replace(temporary, path)


@contextmanager
def controller_lock(path: Path) -> Iterable[None]:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a+", encoding="utf-8") as lock:
        try:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise RuntimeError(f"another DGM controller holds {path}") from error
        try:
            yield
        finally:
            fcntl.flock(lock.fileno(), fcntl.LOCK_UN)


def _slug(value: str) -> str:
    slug = re.sub(r"[^A-Za-z0-9._-]+", "-", value.strip()).strip(".-")
    slug = re.sub(r"-+", "-", slug)[:48]
    return slug or "candidate"


def _proposal_to_prediction(
    proposal: Mapping[str, Any],
    *,
    iteration: int,
    niche: str,
    parent: ArchiveNode,
) -> dict[str, Any]:
    action_kind = ActionKind(str(proposal["action_kind"]))
    if action_kind in {ActionKind.NO_EFFECT, ActionKind.PROMOTION}:
        raise ValueError(f"invalid mutation action kind: {action_kind.value}")
    candidate_id = f"dgm-i{iteration:03d}-{_slug(str(proposal['candidate_id']))}"
    candidate_ref(candidate_id)
    parent_hash = parent.artifact_ops_sha256
    if parent_hash is None:
        raise ValueError(f"parent {parent.candidate_id} has no exact artifact hash")
    return {
        "type": "prediction",
        "iteration": iteration,
        "niche": niche,
        "action_kind": action_kind.value,
        "candidate_id": candidate_id,
        "parent_candidate_id": parent.candidate_id,
        "parent_frontier_submission_id": parent.frontier_submission_id,
        "parent_ops_sha256": parent_hash,
        "parent_canonical_artifact_sha256": parent.canonical_artifact_sha256,
        "parent_average_toffoli": parent.average_toffoli,
        "parent_qubits": parent.qubits,
        "mechanism": str(proposal["mechanism"]),
        "delta_qubits": int(proposal["delta_qubits"]),
        "delta_toffoli_mean": float(proposal["delta_toffoli_mean"]),
        "delta_toffoli_standard_deviation": float(
            proposal["delta_toffoli_standard_deviation"]
        ),
        "correctness_risk": str(proposal["correctness_risk"]),
        "full_verification_budget": int(proposal["full_verification_budget"]),
        "expected_invalidations": sorted(
            dependency.value for dependency in action_impact(action_kind).invalidated
        ),
        "falsifier": str(proposal["falsifier"]),
    }


def diagnosis_prompt(
    *,
    choice: ParentChoice,
    records: Sequence[Mapping[str, Any]],
    first_literature_transfer: bool,
    emitter: str,
) -> str:
    mode = (
        "This is the first DGM iteration after iteration 62. Start with a filtered "
        "literature transfer from both briefs below."
        if first_literature_transfer
        else "Use literature only when it directly attacks the selected niche."
    )
    emitter_job = {
        "refiner": "Improve the selected parent locally.",
        "recombiner": "Import a mechanism from a distant archive lineage into the selected parent.",
        "literature": "Transfer one unused external technique through the verifier contract.",
        "cold-start": "Reason independently from the verifier/ceiling contract, without prior attempt history.",
        "abductor": "Explain the latest mismatch and propose its strongest discriminating successor.",
    }[emitter]
    context_instruction = (
        "Do not read measurements.jsonl or prior research memory; use only the "
        "verifier contract and source code."
        if emitter == "cold-start"
        else (
            "Read the complete copied ledger at "
            ".autoresearch/context/measurements.jsonl and grep raw local "
            "memory/code as needed."
        )
    )
    return f"""You are the read-only diagnosis phase of a verifier-first circuit search.

Goal: minimize the exact ECDSA Fail score toward the proved floor 0. Reality and
the trusted verifier outrank every model. Propose exactly one falsifiable mutation;
do not edit files in this phase.

Iteration: {choice.iteration}
Emitter: {emitter}
Emitter job: {emitter_job}
Selected niche: {choice.niche} — {NICHES[choice.niche]}
Parent: {json.dumps(choice.node.to_mapping(), sort_keys=True)}
Ledger tail: {choice.ledger_tail_sha256}
Best certified score: {_best_score(records)}
Selection seed: {choice.seed}

{mode}
Literature briefs:
{json.dumps(LITERATURE_TRANSFERS, indent=2)}

{context_instruction}
Do not use hidden tests, benchmark-private
answers, leaderboard guesses, or an LLM judge. Approximate arithmetic is not
evidence. Preserve the exact ABI, reversibility, phase, ancilla cleanup, and the
self-seeded Fiat-Shamir draw.

Your JSON prediction must estimate delta executed Toffoli (mean and standard
deviation), delta qubits, name the dominant correctness risk, give a concrete
falsifier, and provide implementation instructions restricted to Rust files
under src/point_add (never memory/, verifier, simulator, benchmark, config, or
tests). A full-verification budget of 1 is allowed only when the conservative
prediction can strictly beat the certified frontier.
"""


def mutation_prompt(
    prediction: Mapping[str, Any],
    mutation_instructions: str,
) -> str:
    return f"""Produce a patch for the preregistered ECDSA Fail candidate.

Prediction (already committed to the external hash-chained ledger):
{json.dumps(dict(prediction), sort_keys=True, indent=2)}

Mutation instructions:
{mutation_instructions}

You are read-only. Return one Git unified diff; the controller validates and
applies it. The patch may touch only existing or new *.rs files under src/point_add, excluding
src/point_add/memory. Do not edit the verifier, simulator, Cargo files,
benchmark scripts, tests, memory, configuration, Git metadata, or .autoresearch.
Do not run benchmark.sh, eval_circuit, ecdsafail, or any full verifier. Do not
access the network or credentials. Do not emit binary patches, mode changes,
renames, symlinks, or submodules. Keep the diff minimal and describe it in the
summary field. The controller owns all mutation, build, and verification.
"""


def _prepare_context(
    worktree: Path,
    ledger: Path,
    source_repo: Path,
    *,
    include_history: bool,
) -> None:
    context = worktree / ".autoresearch/context"
    context.mkdir(parents=True, exist_ok=True)
    if include_history:
        shutil.copy2(ledger, context / "measurements.jsonl")
    memory = source_repo / "src/point_add/memory"
    for name in (
        "CEILING.md",
        "RIG.md",
        "06-research-status.md",
        "reframe_log.md",
        "niche_portfolio.json",
    ):
        source = memory / name
        if include_history and source.is_file():
            shutil.copy2(source, context / name)


def _run_with_timeout(
    command: Sequence[str],
    *,
    cwd: Path,
    environment: Mapping[str, str],
    timeout: int,
    stdin: str | None = None,
) -> subprocess.CompletedProcess[str]:
    process = subprocess.Popen(
        list(command),
        cwd=cwd,
        env=dict(environment),
        stdin=subprocess.PIPE if stdin is not None else None,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(stdin, timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        stdout, stderr = process.communicate()
        raise TimeoutError(f"command timed out after {timeout}s: {command[0]}") from None
    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)


def _run_codex(
    *,
    worktree: Path,
    attempt: Path,
    phase: str,
    prompt: str,
    schema: Mapping[str, Any] | None,
    sandbox: str,
    timeout: int,
) -> Mapping[str, Any] | str:
    trace = attempt / "trace"
    trace.mkdir(parents=True, exist_ok=True)
    schema_path = attempt / f"{phase}-schema.json"
    final_path = attempt / f"{phase}-final.txt"
    command = [
        "codex",
        "exec",
        "--ephemeral",
        "--ignore-user-config",
        "--sandbox",
        sandbox,
        "-c",
        "sandbox_workspace_write.network_access=false",
        "-c",
        "sandbox_workspace_write.exclude_slash_tmp=true",
        "-c",
        "sandbox_workspace_write.exclude_tmpdir_env_var=true",
        "-c",
        "shell_environment_policy.inherit=none",
        "-c",
        "approval_policy=never",
        "-C",
        str(worktree),
        "--json",
        "--color",
        "never",
        "-o",
        str(final_path),
    ]
    if schema is not None:
        _atomic_json(schema_path, schema)
        command.extend(["--output-schema", str(schema_path)])
    command.append("-")
    completed = _run_with_timeout(
        command,
        cwd=worktree,
        environment=sanitized_environment(),
        timeout=timeout,
        stdin=prompt,
    )
    (trace / f"{phase}.jsonl").write_text(completed.stdout, encoding="utf-8")
    (trace / f"{phase}.stderr.log").write_text(completed.stderr, encoding="utf-8")
    if completed.returncode:
        raise RuntimeError(
            f"Codex {phase} failed ({completed.returncode}): {completed.stderr[-1000:]}"
        )
    final = final_path.read_text(encoding="utf-8")
    if schema is None:
        return final
    value = json.loads(final)
    if not isinstance(value, Mapping):
        raise ValueError(f"Codex {phase} output was not an object")
    return value


def _add_worktree(repo: Path, root: Path, iteration: int, parent_ref: str) -> Path:
    root.mkdir(parents=True, exist_ok=True)
    path = Path(tempfile.mkdtemp(prefix=f"i{iteration:03d}-", dir=root))
    path.rmdir()
    subprocess.run(
        ["git", "-C", str(repo), "worktree", "add", "--detach", str(path), parent_ref],
        check=True,
        capture_output=True,
        text=True,
    )
    return path


def _remove_worktree(repo: Path, root: Path, worktree: Path) -> None:
    resolved_root = root.resolve()
    resolved = worktree.resolve()
    if not resolved.is_relative_to(resolved_root):
        raise ValueError(f"refusing to remove unmanaged worktree: {resolved}")
    subprocess.run(
        ["git", "-C", str(repo), "worktree", "remove", "--force", str(worktree)],
        check=True,
        capture_output=True,
        text=True,
    )


def _changed_paths(worktree: Path) -> tuple[str, ...]:
    completed = subprocess.run(
        ["git", "-C", str(worktree), "status", "--porcelain", "-z"],
        check=True,
        capture_output=True,
        text=True,
    )
    output = completed.stdout
    if not output:
        return ()
    paths: list[str] = []
    fields = output.split("\0")
    index = 0
    while index < len(fields):
        field = fields[index]
        if not field:
            break
        status = field[:2]
        path = field[3:]
        if status[0] in {"R", "C"} or status[1] in {"R", "C"}:
            index += 1
            if index < len(fields):
                path = fields[index]
        paths.append(path)
        index += 1
    return tuple(paths)


def _commit_candidate(
    repo: Path,
    worktree: Path,
    prediction: Mapping[str, Any],
    paths: Sequence[str],
) -> str:
    message = f"feat(point-add): test {prediction['candidate_id']}"
    subprocess.run(
        ["committer", message, *paths],
        cwd=worktree,
        check=True,
        capture_output=True,
        text=True,
        env=sanitized_environment(),
    )
    commit = _git_output(worktree, "rev-parse", "HEAD")
    reference = candidate_ref(str(prediction["candidate_id"]))
    existing = _ref_commit(repo, reference)
    if existing is not None and existing != commit:
        raise RuntimeError(f"candidate ref already exists at a different commit: {reference}")
    subprocess.run(
        [
            "git",
            "-C",
            str(repo),
            "update-ref",
            reference,
            commit,
            existing or ("0" * 40),
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    return commit


def _sandbox_command(
    command: Sequence[str],
    *,
    cwd: Path,
    writable: Sequence[Path],
    timeout: int,
    environment: Mapping[str, str],
) -> subprocess.CompletedProcess[str]:
    system = os.uname().sysname
    if system == "Darwin" and shutil.which("sandbox-exec"):
        grants = "".join(
            f'(allow file-write* (subpath "{path.resolve()}"))' for path in writable
        )
        profile = f"(version 1)(allow default)(deny network*)(deny file-write*){grants}"
        wrapped = ["sandbox-exec", "-p", profile, *command]
    elif shutil.which("bwrap"):
        wrapped = [
            "bwrap",
            "--ro-bind",
            "/",
            "/",
            "--dev",
            "/dev",
            "--proc",
            "/proc",
            "--unshare-net",
            "--die-with-parent",
        ]
        for path in writable:
            wrapped.extend(["--bind", str(path.resolve()), str(path.resolve())])
        wrapped.extend(["--chdir", str(cwd.resolve()), "--", *command])
    else:
        raise RuntimeError("no fail-closed sandbox (sandbox-exec or bwrap) is available")
    return _run_with_timeout(
        wrapped,
        cwd=cwd,
        environment=environment,
        timeout=timeout,
    )


def _build_artifact(
    worktree: Path,
    attempt: Path,
    *,
    timeout: int,
) -> dict[str, Any]:
    trace = attempt / "trace"
    target = attempt / "target"
    scratch = attempt / "build-scratch"
    target.mkdir(parents=True, exist_ok=True)
    scratch.mkdir(parents=True, exist_ok=True)
    environment = sanitized_environment()
    environment["CARGO_TARGET_DIR"] = str(target)
    build = _run_with_timeout(
        [
            "cargo",
            "build",
            "--release",
            "--locked",
            "--offline",
            "--bin",
            "build_circuit",
            "--bin",
            "eval_circuit",
        ],
        cwd=worktree,
        environment=environment,
        timeout=timeout,
    )
    (trace / "build.log").write_text(build.stdout + build.stderr, encoding="utf-8")
    if build.returncode:
        raise RuntimeError(f"candidate build failed: {build.stderr[-1000:]}")
    run = _sandbox_command(
        [str(target / "release/build_circuit")],
        cwd=scratch,
        writable=(scratch,),
        timeout=timeout,
        environment={**environment, "TMPDIR": str(scratch)},
    )
    (trace / "build-circuit.log").write_text(
        run.stdout + run.stderr, encoding="utf-8"
    )
    if run.returncode:
        raise RuntimeError(f"build_circuit failed: {run.stderr[-1000:]}")
    generated = scratch / "ops.bin"
    if not generated.is_file():
        raise RuntimeError("sandboxed build_circuit did not produce ops.bin")
    shutil.copy2(generated, worktree / "ops.bin")
    return fingerprint(worktree / "ops.bin")


def verify_instrument_pins(
    worktree: Path,
    controller_repo: Path,
    frontier_record: Mapping[str, Any],
) -> dict[str, str]:
    instruments = InstrumentSet.from_files(
        worktree / "src/bin/eval_circuit.rs",
        worktree / "src/sim.rs",
        controller_repo / "src/point_add/memory/repro/exact_scorer.py",
    )
    actual = {
        "verifier_sha256": instruments.verifier_sha256,
        "simulator_sha256": instruments.simulator_sha256,
        "scorer_sha256": instruments.scorer_sha256,
        "identity_sha256": instruments.identity_sha256,
    }
    expected = frontier_record.get("instruments")
    if not isinstance(expected, Mapping):
        raise ValueError("frontier record has no instrument pin set")
    mismatches = {
        key: {"expected": expected.get(key), "actual": value}
        for key, value in actual.items()
        if expected.get(key) != value
    }
    if mismatches:
        raise RuntimeError(f"trusted instrument mismatch: {mismatches}")
    return actual


def _build_eval_variant(
    worktree: Path,
    attempt: Path,
    shots: int,
    expected_verifier_sha256: str,
    *,
    timeout: int,
) -> Path:
    source = worktree / "src/bin/eval_circuit.rs"
    if hashlib.sha256(source.read_bytes()).hexdigest() != expected_verifier_sha256:
        raise RuntimeError("trusted evaluator hash differs from ledger pin")
    variant_name = f"autoresearch_eval_{shots}"
    variant = worktree / f"src/bin/{variant_name}.rs"
    original = source.read_text(encoding="utf-8")
    needle = "const NUM_TESTS: usize = 9024;"
    if original.count(needle) != 1:
        raise RuntimeError("trusted evaluator shot constant changed unexpectedly")
    variant.write_text(
        original.replace(needle, f"const NUM_TESTS: usize = {shots};"),
        encoding="utf-8",
    )
    environment = sanitized_environment()
    environment["CARGO_TARGET_DIR"] = str(attempt / "target")
    try:
        build = _run_with_timeout(
            [
                "cargo",
                "build",
                "--release",
                "--locked",
                "--offline",
                "--bin",
                variant_name,
            ],
            cwd=worktree,
            environment=environment,
            timeout=timeout,
        )
    finally:
        variant.unlink(missing_ok=True)
    (attempt / "trace" / f"eval-{shots}-build.log").write_text(
        build.stdout + build.stderr, encoding="utf-8"
    )
    if build.returncode:
        raise RuntimeError(f"{shots}-shot evaluator build failed: {build.stderr[-1000:]}")
    return attempt / "target/release" / variant_name


def _parse_evaluator_output(output: str) -> dict[str, Any]:
    patterns = {
        "shots": r"tested shots\s*:\s*([0-9]+)",
        "classical_failures": r"classical mismatches\s*:\s*([0-9]+)",
        "phase_garbage_batches": r"phase-garbage batches\s*:\s*([0-9]+)",
        "ancilla_garbage_batches": r"ancilla-garbage batches\s*:\s*([0-9]+)",
        "qubits": r"qubits\s*:\s*([0-9]+)",
        "average_toffoli": r"avg executed Toffoli\s*:\s*([0-9.]+)",
        "total_toffoli": r"total Toffoli \(sum\)\s*:\s*([0-9]+)",
    }
    values: dict[str, Any] = {}
    for key, pattern in patterns.items():
        matches = re.findall(pattern, output)
        if matches:
            values[key] = float(matches[-1]) if key == "average_toffoli" else int(matches[-1])
    required = {
        "shots",
        "classical_failures",
        "phase_garbage_batches",
        "ancilla_garbage_batches",
        "qubits",
        "average_toffoli",
    }
    missing = sorted(required - values.keys())
    if missing:
        raise ValueError(f"evaluator output missing fields: {missing}")
    values["score"] = score(values["average_toffoli"], values["qubits"])
    return values


def _last_results_measurement(
    worktree: Path,
    *,
    shots: int,
    partial: Mapping[str, Any],
) -> dict[str, Any]:
    with (worktree / "results.tsv").open(
        newline="", encoding="utf-8"
    ) as source:
        rows = list(csv.DictReader(source, delimiter="\t"))
    if not rows:
        raise ValueError("evaluator produced no results.tsv row")
    row = rows[-1]
    average = float(row["toffoli"])
    qubits = int(row["qubits"])
    return {
        "shots": shots,
        "classical_failures": int(partial.get("classical_failures", shots)),
        "phase_garbage_batches": int(partial.get("phase_garbage_batches", 0)),
        "ancilla_garbage_batches": int(
            partial.get("ancilla_garbage_batches", 0)
        ),
        "qubits": qubits,
        "average_toffoli": average,
        "score": score(average, qubits),
    }


def _parse_evaluator_with_results(
    output: str,
    worktree: Path,
    *,
    shots: int,
) -> dict[str, Any]:
    try:
        return _parse_evaluator_output(output)
    except ValueError:
        partial: dict[str, Any] = {}
        for key, pattern in {
            "classical_failures": r"classical mismatches\s*:\s*([0-9]+)",
            "phase_garbage_batches": r"phase-garbage batches\s*:\s*([0-9]+)",
            "ancilla_garbage_batches": r"ancilla-garbage batches\s*:\s*([0-9]+)",
        }.items():
            matches = re.findall(pattern, output)
            if matches:
                partial[key] = int(matches[-1])
        return _last_results_measurement(worktree, shots=shots, partial=partial)


def _run_eval_stage(
    worktree: Path,
    attempt: Path,
    *,
    shots: int,
    expected_verifier_sha256: str,
    timeout: int,
) -> StageResult:
    if shots == FULL_SHOTS:
        executable = attempt / "target/release/eval_circuit"
    else:
        executable = _build_eval_variant(
            worktree,
            attempt,
            shots,
            expected_verifier_sha256,
            timeout=timeout,
        )
    completed = _run_with_timeout(
        [str(executable), "--note", f"dgm staged gate {shots}"],
        cwd=worktree,
        environment=sanitized_environment(),
        timeout=timeout,
    )
    output = completed.stdout + completed.stderr
    (attempt / "trace" / f"eval-{shots}.log").write_text(output, encoding="utf-8")
    measurement = _parse_evaluator_with_results(output, worktree, shots=shots)
    passed = (
        completed.returncode == 0
        and measurement["shots"] == shots
        and measurement["classical_failures"] == 0
        and measurement["phase_garbage_batches"] == 0
        and measurement["ancilla_garbage_batches"] == 0
    )
    artifact = fingerprint(worktree / "ops.bin")
    return StageResult(
        stage="full" if shots == FULL_SHOTS else "proxy",
        passed=passed,
        conclusion=(
            f"exact {shots}-shot verifier stage passed"
            if passed
            else f"exact {shots}-shot verifier stage failed"
        ),
        evidence_kind=(
            EvidenceKind.TRUSTED_FULL.value
            if shots == FULL_SHOTS
            else EvidenceKind.LOW_SHOT_SCREEN.value
        ),
        artifact_ops_sha256=artifact["compressed_ops_sha256"],
        canonical_artifact_sha256=artifact["canonical_semantic_sha256"],
        measurement=measurement,
    )


def _run_official_full(
    worktree: Path,
    attempt: Path,
    *,
    expected_artifact: Mapping[str, Any],
    timeout: int,
) -> StageResult:
    completed = _run_with_timeout(
        ["ecdsafail", "run"],
        cwd=worktree,
        environment=sanitized_environment(),
        timeout=timeout,
    )
    output = completed.stdout + completed.stderr
    (attempt / "trace" / "ecdsafail-run-9024.log").write_text(
        output, encoding="utf-8"
    )
    measurement = _parse_evaluator_with_results(
        output, worktree, shots=FULL_SHOTS
    )
    rebuilt = fingerprint(worktree / "ops.bin")
    identity_match = (
        rebuilt["canonical_semantic_sha256"]
        == expected_artifact["canonical_semantic_sha256"]
    )
    passed = (
        completed.returncode == 0
        and identity_match
        and measurement["shots"] == FULL_SHOTS
        and measurement["classical_failures"] == 0
        and measurement["phase_garbage_batches"] == 0
        and measurement["ancilla_garbage_batches"] == 0
    )
    measurement["staged_artifact_identity_match"] = identity_match
    return StageResult(
        stage="full",
        passed=passed,
        conclusion=(
            "ecdsafail run certified the exact staged artifact"
            if passed
            else "ecdsafail run failed or rebuilt a different semantic artifact"
        ),
        evidence_kind=EvidenceKind.TRUSTED_FULL.value,
        artifact_ops_sha256=rebuilt["compressed_ops_sha256"],
        canonical_artifact_sha256=rebuilt["canonical_semantic_sha256"],
        measurement=measurement,
    )


def _conservative_prediction_score(
    prediction: Mapping[str, Any],
    parent: ArchiveNode,
) -> float:
    if parent.average_toffoli is None or parent.qubits is None:
        return WORST_SCORE
    width = max(0, parent.qubits + int(prediction["delta_qubits"]))
    upper_toffoli = max(
        0.0,
        parent.average_toffoli
        + float(prediction["delta_toffoli_mean"])
        + 2.0 * float(prediction["delta_toffoli_standard_deviation"]),
    )
    return float(score(upper_toffoli, width))


def full_gate_reasons(
    prediction: Mapping[str, Any],
    *,
    artifact_ops_sha256: str,
    supporting_evidence: Iterable[EvidenceKind],
) -> tuple[str, ...]:
    model_prediction = Prediction(
        prediction_id=str(prediction["candidate_id"]),
        mechanism=str(prediction["mechanism"]),
        delta_qubits=int(prediction["delta_qubits"]),
        delta_toffoli_mean=float(prediction["delta_toffoli_mean"]),
        delta_toffoli_standard_deviation=float(
            prediction["delta_toffoli_standard_deviation"]
        ),
        correctness_risk=str(prediction["correctness_risk"]),
        full_verification_budget=int(prediction["full_verification_budget"]),
        expected_invalidations=frozenset(
            Dependency(value) for value in prediction["expected_invalidations"]
        ),
    )
    action = Action(
        kind=ActionKind(str(prediction["action_kind"])),
        before_ops_sha256=str(prediction["parent_ops_sha256"]),
        after_ops_sha256=artifact_ops_sha256,
        prediction=model_prediction,
        supporting_evidence=frozenset(supporting_evidence),
    )
    return full_verification_gate(action).reasons


def frontier_from_archive(
    public: PublicFrontier,
    nodes: Sequence[ArchiveNode],
) -> Frontier:
    matches = [
        node
        for node in nodes
        if node.frontier_submission_id == public.submission_id
        and node.status == "promoted"
        and node.reproducible
    ]
    if not matches:
        raise ValueError("refreshed public frontier is not bootstrapped in the archive")
    node = min(matches, key=lambda item: (item.actual_score or WORST_SCORE, item.candidate_id))
    if (
        node.actual_score != public.score
        or node.qubits != public.qubits
        or node.artifact_ops_sha256 is None
        or node.canonical_artifact_sha256 is None
    ):
        raise ValueError("bootstrapped public frontier metadata is incomplete or stale")
    return Frontier(
        submission_id=public.submission_id,
        source_ref=public.source_ref,
        score=public.score,
        qubits=public.qubits,
        rounded_toffoli=public.rounded_toffoli,
        ops_sha256=node.artifact_ops_sha256,
        canonical_ops_sha256=node.canonical_artifact_sha256,
        emitted_ops=node.emitted_ops or 0,
    )


def promotion_report(
    prediction: Mapping[str, Any],
    *,
    candidate_source_ref: str,
    artifact: Mapping[str, Any],
    result: StageResult,
    refreshed_frontier: Frontier,
) -> dict[str, Any]:
    measurement = result.measurement or {}
    verification = Verification(
        evidence_kind=EvidenceKind(result.evidence_kind),
        ops_sha256=result.artifact_ops_sha256,
        shots=int(measurement.get("shots", 0)),
        qubits=(
            int(measurement["qubits"]) if measurement.get("qubits") is not None else None
        ),
        total_toffoli=(
            int(measurement["total_toffoli"])
            if measurement.get("total_toffoli") is not None
            else None
        ),
        average_toffoli=(
            float(measurement["average_toffoli"])
            if measurement.get("average_toffoli") is not None
            else None
        ),
        classical_failures=int(measurement.get("classical_failures", 0)),
        phase_garbage_batches=int(measurement.get("phase_garbage_batches", 0)),
        ancilla_garbage_batches=int(
            measurement.get("ancilla_garbage_batches", 0)
        ),
    )
    candidate = Candidate(
        candidate_id=str(prediction["candidate_id"]),
        parent_submission_id=str(prediction["parent_frontier_submission_id"]),
        source_ref=candidate_source_ref,
        ops_sha256=result.artifact_ops_sha256,
        canonical_ops_sha256=result.canonical_artifact_sha256,
        qubits=int(artifact["qubits"]),
        emitted_ops=int(artifact["emitted_ops"]),
    )
    decision = promotion_gate(candidate, verification, refreshed_frontier)
    return {
        "allowed": decision.allowed,
        "reasons": list(decision.reasons),
        "candidate_score": decision.candidate_score,
        "refreshed_frontier": {
            "submission_id": refreshed_frontier.submission_id,
            "source_ref": refreshed_frontier.source_ref,
            "score": refreshed_frontier.score,
        },
    }


def _submit_candidate(
    *,
    worktree: Path,
    attempt: Path,
    prediction: Mapping[str, Any],
    result: StageResult,
    candidate_ref_name: str,
    model: str,
    timeout: int,
) -> dict[str, Any]:
    measurement = result.measurement or {}
    claimed_score = int(measurement["score"])
    note_path = attempt / "submission-note.md"
    note_path.write_text(
        "\n".join(
            (
                f"## {prediction['candidate_id']}",
                "",
                str(prediction["mechanism"]),
                "",
                f"Preregistered falsifier: {prediction.get('falsifier', 'n/a')}",
                "",
                (
                    f"Exact `ecdsafail run`: {measurement['shots']} shots, "
                    f"score {claimed_score}, zero classical/phase/ancilla failures."
                ),
                "",
                f"Candidate lineage: `{candidate_ref_name}`.",
            )
        )
        + "\n",
        encoding="utf-8",
    )
    completed = _run_with_timeout(
        [
            "ecdsafail",
            "submit",
            "--claimed-score",
            str(claimed_score),
            "--note-file",
            str(note_path),
            "--model",
            model,
        ],
        cwd=worktree,
        environment=sanitized_environment(),
        timeout=timeout,
    )
    output = completed.stdout + completed.stderr
    (attempt / "trace" / "ecdsafail-submit.log").write_text(
        output, encoding="utf-8"
    )
    if completed.returncode:
        raise RuntimeError(f"ecdsafail submit failed: {output[-1000:]}")
    clean = _ANSI_ESCAPE.sub("", output)
    submission = re.search(
        r"submission\s+([0-9a-f]{8}-[0-9a-f-]{27,})", clean
    )
    status = re.search(r"status\s+([A-Za-z_-]+)", clean)
    if submission is None or status is None:
        raise ValueError("could not parse ecdsafail submit receipt")
    return {
        "submission_id": submission.group(1),
        "status": status.group(1).lower(),
        "claimed_score": claimed_score,
        "outcome": "submitted exact clean beat; official judge pending",
    }


def _observation_payload(
    prediction: Mapping[str, Any],
    result: StageResult,
    *,
    prediction_match: bool,
) -> dict[str, Any]:
    return {
        "type": "observation",
        "iteration": int(prediction["iteration"]),
        "observation_id": f"{prediction['candidate_id']}-{result.stage}",
        "stage": result.stage,
        "evidence_kind": result.evidence_kind,
        "verdict": "pass" if result.passed else "fail",
        "artifact_ops_sha256": result.artifact_ops_sha256,
        "prediction_match": prediction_match,
        "measurement": result.measurement,
        "conclusion": result.conclusion,
    }


def _candidate_payload(
    prediction: Mapping[str, Any],
    *,
    status: str,
    artifact_hash: str | None,
    canonical_artifact_hash: str | None,
    emitted_ops: int | None,
    source_ref: str | None,
    emitter: str,
    evidence: str,
    archive_contribution: bool,
) -> dict[str, Any]:
    payload = {
        "type": "candidate",
        "iteration": int(prediction["iteration"]),
        "candidate_id": str(prediction["candidate_id"]),
        "niche": str(prediction["niche"]),
        "status": status,
        "parent_candidate_id": str(prediction["parent_candidate_id"]),
        "parent_frontier_submission_id": str(
            prediction["parent_frontier_submission_id"]
        ),
        "evidence": evidence,
        "artifact_ops_sha256": artifact_hash,
        "canonical_artifact_sha256": canonical_artifact_hash,
        "emitted_ops": emitted_ops,
        "emitter": emitter,
        "archive_contribution": archive_contribution,
    }
    if source_ref is not None:
        payload["source_ref"] = source_ref
    return payload


def _automatic_reframe(
    *,
    worktree: Path,
    attempt: Path,
    prediction: Mapping[str, Any],
    observation: Mapping[str, Any],
    timeout: int,
) -> Mapping[str, Any]:
    prompt = f"""A preregistered ECDSA Fail prediction mismatched reality.
Deliberate from the raw trace files under {attempt / 'trace'} and return a
minimal evidence-bound reframe. Do not edit files and do not rescue the old
hypothesis with unobserved claims.

Prediction:
{json.dumps(dict(prediction), indent=2, sort_keys=True)}

Observation:
{json.dumps(dict(observation), indent=2, sort_keys=True)}

State one falsified claim, the smallest compression supported by this result,
and one forward prediction that would discriminate the revised mechanism.
"""
    try:
        result = _run_codex(
            worktree=worktree,
            attempt=attempt,
            phase="reframe",
            prompt=prompt,
            schema=_REFRAME_SCHEMA,
            sandbox="read-only",
            timeout=timeout,
        )
        assert isinstance(result, Mapping)
        return result
    except (OSError, ValueError, RuntimeError, TimeoutError, json.JSONDecodeError):
        return {
            "claim": f"{prediction['mechanism']} did not survive {observation['stage']}",
            "compression": str(observation["conclusion"]),
            "forward_prediction": (
                "A revised candidate must change the named mechanism and pass "
                "the same failed gate before receiving more verifier budget."
            ),
        }


def bootstrap_public_frontier(
    *,
    repo: Path,
    ledger: Path,
    attempts_root: Path,
    worktrees_root: Path,
    stage_timeout: int,
) -> dict[str, Any]:
    """Import the exact current promoted source as a reproducible archive seed."""
    records = load_ledger(ledger)
    ensure_ready(records)
    public = refresh_public_frontier(repo)
    candidate_id = f"public-{public.submission_id[:8]}"
    ref = candidate_ref(candidate_id)
    existing = next(
        (
            record
            for record in records
            if record.get("type") == "candidate"
            and record.get("official_submission_id") == public.submission_id
        ),
        None,
    )
    if existing is not None and _ref_commit(repo, ref):
        return {
            "verdict": "green",
            "status": "already_bootstrapped",
            "candidate_id": candidate_id,
            "candidate_ref": ref,
            "public_score": public.score,
        }

    subprocess.run(
        ["git", "-C", str(repo), "fetch", "--no-tags", "origin", "main"],
        check=True,
        capture_output=True,
        text=True,
    )
    if _ref_commit(repo, public.source_ref) is None:
        raise RuntimeError(f"fetched public source is unresolved: {public.source_ref}")
    attempt = attempts_root / f"bootstrap-{candidate_id}-{public.source_ref[:12]}"
    if attempt.exists():
        attempt = Path(
            tempfile.mkdtemp(prefix=f"bootstrap-{candidate_id}-", dir=attempts_root)
        )
    else:
        attempt.mkdir(parents=True)
    (attempt / "trace").mkdir(exist_ok=True)
    worktree = _add_worktree(repo, worktrees_root, 0, public.source_ref)
    try:
        artifact = _build_artifact(worktree, attempt, timeout=stage_timeout)
    finally:
        if worktree.exists():
            _remove_worktree(repo, worktrees_root, worktree)
    if int(artifact["qubits"]) != public.qubits:
        raise RuntimeError(
            "public source build width differs from its official frontier metrics"
        )
    existing_ref_commit = _ref_commit(repo, ref)
    if existing_ref_commit is not None and existing_ref_commit != public.source_ref:
        raise RuntimeError(f"ref {ref} already points at a different commit")
    subprocess.run(
        [
            "git",
            "-C",
            str(repo),
            "update-ref",
            ref,
            public.source_ref,
            existing_ref_commit or ("0" * 40),
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    latest_records = load_ledger(ledger)
    if latest_records[-1]["record_sha256"] != records[-1]["record_sha256"]:
        raise RuntimeError("ledger advanced during public frontier bootstrap")
    root_id = _frontier_id(records[0])
    appended = append_payload(
        ledger,
        {
            "type": "candidate",
            "iteration": 0,
            "candidate_id": candidate_id,
            "niche": "H4-postpasses",
            "status": "promoted",
            "parent_candidate_id": root_id,
            "evidence": (
                "official public promotion refreshed from ecdsafail submissions "
                "and rebuilt from origin/main"
            ),
            "artifact_ops_sha256": artifact["compressed_ops_sha256"],
            "canonical_artifact_sha256": artifact[
                "canonical_semantic_sha256"
            ],
            "source_ref": ref,
            "official_submission_id": public.submission_id,
            "actual_score": public.score,
            "actual_average_toffoli": float(public.rounded_toffoli),
            "actual_qubits": public.qubits,
            "emitted_ops": artifact["emitted_ops"],
            "emitter": "external-frontier",
        },
    )
    return {
        "verdict": "green",
        "status": "bootstrapped",
        "candidate_id": candidate_id,
        "candidate_ref": ref,
        "public_score": public.score,
        "source_ref": public.source_ref,
        "artifact": artifact,
        "record_sha256": appended["record_sha256"],
    }


def _run_once_locked(
    *,
    repo: Path,
    ledger: Path,
    archive_path: Path,
    attempts_root: Path,
    worktrees_root: Path,
    agent_timeout: int,
    stage_timeout: int,
    proposal_path: Path | None = None,
    submit: bool = False,
    model: str = "gpt-5",
) -> dict[str, Any]:
    """Run one diagnose/predict/mutate/verify iteration."""
    verify_upstream_clone(repo)
    records = load_ledger(ledger)
    ensure_ready(records)
    bootstrap_public_frontier(
        repo=repo,
        ledger=ledger,
        attempts_root=attempts_root,
        worktrees_root=worktrees_root,
        stage_timeout=stage_timeout,
    )
    records = load_ledger(ledger)
    status = ensure_ready(records)
    iteration = int(status["iterations_started"]) + 1
    niche = str(status["portfolio"]["selected_niche"])
    nodes = build_archive(records, repo=repo)
    choice = choose_parent(
        nodes,
        niche=niche,
        iteration=iteration,
        ledger_tail_sha256=str(status["tail_sha256"]),
    )
    emitter_plan = select_emitter(
        records,
        iteration=iteration,
        ledger_tail_sha256=str(status["tail_sha256"]),
    )
    emitter = str(emitter_plan["emitter"])
    parent_ref = resolve_parent_ref(repo, choice.node)
    archive = archive_report(records, repo=repo)
    _atomic_json(archive_path, archive)

    attempt = attempts_root / (
        f"i{iteration:03d}-{status['tail_sha256'][:12]}-{choice.node.candidate_id}"
    )
    if attempt.exists():
        raise ValueError(f"attempt directory already exists: {attempt}")
    attempt.mkdir(parents=True)
    _atomic_json(attempt / "selection.json", choice.to_mapping())
    _atomic_json(attempt / "emitter.json", emitter_plan)
    _atomic_json(
        attempt / "meta.json",
        {
            "controller": "dgm_search.py",
            "dgm_upstream_revision": DGM_UPSTREAM_REVISION,
            "codex_version": subprocess.run(
                ["codex", "--version"],
                check=True,
                capture_output=True,
                text=True,
            ).stdout.strip(),
            "model": model,
            "iteration": iteration,
            "ledger_tail_sha256": status["tail_sha256"],
            "selection_seed": choice.seed,
            "agent_timeout_seconds": agent_timeout,
            "stage_timeout_seconds": stage_timeout,
        },
    )
    worktree = _add_worktree(repo, worktrees_root, iteration, parent_ref)
    try:
        _prepare_context(
            worktree,
            ledger,
            repo,
            include_history=emitter != "cold-start",
        )
        if proposal_path is None:
            proposal = _run_codex(
                worktree=worktree,
                attempt=attempt,
                phase="diagnose",
                prompt=diagnosis_prompt(
                    choice=choice,
                    records=records,
                    first_literature_transfer=iteration == 63,
                    emitter=emitter,
                ),
                schema=_PROPOSAL_SCHEMA,
                sandbox="read-only",
                timeout=agent_timeout,
            )
            assert isinstance(proposal, Mapping)
        else:
            proposal_value = json.loads(proposal_path.read_text(encoding="utf-8"))
            if not isinstance(proposal_value, Mapping):
                raise ValueError("proposal file must contain an object")
            proposal = proposal_value

        prediction = _proposal_to_prediction(
            proposal,
            iteration=iteration,
            niche=niche,
            parent=choice.node,
        )
        current = load_ledger(ledger)
        current_status = ensure_ready(current)
        if current_status["tail_sha256"] != status["tail_sha256"]:
            raise RuntimeError("ledger advanced during diagnosis; retry from the new tail")
        append_payload(ledger, prediction)
        _atomic_json(attempt / "prediction.json", prediction)

        patch_result = _run_codex(
            worktree=worktree,
            attempt=attempt,
            phase="mutate",
            prompt=mutation_prompt(prediction, str(proposal["mutation_instructions"])),
            schema=_PATCH_SCHEMA,
            sandbox="read-only",
            timeout=agent_timeout,
        )
        assert isinstance(patch_result, Mapping)
        paths = validate_and_apply_patch(worktree, str(patch_result["patch"]))
        ref: str | None = None
        commit: str | None = None

        artifact: Mapping[str, Any] | None = None
        try:
            artifact = _build_artifact(worktree, attempt, timeout=stage_timeout)
        except (OSError, RuntimeError, TimeoutError) as error:
            result = StageResult(
                stage="hash",
                passed=False,
                conclusion=str(error),
                evidence_kind=EvidenceKind.NARRATIVE.value,
                artifact_ops_sha256=None,
                canonical_artifact_sha256=None,
                measurement=None,
            )
        else:
            commit = _commit_candidate(repo, worktree, prediction, paths)
            ref = candidate_ref(str(prediction["candidate_id"]))
            artifact_hash = str(artifact["compressed_ops_sha256"])
            canonical_hash = str(artifact["canonical_semantic_sha256"])
            is_noop = semantic_noop(
                artifact,
                parent_compressed_sha256=str(prediction["parent_ops_sha256"]),
                parent_canonical_sha256=(
                    str(prediction["parent_canonical_artifact_sha256"])
                    if prediction.get("parent_canonical_artifact_sha256")
                    else None
                ),
            )
            if is_noop:
                result = StageResult(
                    stage="hash",
                    passed=False,
                    conclusion="candidate is byte-identical to its parent artifact",
                    evidence_kind=EvidenceKind.BYTE_IDENTICAL.value,
                    artifact_ops_sha256=artifact_hash,
                    canonical_artifact_sha256=canonical_hash,
                    measurement={"fingerprint": artifact},
                )
            else:
                result = StageResult(
                    stage="proxy",
                    passed=True,
                    conclusion="artifact hash changed; beginning fixed-draw screens",
                    evidence_kind=EvidenceKind.NARRATIVE.value,
                    artifact_ops_sha256=artifact_hash,
                    canonical_artifact_sha256=canonical_hash,
                    measurement={"fingerprint": artifact},
                )
                instrument_report = verify_instrument_pins(
                    worktree, repo, current[0]
                )
                _atomic_json(
                    attempt / "instrument-pins.json",
                    {"verdict": "green", **instrument_report},
                )
                verifier_hash = str(current[0]["instruments"]["verifier_sha256"])
                for shots in SHOT_LADDER[:-1]:
                    result = _run_eval_stage(
                        worktree,
                        attempt,
                        shots=shots,
                        expected_verifier_sha256=verifier_hash,
                        timeout=stage_timeout,
                    )
                    if not result.passed:
                        break
                if result.passed:
                    public_before_full = refresh_public_frontier(repo)
                    best = public_before_full.score
                    conservative = _conservative_prediction_score(
                        prediction, choice.node
                    )
                    evidence_reasons = full_gate_reasons(
                        prediction,
                        artifact_ops_sha256=artifact_hash,
                        supporting_evidence={EvidenceKind.LOW_SHOT_SCREEN},
                    )
                    if (
                        int(prediction["full_verification_budget"]) == 0
                        or conservative >= best
                        or evidence_reasons
                    ):
                        denial = []
                        if int(prediction["full_verification_budget"]) == 0:
                            denial.append("prediction allocated no full-run budget")
                        if conservative >= best:
                            denial.append(
                                f"conservative predicted score {int(conservative)} "
                                f"does not beat {best}"
                            )
                        denial.extend(evidence_reasons)
                        result = replace(
                            result,
                            conclusion=(
                                f"{SHOT_LADDER[-2]}-shot screen passed; full "
                                f"verifier denied: {', '.join(denial)}"
                            ),
                            measurement={
                                **(result.measurement or {}),
                                "conservative_predicted_score": int(conservative),
                                "best_score": best,
                                "full_gate_reasons": list(evidence_reasons),
                            },
                        )
                    else:
                        result = _run_official_full(
                            worktree,
                            attempt,
                            expected_artifact=artifact,
                            timeout=stage_timeout,
                        )

        measurement = result.measurement or {}
        predicted_delta = float(prediction["delta_toffoli_mean"])
        predicted_sd = float(prediction["delta_toffoli_standard_deviation"])
        observed_delta: float | None = None
        if "average_toffoli" in measurement:
            parent_average = choice.node.average_toffoli
            if parent_average is not None:
                observed_delta = float(measurement["average_toffoli"]) - parent_average
        prediction_match = bool(
            result.passed
            and (
                observed_delta is None
                or abs(observed_delta - predicted_delta) <= 2.0 * predicted_sd
                or predicted_sd == 0.0
                and observed_delta == predicted_delta
            )
        )
        observation = _observation_payload(
            prediction, result, prediction_match=prediction_match
        )
        append_payload(ledger, observation)
        clean_full = result.stage == "full" and result.passed
        promotion: dict[str, Any] | None = None
        submission_receipt: dict[str, Any] | None = None
        if (
            clean_full
            and ref is not None
            and isinstance(artifact, Mapping)
        ):
            public_after_full = refresh_public_frontier(repo)
            try:
                refreshed_frontier = frontier_from_archive(
                    public_after_full,
                    build_archive(current, repo=repo),
                )
            except ValueError as error:
                promotion = {
                    "allowed": False,
                    "reasons": [str(error)],
                    "candidate_score": measurement.get("score"),
                    "refreshed_frontier": asdict(public_after_full),
                }
            else:
                promotion = promotion_report(
                    prediction,
                    candidate_source_ref=ref,
                    artifact=artifact,
                    result=result,
                    refreshed_frontier=refreshed_frontier,
                )
                if submit and promotion["allowed"]:
                    submission_receipt = _submit_candidate(
                        worktree=worktree,
                        attempt=attempt,
                        prediction=prediction,
                        result=result,
                        candidate_ref_name=ref,
                        model=model,
                        timeout=stage_timeout,
                    )
            _atomic_json(attempt / "promotion.json", promotion)
        append_payload(
            ledger,
            _candidate_payload(
                prediction,
                status=(
                    "promoted"
                    if submission_receipt is not None
                    and submission_receipt["status"] == "promoted"
                    else ("live" if clean_full else "retired")
                ),
                artifact_hash=result.artifact_ops_sha256,
                canonical_artifact_hash=result.canonical_artifact_sha256,
                emitted_ops=(
                    int(artifact["emitted_ops"])
                    if isinstance(artifact, Mapping)
                    else None
                ),
                source_ref=ref,
                emitter=emitter,
                evidence=result.conclusion,
                archive_contribution=(
                    clean_full
                    and not any(
                        node.functioning and node.niche == niche
                        for node in build_archive(current, repo=repo)
                    )
                ),
            ),
        )
        if submission_receipt is not None:
            append_payload(
                ledger,
                {
                    "type": "submission",
                    "iteration": iteration,
                    "submission_id": submission_receipt["submission_id"],
                    "source_ref": ref,
                    "artifact_ops_sha256": result.artifact_ops_sha256,
                    "status": submission_receipt["status"],
                    "official_score": submission_receipt["claimed_score"],
                    "outcome": submission_receipt["outcome"],
                },
            )
        if not prediction_match:
            reframe = _automatic_reframe(
                worktree=worktree,
                attempt=attempt,
                prediction=prediction,
                observation=observation,
                timeout=agent_timeout,
            )
            append_payload(
                ledger,
                {
                    "type": "reframe",
                    "iteration": iteration,
                    "claim": str(reframe["claim"]),
                    "compression": str(reframe["compression"]),
                    "forward_prediction": str(reframe["forward_prediction"]),
                },
            )

        refreshed = archive_report(load_ledger(ledger), repo=repo)
        _atomic_json(archive_path, refreshed)
        final_report = {
            "verdict": "green" if clean_full else "retired",
            "iteration": iteration,
            "candidate_id": prediction["candidate_id"],
            "candidate_ref": ref,
            "commit": commit,
            "stage": result.stage,
            "passed": result.passed,
            "prediction_match": prediction_match,
            "conclusion": result.conclusion,
            "attempt": str(attempt),
            "promotion": promotion,
            "submission": submission_receipt,
        }
        _atomic_json(attempt / "result.json", final_report)
        return final_report
    finally:
        if worktree.exists():
            _remove_worktree(repo, worktrees_root, worktree)


def run_once(
    *,
    repo: Path,
    ledger: Path,
    archive_path: Path,
    attempts_root: Path,
    worktrees_root: Path,
    agent_timeout: int,
    stage_timeout: int,
    proposal_path: Path | None = None,
    submit: bool = False,
    model: str = "gpt-5",
) -> dict[str, Any]:
    """Hold the controller transaction lock for one complete iteration."""
    with controller_lock(repo / ".autoresearch/dgm.lock"):
        try:
            return _run_once_locked(
                repo=repo,
                ledger=ledger,
                archive_path=archive_path,
                attempts_root=attempts_root,
                worktrees_root=worktrees_root,
                agent_timeout=agent_timeout,
                stage_timeout=stage_timeout,
                proposal_path=proposal_path,
                submit=submit,
                model=model,
            )
        except Exception as error:
            # Once prediction is preregistered, never leave an ordinary Python,
            # tool, or timeout failure masquerading as a scientific result.
            # SIGKILL/power loss is handled by the explicit recover-pending CLI.
            records = load_ledger(ledger)
            if pending_dgm_prediction(records) is not None:
                recover_pending_infrastructure_error(
                    ledger,
                    conclusion=f"controller infrastructure error: {type(error).__name__}: {error}",
                )
            raise


def dry_run(
    *,
    repo: Path,
    ledger: Path,
    archive_path: Path,
) -> dict[str, Any]:
    upstream = verify_upstream_clone(repo)
    records = load_ledger(ledger)
    status = backtest(records)
    archive = archive_report(records, repo=repo)
    _atomic_json(archive_path, archive)
    ready = status["verdict"] == "green" and status["pending_iteration"] is None
    return {
        "verdict": "green" if ready else "waiting",
        "upstream": upstream,
        "harness": status,
        "archive_path": str(archive_path),
        "next_parent": archive["next_parent"],
        "stop": {
            "score_zero": _best_score(records) == 0,
            "iteration_cap": status["iterations_started"] >= MAX_ITERATIONS,
        },
    }


def _absolute(repo: Path, path: Path) -> Path:
    return path if path.is_absolute() else repo / path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=repo_root())
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER)
    parser.add_argument("--archive", type=Path, default=DEFAULT_ARCHIVE)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("upstream")
    subparsers.add_parser("archive")
    subparsers.add_parser("select")
    subparsers.add_parser("dry-run")
    bootstrap_parser = subparsers.add_parser("bootstrap-public")
    bootstrap_parser.add_argument("--attempts", type=Path, default=DEFAULT_ATTEMPTS)
    bootstrap_parser.add_argument("--worktrees", type=Path, default=DEFAULT_WORKTREES)
    bootstrap_parser.add_argument("--stage-timeout", type=int, default=7_200)
    recover_parser = subparsers.add_parser("recover-pending")
    recover_parser.add_argument(
        "--conclusion",
        required=True,
        help="evidence-bound infrastructure failure description",
    )
    run_parser = subparsers.add_parser("run-once")
    run_parser.add_argument("--attempts", type=Path, default=DEFAULT_ATTEMPTS)
    run_parser.add_argument("--worktrees", type=Path, default=DEFAULT_WORKTREES)
    run_parser.add_argument("--agent-timeout", type=int, default=1_800)
    run_parser.add_argument("--stage-timeout", type=int, default=7_200)
    run_parser.add_argument("--proposal", type=Path)
    run_parser.add_argument(
        "--submit",
        action="store_true",
        help="submit only when refreshed world-model promotion gates pass",
    )
    run_parser.add_argument("--model", default="gpt-5")
    args = parser.parse_args()

    repo = args.repo.resolve()
    ledger = _absolute(repo, args.ledger)
    archive_path = _absolute(repo, args.archive)
    try:
        if args.command == "upstream":
            output = verify_upstream_clone(repo)
        elif args.command == "archive":
            output = archive_report(load_ledger(ledger), repo=repo)
            _atomic_json(archive_path, output)
        elif args.command == "select":
            records = load_ledger(ledger)
            status = ensure_ready(records)
            nodes = build_archive(records, repo=repo)
            output = choose_parent(
                nodes,
                niche=str(status["portfolio"]["selected_niche"]),
                iteration=int(status["iterations_started"]) + 1,
                ledger_tail_sha256=str(status["tail_sha256"]),
            ).to_mapping()
        elif args.command == "dry-run":
            output = dry_run(repo=repo, ledger=ledger, archive_path=archive_path)
        elif args.command == "recover-pending":
            with controller_lock(repo / ".autoresearch/dgm.lock"):
                output = recover_pending_infrastructure_error(
                    ledger,
                    conclusion=args.conclusion,
                )
        elif args.command == "bootstrap-public":
            with controller_lock(repo / ".autoresearch/dgm.lock"):
                output = bootstrap_public_frontier(
                    repo=repo,
                    ledger=ledger,
                    attempts_root=_absolute(repo, args.attempts),
                    worktrees_root=_absolute(repo, args.worktrees),
                    stage_timeout=args.stage_timeout,
                )
        else:
            output = run_once(
                repo=repo,
                ledger=ledger,
                archive_path=archive_path,
                attempts_root=_absolute(repo, args.attempts),
                worktrees_root=_absolute(repo, args.worktrees),
                agent_timeout=args.agent_timeout,
                stage_timeout=args.stage_timeout,
                proposal_path=(
                    _absolute(repo, args.proposal) if args.proposal is not None else None
                ),
                submit=args.submit,
                model=args.model,
            )
    except (
        OSError,
        ValueError,
        RuntimeError,
        TimeoutError,
        subprocess.CalledProcessError,
        json.JSONDecodeError,
    ) as error:
        print(json.dumps({"verdict": "red", "error": str(error)}, sort_keys=True))
        return 1
    print(json.dumps(output, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
