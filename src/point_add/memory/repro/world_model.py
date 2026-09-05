#!/usr/bin/env python3
"""Executable evidence and invalidation model for the fixed ECDSA Fail benchmark.

This module models what survives a circuit change and what evidence is required
before spending a trusted 9,024-shot verification. It does not simulate circuits
and cannot certify a novel candidate; only ``eval_circuit`` can do that.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, replace
from enum import Enum
from pathlib import Path
from typing import Any

try:
    from exact_scorer import score as exact_score
    from exact_scorer import score_from_totals
except ModuleNotFoundError:
    from .exact_scorer import score as exact_score
    from .exact_scorer import score_from_totals

FULL_VERIFICATION_SHOTS = 9_024
_SHA256_HEX_LENGTH = 64


def _require_nonempty(name: str, value: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_nonnegative_int(name: str, value: int) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an int")
    if value < 0:
        raise ValueError(f"{name} must be non-negative")
    return value


def _require_sha256(name: str, value: str | None) -> str | None:
    if value is None:
        return None
    if not isinstance(value, str) or len(value) != _SHA256_HEX_LENGTH:
        raise ValueError(f"{name} must be a 64-character SHA-256 hex digest")
    try:
        bytes.fromhex(value)
    except ValueError as error:
        raise ValueError(f"{name} must be hexadecimal") from error
    return value.lower()


def _require_finite_nonnegative(name: str, value: float) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise TypeError(f"{name} must be a real number")
    result = float(value)
    if not math.isfinite(result) or result < 0.0:
        raise ValueError(f"{name} must be finite and non-negative")
    return result


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


class ActionKind(str, Enum):
    NO_EFFECT = "no_effect"
    NONCE_ONLY = "nonce_only"
    EXACT_REWRITE = "exact_rewrite"
    GEOMETRY = "geometry"
    RISK_OR_STRIP_BUDGET = "risk_or_strip_budget"
    REPRESENTATION = "representation"
    PROMOTION = "promotion"


class Dependency(str, Enum):
    FIAT_SHAMIR_SEED = "fiat_shamir_seed"
    TRUSTED_VERIFICATION = "trusted_verification"
    EXECUTED_TOFFOLI_DRAW = "executed_toffoli_draw"
    CIRCUIT_FUNCTION_PROOF = "circuit_function_proof"
    STRIP_KEYS = "strip_keys"
    CAP_OPTIMUM = "cap_optimum"
    COST_CALIBRATION = "cost_calibration"
    CLEAN_DENSITY = "clean_density"
    ABI_CONTRACT = "abi_contract"
    SCORER_CONTRACT = "scorer_contract"
    PROVED_INVARIANTS = "proved_invariants"


class EvidenceKind(str, Enum):
    OFFICIAL_PROMOTED = "official_promoted_result"
    TRUSTED_FULL = "trusted_9024_exact_artifact_result"
    BYTE_IDENTICAL = "byte_identical_operation_stream"
    SCOPED_MACHINE_PROOF = "scoped_machine_proof"
    PAIRED_FIXED_RANDOMNESS = "paired_fixed_randomness_differential"
    EXACT_CENSUS = "exact_stream_census"
    INDEPENDENT_SEED_ESTIMATE = "independent_seed_statistical_estimate"
    LOW_SHOT_SCREEN = "low_shot_screen"
    NARRATIVE = "narrative_claim"


class NoncePolicy(str, Enum):
    INHERITED = "inherited_fixed_artifact"
    FIXED = "fixed_before_verification"
    PREREGISTERED_BRANCH = "preregistered_budgeted_branch"
    NOT_APPLICABLE = "not_applicable"


class PlanStatus(str, Enum):
    ACTIVE = "active"
    ABORTED = "aborted"


_EVIDENCE_STRENGTH = {
    EvidenceKind.OFFICIAL_PROMOTED: 1,
    EvidenceKind.TRUSTED_FULL: 2,
    EvidenceKind.BYTE_IDENTICAL: 3,
    EvidenceKind.SCOPED_MACHINE_PROOF: 3,
    EvidenceKind.PAIRED_FIXED_RANDOMNESS: 4,
    EvidenceKind.EXACT_CENSUS: 4,
    EvidenceKind.INDEPENDENT_SEED_ESTIMATE: 5,
    EvidenceKind.LOW_SHOT_SCREEN: 6,
    EvidenceKind.NARRATIVE: 7,
}


def evidence_strength(kind: EvidenceKind) -> int:
    """Return the evidence rank; lower is stronger."""
    return _EVIDENCE_STRENGTH[kind]


@dataclass(frozen=True, slots=True)
class Frontier:
    submission_id: str
    source_ref: str
    score: int
    qubits: int
    rounded_toffoli: int
    ops_sha256: str
    canonical_ops_sha256: str
    emitted_ops: int

    def __post_init__(self) -> None:
        _require_nonempty("submission_id", self.submission_id)
        _require_nonempty("source_ref", self.source_ref)
        _require_nonnegative_int("score", self.score)
        _require_nonnegative_int("qubits", self.qubits)
        _require_nonnegative_int("rounded_toffoli", self.rounded_toffoli)
        _require_nonnegative_int("emitted_ops", self.emitted_ops)
        object.__setattr__(self, "ops_sha256", _require_sha256("ops_sha256", self.ops_sha256))
        object.__setattr__(
            self,
            "canonical_ops_sha256",
            _require_sha256("canonical_ops_sha256", self.canonical_ops_sha256),
        )
        expected = exact_score(float(self.rounded_toffoli), self.qubits)
        if self.score != expected:
            raise ValueError(f"frontier score {self.score} does not equal exact score {expected}")


@dataclass(frozen=True, slots=True)
class Candidate:
    candidate_id: str
    parent_submission_id: str
    source_ref: str
    ops_sha256: str | None
    canonical_ops_sha256: str | None = None
    nonce: int | None = None
    nonce_policy: NoncePolicy = NoncePolicy.NOT_APPLICABLE
    qubits: int | None = None
    emitted_ops: int | None = None

    def __post_init__(self) -> None:
        _require_nonempty("candidate_id", self.candidate_id)
        _require_nonempty("parent_submission_id", self.parent_submission_id)
        _require_nonempty("source_ref", self.source_ref)
        object.__setattr__(self, "ops_sha256", _require_sha256("ops_sha256", self.ops_sha256))
        object.__setattr__(
            self,
            "canonical_ops_sha256",
            _require_sha256("canonical_ops_sha256", self.canonical_ops_sha256),
        )
        if self.nonce is not None:
            _require_nonnegative_int("nonce", self.nonce)
            if self.nonce >= 1 << 48:
                raise ValueError("nonce must fit the benchmark's 48-bit tail field")
        if self.qubits is not None:
            _require_nonnegative_int("qubits", self.qubits)
        if self.emitted_ops is not None:
            _require_nonnegative_int("emitted_ops", self.emitted_ops)


@dataclass(frozen=True, slots=True)
class InstrumentSet:
    verifier_sha256: str
    simulator_sha256: str
    scorer_sha256: str

    def __post_init__(self) -> None:
        object.__setattr__(
            self, "verifier_sha256", _require_sha256("verifier_sha256", self.verifier_sha256)
        )
        object.__setattr__(
            self, "simulator_sha256", _require_sha256("simulator_sha256", self.simulator_sha256)
        )
        object.__setattr__(self, "scorer_sha256", _require_sha256("scorer_sha256", self.scorer_sha256))

    @classmethod
    def from_files(cls, verifier: Path, simulator: Path, scorer: Path) -> InstrumentSet:
        return cls(
            verifier_sha256=_sha256_file(verifier),
            simulator_sha256=_sha256_file(simulator),
            scorer_sha256=_sha256_file(scorer),
        )

    @property
    def identity_sha256(self) -> str:
        digest = hashlib.sha256()
        for name, value in (
            ("verifier", self.verifier_sha256),
            ("simulator", self.simulator_sha256),
            ("scorer", self.scorer_sha256),
        ):
            digest.update(name.encode("ascii"))
            digest.update(b"\0")
            digest.update(value.encode("ascii"))
            digest.update(b"\0")
        return digest.hexdigest()


@dataclass(frozen=True, slots=True)
class Calibration:
    dependency: Dependency
    artifact_ops_sha256: str | None
    instrument_sha256: str
    evidence_id: str
    samples: int = 0
    mean: float | None = None
    standard_deviation: float | None = None

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "artifact_ops_sha256",
            _require_sha256("artifact_ops_sha256", self.artifact_ops_sha256),
        )
        object.__setattr__(
            self,
            "instrument_sha256",
            _require_sha256("instrument_sha256", self.instrument_sha256),
        )
        _require_nonempty("evidence_id", self.evidence_id)
        _require_nonnegative_int("samples", self.samples)
        if self.mean is not None:
            object.__setattr__(self, "mean", _require_finite_nonnegative("mean", self.mean))
        if self.standard_deviation is not None:
            object.__setattr__(
                self,
                "standard_deviation",
                _require_finite_nonnegative("standard_deviation", self.standard_deviation),
            )
        if self.dependency in {
            Dependency.STRIP_KEYS,
            Dependency.CAP_OPTIMUM,
            Dependency.COST_CALIBRATION,
            Dependency.CLEAN_DENSITY,
        } and self.artifact_ops_sha256 is None:
            raise ValueError(f"{self.dependency.value} calibration requires an artifact hash")


@dataclass(frozen=True, slots=True)
class Prediction:
    prediction_id: str
    mechanism: str
    delta_qubits: int
    delta_toffoli_mean: float
    delta_toffoli_standard_deviation: float
    correctness_risk: str
    full_verification_budget: int
    expected_invalidations: frozenset[Dependency]

    def __post_init__(self) -> None:
        _require_nonempty("prediction_id", self.prediction_id)
        _require_nonempty("mechanism", self.mechanism)
        if type(self.delta_qubits) is not int:
            raise TypeError("delta_qubits must be an int")
        if isinstance(self.delta_toffoli_mean, bool) or not isinstance(
            self.delta_toffoli_mean, (int, float)
        ):
            raise TypeError("delta_toffoli_mean must be a real number")
        if not math.isfinite(float(self.delta_toffoli_mean)):
            raise ValueError("delta_toffoli_mean must be finite")
        object.__setattr__(
            self,
            "delta_toffoli_standard_deviation",
            _require_finite_nonnegative(
                "delta_toffoli_standard_deviation", self.delta_toffoli_standard_deviation
            ),
        )
        _require_nonempty("correctness_risk", self.correctness_risk)
        _require_nonnegative_int("full_verification_budget", self.full_verification_budget)
        invalidations = frozenset(self.expected_invalidations)
        if any(not isinstance(dependency, Dependency) for dependency in invalidations):
            raise TypeError("expected_invalidations must contain Dependency values")
        object.__setattr__(self, "expected_invalidations", invalidations)


@dataclass(frozen=True, slots=True)
class Action:
    kind: ActionKind
    before_ops_sha256: str
    after_ops_sha256: str | None
    prediction: Prediction
    supporting_evidence: frozenset[EvidenceKind] = frozenset()

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "before_ops_sha256",
            _require_sha256("before_ops_sha256", self.before_ops_sha256),
        )
        object.__setattr__(
            self,
            "after_ops_sha256",
            _require_sha256("after_ops_sha256", self.after_ops_sha256),
        )
        evidence = frozenset(self.supporting_evidence)
        if any(not isinstance(kind, EvidenceKind) for kind in evidence):
            raise TypeError("supporting_evidence must contain EvidenceKind values")
        object.__setattr__(self, "supporting_evidence", evidence)


@dataclass(frozen=True, slots=True)
class ActionImpact:
    invalidated: frozenset[Dependency]
    preserved: frozenset[Dependency]
    conditionally_reusable: frozenset[Dependency]
    required_evidence: frozenset[EvidenceKind]
    allow_full_verification: bool


_ALL_DEPENDENCIES = frozenset(Dependency)


def _make_impact(
    invalidated: set[Dependency],
    *,
    conditional: set[Dependency] | None = None,
    required_evidence: set[EvidenceKind] | None = None,
    allow_full_verification: bool = True,
) -> ActionImpact:
    conditional_set = frozenset(conditional or set())
    invalidated_set = frozenset(invalidated)
    return ActionImpact(
        invalidated=invalidated_set,
        preserved=_ALL_DEPENDENCIES - invalidated_set - conditional_set,
        conditionally_reusable=conditional_set,
        required_evidence=frozenset(required_evidence or set()),
        allow_full_verification=allow_full_verification,
    )


_BASE_EMPIRICAL_INVALIDATIONS = {
    Dependency.FIAT_SHAMIR_SEED,
    Dependency.TRUSTED_VERIFICATION,
    Dependency.EXECUTED_TOFFOLI_DRAW,
}

_ACTION_IMPACTS = {
    ActionKind.NO_EFFECT: _make_impact(set(), allow_full_verification=False),
    ActionKind.NONCE_ONLY: _make_impact(set(_BASE_EMPIRICAL_INVALIDATIONS)),
    ActionKind.EXACT_REWRITE: _make_impact(
        _BASE_EMPIRICAL_INVALIDATIONS
        | {
            Dependency.STRIP_KEYS,
            Dependency.COST_CALIBRATION,
            Dependency.CLEAN_DENSITY,
        },
        conditional={Dependency.CIRCUIT_FUNCTION_PROOF},
        required_evidence={EvidenceKind.SCOPED_MACHINE_PROOF},
    ),
    ActionKind.GEOMETRY: _make_impact(
        _BASE_EMPIRICAL_INVALIDATIONS
        | {
            Dependency.CIRCUIT_FUNCTION_PROOF,
            Dependency.STRIP_KEYS,
            Dependency.CAP_OPTIMUM,
            Dependency.COST_CALIBRATION,
            Dependency.CLEAN_DENSITY,
        }
    ),
    ActionKind.RISK_OR_STRIP_BUDGET: _make_impact(
        _BASE_EMPIRICAL_INVALIDATIONS
        | {
            Dependency.CIRCUIT_FUNCTION_PROOF,
            Dependency.STRIP_KEYS,
            Dependency.COST_CALIBRATION,
            Dependency.CLEAN_DENSITY,
        },
        required_evidence={
            EvidenceKind.PAIRED_FIXED_RANDOMNESS,
            EvidenceKind.EXACT_CENSUS,
        },
    ),
    ActionKind.REPRESENTATION: _make_impact(
        _ALL_DEPENDENCIES
        - {
            Dependency.ABI_CONTRACT,
            Dependency.SCORER_CONTRACT,
            Dependency.PROVED_INVARIANTS,
        }
    ),
    ActionKind.PROMOTION: _make_impact(set(), allow_full_verification=False),
}


def action_impact(kind: ActionKind) -> ActionImpact:
    """Return the benchmark-specific dependency invalidation contract."""
    return _ACTION_IMPACTS[kind]


@dataclass(frozen=True, slots=True)
class EvidenceEvent:
    event_id: str
    kind: EvidenceKind
    observed_at: str
    statement: str
    source_ref: str | None = None
    artifact_ops_sha256: str | None = None
    prediction_id: str | None = None
    prediction_match: bool | None = None

    def __post_init__(self) -> None:
        _require_nonempty("event_id", self.event_id)
        _require_nonempty("observed_at", self.observed_at)
        _require_nonempty("statement", self.statement)
        if self.source_ref is not None:
            _require_nonempty("source_ref", self.source_ref)
        object.__setattr__(
            self,
            "artifact_ops_sha256",
            _require_sha256("artifact_ops_sha256", self.artifact_ops_sha256),
        )
        if self.source_ref is None and self.artifact_ops_sha256 is None:
            raise ValueError("evidence must name a source ref or exact artifact hash")
        if self.prediction_id is not None:
            _require_nonempty("prediction_id", self.prediction_id)
        if self.prediction_match is not None and type(self.prediction_match) is not bool:
            raise TypeError("prediction_match must be a bool or None")

    def to_mapping(self) -> dict[str, Any]:
        return {
            "event_id": self.event_id,
            "kind": self.kind.value,
            "observed_at": self.observed_at,
            "statement": self.statement,
            "source_ref": self.source_ref,
            "artifact_ops_sha256": self.artifact_ops_sha256,
            "prediction_id": self.prediction_id,
            "prediction_match": self.prediction_match,
        }

    @classmethod
    def from_mapping(cls, row: Mapping[str, Any]) -> EvidenceEvent:
        return cls(
            event_id=row["event_id"],
            kind=EvidenceKind(row["kind"]),
            observed_at=row["observed_at"],
            statement=row["statement"],
            source_ref=row.get("source_ref"),
            artifact_ops_sha256=row.get("artifact_ops_sha256"),
            prediction_id=row.get("prediction_id"),
            prediction_match=row.get("prediction_match"),
        )


@dataclass(frozen=True, slots=True)
class WorldState:
    frontier: Frontier
    instruments: InstrumentSet
    candidate: Candidate | None = None
    calibrations: tuple[Calibration, ...] = ()
    timeline: tuple[EvidenceEvent, ...] = ()
    invalidated: frozenset[Dependency] = frozenset()
    status: PlanStatus = PlanStatus.ACTIVE
    abort_reason: str | None = None

    def __post_init__(self) -> None:
        invalidated = frozenset(self.invalidated)
        if any(not isinstance(dependency, Dependency) for dependency in invalidated):
            raise TypeError("invalidated must contain Dependency values")
        object.__setattr__(self, "invalidated", invalidated)
        event_ids: set[str] = set()
        for event in self.timeline:
            if event.event_id in event_ids:
                raise ValueError(f"duplicate evidence event_id: {event.event_id}")
            event_ids.add(event.event_id)
        if self.status is PlanStatus.ABORTED and not self.abort_reason:
            raise ValueError("an aborted plan requires abort_reason")


@dataclass(frozen=True, slots=True)
class GateDecision:
    allowed: bool
    reasons: tuple[str, ...]
    candidate_score: int | None = None


def append_evidence(state: WorldState, event: EvidenceEvent) -> WorldState:
    """Append one immutable observation and abort on a prediction mismatch."""
    if any(existing.event_id == event.event_id for existing in state.timeline):
        raise ValueError(f"duplicate evidence event_id: {event.event_id}")
    status = state.status
    reason = state.abort_reason
    if event.prediction_match is False:
        status = PlanStatus.ABORTED
        reason = f"prediction mismatch at evidence event {event.event_id}"
    return replace(
        state,
        timeline=state.timeline + (event,),
        status=status,
        abort_reason=reason,
    )


def load_evidence_jsonl(path: Path) -> tuple[EvidenceEvent, ...]:
    """Load and validate an append-only evidence timeline."""
    events: list[EvidenceEvent] = []
    event_ids: set[str] = set()
    with path.open(encoding="utf-8") as source:
        for line_number, line in enumerate(source, start=1):
            if not line.strip():
                continue
            row = json.loads(line)
            event = EvidenceEvent.from_mapping(row)
            if event.event_id in event_ids:
                raise ValueError(f"duplicate event_id {event.event_id} at line {line_number}")
            event_ids.add(event.event_id)
            events.append(event)
    return tuple(events)


def append_evidence_jsonl(path: Path, event: EvidenceEvent) -> None:
    """Append one event without rewriting prior reality rows."""
    if path.exists():
        if any(existing.event_id == event.event_id for existing in load_evidence_jsonl(path)):
            raise ValueError(f"duplicate evidence event_id: {event.event_id}")
    path.parent.mkdir(parents=True, exist_ok=True)
    row = json.dumps(event.to_mapping(), sort_keys=True, separators=(",", ":"))
    with path.open("a", encoding="utf-8") as destination:
        destination.write(row)
        destination.write("\n")
        destination.flush()
        os.fsync(destination.fileno())


def register_calibration(state: WorldState, calibration: Calibration) -> WorldState:
    """Replace one active calibration after anchoring it to the current artifact."""
    active_hash = state.candidate.ops_sha256 if state.candidate is not None else state.frontier.ops_sha256
    if calibration.artifact_ops_sha256 is not None and calibration.artifact_ops_sha256 != active_hash:
        raise ValueError("calibration artifact does not match the active candidate")
    retained = tuple(
        existing for existing in state.calibrations if existing.dependency is not calibration.dependency
    )
    return replace(
        state,
        calibrations=retained + (calibration,),
        invalidated=state.invalidated - {calibration.dependency},
    )


def full_verification_gate(action: Action) -> GateDecision:
    """Decide whether an expensive trusted run is justified, not whether it will pass."""
    impact = action_impact(action.kind)
    reasons: list[str] = []
    if not impact.allow_full_verification:
        reasons.append(f"action_class_blocks_full_verification:{action.kind.value}")
    if action.after_ops_sha256 is None:
        reasons.append("missing_after_ops_hash")
    elif action.after_ops_sha256 == action.before_ops_sha256:
        reasons.append("byte_identical_no_effect")
    if action.prediction.expected_invalidations != impact.invalidated:
        reasons.append("prediction_invalidation_mismatch")
    for missing in sorted(
        impact.required_evidence - action.supporting_evidence,
        key=lambda kind: kind.value,
    ):
        reasons.append(f"missing_discriminating_evidence:{missing.value}")
    return GateDecision(allowed=not reasons, reasons=tuple(reasons))


def apply_action(state: WorldState, action: Action, candidate: Candidate) -> WorldState:
    """Apply one observed candidate transition and invalidate dependent beliefs."""
    active_hash = state.candidate.ops_sha256 if state.candidate is not None else state.frontier.ops_sha256
    if action.before_ops_sha256 != active_hash:
        return replace(
            state,
            status=PlanStatus.ABORTED,
            abort_reason="action parent hash does not match active artifact",
        )
    if action.after_ops_sha256 is None or candidate.ops_sha256 != action.after_ops_sha256:
        return replace(
            state,
            status=PlanStatus.ABORTED,
            abort_reason="candidate hash does not match the observed action result",
        )
    if action.after_ops_sha256 == action.before_ops_sha256:
        return replace(
            state,
            status=PlanStatus.ABORTED,
            abort_reason="byte-identical operation stream; deny expensive verification",
        )
    impact = action_impact(action.kind)
    if action.prediction.expected_invalidations != impact.invalidated:
        return replace(
            state,
            status=PlanStatus.ABORTED,
            abort_reason="observed action invalidations differ from preregistered prediction",
        )
    retained_calibrations = tuple(
        calibration
        for calibration in state.calibrations
        if calibration.dependency not in impact.invalidated
    )
    return replace(
        state,
        candidate=candidate,
        calibrations=retained_calibrations,
        invalidated=state.invalidated | impact.invalidated,
        status=PlanStatus.ACTIVE,
        abort_reason=None,
    )


@dataclass(frozen=True, slots=True)
class Verification:
    evidence_kind: EvidenceKind
    ops_sha256: str | None
    shots: int
    qubits: int | None
    total_toffoli: int | None
    average_toffoli: float | None
    classical_failures: int
    phase_garbage_batches: int
    ancilla_garbage_batches: int

    def __post_init__(self) -> None:
        object.__setattr__(self, "ops_sha256", _require_sha256("ops_sha256", self.ops_sha256))
        _require_nonnegative_int("shots", self.shots)
        if self.qubits is not None:
            _require_nonnegative_int("qubits", self.qubits)
        if self.total_toffoli is not None:
            _require_nonnegative_int("total_toffoli", self.total_toffoli)
        if self.average_toffoli is not None:
            object.__setattr__(
                self,
                "average_toffoli",
                _require_finite_nonnegative("average_toffoli", self.average_toffoli),
            )
        _require_nonnegative_int("classical_failures", self.classical_failures)
        _require_nonnegative_int("phase_garbage_batches", self.phase_garbage_batches)
        _require_nonnegative_int("ancilla_garbage_batches", self.ancilla_garbage_batches)
        if (
            self.total_toffoli is not None
            and self.average_toffoli is not None
            and self.shots > 0
            and self.qubits is not None
        ):
            from_total = score_from_totals(self.total_toffoli, self.shots, self.qubits)
            from_average = exact_score(self.average_toffoli, self.qubits)
            if from_total != from_average:
                raise ValueError("total and average Toffoli imply different benchmark scores")

    @property
    def has_zero_failures(self) -> bool:
        return (
            self.classical_failures == 0
            and self.phase_garbage_batches == 0
            and self.ancilla_garbage_batches == 0
        )

    @property
    def candidate_score(self) -> int | None:
        if self.qubits is None:
            return None
        if self.total_toffoli is not None and self.shots > 0:
            return score_from_totals(self.total_toffoli, self.shots, self.qubits)
        if self.average_toffoli is not None:
            return exact_score(self.average_toffoli, self.qubits)
        return None


def promotion_gate(
    candidate: Candidate,
    verification: Verification,
    refreshed_frontier: Frontier,
) -> GateDecision:
    """Require an exact passing artifact, a fresh parent, and a strict score beat."""
    reasons: list[str] = []
    if candidate.parent_submission_id != refreshed_frontier.submission_id:
        reasons.append("stale_frontier_parent")
    if candidate.ops_sha256 is None:
        reasons.append("missing_candidate_ops_hash")
    if verification.ops_sha256 is None:
        reasons.append("missing_verification_ops_hash")
    elif candidate.ops_sha256 is not None and verification.ops_sha256 != candidate.ops_sha256:
        reasons.append("verification_artifact_mismatch")
    if candidate.ops_sha256 == refreshed_frontier.ops_sha256:
        reasons.append("current_frontier_is_characterization_only")
    if verification.evidence_kind not in {
        EvidenceKind.OFFICIAL_PROMOTED,
        EvidenceKind.TRUSTED_FULL,
    }:
        reasons.append("verification_not_trusted_full_result")
    if verification.shots != FULL_VERIFICATION_SHOTS:
        reasons.append("verification_not_9024_shots")
    if not verification.has_zero_failures:
        reasons.append("trusted_correctness_failure")
    if candidate.qubits is not None and verification.qubits != candidate.qubits:
        reasons.append("verification_qubit_mismatch")
    candidate_score = verification.candidate_score
    if candidate_score is None:
        reasons.append("missing_candidate_score")
    elif candidate_score >= refreshed_frontier.score:
        reasons.append("score_does_not_strictly_improve_frontier")
    return GateDecision(
        allowed=not reasons,
        reasons=tuple(reasons),
        candidate_score=candidate_score,
    )


@dataclass(frozen=True, slots=True)
class HistoryAnchor:
    submission_id: str
    source_ref: str
    score: int
    created_at: str

    def to_mapping(self) -> dict[str, Any]:
        return {
            "submission_id": self.submission_id,
            "source_ref": self.source_ref,
            "score": self.score,
            "created_at": self.created_at,
        }


@dataclass(frozen=True, slots=True)
class HistoryFailure:
    source_index: int
    submission_id: str
    reason: str

    def to_mapping(self) -> dict[str, Any]:
        return {
            "source_index": self.source_index,
            "submission_id": self.submission_id,
            "reason": self.reason,
        }


@dataclass(frozen=True, slots=True)
class HistoryReport:
    promoted_rows_checked: int
    first: HistoryAnchor | None
    last: HistoryAnchor | None
    failures: tuple[HistoryFailure, ...]

    @property
    def verdict(self) -> str:
        return "green" if not self.failures else "red"

    def to_mapping(self) -> dict[str, Any]:
        return {
            "model": "official promoted frontier replay",
            "verdict": self.verdict,
            "promoted_rows_checked": self.promoted_rows_checked,
            "first": self.first.to_mapping() if self.first is not None else None,
            "last": self.last.to_mapping() if self.last is not None else None,
            "failures": [failure.to_mapping() for failure in self.failures],
        }


def backtest_promoted_history(
    payload: Mapping[str, Any] | Sequence[Mapping[str, Any]],
    *,
    expected_count: int | None = None,
    expected_frontier: Frontier | None = None,
) -> HistoryReport:
    """Replay promoted API rows in source order through the exact scorer."""
    if isinstance(payload, Mapping):
        rows = payload.get("submissions")
    else:
        rows = payload
    if not isinstance(rows, Sequence) or isinstance(rows, (str, bytes, bytearray)):
        raise TypeError("submission payload must be a sequence or contain a submissions sequence")

    failures: list[HistoryFailure] = []
    checked = 0
    first: HistoryAnchor | None = None
    last: HistoryAnchor | None = None
    previous_score: int | None = None
    previous_created_at: str | None = None

    for source_index, row in enumerate(rows):
        if not isinstance(row, Mapping):
            failures.append(HistoryFailure(source_index, "<unknown>", "row_is_not_a_mapping"))
            continue
        if row.get("promotionStatus") != "promoted":
            continue
        checked += 1
        submission_id = str(row.get("id") or "<missing>")
        try:
            if row.get("status") != "accepted":
                raise ValueError("promoted_row_status_is_not_accepted")
            if row.get("improved") is not True:
                raise ValueError("promoted_row_not_marked_improved")
            source_ref = _require_nonempty("promotedSourceRef", row.get("promotedSourceRef"))
            created_at = _require_nonempty("createdAt", row.get("createdAt"))
            official_score = row.get("officialScore")
            _require_nonnegative_int("officialScore", official_score)
            metrics = row.get("officialMetrics")
            if not isinstance(metrics, Mapping):
                raise ValueError("officialMetrics_missing")
            qubits = metrics.get("qubits")
            rounded_toffoli = metrics.get("toffoli")
            _require_nonnegative_int("officialMetrics.qubits", qubits)
            _require_nonnegative_int("officialMetrics.toffoli", rounded_toffoli)
            replayed_score = exact_score(float(rounded_toffoli), qubits)
            if replayed_score != official_score:
                raise ValueError(
                    f"score_mismatch:official={official_score}:replayed={replayed_score}"
                )
            if previous_score is not None and official_score >= previous_score:
                raise ValueError(
                    f"frontier_not_strictly_decreasing:previous={previous_score}:current={official_score}"
                )
            if previous_created_at is not None and created_at <= previous_created_at:
                raise ValueError(
                    f"timeline_not_strictly_increasing:previous={previous_created_at}:current={created_at}"
                )
            anchor = HistoryAnchor(
                submission_id=submission_id,
                source_ref=source_ref,
                score=official_score,
                created_at=created_at,
            )
            if first is None:
                first = anchor
            last = anchor
            previous_score = official_score
            previous_created_at = created_at
        except (TypeError, ValueError) as error:
            failures.append(HistoryFailure(source_index, submission_id, str(error)))

    if expected_count is not None:
        _require_nonnegative_int("expected_count", expected_count)
        if checked != expected_count:
            failures.append(
                HistoryFailure(
                    -1,
                    "<corpus>",
                    f"promoted_count_mismatch:expected={expected_count}:actual={checked}",
                )
            )
    if expected_frontier is not None:
        if last is None:
            failures.append(HistoryFailure(-1, "<corpus>", "missing_promoted_frontier"))
        else:
            if last.submission_id != expected_frontier.submission_id:
                failures.append(
                    HistoryFailure(
                        -1,
                        last.submission_id,
                        "latest_submission_does_not_match_expected_frontier",
                    )
                )
            if last.source_ref != expected_frontier.source_ref:
                failures.append(
                    HistoryFailure(
                        -1,
                        last.submission_id,
                        "latest_source_does_not_match_expected_frontier",
                    )
                )
            if last.score != expected_frontier.score:
                failures.append(
                    HistoryFailure(
                        -1,
                        last.submission_id,
                        "latest_score_does_not_match_expected_frontier",
                    )
                )
    return HistoryReport(
        promoted_rows_checked=checked,
        first=first,
        last=last,
        failures=tuple(failures),
    )


CURRENT_FRONTIER = Frontier(
    submission_id="0c5b1b7b-561a-48a0-abc6-5fefaffdc0ad",
    source_ref="cf5aa02147d4e1a698bbf84c10d33920d4356489",
    score=1_490_805_286,
    qubits=1_154,
    rounded_toffoli=1_291_859,
    ops_sha256="7333b19de3f3171a70d1b5132e867b7fb28cd5d77b34668175b391c420eed8c9",
    canonical_ops_sha256="ec90afeadf8d294819e1e2128764c9da8d0742730c09d4ac1ae19d3b1a99dfba",
    emitted_ops=9_062_420,
)

CURRENT_FRONTIER_VERIFICATION = Verification(
    evidence_kind=EvidenceKind.OFFICIAL_PROMOTED,
    ops_sha256=CURRENT_FRONTIER.ops_sha256,
    shots=FULL_VERIFICATION_SHOTS,
    qubits=CURRENT_FRONTIER.qubits,
    total_toffoli=11_657_738_337,
    average_toffoli=1_291_859.302,
    classical_failures=0,
    phase_garbage_batches=0,
    ancilla_garbage_batches=0,
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--backtest-submissions",
        type=Path,
        required=True,
        metavar="SUBMISSIONS_JSON",
        help="JSON export containing the public submissions array",
    )
    parser.add_argument("--expected-promoted", type=int)
    parser.add_argument(
        "--require-current-frontier",
        action="store_true",
        help="require the replay's last row to match the pinned frontier",
    )
    args = parser.parse_args()
    with args.backtest_submissions.open(encoding="utf-8") as source:
        payload = json.load(source)
    report = backtest_promoted_history(
        payload,
        expected_count=args.expected_promoted,
        expected_frontier=CURRENT_FRONTIER if args.require_current_frontier else None,
    )
    print(json.dumps(report.to_mapping(), sort_keys=True))
    return 0 if report.verdict == "green" else 1


if __name__ == "__main__":
    raise SystemExit(main())
