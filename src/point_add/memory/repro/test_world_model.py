from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

import world_model as wm


HASH_B = "ab" * 32
HASH_C = "cd" * 32
INSTRUMENT_HASH = "ef" * 32


def prediction(kind: wm.ActionKind, prediction_id: str) -> wm.Prediction:
    return wm.Prediction(
        prediction_id=prediction_id,
        mechanism=f"characterize {kind.value}",
        delta_qubits=0,
        delta_toffoli_mean=0.0,
        delta_toffoli_standard_deviation=0.0,
        correctness_risk="characterization fixture",
        full_verification_budget=1,
        expected_invalidations=wm.action_impact(kind).invalidated,
    )


def candidate(
    *,
    candidate_id: str = "candidate",
    parent_submission_id: str = wm.CURRENT_FRONTIER.submission_id,
    ops_sha256: str | None = HASH_B,
    source_ref: str = "working-tree:candidate",
    qubits: int | None = 1_154,
) -> wm.Candidate:
    return wm.Candidate(
        candidate_id=candidate_id,
        parent_submission_id=parent_submission_id,
        source_ref=source_ref,
        ops_sha256=ops_sha256,
        nonce=7,
        nonce_policy=wm.NoncePolicy.FIXED,
        qubits=qubits,
    )


def verification(
    *,
    ops_sha256: str | None = HASH_B,
    shots: int = wm.FULL_VERIFICATION_SHOTS,
    qubits: int = 1_154,
    rounded_toffoli: int = 1_291_858,
    classical_failures: int = 0,
    phase_garbage_batches: int = 0,
    ancilla_garbage_batches: int = 0,
    evidence_kind: wm.EvidenceKind = wm.EvidenceKind.TRUSTED_FULL,
) -> wm.Verification:
    return wm.Verification(
        evidence_kind=evidence_kind,
        ops_sha256=ops_sha256,
        shots=shots,
        qubits=qubits,
        total_toffoli=rounded_toffoli * shots,
        average_toffoli=float(rounded_toffoli),
        classical_failures=classical_failures,
        phase_garbage_batches=phase_garbage_batches,
        ancilla_garbage_batches=ancilla_garbage_batches,
    )


def promoted_row(
    submission_id: str,
    source_ref: str,
    created_at: str,
    qubits: int,
    rounded_toffoli: int,
) -> dict[str, object]:
    return {
        "id": submission_id,
        "status": "accepted",
        "officialScore": qubits * rounded_toffoli,
        "officialMetrics": {"qubits": qubits, "toffoli": rounded_toffoli},
        "improved": True,
        "promotionStatus": "promoted",
        "promotedSourceRef": source_ref,
        "createdAt": created_at,
    }


class WorldModelInvalidationTests(unittest.TestCase):
    def test_nonce_only_invalidates_exact_result_but_preserves_function_proof(self) -> None:
        impact = wm.action_impact(wm.ActionKind.NONCE_ONLY)
        self.assertEqual(
            impact.invalidated,
            {
                wm.Dependency.FIAT_SHAMIR_SEED,
                wm.Dependency.TRUSTED_VERIFICATION,
                wm.Dependency.EXECUTED_TOFFOLI_DRAW,
            },
        )
        self.assertIn(wm.Dependency.CIRCUIT_FUNCTION_PROOF, impact.preserved)

        action = wm.Action(
            kind=wm.ActionKind.NONCE_ONLY,
            before_ops_sha256=wm.CURRENT_FRONTIER.ops_sha256,
            after_ops_sha256=HASH_B,
            prediction=prediction(wm.ActionKind.NONCE_ONLY, "nonce-only"),
        )
        self.assertTrue(wm.full_verification_gate(action).allowed)

    def test_geometry_removes_artifact_bound_calibrations(self) -> None:
        instruments = wm.InstrumentSet(
            verifier_sha256="01" * 32,
            simulator_sha256="02" * 32,
            scorer_sha256="03" * 32,
        )
        calibrations = tuple(
            wm.Calibration(
                dependency=dependency,
                artifact_ops_sha256=wm.CURRENT_FRONTIER.ops_sha256,
                instrument_sha256=INSTRUMENT_HASH,
                evidence_id=f"baseline-{dependency.value}",
                samples=1,
            )
            for dependency in (
                wm.Dependency.STRIP_KEYS,
                wm.Dependency.CAP_OPTIMUM,
                wm.Dependency.COST_CALIBRATION,
                wm.Dependency.CLEAN_DENSITY,
            )
        ) + (
            wm.Calibration(
                dependency=wm.Dependency.SCORER_CONTRACT,
                artifact_ops_sha256=None,
                instrument_sha256=INSTRUMENT_HASH,
                evidence_id="exact-scorer",
                samples=416,
            ),
        )
        state = wm.WorldState(
            frontier=wm.CURRENT_FRONTIER,
            instruments=instruments,
            calibrations=calibrations,
        )
        action = wm.Action(
            kind=wm.ActionKind.GEOMETRY,
            before_ops_sha256=wm.CURRENT_FRONTIER.ops_sha256,
            after_ops_sha256=HASH_B,
            prediction=prediction(wm.ActionKind.GEOMETRY, "geometry"),
        )
        transitioned = wm.apply_action(state, action, candidate())

        self.assertIs(transitioned.status, wm.PlanStatus.ACTIVE)
        self.assertEqual(
            {calibration.dependency for calibration in transitioned.calibrations},
            {wm.Dependency.SCORER_CONTRACT},
        )
        for dependency in (
            wm.Dependency.STRIP_KEYS,
            wm.Dependency.CAP_OPTIMUM,
            wm.Dependency.COST_CALIBRATION,
            wm.Dependency.CLEAN_DENSITY,
        ):
            self.assertIn(dependency, transitioned.invalidated)
        self.assertNotIn(wm.Dependency.SCORER_CONTRACT, transitioned.invalidated)

    def test_byte_identical_action_blocks_expensive_verification(self) -> None:
        action = wm.Action(
            kind=wm.ActionKind.NO_EFFECT,
            before_ops_sha256=wm.CURRENT_FRONTIER.ops_sha256,
            after_ops_sha256=wm.CURRENT_FRONTIER.ops_sha256,
            prediction=prediction(wm.ActionKind.NO_EFFECT, "no-effect"),
        )
        decision = wm.full_verification_gate(action)
        self.assertFalse(decision.allowed)
        self.assertIn("byte_identical_no_effect", decision.reasons)

    def test_prediction_mismatch_aborts_transition(self) -> None:
        instruments = wm.InstrumentSet(
            verifier_sha256="01" * 32,
            simulator_sha256="02" * 32,
            scorer_sha256="03" * 32,
        )
        wrong_prediction = wm.Prediction(
            prediction_id="wrong-invalidation-map",
            mechanism="claim a geometry change is nonce-only",
            delta_qubits=-1,
            delta_toffoli_mean=0.0,
            delta_toffoli_standard_deviation=0.0,
            correctness_risk="understated",
            full_verification_budget=1,
            expected_invalidations=wm.action_impact(wm.ActionKind.NONCE_ONLY).invalidated,
        )
        action = wm.Action(
            kind=wm.ActionKind.GEOMETRY,
            before_ops_sha256=wm.CURRENT_FRONTIER.ops_sha256,
            after_ops_sha256=HASH_B,
            prediction=wrong_prediction,
        )
        transitioned = wm.apply_action(
            wm.WorldState(wm.CURRENT_FRONTIER, instruments),
            action,
            candidate(),
        )
        self.assertIs(transitioned.status, wm.PlanStatus.ABORTED)
        self.assertIn("preregistered prediction", transitioned.abort_reason or "")


class PromotionGateTests(unittest.TestCase):
    def test_exact_full_fresh_strict_beat_is_allowed(self) -> None:
        decision = wm.promotion_gate(candidate(), verification(), wm.CURRENT_FRONTIER)
        self.assertTrue(decision.allowed)
        self.assertLess(decision.candidate_score or wm.CURRENT_FRONTIER.score, wm.CURRENT_FRONTIER.score)

    def test_missing_hash_full_pass_freshness_and_score_each_deny_promotion(self) -> None:
        cases = {
            "missing-hash": (
                candidate(ops_sha256=None),
                verification(),
                "missing_candidate_ops_hash",
            ),
            "short-run": (
                candidate(),
                verification(shots=64),
                "verification_not_9024_shots",
            ),
            "failed-run": (
                candidate(),
                verification(classical_failures=1),
                "trusted_correctness_failure",
            ),
            "stale-frontier": (
                candidate(parent_submission_id="older-frontier"),
                verification(),
                "stale_frontier_parent",
            ),
            "non-improving": (
                candidate(),
                verification(rounded_toffoli=wm.CURRENT_FRONTIER.rounded_toffoli),
                "score_does_not_strictly_improve_frontier",
            ),
        }
        for name, (test_candidate, test_verification, expected_reason) in cases.items():
            with self.subTest(name=name):
                decision = wm.promotion_gate(
                    test_candidate,
                    test_verification,
                    wm.CURRENT_FRONTIER,
                )
                self.assertFalse(decision.allowed)
                self.assertIn(expected_reason, decision.reasons)

    def test_q1145_local_miter_counterexample_remains_denied(self) -> None:
        instruments = wm.InstrumentSet(
            verifier_sha256="01" * 32,
            simulator_sha256="02" * 32,
            scorer_sha256="03" * 32,
        )
        local_proof = wm.EvidenceEvent(
            event_id="q1145-local-miter",
            kind=wm.EvidenceKind.SCOPED_MACHINE_PROOF,
            observed_at="2026-07-10T13:30:00Z",
            statement="isolated comparator and carry miters passed",
            source_ref="422f21d:q1145-v3",
            artifact_ops_sha256=HASH_C,
        )
        state = wm.append_evidence(wm.WorldState(wm.CURRENT_FRONTIER, instruments), local_proof)
        self.assertEqual(len(state.timeline), 1)

        q1145_candidate = candidate(
            candidate_id="q1145-v3",
            ops_sha256=HASH_C,
            source_ref="422f21d:q1145-v3",
            qubits=1_145,
        )
        trusted_failure = verification(
            ops_sha256=HASH_C,
            qubits=1_145,
            rounded_toffoli=1_300_000,
            classical_failures=28,
            phase_garbage_batches=20,
        )
        decision = wm.promotion_gate(
            q1145_candidate,
            trusted_failure,
            wm.CURRENT_FRONTIER,
        )
        self.assertFalse(decision.allowed)
        self.assertIn("trusted_correctness_failure", decision.reasons)

    def test_current_frontier_is_a_fixture_not_a_new_promotion(self) -> None:
        frontier_candidate = wm.Candidate(
            candidate_id="cf5aa02-characterization",
            parent_submission_id=wm.CURRENT_FRONTIER.submission_id,
            source_ref=wm.CURRENT_FRONTIER.source_ref,
            ops_sha256=wm.CURRENT_FRONTIER.ops_sha256,
            canonical_ops_sha256=wm.CURRENT_FRONTIER.canonical_ops_sha256,
            nonce_policy=wm.NoncePolicy.INHERITED,
            qubits=wm.CURRENT_FRONTIER.qubits,
            emitted_ops=wm.CURRENT_FRONTIER.emitted_ops,
        )
        decision = wm.promotion_gate(
            frontier_candidate,
            wm.CURRENT_FRONTIER_VERIFICATION,
            wm.CURRENT_FRONTIER,
        )
        self.assertFalse(decision.allowed)
        self.assertEqual(decision.candidate_score, wm.CURRENT_FRONTIER.score)
        self.assertIn("current_frontier_is_characterization_only", decision.reasons)
        self.assertIn("score_does_not_strictly_improve_frontier", decision.reasons)


class EvidenceTimelineTests(unittest.TestCase):
    def test_jsonl_timeline_is_append_only_and_duplicate_safe(self) -> None:
        first = wm.EvidenceEvent(
            event_id="first",
            kind=wm.EvidenceKind.NARRATIVE,
            observed_at="2026-07-29T00:00:00Z",
            statement="prediction registered",
            source_ref=wm.CURRENT_FRONTIER.source_ref,
            prediction_id="prediction-1",
        )
        second = wm.EvidenceEvent(
            event_id="second",
            kind=wm.EvidenceKind.BYTE_IDENTICAL,
            observed_at="2026-07-29T00:01:00Z",
            statement="candidate emitted the baseline operation stream",
            artifact_ops_sha256=wm.CURRENT_FRONTIER.ops_sha256,
            prediction_id="prediction-1",
            prediction_match=False,
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "measurements.jsonl"
            wm.append_evidence_jsonl(path, first)
            wm.append_evidence_jsonl(path, second)
            self.assertEqual(wm.load_evidence_jsonl(path), (first, second))
            with self.assertRaises(ValueError):
                wm.append_evidence_jsonl(path, first)

        instruments = wm.InstrumentSet(
            verifier_sha256="01" * 32,
            simulator_sha256="02" * 32,
            scorer_sha256="03" * 32,
        )
        state = wm.append_evidence(wm.WorldState(wm.CURRENT_FRONTIER, instruments), second)
        self.assertIs(state.status, wm.PlanStatus.ABORTED)
        self.assertIn("second", state.abort_reason or "")


class PromotedHistoryBacktestTests(unittest.TestCase):
    def test_known_lineage_replays_in_strict_frontier_order(self) -> None:
        rows = [
            promoted_row(
                "30c8dede-fa09-466a-b19d-f4d14bc1ad2a",
                "6f7c159b3cc0ce57e9561cf95b35117e0b012ef6",
                "2026-05-30T07:41:45.340Z",
                2_715,
                3_960_753,
            ),
            promoted_row(
                "middle",
                "1111111111111111111111111111111111111111",
                "2026-06-15T00:00:00.000Z",
                1_300,
                1_200_000,
            ),
            promoted_row(
                wm.CURRENT_FRONTIER.submission_id,
                wm.CURRENT_FRONTIER.source_ref,
                "2026-07-28T22:13:48.764Z",
                wm.CURRENT_FRONTIER.qubits,
                wm.CURRENT_FRONTIER.rounded_toffoli,
            ),
        ]
        report = wm.backtest_promoted_history(
            {"submissions": rows},
            expected_count=3,
            expected_frontier=wm.CURRENT_FRONTIER,
        )
        self.assertEqual(report.verdict, "green")
        self.assertEqual(report.promoted_rows_checked, 3)
        self.assertEqual(report.first.score if report.first else None, 10_753_444_395)
        self.assertEqual(report.last.score if report.last else None, wm.CURRENT_FRONTIER.score)

    def test_history_score_corruption_is_rejected(self) -> None:
        row = promoted_row(
            "corrupt",
            "2222222222222222222222222222222222222222",
            "2026-06-01T00:00:00.000Z",
            2_000,
            2_000_000,
        )
        row["officialScore"] = 1
        report = wm.backtest_promoted_history([row], expected_count=1)
        self.assertEqual(report.verdict, "red")
        self.assertIn("score_mismatch", report.failures[0].reason)


if __name__ == "__main__":
    unittest.main()
