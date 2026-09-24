from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

import schema_harness as harness
import world_model as wm


HASH_A = "11" * 32
HASH_B = "22" * 32
HASH_C = "33" * 32


def frontier_payload() -> dict[str, object]:
    return {
        "type": "frontier",
        "iteration": 0,
        "submission_id": "frontier",
        "source_ref": "source",
        "ops_sha256": HASH_A,
        "canonical_ops_sha256": HASH_B,
        "score": 20,
        "qubits": 2,
        "rounded_toffoli": 10,
        "ceiling_score": 0,
        "max_iterations": harness.MAX_ITERATIONS,
        "instruments": {
            "verifier_sha256": HASH_A,
            "simulator_sha256": HASH_B,
            "scorer_sha256": HASH_C,
            "identity_sha256": "44" * 32,
        },
    }


def prediction_payload(
    iteration: int,
    *,
    niche: str = "H1-gcd-apply",
    action_kind: wm.ActionKind = wm.ActionKind.NONCE_ONLY,
) -> dict[str, object]:
    return {
        "type": "prediction",
        "iteration": iteration,
        "niche": niche,
        "action_kind": action_kind.value,
        "candidate_id": f"candidate-{iteration}",
        "parent_candidate_id": "frontier" if iteration == 1 else f"candidate-{iteration - 1}",
        "parent_ops_sha256": HASH_A,
        "mechanism": "characterization hypothesis",
        "delta_qubits": 0,
        "delta_toffoli_mean": -1.0,
        "delta_toffoli_standard_deviation": 0.5,
        "correctness_risk": "artifact reseed",
        "full_verification_budget": 0,
        "expected_invalidations": sorted(
            dependency.value for dependency in wm.action_impact(action_kind).invalidated
        ),
    }


def observation_payload(
    iteration: int,
    *,
    prediction_match: bool | None = True,
    verdict: str = "pass",
) -> dict[str, object]:
    return {
        "type": "observation",
        "iteration": iteration,
        "observation_id": f"observation-{iteration}",
        "stage": "proxy",
        "evidence_kind": wm.EvidenceKind.LOW_SHOT_SCREEN.value,
        "verdict": verdict,
        "artifact_ops_sha256": f"{iteration:064x}",
        "prediction_match": prediction_match,
        "measurement": {"samples": 64},
        "conclusion": "recorded proxy outcome",
    }


class SchemaHarnessLedgerTests(unittest.TestCase):
    def test_hash_chain_and_iteration_contract_backtest_green(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            ledger = Path(directory) / "measurements.jsonl"
            first = harness.append_payload(
                ledger, frontier_payload(), recorded_at="2026-07-30T00:00:00Z"
            )
            prediction = harness.append_payload(
                ledger,
                prediction_payload(1),
                recorded_at="2026-07-30T00:01:00Z",
            )
            observation = harness.append_payload(
                ledger,
                observation_payload(1),
                recorded_at="2026-07-30T00:02:00Z",
            )
            records = harness.load_ledger(ledger)
            report = harness.backtest(records)

        self.assertEqual(first["previous_sha256"], harness.ZERO_HASH)
        self.assertEqual(prediction["previous_sha256"], first["record_sha256"])
        self.assertEqual(observation["previous_sha256"], prediction["record_sha256"])
        self.assertEqual(report["verdict"], "green")
        self.assertEqual(report["iterations_completed"], 1)
        self.assertEqual(report["remaining_iterations"], 499)

    def test_prediction_rejects_unknown_niche_and_wrong_invalidation_map(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            ledger = Path(directory) / "measurements.jsonl"
            harness.append_payload(ledger, frontier_payload())
            unknown = prediction_payload(1)
            unknown["niche"] = "unknown"
            with self.assertRaisesRegex(ValueError, "unknown niche"):
                harness.append_payload(ledger, unknown)

            wrong = prediction_payload(1)
            wrong["expected_invalidations"] = []
            with self.assertRaisesRegex(ValueError, "prediction invalidations"):
                harness.append_payload(ledger, wrong)

    def test_measurement_only_prediction_allows_no_effect_but_no_claimed_delta(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            ledger = root / "measurements.jsonl"
            harness.append_payload(ledger, frontier_payload())
            measurement = prediction_payload(1, action_kind=wm.ActionKind.NO_EFFECT)
            measurement["delta_toffoli_mean"] = 0.0
            harness.append_payload(ledger, measurement)

            invalid_ledger = root / "invalid.jsonl"
            harness.append_payload(invalid_ledger, frontier_payload())
            invalid = prediction_payload(1, action_kind=wm.ActionKind.NO_EFFECT)
            with self.assertRaisesRegex(ValueError, "measurement-only"):
                harness.append_payload(invalid_ledger, invalid)

    def test_next_prediction_requires_observation_and_mismatch_reframe(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            ledger = Path(directory) / "measurements.jsonl"
            harness.append_payload(ledger, frontier_payload())
            harness.append_payload(ledger, prediction_payload(1))
            with self.assertRaisesRegex(ValueError, "no observation"):
                harness.append_payload(ledger, prediction_payload(2))

            harness.append_payload(
                ledger,
                observation_payload(1, prediction_match=False, verdict="fail"),
            )
            with self.assertRaisesRegex(ValueError, "requires a reframe"):
                harness.append_payload(ledger, prediction_payload(2))

            harness.append_payload(
                ledger,
                {
                    "type": "reframe",
                    "iteration": 1,
                    "claim": "the original mechanism was false",
                    "compression": "one endogenous artifact state explains the mismatch",
                    "forward_prediction": "the revised discriminator will separate the routes",
                },
            )
            harness.append_payload(ledger, prediction_payload(2))
            self.assertEqual(harness.backtest(harness.load_ledger(ledger))["verdict"], "green")

    def test_tenth_iteration_requires_and_builds_content_addressed_checkpoint(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            ledger = root / "measurements.jsonl"
            harness.append_payload(ledger, frontier_payload())
            niches = tuple(harness.NICHES)
            for iteration in range(1, 11):
                harness.append_payload(
                    ledger,
                    prediction_payload(iteration, niche=niches[(iteration - 1) % len(niches)]),
                )
                harness.append_payload(ledger, observation_payload(iteration))
            before = harness.backtest(harness.load_ledger(ledger))
            self.assertEqual(before["verdict"], "red")
            self.assertIn("missing_checkpoint:10", before["failures"])

            result = harness.checkpoint(ledger, root / "checkpoints", 10)
            after = harness.backtest(harness.load_ledger(ledger))
            summary_path = Path(result["record"]["summary_path"])
            summary_bytes = summary_path.read_bytes().strip()

            self.assertEqual(after["verdict"], "green")
            self.assertEqual(result["summary"]["iteration"], 10)
            self.assertEqual(
                result["record"]["summary_sha256"],
                harness.hashlib.sha256(summary_bytes).hexdigest(),
            )

    def test_tampering_breaks_the_hash_chain(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            ledger = Path(directory) / "measurements.jsonl"
            harness.append_payload(ledger, frontier_payload())
            row = json.loads(ledger.read_text(encoding="utf-8"))
            row["score"] = 18
            ledger.write_text(json.dumps(row) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "record hash mismatch"):
                harness.load_ledger(ledger)

    def test_portfolio_selects_the_least_sampled_niche(self) -> None:
        records = (
            {
                "type": "prediction",
                "niche": "H0-zero-rounding",
                "sequence": 1,
            },
            {
                "type": "prediction",
                "niche": "H1-gcd-apply",
                "sequence": 2,
            },
        )
        selected = harness.select_niche(records)
        self.assertEqual(selected["selected_niche"], "H2-square")

    def test_machine_portfolio_matches_harness_niches_and_score_boundaries(self) -> None:
        portfolio_path = Path(__file__).resolve().parents[1] / "niche_portfolio.json"
        portfolio = json.loads(portfolio_path.read_text(encoding="utf-8"))
        niche_ids = {niche["id"] for niche in portfolio["niches"]}
        self.assertEqual(niche_ids, set(harness.NICHES))
        self.assertTrue(
            all(niche["stepping_stones"] for niche in portfolio["niches"])
        )
        frontier_score = portfolio["frontier"]["score"]
        for boundary in portfolio["strict_improvement_thresholds"]:
            qubits = boundary["qubits"]
            maximum_toffoli = boundary["maximum_rounded_toffoli"]
            self.assertLess(maximum_toffoli * qubits, frontier_score)
            self.assertGreaterEqual((maximum_toffoli + 1) * qubits, frontier_score)


if __name__ == "__main__":
    unittest.main()
