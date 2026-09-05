from __future__ import annotations

import json
import subprocess
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path

import dgm_search as dgm
import schema_harness as harness
import test_schema_harness as schema_fixtures
import world_model as wm


HASH_A = "11" * 32
HASH_B = "22" * 32
HASH_C = "33" * 32


def frontier() -> dict[str, object]:
    return {
        "type": "frontier",
        "sequence": 0,
        "submission_id": "frontier-submission",
        "source_ref": "abc1234-source",
        "ops_sha256": HASH_A,
        "canonical_ops_sha256": HASH_B,
        "score": 1_000,
        "rounded_toffoli": 10,
        "qubits": 100,
    }


def prediction(
    iteration: int,
    candidate_id: str,
    parent: str = "abc1234-frontier",
    niche: str = "H1-gcd-apply",
) -> dict[str, object]:
    return {
        "type": "prediction",
        "sequence": iteration,
        "iteration": iteration,
        "candidate_id": candidate_id,
        "parent_candidate_id": parent,
        "niche": niche,
        "delta_qubits": 0,
        "delta_toffoli_mean": -1.0,
        "delta_toffoli_standard_deviation": 0.5,
    }


def node(candidate_id: str, score: float, children: int = 0) -> dgm.ArchiveNode:
    return dgm.ArchiveNode(
        candidate_id=candidate_id,
        parent_candidate_id="root",
        niche="H1-gcd-apply",
        iteration=1,
        status="live",
        frontier_submission_id="submission-root",
        source_ref=f"refs/{candidate_id}",
        artifact_ops_sha256=HASH_A,
        canonical_artifact_sha256=HASH_B,
        actual_score=int(score),
        average_toffoli=score / 100,
        qubits=100,
        emitted_ops=10,
        predicted_score=score,
        prediction_standard_deviation=0.0,
        conservative_score=score,
        functioning=True,
        reproducible=True,
        functioning_children=children,
    )


class DgmArchiveTests(unittest.TestCase):
    def test_archive_has_one_real_root_and_ineligible_external_placeholders(self) -> None:
        records = [
            frontier(),
            prediction(1, "candidate-a"),
            prediction(2, "candidate-b", parent="external-frontier"),
        ]
        archive = {item.candidate_id: item for item in dgm.build_archive(records)}

        self.assertTrue(archive["abc1234-frontier"].functioning)
        self.assertTrue(archive["abc1234-frontier"].reproducible)
        self.assertFalse(archive["external-frontier"].functioning)
        self.assertFalse(archive["external-frontier"].reproducible)
        self.assertEqual(
            [item.candidate_id for item in archive.values() if item.niche == "__frontier__" and item.functioning],
            ["abc1234-frontier"],
        )

    def test_renamed_retained_candidate_owns_same_iteration_full_evidence(self) -> None:
        records = [
            frontier(),
            prediction(1, "predicted-name"),
            {
                "type": "observation",
                "iteration": 1,
                "stage": "full",
                "verdict": "pass",
                "artifact_ops_sha256": HASH_C,
                "measurement": {
                    "average_toffoli": 8.0,
                    "qubits": 100,
                    "score": 800,
                    "classical_failures": 0,
                    "phase_garbage_batches": 0,
                    "ancilla_garbage_batches": 0,
                },
            },
            {
                "type": "candidate",
                "iteration": 1,
                "candidate_id": "retained-name",
                "parent_candidate_id": "abc1234-frontier",
                "niche": "H1-gcd-apply",
                "status": "promoted",
                "source_ref": "retained-source",
                "artifact_ops_sha256": HASH_C,
                "canonical_artifact_sha256": HASH_A,
                "evidence": "trusted full",
            },
        ]
        archive = {item.candidate_id: item for item in dgm.build_archive(records)}

        self.assertFalse(archive["predicted-name"].functioning)
        self.assertTrue(archive["retained-name"].functioning)
        self.assertEqual(archive["retained-name"].actual_score, 800)
        self.assertEqual(archive["retained-name"].predicted_score, 800)

    def test_selection_is_deterministic_and_every_eligible_node_is_nonzero(self) -> None:
        nodes = (node("a", 800), node("b", 900), node("c", 1_000))
        distribution = dgm.parent_distribution(nodes, "H1-gcd-apply")
        first = dgm.choose_parent(
            nodes,
            niche="H1-gcd-apply",
            iteration=17,
            ledger_tail_sha256=HASH_A,
        )
        second = dgm.choose_parent(
            tuple(reversed(nodes)),
            niche="H1-gcd-apply",
            iteration=17,
            ledger_tail_sha256=HASH_A,
        )

        self.assertTrue(all(item[-1] > 0.0 for item in distribution))
        self.assertAlmostEqual(sum(item[-1] for item in distribution), 1.0)
        self.assertEqual(first.to_mapping(), second.to_mapping())

    def test_functioning_child_count_strictly_reduces_equal_quality_weight(self) -> None:
        without_children = node("a", 800, children=0)
        with_children = node("b", 800, children=2)
        distribution = {
            item[0].candidate_id: item for item in dgm.parent_distribution(
                (without_children, with_children), "H1-gcd-apply"
            )
        }
        self.assertGreater(distribution["a"][3], distribution["b"][3])

    def test_selected_problem_niche_keeps_cross_niche_stepping_stones(self) -> None:
        other_niche = replace(node("other", 700), niche="H2-square")
        distribution = dgm.parent_distribution(
            (node("local", 800), other_niche),
            "H1-gcd-apply",
        )
        self.assertEqual(
            {item[0].candidate_id for item in distribution},
            {"local", "other"},
        )

    def test_emitter_ucb_and_mismatch_abductor_are_deterministic(self) -> None:
        first = dgm.select_emitter(
            [frontier()],
            iteration=63,
            ledger_tail_sha256=HASH_A,
        )
        self.assertEqual(first["emitter"], "literature")

        records = [
            frontier(),
            {
                "type": "observation",
                "prediction_match": False,
            },
        ]
        self.assertEqual(
            dgm.select_emitter(
                records,
                iteration=64,
                ledger_tail_sha256=HASH_A,
            )["emitter"],
            "abductor",
        )

        explored = [
            frontier(),
            *[
                {
                    "type": "candidate",
                    "emitter": emitter,
                    "archive_contribution": emitter == "refiner",
                }
                for emitter in dgm.EMITTERS
            ],
        ]
        one = dgm.select_emitter(
            explored,
            iteration=65,
            ledger_tail_sha256=HASH_B,
        )
        two = dgm.select_emitter(
            explored,
            iteration=65,
            ledger_tail_sha256=HASH_B,
        )
        self.assertEqual(one, two)
        self.assertEqual(one["emitter"], "refiner")


class DgmBoundaryTests(unittest.TestCase):
    def test_secret_and_proxy_environment_is_redacted_but_auth_paths_survive(self) -> None:
        clean = dgm.sanitized_environment(
            {
                "PATH": "/bin",
                "HOME": "/safe/home",
                "CODEX_HOME": "/safe/codex",
                "OPENAI_API_KEY": "secret",
                "ECDSAFAIL_TOKEN": "secret",
                "SSH_AUTH_SOCK": "/tmp/agent",
                "HTTPS_PROXY": "http://proxy",
                "LD_PRELOAD": "/bad.so",
            }
        )
        self.assertEqual(clean["HOME"], "/safe/home")
        self.assertEqual(clean["CODEX_HOME"], "/safe/codex")
        self.assertNotIn("OPENAI_API_KEY", clean)
        self.assertNotIn("ECDSAFAIL_TOKEN", clean)
        self.assertNotIn("SSH_AUTH_SOCK", clean)
        self.assertNotIn("HTTPS_PROXY", clean)
        self.assertNotIn("LD_PRELOAD", clean)
        self.assertEqual(clean["CARGO_NET_OFFLINE"], "true")

    def test_candidate_refs_and_mutation_scope_fail_closed(self) -> None:
        self.assertEqual(
            dgm.candidate_ref("safe-id.1"),
            "refs/autoresearch/candidates/safe-id.1",
        )
        for unsafe in ("../escape", "has space", "-option", "a..b"):
            with self.subTest(unsafe=unsafe), self.assertRaises(ValueError):
                dgm.candidate_ref(unsafe)
        self.assertEqual(
            dgm.validate_mutation_paths(["src/point_add/mod.rs"]),
            ("src/point_add/mod.rs",),
        )
        for unsafe in (
            "src/bin/eval_circuit.rs",
            "src/point_add/memory/RIG.md",
            "src/point_add/memory/repro/dgm_search.py",
            "../src/point_add/mod.rs",
        ):
            with self.subTest(unsafe=unsafe), self.assertRaises(ValueError):
                dgm.validate_mutation_paths([unsafe])

    def test_patch_application_rejects_escape_and_symlink_modes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            source = root / "src/point_add"
            source.mkdir(parents=True)
            (source / "mod.rs").write_text("fn old() {}\n", encoding="utf-8")
            subprocess.run(["git", "-C", str(root), "add", "src/point_add/mod.rs"], check=True)
            subprocess.run(
                [
                    "git",
                    "-C",
                    str(root),
                    "-c",
                    "user.name=test",
                    "-c",
                    "user.email=test@example.com",
                    "commit",
                    "-qm",
                    "base",
                ],
                check=True,
            )
            valid = """diff --git a/src/point_add/mod.rs b/src/point_add/mod.rs
--- a/src/point_add/mod.rs
+++ b/src/point_add/mod.rs
@@ -1 +1 @@
-fn old() {}
+fn new() {}
"""
            self.assertEqual(
                dgm.validate_and_apply_patch(root, valid),
                ("src/point_add/mod.rs",),
            )
            escape = valid.replace("src/point_add/mod.rs", "src/bin/eval_circuit.rs")
            with self.assertRaises(ValueError):
                dgm.validate_and_apply_patch(root, escape)
            symlink = """diff --git a/src/point_add/link.rs b/src/point_add/link.rs
new file mode 120000
--- /dev/null
+++ b/src/point_add/link.rs
@@ -0,0 +1 @@
+../../outside
"""
            with self.assertRaises(ValueError):
                dgm.validate_and_apply_patch(root, symlink)

    def test_semantic_hash_outranks_compressed_encoding_hash(self) -> None:
        artifact = {
            "compressed_ops_sha256": HASH_C,
            "canonical_semantic_sha256": HASH_B,
        }
        self.assertTrue(
            dgm.semantic_noop(
                artifact,
                parent_compressed_sha256=HASH_A,
                parent_canonical_sha256=HASH_B,
            )
        )
        self.assertFalse(
            dgm.semantic_noop(
                artifact,
                parent_compressed_sha256=HASH_A,
                parent_canonical_sha256=HASH_A,
            )
        )

    def test_world_model_evidence_gate_blocks_unproved_exact_rewrite(self) -> None:
        base = schema_fixtures.prediction_payload(
            1, action_kind=wm.ActionKind.EXACT_REWRITE
        )
        base["candidate_id"] = "dgm-i001-rewrite"
        reasons = dgm.full_gate_reasons(
            base,
            artifact_ops_sha256=HASH_B,
            supporting_evidence={wm.EvidenceKind.LOW_SHOT_SCREEN},
        )
        self.assertIn(
            "missing_discriminating_evidence:scoped_machine_proof",
            reasons,
        )

        representation = schema_fixtures.prediction_payload(
            1, action_kind=wm.ActionKind.REPRESENTATION
        )
        representation["candidate_id"] = "dgm-i001-representation"
        self.assertEqual(
            dgm.full_gate_reasons(
                representation,
                artifact_ops_sha256=HASH_B,
                supporting_evidence={wm.EvidenceKind.LOW_SHOT_SCREEN},
            ),
            (),
        )

    def test_promotion_report_requires_fresh_frontier_and_exact_clean_beat(self) -> None:
        prediction_row = schema_fixtures.prediction_payload(
            1, action_kind=wm.ActionKind.REPRESENTATION
        )
        prediction_row["candidate_id"] = "dgm-i001-beat"
        prediction_row["parent_frontier_submission_id"] = "frontier-submission"
        artifact = {
            "qubits": 100,
            "emitted_ops": 123,
        }
        result = dgm.StageResult(
            stage="full",
            passed=True,
            conclusion="exact pass",
            evidence_kind=wm.EvidenceKind.TRUSTED_FULL.value,
            artifact_ops_sha256=HASH_B,
            canonical_artifact_sha256=HASH_C,
            measurement={
                "shots": 9_024,
                "qubits": 100,
                "average_toffoli": 8.0,
                "total_toffoli": 8 * 9_024,
                "score": 800,
                "classical_failures": 0,
                "phase_garbage_batches": 0,
                "ancilla_garbage_batches": 0,
            },
        )
        refreshed = wm.Frontier(
            submission_id="frontier-submission",
            source_ref="frontier-source",
            score=1_000,
            qubits=100,
            rounded_toffoli=10,
            ops_sha256=HASH_A,
            canonical_ops_sha256=HASH_A,
            emitted_ops=100,
        )
        accepted = dgm.promotion_report(
            prediction_row,
            candidate_source_ref="refs/autoresearch/candidates/dgm-i001-beat",
            artifact=artifact,
            result=result,
            refreshed_frontier=refreshed,
        )
        self.assertTrue(accepted["allowed"])

        stale = dict(prediction_row)
        stale["parent_frontier_submission_id"] = "older-submission"
        rejected = dgm.promotion_report(
            stale,
            candidate_source_ref="refs/autoresearch/candidates/dgm-i001-beat",
            artifact=artifact,
            result=result,
            refreshed_frontier=refreshed,
        )
        self.assertFalse(rejected["allowed"])
        self.assertIn("stale_frontier_parent", rejected["reasons"])

    def test_evaluator_output_parser_requires_all_exact_channels(self) -> None:
        output = """
  tested shots            : 512
  classical mismatches    : 0
  phase-garbage batches   : 0
  ancilla-garbage batches : 0
  avg executed Toffoli  : 8.250
  total Toffoli (sum)   : 4224 over 512 shots
  qubits                : 100
"""
        parsed = dgm._parse_evaluator_output(output)
        self.assertEqual(parsed["shots"], 512)
        self.assertEqual(parsed["total_toffoli"], 4_224)
        self.assertEqual(parsed["score"], 800)
        with self.assertRaises(ValueError):
            dgm._parse_evaluator_output("tested shots: 512")

    def test_controller_lock_is_exclusive(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            lock = Path(directory) / "dgm.lock"
            with dgm.controller_lock(lock):
                with self.assertRaises(RuntimeError):
                    with dgm.controller_lock(lock):
                        pass

    def test_pending_dgm_crash_recovery_records_error_not_hypothesis_failure(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            ledger = Path(directory) / "measurements.jsonl"
            harness.append_payload(ledger, schema_fixtures.frontier_payload())
            pending = schema_fixtures.prediction_payload(1)
            pending["candidate_id"] = "dgm-i001-test"
            harness.append_payload(ledger, pending)

            recovered = dgm.recover_pending_infrastructure_error(
                ledger,
                conclusion="worker host restarted",
            )
            status = harness.backtest(harness.load_ledger(ledger))

        self.assertEqual(recovered["verdict"], "error")
        self.assertIsNone(recovered["prediction_match"])
        self.assertIsNone(status["pending_iteration"])

    def test_archive_snapshot_json_is_stable(self) -> None:
        records = [frontier(), prediction(1, "candidate-a")]
        first = json.dumps(
            [item.to_mapping() for item in dgm.build_archive(records)],
            sort_keys=True,
            separators=(",", ":"),
        )
        second = json.dumps(
            [item.to_mapping() for item in dgm.build_archive(records)],
            sort_keys=True,
            separators=(",", ":"),
        )
        self.assertEqual(first, second)

    def test_public_frontier_parser_uses_best_promoted_exact_metrics(self) -> None:
        output = """
2684231  solver-a  \x1b[32mpromoted\x1b[39m  1488395734  {"qubits":1154,"toffoli":1289771}  -820494  7726431  7/30/26, 4:13 AM
ce54b72  solver-b  \x1b[31mrejected\x1b[39m  1488395734  {"qubits":1154,"toffoli":1289771}  0  5ac0936  7/30/26, 11:43 AM
9f99e0b  solver-a  \x1b[32mpromoted\x1b[39m  1488026454  {"qubits":1154,"toffoli":1289451}  -369280  5265674  7/30/26, 3:58 PM
"""
        frontier = dgm.parse_public_frontier_table(output)
        self.assertEqual(frontier.submission_id, "9f99e0b")
        self.assertEqual(frontier.source_ref, "5265674")
        self.assertEqual(frontier.score, 1_488_026_454)
        self.assertEqual(frontier.qubits, 1_154)
        self.assertEqual(frontier.rounded_toffoli, 1_289_451)

    def test_promoted_public_seed_updates_certified_best_score(self) -> None:
        records = [
            frontier(),
            {
                "type": "candidate",
                "status": "promoted",
                "official_submission_id": "new-public",
                "actual_score": 700,
            },
        ]
        self.assertEqual(dgm._best_score(records), 700)


if __name__ == "__main__":
    unittest.main()
