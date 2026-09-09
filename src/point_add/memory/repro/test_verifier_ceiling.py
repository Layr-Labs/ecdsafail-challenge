from __future__ import annotations

import unittest
from pathlib import Path

import h0_classical_independence as independence

import verifier_ceiling as ceiling
import zero_score_lookup as lookup


class VerifierCeilingTests(unittest.TestCase):
    def test_pinned_contract_proves_zero_floor_but_current_witness_does_not_attain_it(self) -> None:
        repo = Path(__file__).resolve().parents[4]
        report = ceiling.verify_bounds(repo, repo / "score.json")
        self.assertEqual(report["verdict"], "green")
        self.assertEqual(report["absolute_score_lower_bound"], 0)
        self.assertEqual(report["best_witness_upper_bound"], 1_490_805_286)
        self.assertEqual(report["open_score_gap"], 1_490_805_286)
        self.assertFalse(report["attained"])
        self.assertEqual(report["achievability_status"], "lower_bound_only")
        self.assertTrue(all(check["green"] for check in report["checks"]))

    def test_zero_rounding_boundary_is_exact(self) -> None:
        self.assertEqual(ceiling.ZERO_SCORE_MAX_TOTAL_TOFFOLI, 4_511)
        self.assertEqual(
            ceiling.score_from_totals(4_511, ceiling.FULL_VERIFICATION_SHOTS, 512),
            0,
        )
        self.assertEqual(
            ceiling.score_from_totals(4_512, ceiling.FULL_VERIFICATION_SHOTS, 512),
            512,
        )


class ZeroScoreLookupTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.powers = lookup._fixed_base_table()

    def test_fixed_base_arithmetic_matches_generator_group(self) -> None:
        infinity, generator, doubled, wrapped = lookup._fixed_base_mul_many(
            [0, 1, 2, lookup.ORDER], self.powers
        )
        self.assertEqual(infinity, (0, 0))
        self.assertEqual(generator, (lookup.GX, lookup.GY))
        self.assertEqual(wrapped, (0, 0))
        self.assertEqual(
            doubled,
            (
                0xC6047F9441ED7D6D3045406E95C07CD85C778E4B8CEF3CA7ABAC09B95C709EE5,
                0x1AE168FEA63DC339A3C58419466CEAEEF7F632653266D0E1236431A950CFE52A,
            ),
        )

    def test_frozen_lookup_is_exact_on_unique_classical_prefixes(self) -> None:
        rows = [
            (1, 2, 0, 0, 5, 7),
            (3, 4, 1, 0, 8, 9),
            (10, 11, 2, 0, 12, 13),
        ]
        width = lookup._minimum_unique_prefix(rows)
        table = lookup._lookup_rows(rows, width)
        failures, hits = lookup._lookup_failures(rows, table, width)
        self.assertEqual(width, 2)
        self.assertEqual(failures, 0)
        self.assertEqual(hits, len(rows))
        self.assertEqual(lookup._lookup_op_count(table, width), 1_061)


class ClassicalIndependenceProofTests(unittest.TestCase):
    def test_pinned_transition_table_blocks_quantum_to_classical_extraction(self) -> None:
        repo = Path(__file__).resolve().parents[4]
        report = independence.verify(repo)
        self.assertEqual(report["verdict"], "green")
        self.assertEqual(report["transition_proof"]["operation_types_checked"], 18)
        self.assertEqual(report["transition_proof"]["classical_writers_checked"], 4)

    def test_quantum_leaking_hmr_breaks_the_inductive_invariant(self) -> None:
        report = independence.verify_independence(hmr_leaks_quantum=True)
        self.assertEqual(report["verdict"], "red")
        self.assertEqual(
            report["failures"],
            ["Hmr:classical_target_depends_on_initial_quantum"],
        )


if __name__ == "__main__":
    unittest.main()
