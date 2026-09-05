from __future__ import annotations

import unittest

import h0_fixed_point_census as fixed_point
import h0_nonce_fixed_point_census as nonce_census
from zero_score_lookup import CANONICAL_RECORD_BYTES


class NonceFixedPointCensusTests(unittest.TestCase):
    def test_nonce_tail_is_two_self_cancelling_x_gates_per_bit(self) -> None:
        tail = nonce_census._nonce_tail(5, 3)
        self.assertEqual(len(tail), 6 * CANONICAL_RECORD_BYTES)

    def test_exact_reduced_nonce_census_is_complete(self) -> None:
        report = nonce_census.census(fixed_point.Scope(1, 1), 2)
        self.assertTrue(report["complete"])
        self.assertEqual(report["checked_pairs"], 64)
        self.assertEqual(report["successful_pairs"], 1)
        self.assertAlmostEqual(report["expected_pair_success_density"], 1 / 16)

    def test_invalid_nonce_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            nonce_census._nonce_tail(4, 2)


if __name__ == "__main__":
    unittest.main()
