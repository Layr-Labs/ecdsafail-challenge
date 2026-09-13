from __future__ import annotations

import unittest

import h0_fixed_point_census as fixed_point


class ReducedFixedPointCensusTests(unittest.TestCase):
    def test_candidate_count_uses_distinct_canonical_keys(self) -> None:
        self.assertEqual(fixed_point.Scope(1, 1).candidate_count, 16)
        self.assertEqual(fixed_point.Scope(1, 2).candidate_count, 96)
        self.assertEqual(fixed_point.Scope(2, 2).candidate_count, 30_720)

    def test_exact_small_censuses_have_stable_fixed_points(self) -> None:
        one_row = fixed_point.census(fixed_point.Scope(1, 1))
        two_rows = fixed_point.census(fixed_point.Scope(2, 2))
        self.assertTrue(one_row["complete"])
        self.assertTrue(two_rows["complete"])
        self.assertEqual(one_row["fixed_points"], 1)
        self.assertEqual(two_rows["fixed_points"], 2)

    def test_production_lookup_family_has_inverse_density_scale(self) -> None:
        log2_states = fixed_point._log2_candidate_states(27, 512, 9_024)
        self.assertGreater(log2_states, 4_700_000)
        self.assertLess(log2_states, 4_800_000)


if __name__ == "__main__":
    unittest.main()
