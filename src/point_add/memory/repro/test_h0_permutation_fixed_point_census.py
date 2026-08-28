from __future__ import annotations

import unittest

import h0_permutation_fixed_point_census as permutation
from h0_fixed_point_census import Scope


class SemanticPermutationCensusTests(unittest.TestCase):
    def test_row_variant_count_matches_distinct_serialized_streams(self) -> None:
        variants = list(permutation._row_variants(key=0, correction=3, key_bits=2))
        self.assertEqual(permutation._row_variant_count(0, 3, 2), 16)
        self.assertEqual(len(variants), 16)
        self.assertEqual(len(set(variants)), 16)

    def test_small_exact_census_is_stable(self) -> None:
        report = permutation.census(Scope(half_width=1, rows=1))
        self.assertEqual(report["candidate_tables"], 16)
        self.assertEqual(report["declared_semantic_variants"], 70)
        self.assertEqual(report["checked_semantic_variants"], 70)
        self.assertEqual(report["unique_semantic_sha256"], 70)
        self.assertEqual(report["semantic_sha256_collisions"], 0)
        self.assertEqual(report["fixed_variants"], 8)
        self.assertEqual(report["tables_with_fixed_variant"], 6)


if __name__ == "__main__":
    unittest.main()
