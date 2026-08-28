from __future__ import annotations

import unittest

import h3_affine_shell_rank as affine_rank


class AffineShellRankTests(unittest.TestCase):
    def test_duplicate_features_expose_inconsistent_output_bit(self) -> None:
        first = (0, 0, 0, 0, 0, 0)
        second = (0, 0, 0, 0, 1, 0)
        report = affine_rank.reduce_dataset([first, second])
        self.assertEqual(report["feature_rank"], 1)
        self.assertEqual(report["dependency_rows"], 1)
        self.assertEqual(report["inconsistent_output_bits"], 1)
        self.assertEqual(report["exact_affine_output_bits"], 511)
        self.assertNotIn(0, report["exact_affine_output_indices"])

    def test_independent_rows_can_fit_every_output_bit(self) -> None:
        rows = [(0, 0, 0, 0, 0, 0), (1, 0, 0, 0, 1, 0)]
        report = affine_rank.reduce_dataset(rows)
        self.assertEqual(report["feature_rank"], 2)
        self.assertEqual(report["dependency_rows"], 0)
        self.assertEqual(report["exact_affine_output_bits"], 512)


if __name__ == "__main__":
    unittest.main()
