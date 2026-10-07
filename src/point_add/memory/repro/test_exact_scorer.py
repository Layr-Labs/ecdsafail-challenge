#!/usr/bin/env python3

import math
import unittest

from exact_scorer import U64_MAX, score, score_from_totals


class ExactScorerTests(unittest.TestCase):
    def test_rounds_nonnegative_half_up(self) -> None:
        self.assertEqual(score(1.499999, 2), 2)
        self.assertEqual(score(1.5, 2), 4)

    def test_saturates_product_to_u64(self) -> None:
        self.assertEqual(score(float((1 << 64) - 2048), 2), U64_MAX)

    def test_live_frontier_from_average_and_totals(self) -> None:
        expected = 1_490_805_286
        self.assertEqual(score(1_291_859.302, 1_154), expected)
        self.assertEqual(score_from_totals(11_657_738_337, 9_024, 1_154), expected)

    def test_rejects_invalid_averages(self) -> None:
        for value in (-1.0, math.inf, math.nan, float(1 << 64)):
            with self.subTest(value=value), self.assertRaises(ValueError):
                score(value, 1)
        with self.assertRaises(TypeError):
            score(True, 1)

    def test_rejects_invalid_unsigned_inputs(self) -> None:
        for args in ((-1, 1, 1), (1, 0, 1), (1, 1, -1), (1 << 64, 1, 1)):
            with self.subTest(args=args), self.assertRaises(ValueError):
                score_from_totals(*args)
        with self.assertRaises(TypeError):
            score_from_totals(True, 1, 1)


if __name__ == "__main__":
    unittest.main()
