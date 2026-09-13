from __future__ import annotations

import unittest

import y3_global_codec as codec


class Y3GlobalCodecTests(unittest.TestCase):
    def test_production_tape_sizes(self) -> None:
        iters, schedule = codec.parse_schedule()
        self.assertEqual(len(schedule), iters)
        self.assertEqual(codec.current_tape_bits(iters, tail4=False), 609)
        self.assertEqual(codec.current_tape_bits(iters, tail4=True), 605)

    def test_terminal_reverse_tree_matches_exact_recurrence(self) -> None:
        _, schedule = codec.parse_schedule()
        rows = codec.enumerate_terminal_tree(schedule, state_cap=1_000)
        self.assertEqual([row["reachable_states"] for row in rows[:4]], [3, 13, 63, 313])
        self.assertEqual(
            [row["unrestricted_states"] for row in rows[:4]],
            [(5**depth + 1) // 2 for depth in range(1, 5)],
        )

    def test_implemented_tail4_decoder_is_injective(self) -> None:
        support = codec.decode_tail4_support()
        self.assertEqual(len(support), 32)
        self.assertTrue(all(len(pattern) == 4 for pattern in support))

    def test_small_inputs_reach_the_pinned_terminal_state(self) -> None:
        _, schedule = codec.parse_schedule()
        for value in range(1, 65):
            dialog, outcome = codec.run_walk(value, schedule)
            self.assertEqual(outcome, "terminal")
            self.assertEqual(len(dialog), len(schedule))


if __name__ == "__main__":
    unittest.main()
