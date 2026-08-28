from __future__ import annotations

import math
import tempfile
import unittest
from pathlib import Path

import y5_joint_codec_neighborhood as neighborhood
import y5_joint_codec_synth as joint
import y5_joint_codec_stochastic as stochastic
import y5_joint_codec_triple_fusion as triple_fusion
import y5_joint_codec_two_rebase as two_rebase
import y5_normalizer_synth as normalizer
import y5_pair25_quotient as quotient


class RetainedReproducerContracts(unittest.TestCase):
    def setUp(self) -> None:
        self._width = normalizer.WIDTH
        self._reference_ccx_count = normalizer.REFERENCE_CCX_COUNT
        self._reference_table = normalizer.reference_table

    def tearDown(self) -> None:
        normalizer.WIDTH = self._width
        normalizer.REFERENCE_CCX_COUNT = self._reference_ccx_count
        normalizer.reference_table = self._reference_table

    def test_pair_compressor_derives_the_exact_pair25_domain(self) -> None:
        pair_states = [
            quotient.compress_pair(first, second)
            for first in quotient.VALID_SYMBOLS
            for second in quotient.VALID_SYMBOLS
        ]
        self.assertEqual(len(pair_states), 25)
        self.assertEqual(len(set(pair_states)), 25)
        self.assertEqual(tuple(sorted(pair_states)), normalizer.PAIR25_INPUTS)
        outputs = [normalizer.reference_table()[value] for value in pair_states]
        self.assertEqual(sorted(outputs), list(range(25)))

    def test_joint_reference_is_a_nine_shear_six_wire_permutation(self) -> None:
        operations, table = joint.configure_problem()
        self.assertEqual(len(table), 64)
        self.assertEqual(len(set(table)), 64)
        self.assertEqual(sorted(table[value] for value in joint.PAIR_INPUTS), list(range(25)))

        program = normalizer.reference_program(operations)
        self.assertEqual(len(program["shears"]), 9)
        self.assertEqual(
            normalizer.verify_program(program, table, list(range(64)))["verdict"],
            "green",
        )
        compiled = normalizer.compile_program(program)
        compiled_report = normalizer.verify_compiled(compiled, table, list(range(64)))
        self.assertEqual(compiled_report["verdict"], "green")
        self.assertEqual(compiled_report["ccx"], 9)

    def test_exact_eight_cnf_matches_the_recorded_problem(self) -> None:
        joint.configure_problem()
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            (output / "cnf").mkdir()
            cnf, variables, table, path = joint.build_cnf(8, output)
            self.assertTrue(path.is_file())
        self.assertEqual(cnf.nvars, 11_416)
        self.assertEqual(len(cnf.clauses), 54_051)
        self.assertEqual(len(variables.shears), 8)
        self.assertEqual(len(table), 64)

    def test_stochastic_codec_fitness_distinguishes_exact_noninvertible_drop(self) -> None:
        operations, table = joint.configure_problem()
        reference = stochastic._from_program(normalizer.reference_program(operations))
        domain = list(joint.PAIR_INPUTS)
        targets = [table[value] for value in domain]
        initial_columns = stochastic._columns(domain, joint.WIDTH)
        target_columns = stochastic._columns(targets, joint.WIDTH)
        all_rows = (1 << len(domain)) - 1
        reference_result = stochastic.evaluate_sequence(
            reference, initial_columns, target_columns, all_rows
        )
        dropped_result = stochastic.evaluate_sequence(
            reference[:2] + reference[3:],
            initial_columns,
            target_columns,
            all_rows,
        )
        self.assertEqual(reference_result.fitness, (0, 0, 0))
        self.assertEqual(dropped_result.errors, 0)
        self.assertEqual(dropped_result.output_rank, 5)
        self.assertGreater(dropped_result.fitness, reference_result.fitness)

    def test_neighborhood_branch_counts_match_the_recorded_scopes(self) -> None:
        self.assertEqual(joint.REFERENCE_CCX_COUNT - 1, 8)
        self.assertEqual(
            math.comb(joint.REFERENCE_CCX_COUNT, 2) * two_rebase.BOUND,
            288,
        )
        self.assertEqual(joint.REFERENCE_CCX_COUNT - 2, 7)
        self.assertEqual(neighborhood.BOUND, 8)
        self.assertEqual(triple_fusion.BOUND, 8)


if __name__ == "__main__":
    unittest.main()
