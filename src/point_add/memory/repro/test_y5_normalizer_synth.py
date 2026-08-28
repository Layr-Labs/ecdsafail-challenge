from __future__ import annotations

import unittest

import y5_normalizer_synth as synth


class Y5NormalizerSynthesisTests(unittest.TestCase):
    def test_reference_is_the_expected_five_wire_permutation(self) -> None:
        operations = synth.load_reference_ops()
        table = synth.reference_table(operations)
        self.assertEqual(len(operations), 104)
        self.assertEqual(sum(kind == "CCX" for kind, _, _, _ in operations), 6)
        self.assertEqual(len(set(table)), 32)
        self.assertEqual(synth.anf_report(table)["output_degrees"], [3, 4, 3, 4, 4])

    def test_reference_decomposes_into_six_generalized_shears(self) -> None:
        operations = synth.load_reference_ops()
        table = synth.reference_table(operations)
        program = synth.reference_program(operations)
        self.assertEqual(synth.verify_program(program, table)["verdict"], "green")
        self.assertEqual(len(program["shears"]), 6)
        compiled = synth.compile_program(program)
        report = synth.verify_compiled(compiled, table)
        self.assertEqual(report["verdict"], "green")
        self.assertEqual(report["ccx"], 6)

    def test_generalized_shear_compiles_to_one_ccx_without_ancilla(self) -> None:
        program = {
            "width": 5,
            "shears": [
                {
                    "enabled": 1,
                    "left": [1, 1, 0, 1, 0, 0],
                    "right": [0, 0, 1, 0, 1, 0],
                    "direction": [0, 0, 0, 0, 1],
                }
            ],
            "outputs": [
                [0, 1, 0, 0, 0, 0],
                [0, 0, 1, 0, 0, 0],
                [0, 0, 0, 1, 0, 0],
                [0, 0, 0, 0, 1, 0],
                [0, 0, 0, 0, 0, 1],
            ],
        }
        table = [synth.evaluate_program(program, value) for value in range(32)]
        compiled = synth.compile_program(program)
        report = synth.verify_compiled(compiled, table)
        self.assertEqual(report["verdict"], "green")
        self.assertEqual(report["ccx"], 1)
        self.assertTrue(all(max(first, second, third) < 5 for _, first, second, third in compiled))

    def test_at_most_five_encoding_covers_every_input(self) -> None:
        cnf, variables, table = synth.build_problem(5)
        self.assertEqual(len(table), 32)
        self.assertEqual(len(variables.shears), 5)
        self.assertEqual(len(variables.outputs), 5)
        self.assertGreater(cnf.nvars, 0)
        self.assertGreater(len(cnf.clauses), 0)

    def test_pair25_domain_maps_bijectively_to_canonical_codes(self) -> None:
        table = synth.reference_table()
        outputs = [table[value] for value in synth.PAIR25_INPUTS]
        self.assertEqual(len(synth.PAIR25_INPUTS), 25)
        self.assertEqual(len(set(synth.PAIR25_INPUTS)), 25)
        self.assertEqual(sorted(outputs), list(range(25)))
        _, variables, _ = synth.build_problem(5, list(synth.PAIR25_INPUTS))
        self.assertEqual(len(variables.shears), 5)

    def test_exact_encoding_enables_every_shear(self) -> None:
        cnf, variables, _ = synth.build_problem(
            5, list(synth.PAIR25_INPUTS), exact=True
        )
        unit_clauses = {clause[0] for clause in cnf.clauses if len(clause) == 1}
        self.assertTrue(
            all(shear.enabled in unit_clauses for shear in variables.shears)
        )


if __name__ == "__main__":
    unittest.main()
