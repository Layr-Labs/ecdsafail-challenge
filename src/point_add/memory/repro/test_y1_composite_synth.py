from __future__ import annotations

import itertools
import unittest
import subprocess
import tempfile
from pathlib import Path
from unittest import mock

import y1_composite_synth as synth


def clauses_hold(clauses: list[list[int]], assignment: dict[int, int]) -> bool:
    return all(
        any(
            assignment[abs(literal)] == int(literal > 0)
            for literal in clause
        )
        for clause in clauses
    )


class Y1CompositeSynthesisTests(unittest.TestCase):
    def test_domain_has_every_restricted_input_once(self) -> None:
        rows = synth.samples()
        self.assertEqual(len(rows), 48)
        self.assertEqual(len({row["inputs"] for row in rows}), 48)
        for row in rows:
            self.assertEqual(row["u"] & 1, 1)
            self.assertEqual(row["v"] & 1, row["t"])
            self.assertTrue(not row["s"] or row["t"])

    def test_reference_map_is_injective_on_restricted_domain(self) -> None:
        rows = synth.samples()
        self.assertEqual(len({row["outputs"] for row in rows}), len(rows))

    def test_and_tseitin_encoding_has_exact_truth_table(self) -> None:
        cnf = synth.Cnf()
        left = cnf.variable()
        right = cnf.variable()
        output = cnf.variable()
        cnf.equivalence_and(output, left, right)
        for left_value, right_value, output_value in itertools.product(range(2), repeat=3):
            observed = clauses_hold(
                cnf.clauses,
                {left: left_value, right: right_value, output: output_value},
            )
            self.assertEqual(observed, output_value == (left_value & right_value))

    def test_xor_tseitin_encoding_has_exact_truth_table(self) -> None:
        cnf = synth.Cnf()
        left = cnf.variable()
        right = cnf.variable()
        output = cnf.variable()
        cnf.equivalence_xor(output, left, right)
        for left_value, right_value, output_value in itertools.product(range(2), repeat=3):
            observed = clauses_hold(
                cnf.clauses,
                {left: left_value, right: right_value, output: output_value},
            )
            self.assertEqual(observed, output_value == (left_value ^ right_value))

    def test_semantic_replay_rejects_zero_program(self) -> None:
        program = {
            "basis": ["1", *synth.INPUT_NAMES],
            "gates": [],
            "outputs": [[0] * (1 + len(synth.INPUT_NAMES)) for _ in synth.OUTPUT_NAMES],
        }
        report = synth.verify_program(program, synth.samples())
        self.assertEqual(report["verdict"], "red")
        self.assertGreater(len(report["failures"]), 0)

    def test_resume_reuses_completed_solver_log(self) -> None:
        with tempfile.TemporaryDirectory(dir=synth.REPO_ROOT) as directory:
            root = Path(directory)
            cnf_path = root / "case.cnf"
            log_path = root / "case.log"
            cnf_path.write_text("p cnf 0 0\n")
            log_path.write_text("s UNSATISFIABLE\n")
            with mock.patch.object(synth.subprocess, "run") as run:
                report = synth.run_solver(
                    "solver", "/solver", 4, cnf_path, log_path, 1, True
                )
            run.assert_not_called()
            self.assertEqual(report["status"], "unsat")
            self.assertTrue(report["cached"])
            self.assertTrue(report["returncode_expected"])

    def test_timeout_is_recorded_instead_of_raising(self) -> None:
        with tempfile.TemporaryDirectory(dir=synth.REPO_ROOT) as directory:
            root = Path(directory)
            cnf_path = root / "case.cnf"
            log_path = root / "case.log"
            cnf_path.write_text("p cnf 0 0\n")
            timeout = subprocess.TimeoutExpired(
                ["/solver", str(cnf_path)], 1, output=b"c partial solver log\n"
            )
            with mock.patch.object(synth.subprocess, "run", side_effect=timeout):
                report = synth.run_solver(
                    "solver", "/solver", 4, cnf_path, log_path, 1, False
                )
            self.assertEqual(report["status"], "timeout")
            self.assertFalse(report["cached"])
            self.assertFalse(report["returncode_expected"])
            self.assertEqual(log_path.read_text(), "c partial solver log\n")


if __name__ == "__main__":
    unittest.main()
