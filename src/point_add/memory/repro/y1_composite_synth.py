#!/usr/bin/env python3
"""Exact small-width XOR-AND synthesis for the restricted GCD cswap/subtract map."""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import shutil
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

RESEARCH_DIR = Path(__file__).resolve().parent
REPO_ROOT = RESEARCH_DIR.parents[3]
DEFAULT_OUTPUT = REPO_ROOT / ".autoresearch/measurements/y1-composite-synth-v1"
INPUT_NAMES = ("u0", "u1", "u2", "v0", "v1", "v2", "t", "s")
OUTPUT_NAMES = INPUT_NAMES
REFERENCE_AND_COUNT = 5


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while chunk := source.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def samples() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for u in range(8):
        if u & 1 == 0:
            continue
        for v_high in range(4):
            for t in range(2):
                v = (v_high << 1) | t
                for s in range(t + 1):
                    swapped_u, swapped_v = (v, u) if s else (u, v)
                    result_v = (swapped_v - swapped_u) & 7 if t else swapped_v
                    inputs = tuple(
                        [(u >> bit) & 1 for bit in range(3)]
                        + [(v >> bit) & 1 for bit in range(3)]
                        + [t, s]
                    )
                    outputs = tuple(
                        [(swapped_u >> bit) & 1 for bit in range(3)]
                        + [(result_v >> bit) & 1 for bit in range(3)]
                        + [t, s]
                    )
                    rows.append(
                        {
                            "u": u,
                            "v": v,
                            "t": t,
                            "s": s,
                            "inputs": inputs,
                            "outputs": outputs,
                        }
                    )
    return rows


class Cnf:
    def __init__(self) -> None:
        self.nvars = 0
        self.clauses: list[list[int]] = []

    def variable(self) -> int:
        self.nvars += 1
        return self.nvars

    def clause(self, *literals: int) -> None:
        self.clauses.append(list(literals))

    def equivalence_and(self, output: int, left: int, right: int) -> None:
        self.clause(-left, -right, output)
        self.clause(left, -output)
        self.clause(right, -output)

    def equivalence_xor(self, output: int, left: int, right: int) -> None:
        self.clause(-left, -right, -output)
        self.clause(-left, right, output)
        self.clause(left, -right, output)
        self.clause(left, right, -output)

    def constrain_xor(self, terms: list[int], expected: int) -> None:
        if not terms:
            if expected:
                self.clauses.append([])
            return
        if len(terms) == 1:
            self.clause(terms[0] if expected else -terms[0])
            return
        accumulator = terms[0]
        for term in terms[1:]:
            output = self.variable()
            self.equivalence_xor(output, accumulator, term)
            accumulator = output
        self.clause(accumulator if expected else -accumulator)

    def write(self, path: Path, comments: list[str]) -> None:
        with path.open("w", encoding="ascii") as destination:
            for comment in comments:
                destination.write(f"c {comment}\n")
            destination.write(f"p cnf {self.nvars} {len(self.clauses)}\n")
            for clause in self.clauses:
                destination.write(" ".join(str(value) for value in clause))
                destination.write(" 0\n")


@dataclass
class ProgramVariables:
    gate_coefficients: list[tuple[list[int], list[int]]]
    output_coefficients: list[list[int]]


def selected_signal_term(
    cnf: Cnf,
    coefficient: int,
    signal: int,
    dynamic: bool,
) -> int | None:
    if not dynamic:
        return coefficient if signal else None
    product = cnf.variable()
    cnf.equivalence_and(product, coefficient, signal)
    return product


def affine_terms_for_sample(
    cnf: Cnf,
    coefficients: list[int],
    primary_values: tuple[int, ...],
    prior_gate_values: list[int],
) -> list[int]:
    basis_values = (1,) + primary_values
    terms: list[int] = []
    for coefficient, value in zip(coefficients[: len(basis_values)], basis_values):
        term = selected_signal_term(cnf, coefficient, value, dynamic=False)
        if term is not None:
            terms.append(term)
    for coefficient, value in zip(coefficients[len(basis_values) :], prior_gate_values):
        term = selected_signal_term(cnf, coefficient, value, dynamic=True)
        if term is not None:
            terms.append(term)
    return terms


def build_problem(and_gates: int) -> tuple[Cnf, ProgramVariables, list[dict[str, Any]]]:
    domain = samples()
    cnf = Cnf()
    affine_basis = 1 + len(INPUT_NAMES)
    gate_coefficients: list[tuple[list[int], list[int]]] = []
    gate_values: list[list[int]] = []

    for gate_index in range(and_gates):
        width = affine_basis + gate_index
        left_coefficients = [cnf.variable() for _ in range(width)]
        right_coefficients = [cnf.variable() for _ in range(width)]
        gate_coefficients.append((left_coefficients, right_coefficients))
        values_for_gate: list[int] = []
        for sample_index, row in enumerate(domain):
            prior = [gate_values[index][sample_index] for index in range(gate_index)]
            left_value = cnf.variable()
            right_value = cnf.variable()
            cnf.constrain_xor(
                affine_terms_for_sample(
                    cnf, left_coefficients, row["inputs"], prior
                )
                + [left_value],
                0,
            )
            cnf.constrain_xor(
                affine_terms_for_sample(
                    cnf, right_coefficients, row["inputs"], prior
                )
                + [right_value],
                0,
            )
            gate_value = cnf.variable()
            cnf.equivalence_and(gate_value, left_value, right_value)
            values_for_gate.append(gate_value)
        gate_values.append(values_for_gate)

    output_coefficients: list[list[int]] = []
    for output_index in range(len(OUTPUT_NAMES)):
        coefficients = [cnf.variable() for _ in range(affine_basis + and_gates)]
        output_coefficients.append(coefficients)
        for sample_index, row in enumerate(domain):
            prior = [gate_values[index][sample_index] for index in range(and_gates)]
            cnf.constrain_xor(
                affine_terms_for_sample(cnf, coefficients, row["inputs"], prior),
                row["outputs"][output_index],
            )

    return cnf, ProgramVariables(gate_coefficients, output_coefficients), domain


def coefficient_bits(variable_ids: list[int], true_variables: set[int]) -> list[int]:
    return [int(variable in true_variables) for variable in variable_ids]


def evaluate_affine(coefficients: list[int], signals: list[int]) -> int:
    value = 0
    for coefficient, signal in zip(coefficients, signals):
        value ^= coefficient & signal
    return value


def decode_program(
    variables: ProgramVariables, true_variables: set[int]
) -> dict[str, Any]:
    gates = [
        {
            "left": coefficient_bits(left, true_variables),
            "right": coefficient_bits(right, true_variables),
        }
        for left, right in variables.gate_coefficients
    ]
    outputs = [
        coefficient_bits(coefficients, true_variables)
        for coefficients in variables.output_coefficients
    ]
    return {"basis": ["1", *INPUT_NAMES], "gates": gates, "outputs": outputs}


def verify_program(program: dict[str, Any], domain: list[dict[str, Any]]) -> dict[str, Any]:
    failures: list[dict[str, Any]] = []
    for sample_index, row in enumerate(domain):
        signals = [1, *row["inputs"]]
        for gate in program["gates"]:
            left = evaluate_affine(gate["left"], signals)
            right = evaluate_affine(gate["right"], signals)
            signals.append(left & right)
        observed = tuple(
            evaluate_affine(coefficients, signals)
            for coefficients in program["outputs"]
        )
        if observed != row["outputs"]:
            failures.append(
                {
                    "sample_index": sample_index,
                    "inputs": row["inputs"],
                    "expected": row["outputs"],
                    "observed": observed,
                }
            )
    return {
        "samples": len(domain),
        "failures": failures,
        "verdict": "green" if not failures else "red",
    }


def solver_version(binary: str) -> str:
    process = subprocess.run(
        [binary, "--version"],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=10,
    )
    return process.stdout.strip().splitlines()[0] if process.stdout.strip() else "unknown"


def parse_solver_output(text: str) -> tuple[str, set[int]]:
    status = "unknown"
    assignment: set[int] = set()
    for line in text.splitlines():
        stripped = line.strip()
        if stripped in {"s SATISFIABLE", "SATISFIABLE", "SAT"}:
            status = "sat"
        elif stripped in {"s UNSATISFIABLE", "UNSATISFIABLE", "UNSAT"}:
            status = "unsat"
        if stripped.startswith("v "):
            for token in stripped[2:].split():
                value = int(token)
                if value > 0:
                    assignment.add(value)
    return status, assignment


def run_solver(
    solver_name: str,
    binary: str,
    and_gates: int,
    cnf_path: Path,
    log_path: Path,
    timeout_seconds: int,
    resume: bool,
) -> dict[str, Any]:
    if resume and log_path.is_file():
        cached_output = log_path.read_text(encoding="utf-8")
        cached_status, cached_assignment = parse_solver_output(cached_output)
        if cached_status in {"sat", "unsat"}:
            cached_returncode = 10 if cached_status == "sat" else 20
            return {
                "solver": solver_name,
                "binary": binary,
                "and_gates": and_gates,
                "status": cached_status,
                "returncode": cached_returncode,
                "returncode_expected": True,
                "elapsed_seconds": None,
                "cached": True,
                "log_path": str(log_path.relative_to(REPO_ROOT)),
                "log_sha256": sha256_file(log_path),
                "true_variables": sorted(cached_assignment),
            }

    started = time.monotonic()
    try:
        process = subprocess.run(
            [binary, str(cnf_path)],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=timeout_seconds,
        )
        output = process.stdout
        returncode: int | None = process.returncode
        timed_out = False
    except subprocess.TimeoutExpired as error:
        partial = error.stdout or ""
        if isinstance(partial, bytes):
            partial = partial.decode(errors="replace")
        output = partial
        returncode = None
        timed_out = True
    elapsed = time.monotonic() - started
    log_path.write_text(output, encoding="utf-8")
    status, assignment = parse_solver_output(output)
    if timed_out:
        status = "timeout"
    expected_returncode = 10 if status == "sat" else 20 if status == "unsat" else None
    return {
        "solver": solver_name,
        "binary": binary,
        "and_gates": and_gates,
        "status": status,
        "returncode": returncode,
        "returncode_expected": returncode == expected_returncode and expected_returncode is not None,
        "elapsed_seconds": elapsed,
        "cached": False,
        "log_path": str(log_path.relative_to(REPO_ROOT)),
        "log_sha256": sha256_file(log_path),
        "true_variables": sorted(assignment),
    }


def run(args: argparse.Namespace) -> dict[str, Any]:
    started_unix_ns = time.time_ns()
    started = time.monotonic()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    cnf_dir = output / "cnf"
    log_dir = output / "logs"
    witness_dir = output / "witnesses"
    cnf_dir.mkdir(exist_ok=True)
    log_dir.mkdir(exist_ok=True)
    witness_dir.mkdir(exist_ok=True)

    solvers: dict[str, str] = {}
    for name in ("kissat", "cadical"):
        binary = shutil.which(name)
        if binary is None:
            raise RuntimeError(f"required solver not found: {name}")
        solvers[name] = binary

    problems: dict[int, tuple[Cnf, ProgramVariables, list[dict[str, Any]]]] = {}
    cnf_metadata: list[dict[str, Any]] = []
    for and_gates in range(args.max_gates + 1):
        problem = build_problem(and_gates)
        problems[and_gates] = problem
        cnf, _, domain = problem
        path = cnf_dir / f"restricted-composite-k{and_gates}.cnf"
        cnf.write(
            path,
            [
                "restricted n=3 GCD cswap then controlled-subtract XOR-AND synthesis",
                f"and_gates={and_gates}",
                f"samples={len(domain)}",
                "domain: u odd; v0=t; s implies t",
            ],
        )
        cnf_metadata.append(
            {
                "and_gates": and_gates,
                "path": str(path.relative_to(REPO_ROOT)),
                "sha256": sha256_file(path),
                "variables": cnf.nvars,
                "clauses": len(cnf.clauses),
            }
        )

    work: list[tuple[str, str, int, Path, Path, int, bool]] = []
    for and_gates in range(args.max_gates + 1):
        cnf_path = cnf_dir / f"restricted-composite-k{and_gates}.cnf"
        for solver_name, binary in solvers.items():
            work.append(
                (
                    solver_name,
                    binary,
                    and_gates,
                    cnf_path,
                    log_dir / f"{solver_name}-k{and_gates}.log",
                    args.timeout_seconds,
                    args.resume,
                )
            )
    with concurrent.futures.ThreadPoolExecutor(max_workers=len(solvers)) as executor:
        solver_runs = list(executor.map(lambda item: run_solver(*item), work))

    errors: list[str] = []
    public_runs: list[dict[str, Any]] = []
    by_solver: dict[str, dict[int, str]] = {name: {} for name in solvers}
    for solver_run in solver_runs:
        assignment = set(solver_run.pop("true_variables"))
        and_gates = solver_run["and_gates"]
        solver_name = solver_run["solver"]
        by_solver[solver_name][and_gates] = solver_run["status"]
        verification: dict[str, Any] | None = None
        witness_path: str | None = None
        witness_sha256: str | None = None
        if solver_run["status"] == "sat":
            _, variables, domain = problems[and_gates]
            program = decode_program(variables, assignment)
            verification = verify_program(program, domain)
            witness = {
                "schema_version": 1,
                "solver": solver_name,
                "and_gates": and_gates,
                "program": program,
                "verification": verification,
            }
            path = witness_dir / f"{solver_name}-k{and_gates}.json"
            path.write_text(json.dumps(witness, sort_keys=True, indent=2) + "\n")
            witness_path = str(path.relative_to(REPO_ROOT))
            witness_sha256 = sha256_file(path)
            if verification["verdict"] != "green":
                errors.append(f"{solver_name} k={and_gates}: SAT model failed semantic replay")
        if solver_run["status"] not in {"sat", "unsat"}:
            errors.append(f"{solver_name} k={and_gates}: unknown solver status")
        if not solver_run["returncode_expected"]:
            errors.append(f"{solver_name} k={and_gates}: unexpected solver return code")
        public_runs.append(
            {
                **solver_run,
                "verification": verification,
                "witness_path": witness_path,
                "witness_sha256": witness_sha256,
            }
        )

    for and_gates in range(args.max_gates + 1):
        statuses = {by_solver[name].get(and_gates) for name in solvers}
        if len(statuses) != 1:
            errors.append(f"solver disagreement at k={and_gates}: {sorted(statuses)}")
    minimal_by_solver: dict[str, int | None] = {}
    for solver_name, statuses in by_solver.items():
        sat_counts = [count for count, status in statuses.items() if status == "sat"]
        minimal = min(sat_counts) if sat_counts else None
        minimal_by_solver[solver_name] = minimal
        if statuses.get(args.max_gates) != "sat":
            errors.append(f"{solver_name}: reference upper-bound k={args.max_gates} is not SAT")
        if minimal is not None:
            for count in range(minimal):
                if statuses.get(count) != "unsat":
                    errors.append(f"{solver_name}: non-monotone status below minimal k={minimal}")
            for count in range(minimal, args.max_gates + 1):
                if statuses.get(count) != "sat":
                    errors.append(f"{solver_name}: non-monotone status above minimal k={minimal}")
    minima = set(minimal_by_solver.values())
    if len(minima) != 1:
        errors.append(f"solvers disagree on minimum: {minimal_by_solver}")
    minimum = next(iter(minima)) if len(minima) == 1 else None

    report: dict[str, Any] = {
        "schema_version": 1,
        "scope": "Y1 restricted n=3 cswap plus controlled-subtract multiplicative complexity",
        "prediction_id": args.prediction_id,
        "domain": {
            "width": 3,
            "inputs": list(INPUT_NAMES),
            "outputs": list(OUTPUT_NAMES),
            "constraints": ["u is odd", "v0 equals t", "s implies t"],
            "samples": len(samples()),
        },
        "reference_and_count": REFERENCE_AND_COUNT,
        "max_gates": args.max_gates,
        "solver_versions": {name: solver_version(binary) for name, binary in solvers.items()},
        "cnfs": cnf_metadata,
        "solver_runs": sorted(public_runs, key=lambda row: (row["and_gates"], row["solver"])),
        "minimal_and_count_by_solver": minimal_by_solver,
        "minimal_and_count": minimum,
        "candidate_found": minimum is not None and minimum < REFERENCE_AND_COUNT,
        "predicted_repeated_call_saving": (
            REFERENCE_AND_COUNT - minimum if minimum is not None else None
        ),
        "errors": errors,
        "started_unix_ns": started_unix_ns,
        "recorded_unix_ns": time.time_ns(),
        "wall_seconds": time.monotonic() - started,
        "verdict": "green" if not errors else "red",
    }
    report["report_sha256"] = hashlib.sha256(canonical_json(report)).hexdigest()
    report_path = output / "report.json"
    report_path.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--max-gates", type=int, default=REFERENCE_AND_COUNT)
    parser.add_argument("--timeout-seconds", type=int, default=600)
    parser.add_argument("--prediction-id", default="PRED-Y1-COMPOSITE-N3-V1")
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    if args.max_gates < REFERENCE_AND_COUNT:
        parser.error(f"--max-gates must be at least {REFERENCE_AND_COUNT}")
    report = run(args)
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0 if report["verdict"] == "green" else 1


if __name__ == "__main__":
    raise SystemExit(main())
