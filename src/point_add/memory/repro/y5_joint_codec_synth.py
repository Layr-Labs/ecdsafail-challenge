#!/usr/bin/env python3
"""Exact restricted-domain synthesis for the joint pair compressor and normalizer."""

from __future__ import annotations

import argparse
import json
import shutil
import time
from pathlib import Path
from typing import Any

import y5_normalizer_synth as synth
from y1_composite_synth import canonical_json, sha256_file, solver_version

RESEARCH_DIR = Path(__file__).resolve().parent
REPO_ROOT = RESEARCH_DIR.parents[3]
DEFAULT_OUTPUT = REPO_ROOT / ".autoresearch/measurements/y5-joint-codec-synth-v1"
VALID_SYMBOLS = (0b001, 0b011, 0b100, 0b101, 0b111)
PAIR_INPUTS = tuple(first | (second << 3) for first in VALID_SYMBOLS for second in VALID_SYMBOLS)
WIDTH = 6
REFERENCE_CCX_COUNT = 9
COMPRESSOR_UNITARY: tuple[synth.Gate, ...] = (
    ("X", 3, 0, 0),
    ("CX", 5, 1, 0),
    ("CX", 4, 0, 0),
    ("X", 2, 0, 0),
    ("CCX", 1, 3, 5),
    ("CX", 3, 5, 0),
    ("CX", 3, 0, 0),
    ("CX", 1, 5, 0),
    ("CX", 5, 3, 0),
    ("CCX", 5, 0, 4),
    ("CCX", 3, 4, 5),
)


def configure_problem() -> tuple[list[synth.Gate], list[int]]:
    normalizer_ops = synth.load_reference_ops()
    joint_ops = [*COMPRESSOR_UNITARY, *normalizer_ops]
    if sum(kind == "CCX" for kind, _, _, _ in joint_ops) != REFERENCE_CCX_COUNT:
        raise RuntimeError("joint reference must contain exactly nine CCX gates")

    synth.WIDTH = WIDTH
    synth.REFERENCE_CCX_COUNT = REFERENCE_CCX_COUNT
    table = [synth.simulate_operations(value, joint_ops) for value in range(1 << WIDTH)]
    synth.reference_table = lambda operations=None: table if operations is None else [
        synth.simulate_operations(value, operations) for value in range(1 << WIDTH)
    ]

    pair_outputs = [table[value] for value in PAIR_INPUTS]
    if len(set(PAIR_INPUTS)) != 25 or sorted(pair_outputs) != list(range(25)):
        raise RuntimeError("joint pair25 mapping must be a bijection onto canonical values 0..24")
    return joint_ops, table


def pin_program(cnf: synth.Cnf, variables: synth.SynthesisVariables, program: dict[str, Any]) -> None:
    if len(variables.shears) != len(program["shears"]):
        raise ValueError("program shear count does not match CNF")
    for encoded, expected in zip(variables.shears, program["shears"]):
        cnf.clause(encoded.enabled if expected["enabled"] else -encoded.enabled)
        for variable_ids, coefficients in (
            (encoded.left, expected["left"]),
            (encoded.right, expected["right"]),
            (encoded.direction, expected["direction"]),
        ):
            for variable, value in zip(variable_ids, coefficients):
                cnf.clause(variable if value else -variable)
    for variable_ids, coefficients in zip(variables.outputs, program["outputs"]):
        for variable, value in zip(variable_ids, coefficients):
            cnf.clause(variable if value else -variable)


def public_solver_run(run: dict[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in run.items() if key != "true_variables"}


def build_cnf(
    bound: int,
    output: Path,
    pinned_program: dict[str, Any] | None = None,
) -> tuple[synth.Cnf, synth.SynthesisVariables, list[int], Path]:
    cnf, variables, table = synth.build_problem(bound, list(PAIR_INPUTS), exact=True)
    if pinned_program is not None:
        pin_program(cnf, variables, pinned_program)
    suffix = "-pinned" if pinned_program is not None else ""
    path = output / "cnf" / f"joint-codec-exact-{bound}{suffix}.cnf"
    cnf.write(
        path,
        [
            "six-wire pair compressor plus NORMALIZER_OPS restricted-domain synthesis",
            f"exact_ccx={bound}; valid_inputs=25; invalid_inputs_unbound=39",
            "full-rank affine output map constrained by a symbolic right inverse",
            "enabled generalized shear x <- x + c*(a.x+a0)*(b.x+b0)",
        ],
    )
    return cnf, variables, table, path


def verify_candidate(
    program: dict[str, Any], table: list[int], bound: int
) -> tuple[dict[str, Any], list[synth.Gate], dict[str, Any]]:
    symbolic = synth.verify_program(program, table, list(PAIR_INPUTS))
    compiled = synth.compile_program(program)
    compiled_verification = synth.verify_compiled(compiled, table, list(PAIR_INPUTS))
    compiled_ccx = sum(kind == "CCX" for kind, _, _, _ in compiled)
    if compiled_ccx != bound:
        compiled_verification = {
            **compiled_verification,
            "verdict": "red",
            "failures": [
                *compiled_verification["failures"],
                {"kind": "ccx-count", "expected": bound, "observed": compiled_ccx},
            ],
        }
    return symbolic, compiled, compiled_verification


def run_pinned_reference(
    output: Path,
    solvers: dict[str, str],
    program: dict[str, Any],
) -> tuple[dict[str, Any], float]:
    cnf, _, _, path = build_cnf(REFERENCE_CCX_COUNT, output, program)
    runs: list[dict[str, Any]] = []
    elapsed_total = 0.0
    for solver_name in ("kissat", "cadical"):
        binary = solvers.get(solver_name)
        if binary is None:
            continue
        run = synth.run_solver(
            solver_name,
            binary,
            REFERENCE_CCX_COUNT,
            path,
            output / "logs" / f"{solver_name}-reference-pinned.log",
            120,
            False,
        )
        elapsed_total += float(run["elapsed_seconds"])
        runs.append(public_solver_run(run))
    failures = [
        f"{run['solver']} pinned reference status {run['status']}"
        for run in runs
        if run["status"] != "sat"
    ]
    if not runs:
        failures.append("neither Kissat nor CaDiCaL is available for the pinned reference")
    return {
        "verdict": "green" if not failures else "red",
        "failures": failures,
        "cnf": {
            "path": str(path.relative_to(REPO_ROOT)),
            "sha256": sha256_file(path),
            "variables": cnf.nvars,
            "clauses": len(cnf.clauses),
        },
        "solver_runs": runs,
    }, elapsed_total


def search_bound(
    bound: int,
    output: Path,
    solvers: dict[str, str],
    timeout_seconds: int,
    remaining_seconds: float,
    resume: bool,
) -> tuple[dict[str, Any], dict[str, Any] | None, float]:
    cnf, variables, table, path = build_cnf(bound, output)
    runs: list[dict[str, Any]] = []
    candidate: dict[str, Any] | None = None
    consumed = 0.0
    failures: list[str] = []

    for solver_name in ("cryptominisat5", "kissat", "cadical"):
        binary = solvers.get(solver_name)
        if binary is None or remaining_seconds - consumed <= 0:
            continue
        run_timeout = max(1, min(timeout_seconds, int(remaining_seconds - consumed)))
        run = synth.run_solver(
            solver_name,
            binary,
            bound,
            path,
            output / "logs" / f"{solver_name}-exact-{bound}.log",
            run_timeout,
            resume,
        )
        consumed += float(run["elapsed_seconds"])
        assignment = set(run.pop("true_variables"))
        runs.append(run)
        if run["status"] != "sat":
            continue

        try:
            program = synth.decode_program(variables, assignment)
            symbolic, compiled, compiled_verification = verify_candidate(program, table, bound)
        except Exception as error:
            failures.append(f"{solver_name} SAT witness failed to compile: {error}")
            break
        if symbolic["verdict"] != "green" or compiled_verification["verdict"] != "green":
            failures.append(f"{solver_name} SAT witness failed exhaustive restricted-domain replay")
            break

        candidate = {
            "bound": bound,
            "solver": solver_name,
            "program": program,
            "symbolic_verification": symbolic,
            "compiled_verification": compiled_verification,
            "compiled_operations": compiled,
            "compiled_operation_count": len(compiled),
            "compiled_ccx": sum(kind == "CCX" for kind, _, _, _ in compiled),
            "rust_table": synth.rust_table(compiled),
        }
        witness_path = output / "witnesses" / f"joint-codec-exact-{bound}.json"
        witness_path.write_bytes(canonical_json(candidate) + b"\n")
        candidate["witness_path"] = str(witness_path.relative_to(REPO_ROOT))
        candidate["witness_sha256"] = sha256_file(witness_path)
        break

    statuses = {run["solver"]: run["status"] for run in runs}
    if candidate is not None:
        status = "sat"
    elif failures:
        status = "instrument-failure"
    elif runs and all(value == "unsat" for value in statuses.values()):
        status = "unsat"
    else:
        status = "unresolved"
    return {
        "bound": bound,
        "status": status,
        "failures": failures,
        "cnf": {
            "path": str(path.relative_to(REPO_ROOT)),
            "sha256": sha256_file(path),
            "variables": cnf.nvars,
            "clauses": len(cnf.clauses),
        },
        "solver_runs": runs,
    }, candidate, consumed


def run(args: argparse.Namespace) -> dict[str, Any]:
    started_unix_ns = time.time_ns()
    started = time.monotonic()
    output = args.output.resolve()
    for directory in (output, output / "cnf", output / "logs", output / "witnesses"):
        directory.mkdir(parents=True, exist_ok=True)

    joint_ops, table = configure_problem()
    reference_program = synth.reference_program(joint_ops)
    symbolic_reference = synth.verify_program(reference_program, table, list(range(1 << WIDTH)))
    compiled_reference = synth.compile_program(reference_program)
    compiled_reference_verification = synth.verify_compiled(
        compiled_reference, table, list(range(1 << WIDTH))
    )
    reference_failures: list[str] = []
    if symbolic_reference["verdict"] != "green":
        reference_failures.append("symbolic nine-CCX reference failed all-state replay")
    if compiled_reference_verification["verdict"] != "green":
        reference_failures.append("compiled nine-CCX reference failed all-state forward/inverse replay")
    if sum(kind == "CCX" for kind, _, _, _ in compiled_reference) != REFERENCE_CCX_COUNT:
        reference_failures.append("compiled reference CCX count changed")

    solvers = {
        name: binary
        for name in ("kissat", "cadical", "cryptominisat5")
        if (binary := shutil.which(name)) is not None
    }
    pinned_reference, pinned_elapsed = run_pinned_reference(output, solvers, reference_program)
    if pinned_reference["verdict"] != "green":
        reference_failures.extend(pinned_reference["failures"])

    searches: list[dict[str, Any]] = []
    best_candidate: dict[str, Any] | None = None
    consumed = pinned_elapsed
    if not reference_failures:
        search8, candidate8, elapsed8 = search_bound(
            8,
            output,
            solvers,
            args.timeout_seconds,
            max(0.0, args.max_local_seconds - consumed),
            args.resume,
        )
        searches.append(search8)
        consumed += elapsed8
        best_candidate = candidate8
        if candidate8 is not None and consumed < args.max_local_seconds:
            search7, candidate7, elapsed7 = search_bound(
                7,
                output,
                solvers,
                args.timeout_seconds,
                args.max_local_seconds - consumed,
                args.resume,
            )
            searches.append(search7)
            consumed += elapsed7
            if candidate7 is not None:
                best_candidate = candidate7

    failures = [*reference_failures]
    failures.extend(failure for search in searches for failure in search["failures"])
    if failures:
        verdict = "red"
    elif best_candidate is not None:
        verdict = "green"
    else:
        verdict = "yellow"

    report: dict[str, Any] = {
        "schema_version": 1,
        "prediction_id": args.prediction_id,
        "started_unix_ns": started_unix_ns,
        "wall_seconds": time.monotonic() - started,
        "local_cpu_seconds": consumed,
        "verdict": verdict,
        "failures": failures,
        "domain": {
            "width": WIDTH,
            "inputs": list(PAIR_INPUTS),
            "input_count": len(PAIR_INPUTS),
            "invalid_inputs_unbound": (1 << WIDTH) - len(PAIR_INPUTS),
            "outputs": [table[value] for value in PAIR_INPUTS],
            "outputs_clear_wire_5": all(table[value] < 1 << 5 for value in PAIR_INPUTS),
        },
        "reference": {
            "ccx": REFERENCE_CCX_COUNT,
            "operation_count": len(joint_ops),
            "symbolic_verification": symbolic_reference,
            "compiled_operation_count": len(compiled_reference),
            "compiled_verification": compiled_reference_verification,
            "pinned_invertibility_cnf": pinned_reference,
        },
        "searches": searches,
        "candidate_found": best_candidate is not None,
        "candidate": best_candidate,
        "solver_versions": {
            name: solver_version(binary) for name, binary in solvers.items()
        },
        "source_path": str(Path(__file__).resolve().relative_to(REPO_ROOT)),
        "source_sha256": sha256_file(Path(__file__).resolve()),
        "completeness_contract": {
            "reference_all_64_forward_inverse": symbolic_reference["verdict"] == "green"
            and compiled_reference_verification["verdict"] == "green",
            "output_map_explicitly_invertible": pinned_reference["verdict"] == "green",
            "restricted_domain_forward_inverse_replay": best_candidate is not None,
            "timeouts_are_not_lower_bounds": True,
        },
    }
    report_path = output / "report.json"
    report_path.write_bytes(canonical_json(report) + b"\n")
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--prediction-id", default="PRED-Y5-JOINT-CODEC-SYNTH-V3")
    parser.add_argument("--timeout-seconds", type=int, default=600)
    parser.add_argument("--max-local-seconds", type=float, default=7200.0)
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    report = run(args)
    print(json.dumps(report, sort_keys=True, indent=2))
    return 1 if report["verdict"] == "red" else 0


if __name__ == "__main__":
    raise SystemExit(main())
