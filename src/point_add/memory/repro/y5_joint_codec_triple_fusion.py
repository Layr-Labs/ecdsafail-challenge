#!/usr/bin/env python3
"""Search exact-eight joint codecs by replacing each reference triple with two shears."""

from __future__ import annotations

import argparse
import json
import shutil
import time
from pathlib import Path
from typing import Any

import y5_joint_codec_synth as joint
from y1_composite_synth import canonical_json, sha256_file, solver_version

RESEARCH_DIR = Path(__file__).resolve().parent
REPO_ROOT = RESEARCH_DIR.parents[3]
DEFAULT_OUTPUT = REPO_ROOT / ".autoresearch/measurements/y5-joint-codec-triple-fusion-v1"
BOUND = 8


def pin_shear(cnf: joint.synth.Cnf, encoded: joint.synth.ShearVariables, expected: dict[str, Any]) -> None:
    cnf.clause(encoded.enabled)
    for variable_ids, coefficients in (
        (encoded.left, expected["left"]),
        (encoded.right, expected["right"]),
        (encoded.direction, expected["direction"]),
    ):
        for variable, value in zip(variable_ids, coefficients):
            cnf.clause(variable if value else -variable)


def run(args: argparse.Namespace) -> dict[str, Any]:
    started_unix_ns = time.time_ns()
    started = time.monotonic()
    output = args.output.resolve()
    for directory in (output, output / "cnf", output / "logs", output / "witnesses"):
        directory.mkdir(parents=True, exist_ok=True)

    joint_ops, _ = joint.configure_problem()
    reference = joint.synth.reference_program(joint_ops)
    solvers = {
        name: binary
        for name in ("cryptominisat5", "kissat", "cadical")
        if (binary := shutil.which(name)) is not None
    }
    branches: list[dict[str, Any]] = []
    candidate: dict[str, Any] | None = None
    failures: list[str] = []
    consumed = 0.0

    for start_index in range(joint.REFERENCE_CCX_COUNT - 2):
        if consumed >= args.max_local_seconds:
            break
        template: list[dict[str, Any] | None] = [
            *reference["shears"][:start_index],
            None,
            None,
            *reference["shears"][start_index + 3 :],
        ]
        cnf, variables, table = joint.synth.build_problem(
            BOUND, list(joint.PAIR_INPUTS), exact=True
        )
        for encoded, expected in zip(variables.shears, template):
            if expected is not None:
                pin_shear(cnf, encoded, expected)
        branch_id = f"fuse-{start_index}-{start_index + 1}-{start_index + 2}"
        cnf_path = output / "cnf" / f"{branch_id}.cnf"
        cnf.write(
            cnf_path,
            [
                "exact-eight joint codec with two free shears replacing three adjacent reference shears",
                f"removed_reference_shears={start_index},{start_index + 1},{start_index + 2}",
                "full-rank affine output map constrained by symbolic right inverse",
            ],
        )
        solver_runs: list[dict[str, Any]] = []
        branch_failure: str | None = None
        for solver_name in ("cryptominisat5", "kissat", "cadical"):
            binary = solvers.get(solver_name)
            if binary is None or consumed >= args.max_local_seconds:
                continue
            timeout = max(
                1,
                min(args.timeout_seconds, int(args.max_local_seconds - consumed)),
            )
            solver_run = joint.synth.run_solver(
                solver_name,
                binary,
                BOUND,
                cnf_path,
                output / "logs" / f"{solver_name}-{branch_id}.log",
                timeout,
                args.resume,
            )
            if solver_run["elapsed_seconds"] is not None:
                consumed += float(solver_run["elapsed_seconds"])
            assignment = set(solver_run.pop("true_variables"))
            solver_runs.append(solver_run)
            if solver_run["status"] != "sat":
                continue
            try:
                program = joint.synth.decode_program(variables, assignment)
                symbolic, compiled, compiled_verification = joint.verify_candidate(
                    program, table, BOUND
                )
            except Exception as error:
                branch_failure = f"SAT witness failed to compile: {error}"
            else:
                if symbolic["verdict"] != "green" or compiled_verification["verdict"] != "green":
                    branch_failure = "SAT witness failed exhaustive restricted-domain replay"
                else:
                    candidate = {
                        "bound": BOUND,
                        "replaced_reference_shears": [
                            start_index,
                            start_index + 1,
                            start_index + 2,
                        ],
                        "solver": solver_name,
                        "program": program,
                        "symbolic_verification": symbolic,
                        "compiled_verification": compiled_verification,
                        "compiled_operations": compiled,
                        "compiled_operation_count": len(compiled),
                        "compiled_ccx": sum(
                            kind == "CCX" for kind, _, _, _ in compiled
                        ),
                        "rust_table": joint.synth.rust_table(compiled),
                    }
                    witness_path = output / "witnesses" / f"{branch_id}.json"
                    witness_path.write_bytes(canonical_json(candidate) + b"\n")
                    candidate["witness_path"] = str(witness_path.relative_to(REPO_ROOT))
                    candidate["witness_sha256"] = sha256_file(witness_path)
            break
        if branch_failure is not None:
            failures.append(f"{branch_id}: {branch_failure}")
        statuses = {run["solver"]: run["status"] for run in solver_runs}
        branches.append(
            {
                "id": branch_id,
                "replaced_reference_shears": [
                    start_index,
                    start_index + 1,
                    start_index + 2,
                ],
                "status": "instrument-failure"
                if branch_failure is not None
                else "sat"
                if candidate is not None
                else "unsat"
                if solver_runs and all(status == "unsat" for status in statuses.values())
                else "unresolved",
                "failure": branch_failure,
                "cnf_path": str(cnf_path.relative_to(REPO_ROOT)),
                "cnf_sha256": sha256_file(cnf_path),
                "cnf_variables": cnf.nvars,
                "cnf_clauses": len(cnf.clauses),
                "solver_runs": solver_runs,
            }
        )
        if candidate is not None or branch_failure is not None:
            break

    verdict = "red" if failures else "green" if candidate is not None else "yellow"
    report: dict[str, Any] = {
        "schema_version": 1,
        "prediction_id": args.prediction_id,
        "started_unix_ns": started_unix_ns,
        "wall_seconds": time.monotonic() - started,
        "local_cpu_seconds": consumed,
        "verdict": verdict,
        "failures": failures,
        "search_class": "replace each contiguous three-shear block of the nine-shear reference by two arbitrary generalized shears",
        "expected_branches": 7,
        "branches_run": len(branches),
        "branches": branches,
        "candidate_found": candidate is not None,
        "candidate": candidate,
        "solver_versions": {
            name: solver_version(binary) for name, binary in solvers.items()
        },
        "source_path": str(Path(__file__).resolve().relative_to(REPO_ROOT)),
        "source_sha256": sha256_file(Path(__file__).resolve()),
        "completeness_contract": {
            "all_seven_triples_attempted": len(branches) == 7,
            "restricted_domain_forward_inverse_replay": candidate is not None,
            "output_map_explicitly_invertible": True,
            "timeouts_are_not_lower_bounds": True,
        },
    }
    (output / "report.json").write_bytes(canonical_json(report) + b"\n")
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--prediction-id", default="PRED-Y5-JOINT-CODEC-SYNTH-V4")
    parser.add_argument("--timeout-seconds", type=int, default=60)
    parser.add_argument("--max-local-seconds", type=float, default=1200.0)
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    report = run(args)
    print(json.dumps(report, sort_keys=True, indent=2))
    return 1 if report["verdict"] == "red" else 0


if __name__ == "__main__":
    raise SystemExit(main())
