#!/usr/bin/env python3
"""Search exact-eight joint codecs obtained by fusing adjacent reference shears."""

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
DEFAULT_OUTPUT = REPO_ROOT / ".autoresearch/measurements/y5-joint-codec-neighborhood-v1"
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

    joint_ops, table = joint.configure_problem()
    reference = joint.synth.reference_program(joint_ops)
    if len(reference["shears"]) != joint.REFERENCE_CCX_COUNT:
        raise RuntimeError("reference shear count changed")
    solvers = {
        name: binary
        for name in ("cryptominisat5", "kissat", "cadical")
        if (binary := shutil.which(name)) is not None
    }

    branches: list[dict[str, Any]] = []
    candidate: dict[str, Any] | None = None
    consumed = 0.0
    failures: list[str] = []
    for boundary in range(joint.REFERENCE_CCX_COUNT - 1):
        if consumed >= args.max_local_seconds:
            break
        cnf, variables, branch_table = joint.synth.build_problem(
            BOUND, list(joint.PAIR_INPUTS), exact=True
        )
        template: list[dict[str, Any] | None] = [
            *reference["shears"][:boundary],
            None,
            *reference["shears"][boundary + 2 :],
        ]
        if len(template) != BOUND:
            raise AssertionError("adjacent-fusion template must have eight shears")
        for encoded, expected in zip(variables.shears, template):
            if expected is not None:
                pin_shear(cnf, encoded, expected)

        cnf_path = output / "cnf" / f"fuse-{boundary}-{boundary + 1}.cnf"
        cnf.write(
            cnf_path,
            [
                "exact-eight joint codec with one free shear replacing an adjacent reference pair",
                f"removed_reference_shears={boundary},{boundary + 1}",
                "full-rank affine output map constrained by symbolic right inverse",
            ],
        )
        branch_runs: list[dict[str, Any]] = []
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
                output / "logs" / f"{solver_name}-fuse-{boundary}-{boundary + 1}.log",
                timeout,
                args.resume,
            )
            if solver_run["elapsed_seconds"] is not None:
                consumed += float(solver_run["elapsed_seconds"])
            assignment = set(solver_run.pop("true_variables"))
            branch_runs.append(solver_run)
            if solver_run["status"] != "sat":
                continue
            try:
                program = joint.synth.decode_program(variables, assignment)
                symbolic, compiled, compiled_verification = joint.verify_candidate(
                    program, branch_table, BOUND
                )
            except Exception as error:
                branch_failure = f"SAT witness failed to compile: {error}"
                failures.append(f"branch {boundary}: {branch_failure}")
                break
            if symbolic["verdict"] != "green" or compiled_verification["verdict"] != "green":
                branch_failure = "SAT witness failed exhaustive restricted-domain replay"
                failures.append(f"branch {boundary}: {branch_failure}")
                break
            candidate = {
                "bound": BOUND,
                "fused_reference_shears": [boundary, boundary + 1],
                "solver": solver_name,
                "program": program,
                "symbolic_verification": symbolic,
                "compiled_verification": compiled_verification,
                "compiled_operations": compiled,
                "compiled_operation_count": len(compiled),
                "compiled_ccx": sum(kind == "CCX" for kind, _, _, _ in compiled),
                "rust_table": joint.synth.rust_table(compiled),
            }
            witness_path = output / "witnesses" / f"fuse-{boundary}-{boundary + 1}.json"
            witness_path.write_bytes(canonical_json(candidate) + b"\n")
            candidate["witness_path"] = str(witness_path.relative_to(REPO_ROOT))
            candidate["witness_sha256"] = sha256_file(witness_path)
            break

        branches.append(
            {
                "fused_reference_shears": [boundary, boundary + 1],
                "status": "sat"
                if candidate is not None
                else "instrument-failure"
                if branch_failure is not None
                else "unsat"
                if branch_runs and all(run["status"] == "unsat" for run in branch_runs)
                else "unresolved",
                "failure": branch_failure,
                "cnf": {
                    "path": str(cnf_path.relative_to(REPO_ROOT)),
                    "sha256": sha256_file(cnf_path),
                    "variables": cnf.nvars,
                    "clauses": len(cnf.clauses),
                },
                "solver_runs": branch_runs,
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
        "search_class": "replace each adjacent pair of the nine-shear reference by one arbitrary generalized shear",
        "branches": branches,
        "candidate_found": candidate is not None,
        "candidate": candidate,
        "solver_versions": {
            name: solver_version(binary) for name, binary in solvers.items()
        },
        "source_path": str(Path(__file__).resolve().relative_to(REPO_ROOT)),
        "source_sha256": sha256_file(Path(__file__).resolve()),
        "completeness_contract": {
            "all_eight_adjacent_pairs_attempted": len(branches) == 8,
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
    parser.add_argument("--timeout-seconds", type=int, default=30)
    parser.add_argument("--max-local-seconds", type=float, default=900.0)
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    report = run(args)
    print(json.dumps(report, sort_keys=True, indent=2))
    return 1 if report["verdict"] == "red" else 0


if __name__ == "__main__":
    raise SystemExit(main())
