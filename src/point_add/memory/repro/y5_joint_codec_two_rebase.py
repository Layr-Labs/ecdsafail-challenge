#!/usr/bin/env python3
"""Search exact-eight joint codecs near every seven-shear reference subsequence."""

from __future__ import annotations

import argparse
import itertools
import json
import shutil
import time
from pathlib import Path
from typing import Any

import y5_joint_codec_synth as joint
from y1_composite_synth import canonical_json, sha256_file, solver_version

RESEARCH_DIR = Path(__file__).resolve().parent
REPO_ROOT = RESEARCH_DIR.parents[3]
DEFAULT_OUTPUT = REPO_ROOT / ".autoresearch/measurements/y5-joint-codec-two-rebase-v1"
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
    if len(reference["shears"]) != joint.REFERENCE_CCX_COUNT:
        raise RuntimeError("reference shear count changed")
    solver_name = args.solver
    binary = shutil.which(solver_name)
    if binary is None:
        raise RuntimeError(f"required solver not found: {solver_name}")

    branches: list[dict[str, Any]] = []
    candidate: dict[str, Any] | None = None
    consumed = 0.0
    failures: list[str] = []
    pairs = list(itertools.combinations(range(joint.REFERENCE_CCX_COUNT), 2))
    for removed in pairs:
        kept = [
            shear for index, shear in enumerate(reference["shears"]) if index not in removed
        ]
        for insertion in range(BOUND):
            if consumed >= args.max_local_seconds:
                break
            template: list[dict[str, Any] | None] = [
                *kept[:insertion], None, *kept[insertion:]
            ]
            if len(template) != BOUND:
                raise AssertionError("two-rebase template must have eight shears")
            cnf, variables, table = joint.synth.build_problem(
                BOUND, list(joint.PAIR_INPUTS), exact=True
            )
            for encoded, expected in zip(variables.shears, template):
                if expected is not None:
                    pin_shear(cnf, encoded, expected)

            branch_id = f"drop-{removed[0]}-{removed[1]}-insert-{insertion}"
            cnf_path = output / "cnf" / f"{branch_id}.cnf"
            cnf.write(
                cnf_path,
                [
                    "exact-eight joint codec with seven pinned reference shears and one free shear",
                    f"removed_reference_shears={removed[0]},{removed[1]}; free_insertion={insertion}",
                    "full-rank affine output map constrained by symbolic right inverse",
                ],
            )
            timeout = max(
                1,
                min(args.timeout_seconds, int(args.max_local_seconds - consumed)),
            )
            solver_run = joint.synth.run_solver(
                solver_name,
                binary,
                BOUND,
                cnf_path,
                output / "logs" / f"{branch_id}.log",
                timeout,
                args.resume,
            )
            if solver_run["elapsed_seconds"] is not None:
                consumed += float(solver_run["elapsed_seconds"])
            assignment = set(solver_run.pop("true_variables"))
            branch_failure: str | None = None
            if solver_run["status"] == "sat":
                try:
                    program = joint.synth.decode_program(variables, assignment)
                    symbolic, compiled, compiled_verification = joint.verify_candidate(
                        program, table, BOUND
                    )
                except Exception as error:
                    branch_failure = f"SAT witness failed to compile: {error}"
                else:
                    if (
                        symbolic["verdict"] != "green"
                        or compiled_verification["verdict"] != "green"
                    ):
                        branch_failure = "SAT witness failed exhaustive restricted-domain replay"
                    else:
                        candidate = {
                            "bound": BOUND,
                            "removed_reference_shears": list(removed),
                            "free_insertion": insertion,
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
                        candidate["witness_path"] = str(
                            witness_path.relative_to(REPO_ROOT)
                        )
                        candidate["witness_sha256"] = sha256_file(witness_path)
            if branch_failure is not None:
                failures.append(f"{branch_id}: {branch_failure}")
            branches.append(
                {
                    "id": branch_id,
                    "removed_reference_shears": list(removed),
                    "free_insertion": insertion,
                    "status": "instrument-failure"
                    if branch_failure is not None
                    else "sat"
                    if candidate is not None
                    else solver_run["status"],
                    "failure": branch_failure,
                    "cnf_path": str(cnf_path.relative_to(REPO_ROOT)),
                    "cnf_sha256": sha256_file(cnf_path),
                    "cnf_variables": cnf.nvars,
                    "cnf_clauses": len(cnf.clauses),
                    "solver_run": solver_run,
                }
            )
            if candidate is not None or branch_failure is not None:
                break
        if candidate is not None or failures or consumed >= args.max_local_seconds:
            break

    total_branches = len(pairs) * BOUND
    verdict = "red" if failures else "green" if candidate is not None else "yellow"
    report: dict[str, Any] = {
        "schema_version": 1,
        "prediction_id": args.prediction_id,
        "started_unix_ns": started_unix_ns,
        "wall_seconds": time.monotonic() - started,
        "local_cpu_seconds": consumed,
        "verdict": verdict,
        "failures": failures,
        "search_class": "remove every pair of the nine reference shears, preserve the other seven in order, and insert one arbitrary generalized shear at every position",
        "expected_branches": total_branches,
        "branches_run": len(branches),
        "status_counts": {
            status: sum(branch["status"] == status for branch in branches)
            for status in ("sat", "unsat", "timeout", "unknown", "instrument-failure")
        },
        "branches": branches,
        "candidate_found": candidate is not None,
        "candidate": candidate,
        "solver_version": solver_version(binary),
        "source_path": str(Path(__file__).resolve().relative_to(REPO_ROOT)),
        "source_sha256": sha256_file(Path(__file__).resolve()),
        "completeness_contract": {
            "all_288_rebases_settled": len(branches) == total_branches
            and all(branch["status"] in {"sat", "unsat"} for branch in branches),
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
    parser.add_argument("--solver", default="cryptominisat5")
    parser.add_argument("--timeout-seconds", type=int, default=5)
    parser.add_argument("--max-local-seconds", type=float, default=600.0)
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    report = run(args)
    print(json.dumps(report, sort_keys=True, indent=2))
    return 1 if report["verdict"] == "red" else 0


if __name__ == "__main__":
    raise SystemExit(main())
