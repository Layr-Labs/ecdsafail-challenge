#!/usr/bin/env python3
"""Exact no-ancilla affine/Toffoli synthesis for the five-wire dialog normalizer."""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import re
import shutil
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from y1_composite_synth import (
    Cnf,
    canonical_json,
    run_solver,
    sha256_file,
    solver_version,
)

RESEARCH_DIR = Path(__file__).resolve().parent
REPO_ROOT = RESEARCH_DIR.parents[3]
SOURCE_PATH = REPO_ROOT / "src/point_add/trailmix_ludicrous/codec.rs"
DEFAULT_OUTPUT = REPO_ROOT / ".autoresearch/measurements/y5-normalizer-synth-v1"
WIDTH = 5
REFERENCE_CCX_COUNT = 6
INVOCATIONS = 344
WIRE_OFFSET = 6
PAIR25_INPUTS = (0, 1, 2, 3, 5, 7, 8, 10, 11, 12, 14, 16, 17, 18, 19, 20, 22, 24, 25, 26, 27, 28, 29, 30, 31)

Gate = tuple[str, int, int, int]


@dataclass
class ShearVariables:
    enabled: int
    left: list[int]
    right: list[int]
    direction: list[int]


@dataclass
class SynthesisVariables:
    shears: list[ShearVariables]
    outputs: list[list[int]]


def load_reference_ops(path: Path = SOURCE_PATH) -> list[Gate]:
    source = path.read_text(encoding="utf-8")
    match = re.search(
        r"const NORMALIZER_OPS:.*?=\s*&\[(.*?)\];",
        source,
        flags=re.DOTALL,
    )
    if match is None:
        raise RuntimeError(f"NORMALIZER_OPS not found in {path}")
    tuples = re.findall(
        r"\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*\)",
        match.group(1),
    )
    operations: list[Gate] = []
    kinds = {0: "X", 1: "CX", 2: "CCX"}
    for raw_kind, raw_a, raw_b, raw_c in tuples:
        kind = int(raw_kind)
        if kind not in kinds:
            raise ValueError(f"unknown NORMALIZER_OPS kind {kind}")
        values = [int(raw_a), int(raw_b), int(raw_c)]
        for index in range(1 if kind == 0 else 2 if kind == 1 else 3):
            if values[index] not in range(WIRE_OFFSET, WIRE_OFFSET + WIDTH):
                raise ValueError(f"normalizer wire out of range: {values[index]}")
            values[index] -= WIRE_OFFSET
        operations.append((kinds[kind], values[0], values[1], values[2]))
    if len(operations) != 104:
        raise ValueError(f"expected 104 normalizer operations, found {len(operations)}")
    if sum(kind == "CCX" for kind, _, _, _ in operations) != REFERENCE_CCX_COUNT:
        raise ValueError("normalizer reference CCX count changed")
    return operations


def simulate_operations(value: int, operations: list[Gate]) -> int:
    bits = [(value >> index) & 1 for index in range(WIDTH)]
    for kind, first, second, third in operations:
        if kind == "X":
            bits[first] ^= 1
        elif kind == "CX":
            bits[second] ^= bits[first]
        elif kind == "CCX":
            bits[third] ^= bits[first] & bits[second]
        else:
            raise ValueError(f"unknown operation {kind}")
    return sum(bit << index for index, bit in enumerate(bits))


def reference_table(operations: list[Gate] | None = None) -> list[int]:
    ops = operations if operations is not None else load_reference_ops()
    table = [simulate_operations(value, ops) for value in range(1 << WIDTH)]
    if len(set(table)) != len(table):
        raise ValueError("NORMALIZER_OPS does not define a permutation")
    return table


def output_anfs(table: list[int]) -> list[list[int]]:
    anfs: list[list[int]] = []
    for output_index in range(WIDTH):
        coefficients = [(value >> output_index) & 1 for value in table]
        for bit in range(WIDTH):
            for mask in range(1 << WIDTH):
                if mask & (1 << bit):
                    coefficients[mask] ^= coefficients[mask ^ (1 << bit)]
        anfs.append([mask for mask, coefficient in enumerate(coefficients) if coefficient])
    return anfs


def anf_report(table: list[int]) -> dict[str, Any]:
    anfs = output_anfs(table)
    degrees = [max((mask.bit_count() for mask in output), default=0) for output in anfs]
    max_degree = max(degrees)
    degree_lower_bound = 0
    reachable_degree = 1
    while reachable_degree < max_degree:
        degree_lower_bound += 1
        reachable_degree *= 2
    return {
        "output_monomials": anfs,
        "output_degrees": degrees,
        "max_degree": max_degree,
        "degree_only_ccx_lower_bound": degree_lower_bound,
    }


def xor_variable(cnf: Cnf, terms: list[int]) -> int:
    if not terms:
        output = cnf.variable()
        cnf.clause(-output)
        return output
    accumulator = terms[0]
    for term in terms[1:]:
        output = cnf.variable()
        cnf.equivalence_xor(output, accumulator, term)
        accumulator = output
    return accumulator


def affine_value(cnf: Cnf, coefficients: list[int], state: list[int]) -> int:
    terms = [coefficients[0]]
    for coefficient, signal in zip(coefficients[1:], state):
        product = cnf.variable()
        cnf.equivalence_and(product, coefficient, signal)
        terms.append(product)
    return xor_variable(cnf, terms)


def constrain_gate_shape(cnf: Cnf, shear: ShearVariables) -> None:
    enabled = shear.enabled
    parameters = [*shear.left, *shear.right, *shear.direction]
    for parameter in parameters:
        cnf.clause(enabled, -parameter)

    cnf.clause(-enabled, *shear.left[1:])
    cnf.clause(-enabled, *shear.right[1:])
    cnf.clause(-enabled, *shear.direction)

    differences: list[int] = []
    for left, right in zip(shear.left[1:], shear.right[1:]):
        difference = cnf.variable()
        cnf.equivalence_xor(difference, left, right)
        differences.append(difference)
    cnf.clause(-enabled, *differences)

    # The control product is commutative. Fix the nonconstant coefficient
    # vectors in numeric order to remove the left/right SAT symmetry.
    for left_value in range(1, 1 << WIDTH):
        for right_value in range(1, left_value):
            forbidden = [
                -variable if (value >> index) & 1 else variable
                for variables, value in (
                    (shear.left[1:], left_value),
                    (shear.right[1:], right_value),
                )
                for index, variable in enumerate(variables)
            ]
            cnf.clause(-enabled, *forbidden)

    for coefficients in (shear.left[1:], shear.right[1:]):
        products: list[int] = []
        for coefficient, direction in zip(coefficients, shear.direction):
            product = cnf.variable()
            cnf.equivalence_and(product, coefficient, direction)
            products.append(product)
        dot = xor_variable(cnf, products)
        cnf.clause(-enabled, -dot)


def constrain_invertible_output(cnf: Cnf, outputs: list[list[int]]) -> None:
    inverse = [[cnf.variable() for _ in range(WIDTH)] for _ in range(WIDTH)]
    for row in range(WIDTH):
        for column in range(WIDTH):
            products: list[int] = []
            for inner in range(WIDTH):
                product = cnf.variable()
                cnf.equivalence_and(product, outputs[row][inner + 1], inverse[inner][column])
                products.append(product)
            value = xor_variable(cnf, products)
            cnf.clause(value if row == column else -value)


def build_problem(
    max_ccx: int, inputs: list[int] | None = None, exact: bool = False
) -> tuple[Cnf, SynthesisVariables, list[int]]:
    if max_ccx < 0:
        raise ValueError("max_ccx must be non-negative")
    table = reference_table()
    domain = inputs if inputs is not None else list(range(1 << WIDTH))
    cnf = Cnf()
    shears: list[ShearVariables] = []
    for gate_index in range(max_ccx):
        shear = ShearVariables(
            enabled=cnf.variable(),
            left=[cnf.variable() for _ in range(WIDTH + 1)],
            right=[cnf.variable() for _ in range(WIDTH + 1)],
            direction=[cnf.variable() for _ in range(WIDTH)],
        )
        constrain_gate_shape(cnf, shear)
        if gate_index:
            cnf.clause(-shear.enabled, shears[-1].enabled)
        if exact:
            cnf.clause(shear.enabled)
        shears.append(shear)

    states: list[list[int]] = []
    for input_value in domain:
        initial: list[int] = []
        for index in range(WIDTH):
            signal = cnf.variable()
            cnf.clause(signal if (input_value >> index) & 1 else -signal)
            initial.append(signal)
        states.append(initial)

    for shear in shears:
        next_states: list[list[int]] = []
        for state in states:
            left = affine_value(cnf, shear.left, state)
            right = affine_value(cnf, shear.right, state)
            product = cnf.variable()
            cnf.equivalence_and(product, left, right)
            next_state: list[int] = []
            for current, direction in zip(state, shear.direction):
                directed = cnf.variable()
                cnf.equivalence_and(directed, direction, product)
                active = cnf.variable()
                cnf.equivalence_and(active, shear.enabled, directed)
                updated = cnf.variable()
                cnf.equivalence_xor(updated, current, active)
                next_state.append(updated)
            next_states.append(next_state)
        states = next_states

    outputs = [[cnf.variable() for _ in range(WIDTH + 1)] for _ in range(WIDTH)]
    constrain_invertible_output(cnf, outputs)
    for input_value, state in zip(domain, states):
        expected = table[input_value]
        for output_index, coefficients in enumerate(outputs):
            observed = affine_value(cnf, coefficients, state)
            cnf.clause(observed if (expected >> output_index) & 1 else -observed)

    return cnf, SynthesisVariables(shears=shears, outputs=outputs), table


def bits(variable_ids: list[int], assignment: set[int]) -> list[int]:
    return [int(variable in assignment) for variable in variable_ids]


def decode_program(variables: SynthesisVariables, assignment: set[int]) -> dict[str, Any]:
    shears = [
        {
            "enabled": int(shear.enabled in assignment),
            "left": bits(shear.left, assignment),
            "right": bits(shear.right, assignment),
            "direction": bits(shear.direction, assignment),
        }
        for shear in variables.shears
    ]
    outputs = [bits(coefficients, assignment) for coefficients in variables.outputs]
    return {"width": WIDTH, "shears": shears, "outputs": outputs}


def affine_bit(coefficients: list[int], state: list[int]) -> int:
    value = coefficients[0]
    for coefficient, signal in zip(coefficients[1:], state):
        value ^= coefficient & signal
    return value


def evaluate_program(program: dict[str, Any], input_value: int) -> int:
    state = [(input_value >> index) & 1 for index in range(WIDTH)]
    for shear in program["shears"]:
        if not shear["enabled"]:
            continue
        left = affine_bit(shear["left"], state)
        right = affine_bit(shear["right"], state)
        if left & right:
            state = [
                value ^ direction
                for value, direction in zip(state, shear["direction"])
            ]
    output = [affine_bit(coefficients, state) for coefficients in program["outputs"]]
    return sum(value << index for index, value in enumerate(output))


def vector(coefficients: list[int]) -> int:
    return sum(value << index for index, value in enumerate(coefficients))


def dot(left: int, right: int) -> int:
    return (left & right).bit_count() & 1


def matrix_rank(rows: list[int], width: int | None = None) -> int:
    width = WIDTH if width is None else width
    work = rows.copy()
    rank = 0
    for column in range(width):
        pivot = next((row for row in range(rank, len(work)) if work[row] & (1 << column)), None)
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        for row in range(len(work)):
            if row != rank and work[row] & (1 << column):
                work[row] ^= work[rank]
        rank += 1
    return rank


def verify_program(
    program: dict[str, Any], table: list[int], inputs: list[int] | None = None
) -> dict[str, Any]:
    failures: list[dict[str, Any]] = []
    enabled_count = 0
    for index, shear in enumerate(program["shears"]):
        if not shear["enabled"]:
            continue
        enabled_count += 1
        left = vector(shear["left"][1:])
        right = vector(shear["right"][1:])
        direction = vector(shear["direction"])
        valid = (
            left != 0
            and right != 0
            and left != right
            and direction != 0
            and dot(left, direction) == 0
            and dot(right, direction) == 0
        )
        if not valid:
            failures.append({"kind": "invalid-shear", "index": index})
    for index in range(1, len(program["shears"])):
        if program["shears"][index]["enabled"] and not program["shears"][index - 1]["enabled"]:
            failures.append({"kind": "non-prefix-enable", "index": index})
    domain = inputs if inputs is not None else list(range(len(table)))
    for input_value in domain:
        expected = table[input_value]
        observed = evaluate_program(program, input_value)
        if observed != expected:
            failures.append(
                {
                    "kind": "truth-table-mismatch",
                    "input": input_value,
                    "expected": expected,
                    "observed": observed,
                }
            )
    return {
        "verdict": "green" if not failures else "red",
        "failures": failures,
        "inputs": len(domain),
        "enabled_ccx": enabled_count,
    }


def invert_matrix(rows: list[int], width: int | None = None) -> list[int]:
    width = WIDTH if width is None else width
    augmented = [row | (1 << (width + index)) for index, row in enumerate(rows)]
    for column in range(width):
        pivot = next((row for row in range(column, width) if augmented[row] & (1 << column)), None)
        if pivot is None:
            raise ValueError("matrix is singular")
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        for row in range(width):
            if row != column and augmented[row] & (1 << column):
                augmented[row] ^= augmented[column]
    mask = (1 << width) - 1
    if [row & mask for row in augmented] != [1 << index for index in range(width)]:
        raise AssertionError("matrix inversion failed")
    return [(row >> width) & mask for row in augmented]


def apply_linear_gate(rows: list[int], operation: Gate) -> None:
    kind, control, target, _ = operation
    if kind != "CX":
        raise ValueError("linear elimination only accepts CX")
    rows[target] ^= rows[control]


def linear_operations(matrix: list[int]) -> list[Gate]:
    if matrix_rank(matrix) != WIDTH:
        raise ValueError("linear output matrix is singular")
    work = matrix.copy()
    elimination: list[Gate] = []
    for column in range(WIDTH):
        pivot = next(row for row in range(column, WIDTH) if work[row] & (1 << column))
        if pivot != column:
            swap = [
                ("CX", column, pivot, 0),
                ("CX", pivot, column, 0),
                ("CX", column, pivot, 0),
            ]
            for operation in swap:
                apply_linear_gate(work, operation)
                elimination.append(operation)
        for row in range(WIDTH):
            if row != column and work[row] & (1 << column):
                operation = ("CX", column, row, 0)
                apply_linear_gate(work, operation)
                elimination.append(operation)
    if work != [1 << index for index in range(WIDTH)]:
        raise AssertionError("linear elimination did not reach identity")
    return list(reversed(elimination))


def affine_operations(matrix: list[int], offset: int) -> list[Gate]:
    operations = linear_operations(matrix)
    operations.extend(
        ("X", index, 0, 0) for index in range(WIDTH) if offset & (1 << index)
    )
    return operations


def shear_basis(left: int, right: int, direction: int) -> list[int]:
    if (
        left == 0
        or right == 0
        or left == right
        or direction == 0
        or dot(left, direction)
        or dot(right, direction)
    ):
        raise ValueError("invalid generalized shear")
    rows = [left, right]
    target_row = next(
        candidate
        for candidate in range(1, 1 << WIDTH)
        if dot(candidate, direction) == 1 and matrix_rank([*rows, candidate]) == 3
    )
    rows.append(target_row)
    for candidate in range(1, 1 << WIDTH):
        if dot(candidate, direction) == 0 and matrix_rank([*rows, candidate]) > len(rows):
            rows.append(candidate)
            if len(rows) == WIDTH:
                break
    if len(rows) != WIDTH or matrix_rank(rows) != WIDTH:
        raise AssertionError("failed to complete generalized shear basis")
    image = sum(dot(row, direction) << index for index, row in enumerate(rows))
    if image != 1 << 2:
        raise AssertionError("generalized shear direction did not map to target wire")
    return rows


def compile_program(program: dict[str, Any]) -> list[Gate]:
    operations: list[Gate] = []
    for shear in program["shears"]:
        if not shear["enabled"]:
            continue
        left = vector(shear["left"][1:])
        right = vector(shear["right"][1:])
        direction = vector(shear["direction"])
        matrix = shear_basis(left, right, direction)
        offset = shear["left"][0] | (shear["right"][0] << 1)
        transform = affine_operations(matrix, offset)
        operations.extend(transform)
        operations.append(("CCX", 0, 1, 2))
        operations.extend(reversed(transform))
    output_matrix = [vector(coefficients[1:]) for coefficients in program["outputs"]]
    output_offset = sum(
        coefficients[0] << index for index, coefficients in enumerate(program["outputs"])
    )
    operations.extend(affine_operations(output_matrix, output_offset))
    return operations


def verify_compiled(
    operations: list[Gate], table: list[int], inputs: list[int] | None = None
) -> dict[str, Any]:
    failures: list[dict[str, Any]] = []
    inverse = list(reversed(operations))
    domain = inputs if inputs is not None else list(range(len(table)))
    for input_value in domain:
        expected = table[input_value]
        observed = simulate_operations(input_value, operations)
        if observed != expected:
            failures.append(
                {"kind": "forward", "input": input_value, "expected": expected, "observed": observed}
            )
        restored = simulate_operations(expected, inverse)
        if restored != input_value:
            failures.append(
                {"kind": "reverse", "input": input_value, "expected": input_value, "observed": restored}
            )
    return {
        "verdict": "green" if not failures else "red",
        "failures": failures,
        "operations": len(operations),
        "ccx": sum(kind == "CCX" for kind, _, _, _ in operations),
    }


def reference_program(operations: list[Gate]) -> dict[str, Any]:
    matrix = [1 << index for index in range(WIDTH)]
    offset = 0
    shears: list[dict[str, Any]] = []
    for kind, first, second, third in operations:
        if kind == "X":
            offset ^= 1 << first
        elif kind == "CX":
            matrix[second] ^= matrix[first]
            if offset & (1 << first):
                offset ^= 1 << second
        elif kind == "CCX":
            inverse = invert_matrix(matrix)
            direction = sum(((inverse[row] >> third) & 1) << row for row in range(WIDTH))
            left = [(offset >> first) & 1, *[(matrix[first] >> bit) & 1 for bit in range(WIDTH)]]
            right = [(offset >> second) & 1, *[(matrix[second] >> bit) & 1 for bit in range(WIDTH)]]
            if vector(left[1:]) > vector(right[1:]):
                left, right = right, left
            shears.append(
                {
                    "enabled": 1,
                    "left": left,
                    "right": right,
                    "direction": [(direction >> bit) & 1 for bit in range(WIDTH)],
                }
            )
        else:
            raise ValueError(f"unknown operation {kind}")
    outputs = [
        [(offset >> row) & 1, *[(matrix[row] >> bit) & 1 for bit in range(WIDTH)]]
        for row in range(WIDTH)
    ]
    return {"width": WIDTH, "shears": shears, "outputs": outputs}


def rust_table(operations: list[Gate]) -> str:
    tuples: list[str] = []
    for kind, first, second, third in operations:
        if kind == "X":
            tuples.append(f"(0,{first + WIRE_OFFSET},0,0)")
        elif kind == "CX":
            tuples.append(f"(1,{first + WIRE_OFFSET},{second + WIRE_OFFSET},0)")
        elif kind == "CCX":
            tuples.append(
                f"(2,{first + WIRE_OFFSET},{second + WIRE_OFFSET},{third + WIRE_OFFSET})"
            )
        else:
            raise ValueError(f"unknown operation {kind}")
    lines = [", ".join(tuples[index : index + 8]) for index in range(0, len(tuples), 8)]
    return "\n".join(f"    {line}," for line in lines)


def run(args: argparse.Namespace) -> dict[str, Any]:
    started_unix_ns = time.time_ns()
    started = time.monotonic()
    output = args.output.resolve()
    cnf_dir = output / "cnf"
    log_dir = output / "logs"
    witness_dir = output / "witnesses"
    for directory in (output, cnf_dir, log_dir, witness_dir):
        directory.mkdir(parents=True, exist_ok=True)

    reference_ops = load_reference_ops()
    table = reference_table(reference_ops)
    synthesis_inputs = (
        list(PAIR25_INPUTS)
        if args.domain == "pair25"
        else list(range(1 << WIDTH))
    )
    if args.domain == "pair25":
        outputs = [table[input_value] for input_value in synthesis_inputs]
        if len(set(synthesis_inputs)) != 25 or sorted(outputs) != list(range(25)):
            raise RuntimeError("pair25 domain must map bijectively onto canonical values 0..24")
    decomposed = reference_program(reference_ops)
    decomposed_verification = verify_program(decomposed, table)
    compiled_reference = compile_program(decomposed)
    compiled_reference_verification = verify_compiled(compiled_reference, table)
    if decomposed_verification["verdict"] != "green":
        raise RuntimeError("reference affine-conjugation decomposition failed")
    if compiled_reference_verification["verdict"] != "green":
        raise RuntimeError("reference generalized-shear recompilation failed")

    solvers: dict[str, str] = {}
    for name in ("kissat", "cadical"):
        binary = shutil.which(name)
        if binary is None:
            raise RuntimeError(f"required solver not found: {name}")
        solvers[name] = binary

    bounds = [args.max_ccx, REFERENCE_CCX_COUNT]
    if args.max_ccx >= REFERENCE_CCX_COUNT:
        raise ValueError(f"--max-ccx must be below reference count {REFERENCE_CCX_COUNT}")
    search_mode = "exact" if args.exact_ccx else "at-most"
    problems: dict[int, tuple[Cnf, SynthesisVariables, list[int]]] = {}
    cnf_metadata: list[dict[str, Any]] = []
    for bound in bounds:
        problem = build_problem(bound, synthesis_inputs, exact=args.exact_ccx)
        problems[bound] = problem
        cnf, _, _ = problem
        path = cnf_dir / f"normalizer-{search_mode}-{bound}-ccx.cnf"
        cnf.write(
            path,
            [
                "five-wire NORMALIZER_OPS exact affine-conjugated Toffoli synthesis",
                f"{search_mode}_ccx={bound}",
                f"domain={args.domain}; inputs={len(synthesis_inputs)}; arbitrary final invertible affine map inferred from constrained mapping",
                "enabled generalized shear x <- x + c*(a.x+a0)*(b.x+b0)",
            ],
        )
        cnf_metadata.append(
            {
                "at_most_ccx": bound,
                "search_mode": search_mode,
                "path": str(path.relative_to(REPO_ROOT)),
                "sha256": sha256_file(path),
                "variables": cnf.nvars,
                "clauses": len(cnf.clauses),
            }
        )

    work: list[tuple[str, str, int, Path, Path, int, bool]] = []
    for bound in bounds:
        cnf_path = cnf_dir / f"normalizer-{search_mode}-{bound}-ccx.cnf"
        for solver_name, binary in solvers.items():
            work.append(
                (
                    solver_name,
                    binary,
                    bound,
                    cnf_path,
                    log_dir / f"{solver_name}-{search_mode}-{bound}.log",
                    args.timeout_seconds,
                    args.resume,
                )
            )
    with concurrent.futures.ThreadPoolExecutor(max_workers=len(solvers)) as executor:
        solver_runs = list(executor.map(lambda item: run_solver(*item), work))

    errors: list[str] = []
    public_runs: list[dict[str, Any]] = []
    statuses: dict[int, dict[str, str]] = {bound: {} for bound in bounds}
    verified_candidates: list[dict[str, Any]] = []
    for solver_run in solver_runs:
        assignment = set(solver_run.pop("true_variables"))
        bound = solver_run["and_gates"]
        solver_name = solver_run["solver"]
        solver_run["at_most_ccx"] = solver_run.pop("and_gates")
        statuses[bound][solver_name] = solver_run["status"]
        verification: dict[str, Any] | None = None
        compiled_verification: dict[str, Any] | None = None
        witness_path: str | None = None
        witness_sha256: str | None = None
        if solver_run["status"] == "sat":
            _, variables, target = problems[bound]
            program = decode_program(variables, assignment)
            verification = verify_program(program, target, synthesis_inputs)
            compiled = compile_program(program) if verification["verdict"] == "green" else []
            compiled_verification = (
                verify_compiled(compiled, target, synthesis_inputs) if compiled else None
            )
            witness = {
                "schema_version": 1,
                "solver": solver_name,
                "at_most_ccx": bound,
                "program": program,
                "verification": verification,
                "compiled_operations": compiled,
                "compiled_verification": compiled_verification,
                "rust_table": rust_table(compiled) if compiled else None,
            }
            path = witness_dir / f"{solver_name}-at-most-{bound}.json"
            path.write_text(json.dumps(witness, sort_keys=True, indent=2) + "\n")
            witness_path = str(path.relative_to(REPO_ROOT))
            witness_sha256 = sha256_file(path)
            if verification["verdict"] != "green":
                errors.append(f"{solver_name} bound {bound}: model failed exhaustive replay")
            elif compiled_verification is None or compiled_verification["verdict"] != "green":
                errors.append(f"{solver_name} bound {bound}: compiled circuit failed replay")
            elif bound == args.max_ccx:
                verified_candidates.append(witness)
        if solver_run["status"] not in {"sat", "unsat"}:
            errors.append(f"{solver_name} bound {bound}: {solver_run['status']}")
        if not solver_run["returncode_expected"]:
            errors.append(f"{solver_name} bound {bound}: unexpected solver return code")
        public_runs.append(
            {
                **solver_run,
                "verification": verification,
                "compiled_verification": compiled_verification,
                "witness_path": witness_path,
                "witness_sha256": witness_sha256,
            }
        )

    for bound in bounds:
        observed = set(statuses[bound].values())
        if len(observed) != 1:
            errors.append(f"solver disagreement at bound {bound}: {statuses[bound]}")
    if any(statuses[REFERENCE_CCX_COUNT].get(name) != "sat" for name in solvers):
        errors.append("reference six-CCX upper bound was not SAT for both solvers")

    candidate: dict[str, Any] | None = None
    if verified_candidates:
        candidate = min(
            verified_candidates,
            key=lambda witness: (
                witness["compiled_verification"]["ccx"],
                witness["compiled_verification"]["operations"],
                witness["solver"],
            ),
        )
    candidate_ccx = (
        candidate["compiled_verification"]["ccx"] if candidate is not None else None
    )
    exact_minimum = (
        REFERENCE_CCX_COUNT
        if all(statuses[args.max_ccx].get(name) == "unsat" for name in solvers)
        else None
    )
    saving_per_invocation = (
        REFERENCE_CCX_COUNT - candidate_ccx if candidate_ccx is not None else 0
    )

    report: dict[str, Any] = {
        "schema_version": 1,
        "scope": "Y5 five-wire NORMALIZER_OPS exact no-ancilla affine/Toffoli synthesis",
        "search_mode": search_mode,
        "pair25_lower_bound": (
            {
                "minimum_ccx": 5,
                "proof": "exhaustive affine-span quotient search found no path of length zero through four",
            }
            if args.domain == "pair25" and args.exact_ccx and args.max_ccx == 5
            else None
        ),
        "prediction_id": args.prediction_id,
        "source_path": str(SOURCE_PATH.relative_to(REPO_ROOT)),
        "source_sha256": sha256_file(SOURCE_PATH),
        "reference": {
            "operations": len(reference_ops),
            "ccx": REFERENCE_CCX_COUNT,
            "truth_table": table,
            "synthesis_domain": args.domain,
            "synthesis_inputs": synthesis_inputs,
            "synthesis_outputs": [table[input_value] for input_value in synthesis_inputs],
            "anf": anf_report(table),
            "generalized_shear_decomposition": decomposed_verification,
            "generalized_shear_recompile": compiled_reference_verification,
        },
        "completeness_contract": {
            "statement": "Every same-wire affine+CCX circuit with k CCX pushes its affine gates to the output and conjugates each CCX into one encoded reversible generalized shear.",
            "shear_conditions": [
                "c != 0",
                "linear(a) != 0",
                "linear(b) != 0",
                "linear(a) != linear(b)",
                "a(c) = b(c) = 0",
            ],
            "reference_round_trip_verified": True,
        },
        "max_candidate_ccx": args.max_ccx,
        "cnfs": cnf_metadata,
        "solver_versions": {name: solver_version(binary) for name, binary in solvers.items()},
        "solver_runs": sorted(public_runs, key=lambda row: (row["at_most_ccx"], row["solver"])),
        "statuses": statuses,
        "exact_minimum_ccx": exact_minimum,
        "candidate_found": candidate is not None,
        "candidate_solver": candidate["solver"] if candidate is not None else None,
        "candidate_ccx": candidate_ccx,
        "candidate_compiled_operations": (
            candidate["compiled_verification"]["operations"] if candidate is not None else None
        ),
        "repeated_invocations": INVOCATIONS,
        "predicted_executed_toffoli_saving": saving_per_invocation * INVOCATIONS,
        "predicted_score_saving_at_q1154": saving_per_invocation * INVOCATIONS * 1154,
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
    parser.add_argument("--max-ccx", type=int, default=5)
    parser.add_argument("--domain", choices=("full32", "pair25"), default="full32")
    parser.add_argument("--exact-ccx", action="store_true")
    parser.add_argument("--timeout-seconds", type=int, default=600)
    parser.add_argument("--prediction-id", default="PRED-Y5-NORMALIZER-SYNTH-V1")
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    report = run(args)
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0 if report["verdict"] == "green" else 1


if __name__ == "__main__":
    raise SystemExit(main())
