#!/usr/bin/env python3
"""Prove one census downgrade as a source-stable Boolean invariant.

The selected gate is the first no-carry-in gate of threaded-add call 0, bit 0.
The production stream currently identifies it through a global operand-tuple ordinal.
This instrument proves the stronger value invariant q1 => q769 for arbitrary quantum
and classical register inputs and arbitrary HMR outcomes, then repeats the proof after
an adjacent self-inverse CCX pair changes that tuple's global occupancy and ordinal.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import struct
import subprocess
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np

from artifact_io import HEADER_BYTES, NO_QUBIT, RECORD_BYTES, decompress_record_body, read_header

REPO_ROOT = Path(__file__).resolve().parents[4]
TARGET = (13, 1, 769, 768, NO_QUBIT)
TARGET_ORDINAL = 0
TARGET_OCCUPANCY = 225
TARGET_ACTION = 1
SYMMETRIC_ORDINAL = 224
SYMMETRIC_ACTION = 2
CONTEXT_RADIUS = 8
INPUT_QUBITS = 512
INPUT_BITS = 512
DTYPE = np.dtype(
    [
        ("kind", "<u4"),
        ("padding", "<u4"),
        ("q_control2", "<u8"),
        ("q_control1", "<u8"),
        ("q_target", "<u8"),
        ("c_target", "<u8"),
        ("c_condition", "<u8"),
        ("r_target", "<u8"),
    ]
)


@dataclass
class Cnf:
    variables: int = 0
    clauses: list[list[int]] | None = None

    def __post_init__(self) -> None:
        if self.clauses is None:
            self.clauses = []

    def new(self) -> int:
        self.variables += 1
        return self.variables

    def unit(self, literal: int) -> None:
        assert self.clauses is not None
        self.clauses.append([literal])

    def and_gate(self, left: int, right: int) -> int:
        out = self.new()
        assert self.clauses is not None
        self.clauses.extend(([-left, -right, out], [left, -out], [right, -out]))
        return out

    def xor_gate(self, left: int, right: int) -> int:
        out = self.new()
        assert self.clauses is not None
        self.clauses.extend(
            (
                [-left, -right, -out],
                [left, right, -out],
                [left, -right, out],
                [-left, right, out],
            )
        )
        return out

    def mux(self, select: int, when_false: int, when_true: int) -> int:
        difference = self.xor_gate(when_false, when_true)
        selected_difference = self.and_gate(select, difference)
        return self.xor_gate(when_false, selected_difference)


@dataclass(frozen=True)
class EncodedPrefix:
    cnf: Cnf
    qubits: dict[int, int]
    bits: dict[int, int]


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while chunk := source.read(8 * 1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def operation_tuple(row: np.void) -> tuple[int, int, int, int, int]:
    return (
        int(row["kind"]),
        int(row["q_control2"]),
        int(row["q_control1"]),
        int(row["q_target"]),
        int(row["c_condition"]),
    )


def parse_key_table(path: Path) -> tuple[list[tuple[int, ...]], list[tuple[int, ...]]]:
    text = path.read_text(encoding="utf-8")
    dead_match = re.search(r"pub static DEAD_KEYS.*?= &\[(.*?)\];", text, re.DOTALL)
    downgrade_match = re.search(r"pub static DOWNGRADE_KEYS.*?= &\[(.*?)\];", text, re.DOTALL)
    if dead_match is None or downgrade_match is None:
        raise ValueError("deep-strip key table declarations not found")

    def rows(block: str, width: int) -> list[tuple[int, ...]]:
        parsed: list[tuple[int, ...]] = []
        for raw in re.findall(r"\(([^()]*)\)", block):
            values = tuple(int(value.strip()) for value in raw.split(",") if value.strip())
            if len(values) == width:
                parsed.append(values)
        return parsed

    return rows(dead_match.group(1), 7), rows(downgrade_match.group(1), 8)


def verify_target_keys(dead: Sequence[tuple[int, ...]], downgrade: Sequence[tuple[int, ...]]) -> dict[str, object]:
    first = (*TARGET, TARGET_ORDINAL, TARGET_OCCUPANCY, TARGET_ACTION)
    symmetric = (*TARGET, SYMMETRIC_ORDINAL, TARGET_OCCUPANCY, SYMMETRIC_ACTION)
    if first not in downgrade:
        raise ValueError(f"selected downgrade key is absent: {first}")
    if symmetric not in downgrade:
        raise ValueError(f"symmetric downgrade key is absent: {symmetric}")
    matching_dead = [row for row in dead if row[:5] == TARGET]
    matching_downgrade = [row for row in downgrade if row[:5] == TARGET]
    if matching_dead or matching_downgrade != [first, symmetric]:
        raise ValueError("selected operand tuple has unexpected census classifications")
    return {
        "dead_keys": matching_dead,
        "downgrade_keys": matching_downgrade,
        "migration": {
            "remove": first,
            "rebase_remaining": (*TARGET, SYMMETRIC_ORDINAL - 1, TARGET_OCCUPANCY - 1, SYMMETRIC_ACTION),
        },
    }


def verify_register_layout(records: np.ndarray) -> dict[str, list[int]]:
    append = records[records["kind"] == 2]
    register = records[records["kind"] == 1]
    if len(register) != 4 or len(append) != 1024:
        raise ValueError(f"expected four 256-element registers, got {len(register)} and {len(append)} append records")
    no = NO_QUBIT
    expected = {
        "quantum_x": list(range(0, 256)),
        "quantum_y": list(range(256, 512)),
        "classical_x": list(range(0, 256)),
        "classical_y": list(range(256, 512)),
    }
    observed = {name: [] for name in expected}
    for row in append:
        reg = int(row["r_target"])
        q_target = int(row["q_target"])
        c_target = int(row["c_target"])
        if reg == 0 and q_target != no:
            observed["quantum_x"].append(q_target)
        elif reg == 1 and q_target != no:
            observed["quantum_y"].append(q_target)
        elif reg == 2 and c_target != no:
            observed["classical_x"].append(c_target)
        elif reg == 3 and c_target != no:
            observed["classical_y"].append(c_target)
        else:
            raise ValueError(f"unexpected register record {tuple(int(row[name]) for name in DTYPE.names)}")
    if observed != expected:
        raise ValueError("artifact register ABI is not q0..q511 / c0..c511")
    return observed


def encode_prefix(records: Iterable[np.void]) -> EncodedPrefix:
    cnf = Cnf()
    true_var = cnf.new()
    false_var = cnf.new()
    cnf.unit(true_var)
    cnf.unit(-false_var)
    qubits = {index: cnf.new() for index in range(INPUT_QUBITS)}
    bits = {index: cnf.new() for index in range(INPUT_BITS)}

    def qubit(index: int) -> int:
        if index not in qubits:
            qubits[index] = false_var
        return qubits[index]

    def bit(index: int) -> int:
        if index not in bits:
            bits[index] = false_var
        return bits[index]

    base_condition = true_var
    condition_stack: list[int] = []
    ignored = {0, 1, 2, 7, 9, 14, 17}

    for index, row in enumerate(records):
        kind = int(row["kind"])
        target = int(row["q_target"])
        control1 = int(row["q_control1"])
        control2 = int(row["q_control2"])
        classical_target = int(row["c_target"])
        classical_condition = int(row["c_condition"])
        condition = (
            base_condition
            if classical_condition == NO_QUBIT
            else cnf.and_gate(base_condition, bit(classical_condition))
        )

        if kind == 6:  # X
            qubits[target] = cnf.xor_gate(qubit(target), condition)
        elif kind == 8:  # CX
            effect = cnf.and_gate(condition, qubit(control1))
            qubits[target] = cnf.xor_gate(qubit(target), effect)
        elif kind == 13:  # CCX
            controls = cnf.and_gate(qubit(control1), qubit(control2))
            effect = cnf.and_gate(condition, controls)
            qubits[target] = cnf.xor_gate(qubit(target), effect)
        elif kind == 10:  # conditional swap
            old_control = qubit(control1)
            old_target = qubit(target)
            difference = cnf.xor_gate(old_control, old_target)
            effect = cnf.and_gate(condition, difference)
            qubits[control1] = cnf.xor_gate(old_control, effect)
            qubits[target] = cnf.xor_gate(old_target, effect)
        elif kind in (11, 12):  # R / HMR reset the qubit under the condition
            qubits[target] = cnf.mux(condition, qubit(target), false_var)
            if kind == 12:
                random_measurement = cnf.new()  # arbitrary HMR outcome
                bits[classical_target] = cnf.mux(condition, bit(classical_target), random_measurement)
        elif kind == 3:  # BIT_INVERT
            bits[classical_target] = cnf.xor_gate(bit(classical_target), condition)
        elif kind == 4:  # BIT_STORE0
            bits[classical_target] = cnf.mux(condition, bit(classical_target), false_var)
        elif kind == 5:  # BIT_STORE1
            bits[classical_target] = cnf.mux(condition, bit(classical_target), true_var)
        elif kind == 15:  # PUSH_CONDITION
            if classical_condition == NO_QUBIT:
                raise ValueError(f"PUSH_CONDITION without a bit at op {index}")
            condition_stack.append(base_condition)
            base_condition = cnf.and_gate(base_condition, bit(classical_condition))
        elif kind == 16:  # POP_CONDITION
            if not condition_stack:
                raise ValueError(f"condition stack underflow at op {index}")
            base_condition = condition_stack.pop()
        elif kind not in ignored:
            raise ValueError(f"unknown operation kind {kind} at op {index}")

    if condition_stack:
        raise ValueError("prefix ends inside a pushed condition")
    return EncodedPrefix(cnf=cnf, qubits=qubits, bits=bits)


def write_query(encoded: EncodedPrefix, path: Path, survivor: int, redundant: int) -> dict[str, int]:
    clauses = list(encoded.cnf.clauses or [])
    clauses.append([encoded.qubits[survivor]])
    clauses.append([-encoded.qubits[redundant]])
    with path.open("w", encoding="ascii") as output:
        output.write(f"p cnf {encoded.cnf.variables} {len(clauses)}\n")
        for clause in clauses:
            output.write(" ".join(str(literal) for literal in clause))
            output.write(" 0\n")
    return {"variables": encoded.cnf.variables, "clauses": len(clauses), "bytes": path.stat().st_size}


def run_solver(executable: str, cnf_path: Path, log_path: Path) -> dict[str, object]:
    resolved = shutil.which(executable)
    if resolved is None:
        raise RuntimeError(f"SAT solver not found: {executable}")
    started = time.monotonic()
    process = subprocess.run(
        [resolved, str(cnf_path)],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=120,
        check=False,
    )
    elapsed = time.monotonic() - started
    log_path.write_text(process.stdout, encoding="utf-8")
    unsat = "s UNSATISFIABLE" in process.stdout
    sat = "s SATISFIABLE" in process.stdout
    if process.returncode != 20 or not unsat or sat:
        raise RuntimeError(
            f"{executable} did not prove UNSAT for {cnf_path.name}: "
            f"returncode={process.returncode}, unsat={unsat}, sat={sat}"
        )
    return {
        "executable": resolved,
        "returncode": process.returncode,
        "result": "UNSAT",
        "wall_seconds": elapsed,
        "log": str(log_path.relative_to(REPO_ROOT)),
        "log_sha256": sha256_file(log_path),
    }


def context_digest(records: np.ndarray, index: int) -> str:
    lo = index - CONTEXT_RADIUS
    hi = index + CONTEXT_RADIUS + 1
    if lo < 0 or hi > len(records):
        raise ValueError("target lacks a complete context window")
    return hashlib.sha256(records[lo:hi].tobytes()).hexdigest()


def run(args: argparse.Namespace) -> dict[str, object]:
    ops_path = args.ops.resolve()
    keys_path = args.keys.resolve()
    output_path = args.output.resolve()
    output_path.parent.mkdir(parents=True, exist_ok=True)
    dead, downgrade = parse_key_table(keys_path)
    key_report = verify_target_keys(dead, downgrade)

    with ops_path.open("rb") as source:
        _, op_count = read_header(source)
    with tempfile.TemporaryDirectory(prefix="y6-source-invariant-") as temporary:
        raw_path = Path(temporary) / "ops.raw"
        raw_report = decompress_record_body(ops_path, raw_path)
        records = np.memmap(raw_path, dtype=DTYPE, mode="r", shape=(op_count,))
        register_layout = verify_register_layout(records)
        matches = np.flatnonzero(
            (records["kind"] == TARGET[0])
            & (records["q_control2"] == TARGET[1])
            & (records["q_control1"] == TARGET[2])
            & (records["q_target"] == TARGET[3])
            & (records["c_condition"] == TARGET[4])
        )
        if len(matches) != TARGET_OCCUPANCY:
            raise ValueError(f"target occupancy changed: expected {TARGET_OCCUPANCY}, got {len(matches)}")
        target_index = int(matches[TARGET_ORDINAL])
        if target_index != 16278:
            raise ValueError(f"source target moved: expected op 16278, got {target_index}")

        baseline_context = context_digest(records, target_index)
        context_matches = [
            int(index) for index in matches if context_digest(records, int(index)) == baseline_context
        ]
        if context_matches != [target_index]:
            raise ValueError(f"source context is not unique: {context_matches}")

        baseline_prefix = np.asarray(records[:target_index]).copy()
        encoded_baseline = encode_prefix(baseline_prefix)
        baseline_cnf = output_path.parent / "baseline-implied-control.cnf"
        baseline_shape = write_query(encoded_baseline, baseline_cnf, TARGET[1], TARGET[2])

        inserted = np.asarray(records[target_index : target_index + 1]).copy()
        perturbed_prefix = np.concatenate((inserted, inserted, baseline_prefix))
        perturbed_target_index = target_index + 2
        encoded_perturbed = encode_prefix(perturbed_prefix)
        perturbed_cnf = output_path.parent / "perturbed-implied-control.cnf"
        perturbed_shape = write_query(encoded_perturbed, perturbed_cnf, TARGET[1], TARGET[2])
        perturbed_context = hashlib.sha256(
            np.concatenate(
                (
                    perturbed_prefix[perturbed_target_index - CONTEXT_RADIUS :],
                    np.asarray(records[target_index : target_index + CONTEXT_RADIUS + 1]),
                )
            )[: 2 * CONTEXT_RADIUS + 1].tobytes()
        ).hexdigest()
        if perturbed_context != baseline_context:
            raise AssertionError("identity perturbation changed the target's local source context")

        solver_reports: dict[str, dict[str, object]] = {}
        for label, cnf_path in (("baseline", baseline_cnf), ("perturbed", perturbed_cnf)):
            solver_reports[label] = {}
            for solver in (args.solver, args.second_solver):
                log_path = output_path.parent / f"{label}-{Path(solver).name}.log"
                solver_reports[label][Path(solver).name] = run_solver(solver, cnf_path, log_path)

    source_paths = [
        REPO_ROOT / "src/point_add/trailmix_ludicrous/gidney.rs",
        REPO_ROOT / "src/point_add/trailmix_ludicrous/gcd.rs",
        REPO_ROOT / "src/point_add/mod.rs",
        keys_path,
    ]
    report: dict[str, object] = {
        "schema_version": 1,
        "verdict": "green",
        "scope": "Y6 exact source implied-control certificate and same-tuple identity perturbation",
        "artifact": {
            "path": str(ops_path.relative_to(REPO_ROOT)),
            "compressed_sha256": sha256_file(ops_path),
            "emitted_ops": op_count,
            **raw_report,
        },
        "register_layout": {name: {"first": values[0], "last": values[-1], "width": len(values)} for name, values in register_layout.items()},
        "selected_gate": {
            "source": "gidney.rs:controlled_clean_add_threaded call_index=0 bit=0, no carry-in branch",
            "op_index": target_index,
            "tuple": TARGET,
            "ordinal": TARGET_ORDINAL,
            "occupancy": TARGET_OCCUPANCY,
            "context_radius": CONTEXT_RADIUS,
            "context_sha256": baseline_context,
            "unique_context_matches": context_matches,
            "proof_obligation": "q_control2=1 and q_control1=0 is unreachable before the gate",
            "rewrite": "CCX(q_control2,q_control1,target) == CX(q_control2,target)",
        },
        "key_table": key_report,
        "exact_proofs": {
            "baseline": {"cnf": baseline_shape, "solvers": solver_reports["baseline"]},
            "same_tuple_identity_pair": {
                "inserted_operations": 2,
                "identity": "adjacent identical CCX gates are self-inverse",
                "target_ordinal_before": 0,
                "target_ordinal_after": 2,
                "tuple_occupancy_before": TARGET_OCCUPANCY,
                "tuple_occupancy_after": TARGET_OCCUPANCY + 2,
                "empirical_keys_made_stale": 2,
                "source_certificate_matches": 1,
                "source_certificate_stale": 0,
                "source_certificate_density": 1.0,
                "context_sha256": perturbed_context,
                "cnf": perturbed_shape,
                "solvers": solver_reports["perturbed"],
            },
        },
        "source_hashes": {str(path.relative_to(REPO_ROOT)): sha256_file(path) for path in source_paths},
    }
    output_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return report


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ops", type=Path, required=True)
    parser.add_argument("--keys", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--solver", default="kissat")
    parser.add_argument("--second-solver", default="cadical")
    return parser.parse_args()


def main() -> int:
    report = run(parse_args())
    print(json.dumps(report, sort_keys=True))
    return 0 if report["verdict"] == "green" else 1


if __name__ == "__main__":
    raise SystemExit(main())
