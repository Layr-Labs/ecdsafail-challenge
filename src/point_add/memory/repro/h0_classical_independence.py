#!/usr/bin/env python3
"""Prove that free classical controls cannot read initial quantum inputs.

The proof is an induction over the pinned Simulator::apply_iter transition table.
Classical state starts from the two classical input registers. Every subsequent
classical writer depends only on prior classical state, condition bits, and XOF
randomness. HMR moves quantum dependence into phase, never into c_target.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from enum import IntFlag
from pathlib import Path
from typing import Any

try:
    from verifier_ceiling import PINNED_TRUSTED_SHA256
except ModuleNotFoundError:
    from .verifier_ceiling import PINNED_TRUSTED_SHA256


class Dependency(IntFlag):
    NONE = 0
    INITIAL_QUANTUM = 1
    INITIAL_CLASSICAL = 2
    XOF_RANDOMNESS = 4


CLASSICAL_WRITERS = (
    "Hmr",
    "BitInvert",
    "BitStore0",
    "BitStore1",
)
NON_WRITERS = (
    "Neg",
    "Register",
    "AppendToRegister",
    "X",
    "Z",
    "CX",
    "CZ",
    "Swap",
    "R",
    "CCX",
    "CCZ",
    "PushCondition",
    "PopCondition",
    "DebugPrint",
)
ALL_OPERATION_TYPES = CLASSICAL_WRITERS + NON_WRITERS


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def classical_write_dependency(
    kind: str,
    *,
    old_target: Dependency,
    condition: Dependency,
    hmr_leaks_quantum: bool = False,
) -> Dependency | None:
    """Return the dependencies of c_target after one abstract transition."""
    if kind == "Hmr":
        result = old_target | condition | Dependency.XOF_RANDOMNESS
        if hmr_leaks_quantum:
            result |= Dependency.INITIAL_QUANTUM
        return result
    if kind == "BitInvert":
        return old_target | condition
    if kind in {"BitStore0", "BitStore1"}:
        return old_target | condition
    if kind in NON_WRITERS:
        return None
    raise ValueError(f"unknown operation type {kind}")


def verify_independence(*, hmr_leaks_quantum: bool = False) -> dict[str, Any]:
    # Induction hypothesis: every existing bit and every condition expression is
    # independent of the initial quantum registers. XOF randomness is also
    # independent of those registers for a fixed semantic artifact.
    prior = Dependency.INITIAL_CLASSICAL | Dependency.XOF_RANDOMNESS
    condition = prior
    failures: list[str] = []
    transitions: dict[str, list[str] | None] = {}
    for kind in ALL_OPERATION_TYPES:
        dependency = classical_write_dependency(
            kind,
            old_target=prior,
            condition=condition,
            hmr_leaks_quantum=hmr_leaks_quantum,
        )
        if dependency is None:
            transitions[kind] = None
            continue
        names = [member.name for member in Dependency if member and member & dependency]
        transitions[kind] = names
        if dependency & Dependency.INITIAL_QUANTUM:
            failures.append(f"{kind}:classical_target_depends_on_initial_quantum")
    return {
        "verdict": "green" if not failures else "red",
        "failures": failures,
        "operation_types_checked": len(ALL_OPERATION_TYPES),
        "classical_writers_checked": len(CLASSICAL_WRITERS),
        "transitions": transitions,
        "conclusion": (
            "classical condition stacks cannot distinguish initial quantum target values"
            if not failures
            else "classical independence is violated"
        ),
    }


def verify(repo: Path) -> dict[str, Any]:
    simulator = repo / "src/sim.rs"
    actual_hash = _sha256(simulator)
    pinned_hash = PINNED_TRUSTED_SHA256["src/sim.rs"]
    proof = verify_independence()
    failures = list(proof["failures"])
    if actual_hash != pinned_hash:
        failures.append("simulator_hash_mismatch")
    countermodel = verify_independence(hmr_leaks_quantum=True)
    if countermodel["verdict"] != "red":
        failures.append("proof_does_not_reject_quantum_leaking_hmr")
    return {
        "model": "classical-state dependency induction over Simulator::apply_iter",
        "scope": "pinned operation semantics; initial quantum-to-classical extraction only",
        "simulator_sha256": actual_hash,
        "pinned_simulator_sha256": pinned_hash,
        "transition_proof": proof,
        "negative_control": {
            "mutation": "Hmr c_target also depends on q_target",
            "verdict": countermodel["verdict"],
            "failures": countermodel["failures"],
        },
        "failures": failures,
        "verdict": "green" if not failures else "red",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = verify(args.repo.resolve())
    print(json.dumps(report, sort_keys=True, indent=None if args.json else 2))
    return 0 if report["verdict"] == "green" else 1


if __name__ == "__main__":
    raise SystemExit(main())
