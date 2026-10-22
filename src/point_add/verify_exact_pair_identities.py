#!/usr/bin/env python3
"""Independent, dependency-free Boolean verification of the pair identities.

This file does not import, read, compile, or execute the contestant Rust code.
It is an algebra check, not the official circuit/phase/score validation, and
does not establish that an implementation or a full generated circuit passes.
"""

from collections import Counter
from dataclasses import dataclass
from itertools import permutations, product
import json


@dataclass(frozen=True)
class Gate:
    controls: tuple[int, ...]
    target: int
    condition: int | None


def simulate(gates, state, classical):
    for gate in gates:
        assert gate.target not in gate.controls
        assert len(set(gate.controls)) == len(gate.controls)
        enabled = gate.condition is None or (classical >> gate.condition) & 1
        if enabled and all((state >> q) & 1 for q in gate.controls):
            state ^= 1 << gate.target
    return state


def algebraic_replacement(first, second):
    """Reference rule written with set algebra, independent of Rust matching."""
    if first.condition != second.condition:
        return None
    left, right = set(first.controls), set(second.controls)
    if left == right:
        if first.target == second.target:
            return "cancel", ()
        helper = Gate((first.target,), second.target, first.condition)
        return "fanout", (helper, first, helper)
    if first.target == second.target and len(left & right) == 1:
        source, = left - right
        target, = right - left
        helper = Gate((source,), target, first.condition)
        return "shared_target", (helper, second, helper)
    return None


def main():
    # Every legal ordered CCX on four wires, either unconditioned or under
    # either of two independent classical bits. Both bits are exhaustively set.
    gates = [
        Gate(controls, target, condition)
        for target in range(4)
        for controls in permutations([q for q in range(4) if q != target], 2)
        for condition in (None, 0, 1)
    ]
    counts = Counter()
    basis_checks = 0
    for first, second in product(gates, repeat=2):
        result = algebraic_replacement(first, second)
        if result is None:
            counts["unmatched_pairs"] += 1
            continue
        identity, replacement = result
        counts[identity] += 1
        assert {q for g in replacement for q in (*g.controls, g.target)} <= {
            q for g in (first, second) for q in (*g.controls, g.target)
        }
        assert all(g.condition == first.condition for g in replacement)
        for state, classical in product(range(16), range(4)):
            expected = simulate((first, second), state, classical)
            actual = simulate(replacement, state, classical)
            assert actual == expected, (first, second, replacement, state, classical)
            basis_checks += 1

    # The rule must not accidentally be generalized to distinct conditions.
    # These concrete assignments distinguish each original from an invalid
    # rewrite carrying only the first condition.
    negative_checks = 0
    for variant in ("fanout", "shared_target", "cancel"):
        first = Gate((0, 1), 2, 0)
        second = {
            "fanout": Gate((0, 1), 3, 1),
            "shared_target": Gate((0, 3), 2, 1),
            "cancel": Gate((0, 1), 2, 1),
        }[variant]
        assert algebraic_replacement(first, second) is None
        pretend_same = Gate(second.controls, second.target, first.condition)
        _, invalid = algebraic_replacement(first, pretend_same)
        assert any(
            simulate((first, second), state, classical)
            != simulate(invalid, state, classical)
            for state, classical in product(range(16), range(4))
        )
        negative_checks += 1

    # Dirty-target necessity: no assumption that either target starts at zero.
    # Every basis assignment above already includes 00, 01, 10 and 11 targets.
    assert counts == Counter(cancel=144, fanout=144, shared_target=288, unmatched_pairs=4608)
    assert basis_checks == 36864
    print(json.dumps({
        "status": "PASS",
        "all_ordered_gate_pairs": len(gates) ** 2,
        "matched_pairs": sum(counts[k] for k in ("cancel", "fanout", "shared_target")),
        "basis_state_and_classical_assignments_checked": basis_checks,
        "different_condition_counterexamples": negative_checks,
        "pair_counts": dict(sorted(counts.items())),
        "contestant_code_executed": False,
        "full_circuit_validated": False,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
