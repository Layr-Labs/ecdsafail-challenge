#!/usr/bin/env python3
"""Cancel source-bound commuting X/CX/CCX involutions with bounded memory.

Every accepted primitive is an unconditional computational-basis
permutation, so cancelling a repeated involution past pairwise commuting
interveners preserves the complete quantum unitary, not merely a particular
classical test input.  This module never changes the authenticated generator,
its recursive primitive flattener, or the official harness.
"""

from __future__ import annotations

from collections import Counter, deque
from dataclasses import dataclass, field
from typing import Iterable, Iterator, TypeAlias


Gate: TypeAlias = tuple[str, tuple[int, ...]]
GateKey: TypeAlias = tuple[str, tuple[int, ...], int]
LOCAL_WIDTH = 566
MAX_PENDING = 32
ARITY = {"x": 1, "cx": 2, "ccx": 3}


class ReductionError(ValueError):
    """The purported source stream is not the proved X/CX/CCX domain."""


@dataclass(slots=True)
class ReductionStats:
    input_operations: int = 0
    output_operations: int = 0
    maximum_buffered_operations: int = 0
    cancelled_pairs: Counter[str] = field(default_factory=Counter)

    @property
    def removed_operations(self) -> int:
        return 2 * sum(self.cancelled_pairs.values())

    @property
    def removed_toffoli(self) -> int:
        return 2 * self.cancelled_pairs["ccx"]


def validate(gate: Gate, *, width: int = LOCAL_WIDTH) -> GateKey:
    """Normalize symmetric CCX controls while preserving emitted wire order."""
    if not isinstance(gate, tuple) or len(gate) != 2:
        raise ReductionError("source primitive is not a (kind, wires) tuple")
    kind, wires = gate
    if kind not in ARITY or not isinstance(wires, tuple):
        raise ReductionError("only unconditional X/CX/CCX primitives are allowed")
    if len(wires) != ARITY[kind]:
        raise ReductionError(f"source {kind} has an invalid wire arity")
    if any(type(wire) is not int or not 0 <= wire < width for wire in wires):
        raise ReductionError("source primitive escaped its exact physical wire width")
    if len(set(wires)) != len(wires):
        raise ReductionError("source primitive target or controls alias")
    return kind, tuple(sorted(wires[:-1])), wires[-1]


def commute(left: GateKey, right: GateKey) -> bool:
    """Sufficient exact commutation criterion for controlled XOR gates."""
    return left[2] not in right[1] and right[2] not in left[1]


def reduce_stream(
    stream: Iterable[Gate],
    *,
    max_pending: int = MAX_PENDING,
    width: int = LOCAL_WIDTH,
    stats: ReductionStats | None = None,
) -> Iterator[Gate]:
    """Lazily emit an exactly equivalent source stream using at most 32 gates."""
    if type(max_pending) is not int or not 1 <= max_pending <= MAX_PENDING:
        raise ReductionError("pending source-involution window must be between one and 32")
    if type(width) is not int or not 1 <= width <= LOCAL_WIDTH:
        raise ReductionError("source-involution width escaped its authenticated 566 wires")
    report = stats if stats is not None else ReductionStats()
    pending: deque[tuple[Gate, GateKey]] = deque()
    present: Counter[GateKey] = Counter()

    for gate in stream:
        key = validate(gate, width=width)
        report.input_operations += 1
        matched: int | None = None
        if present[key]:
            for index in range(len(pending) - 1, -1, -1):
                _previous, previous_key = pending[index]
                if previous_key == key:
                    matched = index
                    break
                if not commute(previous_key, key):
                    break

        if matched is None:
            pending.append((gate, key))
            present[key] += 1
            if len(pending) > max_pending:
                emitted, emitted_key = pending.popleft()
                present[emitted_key] -= 1
                if not present[emitted_key]:
                    del present[emitted_key]
                report.output_operations += 1
                yield emitted
        else:
            del pending[matched]
            present[key] -= 1
            if not present[key]:
                del present[key]
            report.cancelled_pairs[key[0]] += 1
        report.maximum_buffered_operations = max(
            report.maximum_buffered_operations, len(pending),
        )

    while pending:
        emitted, emitted_key = pending.popleft()
        present[emitted_key] -= 1
        if not present[emitted_key]:
            del present[emitted_key]
        report.output_operations += 1
        yield emitted

    if report.input_operations != report.output_operations + report.removed_operations:
        raise ReductionError("source-involution operation accounting drifted")
    if report.maximum_buffered_operations > max_pending:
        raise ReductionError("source-involution pending buffer exceeded its proved bound")

