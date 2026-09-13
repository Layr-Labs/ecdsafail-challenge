#!/usr/bin/env python3
"""gpt-5: exact production recursive primitive traversal; no source loader."""
from __future__ import annotations
from typing import Any, Iterator

class FallbackError(RuntimeError):
    """The pinned support or bounded no-Qiskit facade is invalid."""

def require(condition: bool, message: str) -> None:
    if not condition:
        raise FallbackError(message)

def primitives(circuit: Any, mapping: dict[Any, int] | None = None) -> Iterator[tuple[str, tuple[int, ...]]]:
    if mapping is None:
        mapping = {qubit: index for index, qubit in enumerate(circuit.qubits)}
    for item in circuit.data:
        require(not item.clbits, "fallback primitive contains classical control")
        wires = tuple(mapping[qubit] for qubit in item.qubits)
        name = item.operation.name.lower()
        if name in ("x", "cx", "ccx"):
            yield name, wires
            continue
        definition = getattr(item.operation, "definition", None)
        require(definition is not None, f"opaque composite fallback instruction: {name}")
        child = {qubit: wires[index] for index, qubit in enumerate(definition.qubits)}
        yield from primitives(definition, child)
