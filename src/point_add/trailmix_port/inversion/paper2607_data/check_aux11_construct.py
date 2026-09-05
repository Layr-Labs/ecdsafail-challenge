#!/usr/bin/env python3
"""Construct representative aux11 steps and check their register width."""

from __future__ import annotations

import eea_circuit_s835_exactwidth_dirty12 as candidate


def check_alias_guards() -> None:
    from qiskit import QuantumCircuit, QuantumRegister

    qubits = QuantumRegister(6, "alias")
    circuit = QuantumCircuit(qubits)
    try:
        candidate._borrowed_c3x(
            circuit, qubits[0], qubits[1], qubits[2], qubits[0], qubits[3]
        )
    except ValueError:
        pass
    else:
        raise AssertionError("borrowed C3X accepted a logical lane alias")
    try:
        candidate._mcx_dirty_ladder(
            circuit,
            [qubits[0], qubits[1], qubits[2]],
            qubits[0],
            [qubits[3]],
        )
    except ValueError:
        pass
    else:
        raise AssertionError("dirty MCX accepted a logical lane alias")
    print("PASS logical-Qubit alias guards")


def main() -> None:
    check_alias_guards()
    for step in (1, 4, 6, 401, 1470, 1524, 1616):
        circuit = candidate.build_step_circuit(
            256,
            step,
            T_max=1616,
            aux_size=11,
            measurement_uncompute=False,
        )
        if circuit.num_qubits != 577:
            raise AssertionError(f"step={step} width={circuit.num_qubits}")
        print(
            f"PASS construct step={step} width={circuit.num_qubits} "
            f"top_level_ops={len(circuit.data)}",
            flush=True,
        )


if __name__ == "__main__":
    main()
