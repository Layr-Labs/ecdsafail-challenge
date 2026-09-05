# INERT codec draft. No record or circuit has been generated with this code.
# Integration replaces only the production flattener/codec implementation;
# the baseline file and historical repro streams remain immutable.
import struct
from qiskit.circuit.annotated_operation import AnnotatedOperation

KIND = {"x": 1, "cx": 2, "ccx": 3, "z": 4, "cz": 5, "swap": 6,
        "clean_c3x_mbu": 7, "paired_tsub_compute_v1": 8,
        "paired_tsub_uncompute_v1": 9}
ARITY = {1: 1, 2: 2, 3: 3, 4: 1, 5: 2, 6: 2, 7: 5, 8: 3, 9: 3}
ROLES = {"paired_tsub_compute_v1": "C", "paired_tsub_uncompute_v1": "U"}
MAGIC = b"P26EEA3\0"
BASELINE_MAGIC = b"P26EEA2\0"


def flatten_paired_v1(circuit, qmap=None):
    if qmap is None:
        qmap = {q: i for i, q in enumerate(circuit.qubits)}
    if circuit.num_clbits or circuit.global_phase != 0:
        raise ValueError("nonzero phase or classical bits in paired transport")
    for item in circuit.data:
        op = item.operation
        if isinstance(op, AnnotatedOperation):
            raise ValueError("annotated operation unsupported in paired transport")
        name = op.name.lower()
        args = [qmap[q] for q in item.qubits]
        if item.clbits or getattr(op, "condition", None) is not None:
            raise ValueError("dynamic/conditioned operation in paired transport")
        if name.startswith("paired_") or hasattr(op, "_paired_tsub_role_v1"):
            if name not in ROLES or getattr(op, "_paired_tsub_role_v1", None) != ROLES[name]:
                raise ValueError("lost/renamed/inverted paired marker role")
            if op.num_qubits != 3 or op.num_clbits != 0 or op.params:
                raise ValueError("paired marker interface")
            definition = op.definition
            if definition is None or definition.num_qubits != 3 or definition.num_clbits:
                raise ValueError("missing paired coherent definition")
            if definition.global_phase != 0 or len(definition.data) != 1:
                raise ValueError("paired coherent definition is not one CCX")
            leaf = definition.data[0]
            if (leaf.operation.name != "ccx" or leaf.clbits or
                    list(leaf.qubits) != list(definition.qubits) or
                    getattr(leaf.operation, "condition", None) is not None):
                raise ValueError("paired coherent definition operands")
            yield name, args
        elif name in KIND:
            yield name, args
        else:
            definition = op.definition
            if definition is None:
                raise ValueError("opaque/annotated operation in paired transport")
            child_map = {q: args[i] for i, q in enumerate(definition.qubits)}
            yield from flatten_paired_v1(definition, child_map)


def pack_paired_v1(name, args):
    kind = KIND[name]
    if len(args) != ARITY[kind] or len(set(args)) != len(args):
        raise ValueError("paired record arity/alias")
    if any(type(q) is not int or not 0 <= q < 577 for q in args):
        raise ValueError("paired physical wire bound")
    word = kind | (len(args) << 4)
    for i, q in enumerate(args):
        word |= q << (8 + 10*i)
    return struct.pack("<Q", word)


def decode_word_paired_v1(word):
    kind, arity = word & 15, (word >> 4) & 15
    if kind not in ARITY or arity != ARITY[kind] or word >> (8 + 10*arity):
        raise ValueError("paired record kind/arity/padding")
    args = [(word >> (8 + 10*i)) & 1023 for i in range(arity)]
    if len(set(args)) != arity or any(q >= 577 for q in args):
        raise ValueError("paired record alias/bound")
    return kind, args


def coherent_reference_frame_v1(raw):
    if len(raw) < 24 or raw[:8] != MAGIC or (len(raw)-24) % 8:
        raise ValueError("paired frame header/length")
    n, width, start, end = struct.unpack("<4I", raw[8:24])
    if (n, width) != (256, 577) or not 1 <= start <= end <= 1616:
        raise ValueError("paired frame dimensions/range")
    out = bytearray(BASELINE_MAGIC + raw[8:24])
    for word, in struct.iter_unpack("<Q", raw[24:]):
        kind, _ = decode_word_paired_v1(word)
        # Both coherent definitions are exact CCX; preserve every other bit.
        if kind in (8, 9):
            word = (word & ~15) | 3
        out.extend(struct.pack("<Q", word))
    return bytes(out)
