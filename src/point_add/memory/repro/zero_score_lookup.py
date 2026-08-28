#!/usr/bin/env python3
"""Test the zero-score lookup route against Fiat-Shamir self-seeding.

For a frozen 9,024-shot dataset, free classical condition stacks can select a
unique offset prefix and apply an X-only correction to the two quantum output
registers. That circuit has zero Toffoli cost. Its semantic operation stream,
however, changes the Fiat-Shamir dataset. This reproducer builds the semantic
lookup stream, derives its new dataset, and measures the resulting failure.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import struct
import subprocess
from pathlib import Path
from typing import Any

try:
    import numpy as np
except ImportError as error:
    raise RuntimeError("zero_score_lookup.py requires numpy") from error

try:
    from artifact_io import HEADER_BYTES, MAGIC, MAX_OPS, NO_QUBIT, RECORD_BYTES
    from world_model import FULL_VERIFICATION_SHOTS
except ModuleNotFoundError:
    from .artifact_io import HEADER_BYTES, MAGIC, MAX_OPS, NO_QUBIT, RECORD_BYTES
    from .world_model import FULL_VERIFICATION_SHOTS

P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
NO_FIELD = (1 << 64) - 1
DOMAIN = b"quantum_ecc-fiat-shamir-v2"
CANONICAL_RECORD_BYTES = 49

REGISTER = 1
APPEND_TO_REGISTER = 2
BIT_INVERT = 3
X = 6
PUSH_CONDITION = 15
POP_CONDITION = 16

AffinePoint = tuple[int, int]
JacobianPoint = tuple[int, int, int]
DatasetRow = tuple[int, int, int, int, int, int]


def _artifact_seed(path: Path) -> tuple[Any, str, int]:
    zstd = shutil.which("zstd")
    if zstd is None:
        raise RuntimeError("zstd executable is required")
    with path.open("rb", buffering=0) as source:
        header = source.read(HEADER_BYTES)
        if len(header) != HEADER_BYTES or header[: len(MAGIC)] != MAGIC:
            raise ValueError("invalid ops artifact header")
        count = struct.unpack_from("<Q", header, len(MAGIC))[0]
        if count > MAX_OPS:
            raise ValueError(f"op count {count} exceeds verifier cap")
        shake = hashlib.shake_256(DOMAIN + struct.pack("<Q", count))
        canonical_sha = hashlib.sha256(struct.pack("<Q", count))
        decoder = subprocess.Popen(
            [zstd, "-d", "-q", "-c"],
            stdin=source,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        assert decoder.stdout is not None
        remainder = b""
        decoded = 0
        while data := decoder.stdout.read(RECORD_BYTES * 500_000):
            data = remainder + data
            complete = len(data) - len(data) % RECORD_BYTES
            raw = np.frombuffer(memoryview(data)[:complete], dtype=np.uint8).reshape(
                -1, RECORD_BYTES
            )
            kinds = raw[:, :4].copy().view("<u4").reshape(-1)
            if np.any(kinds > 17):
                raise ValueError("artifact contains an unknown operation kind")
            if np.any(raw[:, 4:8] != 0):
                raise ValueError("artifact contains nonzero reserved padding")
            canonical = np.empty((len(kinds), CANONICAL_RECORD_BYTES), dtype=np.uint8)
            canonical[:, 0] = kinds
            canonical[:, 1:] = raw[:, 8:RECORD_BYTES]
            shake.update(canonical)
            canonical_sha.update(canonical)
            decoded += len(kinds)
            remainder = data[complete:]
        decoder.stdout.close()
        stderr = decoder.stderr.read().decode("utf-8", errors="replace") if decoder.stderr else ""
        if decoder.stderr:
            decoder.stderr.close()
        returncode = decoder.wait()
    if returncode != 0:
        raise RuntimeError(f"zstd decoder failed: {stderr.strip()}")
    if remainder or decoded != count:
        raise ValueError(f"decoded {decoded} complete records for declared count {count}")
    return shake, canonical_sha.hexdigest(), count


def _jacobian_double(point: JacobianPoint) -> JacobianPoint:
    x, y, z = point
    if z == 0 or y == 0:
        return (0, 1, 0)
    yy = y * y % P
    s = 4 * x * yy % P
    m = 3 * x * x % P
    x3 = (m * m - 2 * s) % P
    y3 = (m * (s - x3) - 8 * yy * yy) % P
    z3 = 2 * y * z % P
    return (x3, y3, z3)


def _jacobian_mixed_add(point: JacobianPoint, affine: AffinePoint) -> JacobianPoint:
    x1, y1, z1 = point
    x2, y2 = affine
    if z1 == 0:
        return (x2, y2, 1)
    z1z1 = z1 * z1 % P
    u2 = x2 * z1z1 % P
    s2 = y2 * z1 * z1z1 % P
    h = (u2 - x1) % P
    r = 2 * (s2 - y1) % P
    if h == 0:
        return _jacobian_double(point) if r == 0 else (0, 1, 0)
    hh = h * h % P
    i = 4 * hh % P
    j = h * i % P
    v = x1 * i % P
    x3 = (r * r - j - 2 * v) % P
    y3 = (r * (v - x3) - 2 * y1 * j) % P
    z3 = ((z1 + h) * (z1 + h) - z1z1 - hh) % P
    return (x3, y3, z3)


def _batch_inverse(values: list[int]) -> list[int]:
    if any(value == 0 for value in values):
        raise ValueError("batch inversion received zero")
    prefixes: list[int] = []
    product = 1
    for value in values:
        prefixes.append(product)
        product = product * value % P
    inverse = pow(product, P - 2, P)
    outputs = [0] * len(values)
    for index in range(len(values) - 1, -1, -1):
        outputs[index] = inverse * prefixes[index] % P
        inverse = inverse * values[index] % P
    return outputs


def _normalize_many(points: list[JacobianPoint]) -> list[AffinePoint]:
    nonzero = [point[2] for point in points if point[2] != 0]
    inverses = iter(_batch_inverse(nonzero)) if nonzero else iter(())
    affine: list[AffinePoint] = []
    for x, y, z in points:
        if z == 0:
            affine.append((0, 0))
            continue
        z_inv = next(inverses)
        z2 = z_inv * z_inv % P
        affine.append((x * z2 % P, y * z2 * z_inv % P))
    return affine


def _fixed_base_table() -> tuple[AffinePoint, ...]:
    powers: list[JacobianPoint] = [(GX, GY, 1)]
    for _ in range(1, 256):
        powers.append(_jacobian_double(powers[-1]))
    return tuple(_normalize_many(powers))


def _fixed_base_mul_many(scalars: list[int], powers: tuple[AffinePoint, ...]) -> list[AffinePoint]:
    outputs: list[JacobianPoint] = []
    for scalar in scalars:
        point = (0, 1, 0)
        bit = 0
        value = scalar
        while value:
            if value & 1:
                point = _jacobian_mixed_add(point, powers[bit])
            value >>= 1
            bit += 1
        outputs.append(point)
    return _normalize_many(outputs)


def _add_many(first: list[AffinePoint], second: list[AffinePoint]) -> list[AffinePoint]:
    denominators: list[int] = []
    for (x1, y1), (x2, y2) in zip(first, second):
        if (x1, y1) == (0, 0) or (x2, y2) == (0, 0) or x1 == x2:
            raise ValueError("dataset contains an exceptional addition")
        denominators.append((x2 - x1) % P)
    inverses = _batch_inverse(denominators)
    outputs: list[AffinePoint] = []
    for ((x1, y1), (x2, y2)), inverse in zip(zip(first, second), inverses):
        slope = (y2 - y1) * inverse % P
        x3 = (slope * slope - x1 - x2) % P
        y3 = (slope * (x1 - x3) - y1) % P
        outputs.append((x3, y3))
    return outputs


def _draw_dataset(shake: Any, shots: int, powers: tuple[AffinePoint, ...]) -> list[DatasetRow]:
    extra = 32
    raw = shake.digest((shots + extra) * 64)
    scalars_t = [
        int.from_bytes(raw[offset : offset + 32], "little")
        for offset in range(0, len(raw), 64)
    ]
    scalars_o = [
        int.from_bytes(raw[offset + 32 : offset + 64], "little")
        for offset in range(0, len(raw), 64)
    ]
    targets = _fixed_base_mul_many(scalars_t, powers)
    offsets = _fixed_base_mul_many(scalars_o, powers)
    selected_t: list[AffinePoint] = []
    selected_o: list[AffinePoint] = []
    for target, offset in zip(targets, offsets):
        if target == (0, 0) or offset == (0, 0) or target[0] == offset[0]:
            continue
        selected_t.append(target)
        selected_o.append(offset)
        if len(selected_t) == shots:
            break
    if len(selected_t) != shots:
        raise RuntimeError("insufficient non-exceptional Fiat-Shamir inputs")
    sums = _add_many(selected_t, selected_o)
    return [
        (target[0], target[1], offset[0], offset[1], result[0], result[1])
        for target, offset, result in zip(selected_t, selected_o, sums)
    ]


def _minimum_unique_prefix(rows: list[DatasetRow]) -> int:
    combined = [offset_x | (offset_y << 256) for _, _, offset_x, offset_y, _, _ in rows]
    for width in range(1, 513):
        mask = (1 << width) - 1
        keys = {value & mask for value in combined}
        if len(keys) == len(rows):
            return width
    raise ValueError("classical offsets are not unique")


def _lookup_rows(
    dataset: list[DatasetRow], prefix_width: int
) -> dict[int, tuple[int, int]]:
    mask = (1 << prefix_width) - 1
    return {
        (offset_x | (offset_y << 256)) & mask: (target_x ^ result_x, target_y ^ result_y)
        for target_x, target_y, offset_x, offset_y, result_x, result_y in dataset
    }


def _lookup_op_count(table: dict[int, tuple[int, int]], prefix_width: int) -> int:
    count = 4 + 4 * 256
    prefix_mask = (1 << prefix_width) - 1
    for key, (mask_x, mask_y) in table.items():
        zero_bits = prefix_width - (key & prefix_mask).bit_count()
        count += 2 * zero_bits + 2 * prefix_width + mask_x.bit_count() + mask_y.bit_count()
    return count


def _record(
    kind: int,
    *,
    q2: int = NO_FIELD,
    q1: int = NO_FIELD,
    qt: int = NO_FIELD,
    ct: int = NO_FIELD,
    cc: int = NO_FIELD,
    rt: int = NO_FIELD,
) -> bytes:
    return bytes((kind,)) + struct.pack("<6Q", q2, q1, qt, ct, cc, rt)


def _lookup_seed(
    table: dict[int, tuple[int, int]], prefix_width: int
) -> tuple[Any, str, int]:
    count = _lookup_op_count(table, prefix_width)
    shake = hashlib.shake_256(DOMAIN + struct.pack("<Q", count))
    semantic_sha = hashlib.sha256(struct.pack("<Q", count))
    buffer = bytearray()

    def emit(record: bytes) -> None:
        buffer.extend(record)
        if len(buffer) >= 4 * 1024 * 1024:
            shake.update(buffer)
            semantic_sha.update(buffer)
            buffer.clear()

    for register in range(4):
        emit(_record(REGISTER, rt=register))
    for qubit in range(256):
        emit(_record(APPEND_TO_REGISTER, qt=qubit, rt=0))
    for qubit in range(256, 512):
        emit(_record(APPEND_TO_REGISTER, qt=qubit, rt=1))
    for bit in range(256):
        emit(_record(APPEND_TO_REGISTER, ct=bit, rt=2))
    for bit in range(256, 512):
        emit(_record(APPEND_TO_REGISTER, ct=bit, rt=3))

    prefix_mask = (1 << prefix_width) - 1
    for key, (mask_x, mask_y) in sorted(table.items()):
        zero_positions = [bit for bit in range(prefix_width) if not (key >> bit) & 1]
        for bit in zero_positions:
            emit(_record(BIT_INVERT, ct=bit))
        for bit in range(prefix_width):
            emit(_record(PUSH_CONDITION, cc=bit))
        for bit in range(256):
            if (mask_x >> bit) & 1:
                emit(_record(X, qt=bit))
        for bit in range(256):
            if (mask_y >> bit) & 1:
                emit(_record(X, qt=256 + bit))
        for _ in range(prefix_width):
            emit(_record(POP_CONDITION))
        for bit in zero_positions:
            emit(_record(BIT_INVERT, ct=bit))
    if buffer:
        shake.update(buffer)
        semantic_sha.update(buffer)
    return shake, semantic_sha.hexdigest(), count


def _lookup_failures(
    dataset: list[DatasetRow], table: dict[int, tuple[int, int]], prefix_width: int
) -> tuple[int, int]:
    prefix_mask = (1 << prefix_width) - 1
    failures = 0
    table_hits = 0
    for target_x, target_y, offset_x, offset_y, result_x, result_y in dataset:
        key = (offset_x | (offset_y << 256)) & prefix_mask
        correction = table.get(key)
        if correction is None:
            output = (target_x, target_y)
        else:
            table_hits += 1
            output = (target_x ^ correction[0], target_y ^ correction[1])
        failures += output != (result_x, result_y)
    return failures, table_hits


def run(ops_path: Path, shots: int) -> dict[str, Any]:
    original_seed, original_semantic_sha, original_ops = _artifact_seed(ops_path)
    powers = _fixed_base_table()
    original_dataset = _draw_dataset(original_seed, shots, powers)
    prefix_width = _minimum_unique_prefix(original_dataset)
    table = _lookup_rows(original_dataset, prefix_width)
    original_failures, original_hits = _lookup_failures(
        original_dataset, table, prefix_width
    )
    lookup_seed, lookup_semantic_sha, lookup_ops = _lookup_seed(table, prefix_width)
    self_seeded_dataset = _draw_dataset(lookup_seed, shots, powers)
    self_seeded_failures, self_seeded_hits = _lookup_failures(
        self_seeded_dataset, table, prefix_width
    )
    verdict = (
        "green"
        if original_failures == 0
        and original_hits == shots
        and lookup_ops <= MAX_OPS
        and self_seeded_failures > 0
        else "red"
    )
    return {
        "experiment": "zero-Toffoli frozen-dataset lookup versus Fiat-Shamir reseed",
        "verdict": verdict,
        "shots": shots,
        "original_artifact": {
            "semantic_sha256": original_semantic_sha,
            "emitted_ops": original_ops,
        },
        "frozen_lookup": {
            "classical_prefix_bits": prefix_width,
            "table_entries": len(table),
            "emitted_ops": lookup_ops,
            "toffoli_ops": 0,
            "qubits": 512,
            "predicted_score_on_frozen_dataset": 0,
            "classical_failures_on_frozen_dataset": original_failures,
            "table_hits_on_frozen_dataset": original_hits,
            "semantic_sha256": lookup_semantic_sha,
        },
        "fiat_shamir_reseed": {
            "classical_failures": self_seeded_failures,
            "table_hits": self_seeded_hits,
        },
        "conclusion": (
            "A zero-score lookup fits any frozen dataset within the operation cap, but changing "
            "the semantic stream reseeds the verifier. The direct lookup is not a candidate."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ops", type=Path, default=Path("ops.bin"))
    parser.add_argument("--shots", type=int, default=FULL_VERIFICATION_SHOTS)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    if args.shots <= 0:
        parser.error("--shots must be positive")
    report = run(args.ops, args.shots)
    print(json.dumps(report, sort_keys=True, indent=None if args.json else 2))
    return 0 if report["verdict"] == "green" else 1


if __name__ == "__main__":
    raise SystemExit(main())
