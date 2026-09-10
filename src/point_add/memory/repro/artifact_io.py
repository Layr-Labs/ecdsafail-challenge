#!/usr/bin/env python3
"""Canonical hashing and bounded record I/O for QECCOPSZ artifacts."""

from __future__ import annotations

import hashlib
import shutil
import struct
import subprocess
from pathlib import Path
from typing import Any, BinaryIO

try:
    import numpy as _numpy
except ImportError:
    _numpy = None

MAGIC = b"QECCOPSZ"
HEADER_BYTES = 16
RECORD_BYTES = 56
CANONICAL_RECORD_BYTES = 49
MAX_OPS = 4_000_000_000
NO_QUBIT = (1 << 64) - 1
X_KIND = 6
TAIL_RECORDS = 96


def _zstd() -> str:
    executable = shutil.which("zstd")
    if executable is None:
        raise RuntimeError("zstd executable not found")
    return executable


def read_header(source: BinaryIO) -> tuple[bytes, int]:
    header = source.read(HEADER_BYTES)
    if len(header) != HEADER_BYTES:
        raise ValueError("ops artifact is too short for its header")
    if header[: len(MAGIC)] != MAGIC:
        raise ValueError("ops artifact has invalid magic")
    count = struct.unpack("<Q", header[len(MAGIC) :])[0]
    if count > MAX_OPS:
        raise ValueError(f"op count {count} exceeds cap {MAX_OPS}")
    return header, count


def fingerprint(path: Path) -> dict[str, Any]:
    compressed_hasher = hashlib.sha256()
    with path.open("rb") as source:
        header, count = read_header(source)
        compressed_hasher.update(header)
        while chunk := source.read(8 * 1024 * 1024):
            compressed_hasher.update(chunk)

    canonical_hasher = hashlib.sha256(struct.pack("<Q", count))
    kind_counts = [0] * 18
    max_qubit_id = -1
    decoded_records = 0
    remainder = b""
    with path.open("rb", buffering=0) as source:
        source.seek(HEADER_BYTES)
        decoder = subprocess.Popen(
            [_zstd(), "-d", "-q", "-c"],
            stdin=source,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        assert decoder.stdout is not None
        records_per_chunk = 1_000_000 if _numpy is not None else 100_000
        while data := decoder.stdout.read(RECORD_BYTES * records_per_chunk):
            data = remainder + data
            complete = len(data) - len(data) % RECORD_BYTES
            records = memoryview(data)
            if _numpy is not None:
                raw = _numpy.frombuffer(records[:complete], dtype=_numpy.uint8).reshape(
                    -1, RECORD_BYTES
                )
                kinds = raw[:, :4].copy().view("<u4").reshape(-1)
                invalid_kinds = _numpy.flatnonzero(kinds >= len(kind_counts))
                if invalid_kinds.size:
                    index = int(invalid_kinds[0])
                    raise ValueError(
                        f"unknown kind {int(kinds[index])} at op {decoded_records + index}"
                    )
                invalid_padding = _numpy.flatnonzero(_numpy.any(raw[:, 4:8] != 0, axis=1))
                if invalid_padding.size:
                    raise ValueError(
                        f"nonzero reserved padding at op {decoded_records + int(invalid_padding[0])}"
                    )
                counts = _numpy.bincount(kinds, minlength=len(kind_counts))
                kind_counts = [
                    current + int(delta) for current, delta in zip(kind_counts, counts)
                ]
                canonical = _numpy.empty(
                    (len(kinds), CANONICAL_RECORD_BYTES), dtype=_numpy.uint8
                )
                canonical[:, 0] = kinds
                canonical[:, 1:] = raw[:, 8:RECORD_BYTES]
                canonical_hasher.update(canonical)
                qubits = raw[:, 8:32].copy().view("<u8").reshape(-1, 3)
                referenced = qubits[qubits != NO_QUBIT]
                if referenced.size:
                    max_qubit_id = max(max_qubit_id, int(referenced.max()))
                decoded_records += len(kinds)
            else:
                canonical = bytearray(
                    (complete // RECORD_BYTES) * CANONICAL_RECORD_BYTES
                )
                canonical_offset = 0
                for offset in range(0, complete, RECORD_BYTES):
                    kind = struct.unpack_from("<I", records, offset)[0]
                    if kind >= len(kind_counts):
                        raise ValueError(f"unknown kind {kind} at op {decoded_records}")
                    if records[offset + 4 : offset + 8].tobytes() != b"\0\0\0\0":
                        raise ValueError(f"nonzero reserved padding at op {decoded_records}")
                    kind_counts[kind] += 1
                    canonical[canonical_offset] = kind
                    canonical[
                        canonical_offset + 1 : canonical_offset + CANONICAL_RECORD_BYTES
                    ] = records[offset + 8 : offset + RECORD_BYTES]
                    for operand_offset in (offset + 8, offset + 16, offset + 24):
                        qubit = struct.unpack_from("<Q", records, operand_offset)[0]
                        if qubit != NO_QUBIT and qubit > max_qubit_id:
                            max_qubit_id = qubit
                    canonical_offset += CANONICAL_RECORD_BYTES
                    decoded_records += 1
                canonical_hasher.update(canonical)
            remainder = records[complete:].tobytes()
        decoder.stdout.close()
        stderr = decoder.stderr.read().decode("utf-8", errors="replace") if decoder.stderr else ""
        if decoder.stderr:
            decoder.stderr.close()
        returncode = decoder.wait()
    if returncode != 0:
        raise RuntimeError(f"zstd decoder failed: {stderr.strip()}")
    if remainder:
        raise ValueError(f"decompressed body has {len(remainder)} trailing partial-record bytes")
    if decoded_records != count:
        raise ValueError(f"decoded {decoded_records} records, expected {count}")
    return {
        "emitted_ops": count,
        "canonical_semantic_sha256": canonical_hasher.hexdigest(),
        "compressed_ops_sha256": compressed_hasher.hexdigest(),
        "max_referenced_qubit_id": max_qubit_id,
        "qubits": max_qubit_id + 1,
        "operation_kind_counts": kind_counts,
    }


def decompress_record_body(source_path: Path, destination_path: Path) -> dict[str, Any]:
    raw_hasher = hashlib.sha256()
    with source_path.open("rb", buffering=0) as source:
        _, count = read_header(source)
        source.seek(HEADER_BYTES)
        decoder = subprocess.Popen(
            [_zstd(), "-d", "-q", "-c"],
            stdin=source,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        assert decoder.stdout is not None
        size = 0
        with destination_path.open("wb") as destination:
            while chunk := decoder.stdout.read(8 * 1024 * 1024):
                destination.write(chunk)
                raw_hasher.update(chunk)
                size += len(chunk)
        decoder.stdout.close()
        stderr = decoder.stderr.read().decode("utf-8", errors="replace") if decoder.stderr else ""
        if decoder.stderr:
            decoder.stderr.close()
        returncode = decoder.wait()
    expected_size = count * RECORD_BYTES
    if returncode != 0:
        raise RuntimeError(f"zstd decoder failed: {stderr.strip()}")
    if size != expected_size:
        raise ValueError(f"decompressed body has {size} bytes, expected {expected_size}")
    return {"emitted_ops": count, "raw_bytes": size, "raw_sha256": raw_hasher.hexdigest()}


def write_nonce_artifact(
    raw_records_path: Path,
    destination_path: Path,
    emitted_ops: int,
    nonce: int,
) -> None:
    if nonce < 0 or nonce >= 1 << 48:
        raise ValueError("nonce must be a 48-bit unsigned integer")
    expected_size = emitted_ops * RECORD_BYTES
    if raw_records_path.stat().st_size != expected_size:
        raise ValueError("raw record body size does not match emitted op count")
    tail_bytes = TAIL_RECORDS * RECORD_BYTES
    prefix_bytes = expected_size - tail_bytes
    if prefix_bytes < 0:
        raise ValueError("artifact is shorter than the protected nonce tail")

    destination_path.parent.mkdir(parents=True, exist_ok=True)
    with raw_records_path.open("rb") as raw, destination_path.open("wb", buffering=0) as destination:
        destination.write(MAGIC)
        destination.write(struct.pack("<Q", emitted_ops))
        encoder = subprocess.Popen(
            [_zstd(), "-1", "-q", "-c"],
            stdin=subprocess.PIPE,
            stdout=destination,
            stderr=subprocess.PIPE,
        )
        assert encoder.stdin is not None
        remaining = prefix_bytes
        while remaining:
            chunk = raw.read(min(8 * 1024 * 1024, remaining))
            if not chunk:
                raise ValueError("raw record body ended inside the nonce prefix")
            encoder.stdin.write(chunk)
            remaining -= len(chunk)
        tail = bytearray(raw.read(tail_bytes))
        if len(tail) != tail_bytes or raw.read(1):
            raise ValueError("raw record body has an invalid nonce-tail boundary")
        for index in range(TAIL_RECORDS):
            offset = index * RECORD_BYTES
            kind = struct.unpack_from("<I", tail, offset)[0]
            if kind != X_KIND:
                raise ValueError(f"protected tail op {index} has kind {kind}, expected X")
        for bit in range(48):
            target = 1 if nonce >> bit & 1 else 0
            for pair_offset in (2 * bit, 2 * bit + 1):
                struct.pack_into("<Q", tail, pair_offset * RECORD_BYTES + 24, target)
        encoder.stdin.write(tail)
        encoder.stdin.close()
        stderr = encoder.stderr.read().decode("utf-8", errors="replace") if encoder.stderr else ""
        if encoder.stderr:
            encoder.stderr.close()
        returncode = encoder.wait()
    if returncode != 0:
        destination_path.unlink(missing_ok=True)
        raise RuntimeError(f"zstd encoder failed: {stderr.strip()}")
