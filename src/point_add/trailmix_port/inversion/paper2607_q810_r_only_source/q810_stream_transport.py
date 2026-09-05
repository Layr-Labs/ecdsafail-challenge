#!/usr/bin/env python3
"""gpt-5: exact selected production transport, no baseline loader or CLI.

The constructor and release callbacks must come from an independently
authenticated portable Q810 baseline. This module alone generates no source.
"""
from __future__ import annotations
from collections import Counter
import gc
import hashlib
import json
import os
from pathlib import Path
import struct
import sys
import time
from typing import Any, BinaryIO, Callable, Iterable
import zstandard

MAGIC = b"P26EEA2\0"
SCHEDULE_STEPS = 1616
CHUNK_STEPS = 45
LOCAL_WIDTH = 564
BUFFER_RECORDS = 65_536
KINDS = {"x": 1, "cx": 2, "ccx": 3}

class StreamError(RuntimeError):
    """A source binding, generated primitive, or published shard is unsafe."""

def require(condition: bool, message: str) -> None:
    if not condition:
        raise StreamError(message)

def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()

def pack_word(kind: str, wires: tuple[int, ...]) -> int:
    if kind == "x":
        require(len(wires) == 1, "X primitive arity changed")
        a, = wires
        require(0 <= a < LOCAL_WIDTH, "X primitive escaped its 566-wire register")
        return 0x11 | (a << 8)
    if kind == "cx":
        require(len(wires) == 2, "CX primitive arity changed")
        a, b = wires
        require(0 <= a < LOCAL_WIDTH and 0 <= b < LOCAL_WIDTH and a != b,
                "CX primitive has invalid or aliased wires")
        return 0x22 | (a << 8) | (b << 18)
    if kind == "ccx":
        require(len(wires) == 3, "CCX primitive arity changed")
        a, b, c = wires
        require(0 <= a < LOCAL_WIDTH and 0 <= b < LOCAL_WIDTH and 0 <= c < LOCAL_WIDTH
                and a != b and a != c and b != c,
                "CCX primitive has invalid or aliased wires")
        return 0x33 | (a << 8) | (b << 18) | (c << 28)
    raise StreamError(f"unsupported non-unitary primitive {kind!r}")

def normalized_counts(counts: Counter[str]) -> dict[str, int]:
    require(not set(counts).difference(KINDS), "unexpected primitive counter key")
    return {kind: int(counts[kind]) for kind in ("x", "cx", "ccx")}

def clear_gate_caches(source: Any) -> None:
    for value in vars(source).values():
        clear = getattr(value, "cache_clear", None)
        if callable(clear):
            clear()
    support = sys.modules.get("eea_circuit_updated")
    inverse = getattr(getattr(support, "Instruction", None), "inverse", None)
    clear_inverse = getattr(inverse, "cache_clear", None)
    if callable(clear_inverse):
        clear_inverse()
    gc.collect()

def generate_records(
    destination: BinaryIO,
    *,
    start: int,
    end: int,
    build_step: Callable[[int], Any],
    primitive_stream: Callable[[Any], Iterable[tuple[str, tuple[int, ...]]]],
    compression_level: int = 3,
    release_step: Callable[[], None] | None = None,
    announce: bool = True,
) -> dict[str, Any]:
    require(1 <= start <= end <= SCHEDULE_STEPS, "invalid source step range")
    compressor = zstandard.ZstdCompressor(level=compression_level)
    digest = hashlib.sha256()
    aggregate: Counter[str] = Counter()
    per_step: list[dict[str, Any]] = []
    buffer = bytearray(BUFFER_RECORDS * 8)
    used = 0

    with compressor.stream_writer(destination, closefd=False) as compressed:
        compressed.write(MAGIC + struct.pack("<IIII", 256, LOCAL_WIDTH, start, end))
        for step in range(start, end + 1):
            began = time.monotonic()
            circuit = build_step(step)
            require(getattr(circuit, "num_qubits", None) == LOCAL_WIDTH,
                    f"source step {step} is not exactly 566 qubits")
            counts: Counter[str] = Counter()
            for kind, wires in primitive_stream(circuit):
                word = pack_word(kind, wires)
                struct.pack_into("<Q", buffer, used, word)
                used += 8
                counts[kind] += 1
                if used == len(buffer):
                    chunk = memoryview(buffer)[:used]
                    compressed.write(chunk)
                    digest.update(chunk)
                    used = 0
            aggregate.update(counts)
            row = {
                "step": step,
                "records": sum(counts.values()),
                "counts": normalized_counts(counts),
                "executed_toffoli": counts["ccx"],
            }
            per_step.append(row)
            if announce:
                print(json.dumps({
                    "event": "q812-step-compressed",
                    "step": step,
                    "records": row["records"],
                    "toffoli": row["executed_toffoli"],
                    "elapsed_seconds": round(time.monotonic() - began, 3),
                    "worker_pid": os.getpid(),
                }, sort_keys=True), flush=True)
            del circuit
            if release_step is not None:
                release_step()
        if used:
            final = memoryview(buffer)[:used]
            compressed.write(final)
            digest.update(final)

    return {
        "schema": "paper2607-eea-primitive-stream-v3",
        "n": 256,
        "qubits": LOCAL_WIDTH,
        "aux_size": 0,
        "step_start": start,
        "step_end": end,
        "schedule_end": SCHEDULE_STEPS,
        "record_bytes": 8,
        "records": sum(aggregate.values()),
        "counts": normalized_counts(aggregate),
        "executed_toffoli": aggregate["ccx"],
        "raw_record_sha256": digest.hexdigest(),
        "per_step": per_step,
    }

def validate_chunk(path: Path, report: dict[str, Any]) -> None:
    require(sha256(path) == report["compressed_sha256"], "compressed Q812 shard hash mismatch")
    decompressor = zstandard.ZstdDecompressor()
    with path.open("rb") as compressed:
        with decompressor.stream_reader(compressed) as stream:
            header = stream.read(24)
            require(len(header) == 24 and header[:8] == MAGIC,
                    "Q812 shard header magic is invalid")
            require(struct.unpack("<IIII", header[8:]) ==
                    (256, LOCAL_WIDTH, report["step_start"], report["step_end"]),
                    "Q812 shard header dimensions or step range drifted")
            digest = hashlib.sha256()
            size = 0
            for block in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(block)
                size += len(block)
    require(size == report["records"] * 8, "Q812 shard raw record count mismatch")
    require(digest.hexdigest() == report["raw_record_sha256"],
            "Q812 shard records-only SHA256 mismatch")

def chunk_ranges(start: int, end: int) -> list[tuple[int, int]]:
    require(1 <= start <= end <= SCHEDULE_STEPS, "invalid Q812 schedule range")
    require(start == 1 or (start - 1) % CHUNK_STEPS == 0,
            "Q812 production chunk must begin on a pinned 45-step boundary")
    ranges: list[tuple[int, int]] = []
    for first in range(start, end + 1, CHUNK_STEPS):
        last = min(first + CHUNK_STEPS - 1, SCHEDULE_STEPS)
        require(last <= end, "partial production shard would not match Rust include_bytes")
        ranges.append((first, last))
    return ranges
