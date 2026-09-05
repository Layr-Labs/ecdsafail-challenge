#!/usr/bin/env python3
"""Verify and aggregate certified Q817 Aux5 paper2607 primitive shards."""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import struct

import zstandard as zstd

import verify_q819_stream as verifier


verifier.LOCAL_WIDTH = 571
verifier.AUX_SIZE = 5


def verify_chunk(path: Path, expected_start: int) -> tuple[dict[str, object], int]:
    """Verify one shard using Python zstandard, including on Windows."""
    match = verifier.NAME.fullmatch(path.name)
    if match is None:
        raise AssertionError(f"unexpected chunk name: {path.name}")
    name_start, name_end = map(int, match.groups())
    report_path = path.with_suffix(path.suffix + ".json")
    report = json.loads(report_path.read_text(encoding="utf-8"))

    with path.open("rb") as compressed:
        with zstd.ZstdDecompressor().stream_reader(compressed) as stream:
            header = verifier.read_exact(stream, 24)
            if header[:8] != verifier.MAGIC:
                raise AssertionError(f"{path.name}: wrong magic")
            field_width, local_width, start, end = struct.unpack("<IIII", header[8:])
            if (field_width, local_width) != (
                verifier.FIELD_WIDTH,
                verifier.LOCAL_WIDTH,
            ):
                raise AssertionError(
                    f"{path.name}: wrong widths {(field_width, local_width)}"
                )
            if (start, end) != (name_start, name_end):
                raise AssertionError(f"{path.name}: header/name range mismatch")
            if start != expected_start or not start <= end <= verifier.SCHEDULE_STEPS:
                raise AssertionError(f"{path.name}: noncontiguous range")

            digest = hashlib.sha256()
            payload_bytes = 0
            while True:
                block = stream.read(8 * 1024 * 1024)
                if not block:
                    break
                digest.update(block)
                payload_bytes += len(block)
    if payload_bytes % 8:
        raise AssertionError(f"{path.name}: partial primitive record")

    records = payload_bytes // 8
    checks = {
        "schema": "paper2607-eea-primitive-stream-v3",
        "n": verifier.FIELD_WIDTH,
        "qubits": verifier.LOCAL_WIDTH,
        "source_module": verifier.SOURCE_MODULE,
        "aux_size": verifier.AUX_SIZE,
        "step_start": start,
        "step_end": end,
        "schedule_end": verifier.SCHEDULE_STEPS,
        "measurement_uncompute": False,
        "records": records,
        "raw_record_sha256": digest.hexdigest(),
        "compressed_bytes": path.stat().st_size,
    }
    for key, expected in checks.items():
        if report.get(key) != expected:
            raise AssertionError(
                f"{path.name}: report {key}={report.get(key)!r}, "
                f"expected {expected!r}"
            )

    per_step = report.get("per_step")
    if not isinstance(per_step, list) or len(per_step) != end - start + 1:
        raise AssertionError(f"{path.name}: malformed per-step report")
    if [int(row["step"]) for row in per_step] != list(range(start, end + 1)):
        raise AssertionError(f"{path.name}: noncontiguous per-step report")
    if sum(int(row["records"]) for row in per_step) != records:
        raise AssertionError(f"{path.name}: per-step record total mismatch")
    report_counts = Counter(
        {key: int(value) for key, value in report["counts"].items()}
    )
    per_step_counts: Counter[str] = Counter()
    for row in per_step:
        per_step_counts.update(
            {key: int(value) for key, value in row["counts"].items()}
        )
    if per_step_counts != report_counts:
        raise AssertionError(f"{path.name}: per-step primitive counts mismatch")
    if int(report["executed_toffoli"]) != (
        report_counts["ccx"] + 2 * report_counts["clean_c3x_mbu"]
    ):
        raise AssertionError(f"{path.name}: executed Toffoli total mismatch")

    report["file"] = path.name
    report["compressed_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
    return report, end + 1


verifier.verify_chunk = verify_chunk


if __name__ == "__main__":
    verifier.main()
