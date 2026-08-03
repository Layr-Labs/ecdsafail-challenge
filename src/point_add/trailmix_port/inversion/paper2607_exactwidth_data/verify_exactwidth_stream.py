#!/usr/bin/env python3
"""Independently verify a Q819 prefix/XOR-normal-form stream bundle."""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import re
import struct
import subprocess
import tempfile


SCOPE = "open public ECDSA Fail reversible point-addition benchmark"
PREFIX_SOURCE_SHA256 = "bbb660ee3f128a30aa2c4c1ee6b71a983263a32973ea7141a631697401f99506"
SIDE_SCHEMA = "paper2607-eea-primitive-stream-v7-prefix-xor-unbounded-fixed-point"
AGGREGATE_SCHEMA = (
    "paper2607-eea-primitive-stream-aggregate-v7-prefix-xor-unbounded-fixed-point"
)
REDUCTION_SCHEMA = "ecdsafail-paper2607-prefix-unbounded-xor-normal-form-v1"
NAME = re.compile(r"chunk-(\d{4})-(\d{4})\.zst$")
AUDIT_PATTERN = re.compile(
    r"value_width=(\d+) local_width=(\d+) step_start=(\d+) step_end=(\d+) "
    r"records=(\d+) x=(\d+) cx=(\d+) ccx=(\d+) kind7=(\d+)"
)
TRANSFORM_PATTERN = re.compile(
    r"input=(\d+) output=(\d+) removed=(\d+) reordered=(\d+) barriers=(\d+) "
    r"max_segment=(\d+) hash_capacity=(\d+) blocker_queries=(\d+) "
    r"hash_probes=(\d+) max_hash_probe=(\d+) x=(\d+) cx=(\d+) ccx=(\d+) "
    r"step_start=(\d+) step_end=(\d+)"
)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb", buffering=0) as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def verify_sha256sums(directory: Path) -> str:
    path = directory / "SHA256SUMS"
    raw = path.read_bytes()
    rows: dict[str, str] = {}
    for line in raw.decode("ascii").splitlines():
        digest, separator, name = line.partition("  ")
        if separator != "  " or not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise AssertionError(f"malformed SHA256SUMS row: {line!r}")
        if not name or "/" in name or name in rows or name == "SHA256SUMS":
            raise AssertionError(f"unsafe SHA256SUMS name: {name!r}")
        rows[name] = digest
    actual = {item.name for item in directory.iterdir() if item.name != "SHA256SUMS"}
    allowed_unlisted = {"verify_exactwidth_stream.py"} & actual
    covered = actual - allowed_unlisted
    if set(rows) != covered:
        raise AssertionError(
            f"SHA256SUMS coverage mismatch: missing={sorted(covered - set(rows))} "
            f"extra={sorted(set(rows) - covered)}"
        )
    for name, expected in rows.items():
        observed = sha256_file(directory / name)
        if observed != expected:
            raise AssertionError(f"{name}: SHA-256 mismatch")
    return hashlib.sha256(raw).hexdigest()


def parse_audit(text: str) -> dict[str, object]:
    match = AUDIT_PATTERN.fullmatch(text.strip())
    if match is None:
        raise AssertionError(f"malformed word audit: {text!r}")
    values = list(map(int, match.groups()))
    return {
        "value_width": values[0], "local_width": values[1],
        "step_start": values[2], "step_end": values[3],
        "records": values[4],
        "counts": {
            "x": values[5], "cx": values[6], "ccx": values[7],
            "clean_c3x_mbu": values[8],
        },
    }


def parse_transform(text: str) -> dict[str, int]:
    match = TRANSFORM_PATTERN.fullmatch(text.strip())
    if match is None:
        raise AssertionError(f"malformed fixed-point scan: {text!r}")
    keys = (
        "input", "output", "removed", "reordered", "barriers",
        "max_segment", "hash_capacity", "blocker_queries", "hash_probes",
        "max_hash_probe", "x", "cx", "ccx", "step_start", "step_end",
    )
    return dict(zip(keys, map(int, match.groups()), strict=True))


def verify_chunk(
    path: Path,
    committed: dict[str, object],
    expected_start: int,
    word_auditor: Path,
    transformer: Path,
    scratch_root: Path,
) -> tuple[dict[str, object], int]:
    match = NAME.fullmatch(path.name)
    if match is None:
        raise AssertionError(f"unexpected chunk name: {path.name}")
    name_start, name_end = map(int, match.groups())
    report_path = path.with_suffix(path.suffix + ".json")
    report = json.loads(report_path.read_text(encoding="ascii"))
    with tempfile.TemporaryDirectory(prefix=path.name + ".", dir=scratch_root) as temporary:
        scratch = Path(temporary)
        raw = scratch / "stream.raw"
        fixed = scratch / "fixed.raw"
        with raw.open("wb") as output:
            subprocess.run(
                ["/usr/bin/zstd", "-q", "-dc", str(path)],
                check=True, stdout=output, stderr=subprocess.PIPE,
            )
        with raw.open("rb", buffering=0) as stream:
            header = stream.read(24)
            if len(header) != 24 or header[:8] != b"P26EEA2\0":
                raise AssertionError(f"{path.name}: invalid header")
            field_width, local_width, start, end = struct.unpack("<IIII", header[8:])
            body_digest = hashlib.sha256()
            for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
                body_digest.update(block)
        if (field_width, local_width) != (256, 573):
            raise AssertionError(f"{path.name}: wrong widths")
        if (start, end) != (name_start, name_end):
            raise AssertionError(f"{path.name}: header/name range mismatch")
        if start != expected_start or not start <= end <= 1616:
            raise AssertionError(f"{path.name}: noncontiguous range")
        if (raw.stat().st_size - 24) % 8:
            raise AssertionError(f"{path.name}: partial primitive record")
        records = (raw.stat().st_size - 24) // 8

        audited = subprocess.run(
            [str(word_auditor), str(raw)], check=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        ).stdout
        audit = parse_audit(audited)
        if (
            audit["value_width"], audit["local_width"], audit["step_start"],
            audit["step_end"], audit["records"],
        ) != (256, 573, start, end, records):
            raise AssertionError(f"{path.name}: independent audit contract mismatch")
        fixed_run = subprocess.run(
            [str(transformer), str(raw), str(fixed)], check=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        ).stdout
        fixed_row = parse_transform(fixed_run)
        if fixed_row["input"] != records or fixed_row["output"] != records:
            raise AssertionError(f"{path.name}: fixed-point record mismatch")
        if any(fixed_row[key] for key in ("removed", "reordered", "x", "cx", "ccx")):
            raise AssertionError(f"{path.name}: not an XOR normal-form fixed point")
        if sha256_file(raw) != sha256_file(fixed):
            raise AssertionError(f"{path.name}: zero pass changed bytes")
        raw_file_sha = sha256_file(raw)
        raw_body_sha = body_digest.hexdigest()

    checks = {
        "schema": SIDE_SCHEMA,
        "scope_predicate": SCOPE,
        "model_attribution": "GPT-Codex",
        "python_candidate_sha256": PREFIX_SOURCE_SHA256,
        "source_module": "eea_circuit_s835_exactwidth_dirty12",
        "n": 256,
        "qubits": 573,
        "aux_size": 7,
        "step_start": start,
        "step_end": end,
        "schedule_end": 1616,
        "measurement_uncompute": False,
        "records": records,
        "compressed_bytes": path.stat().st_size,
        "compressed_sha256": sha256_file(path),
        "raw_file_sha256": raw_file_sha,
        "raw_record_sha256": raw_body_sha,
        "counts": audit["counts"],
    }
    for key, expected in checks.items():
        if report.get(key) != expected:
            raise AssertionError(
                f"{path.name}: sidecar {key}={report.get(key)!r}, expected {expected!r}"
            )
    counts = {key: int(value) for key, value in report["counts"].items()}
    if set(counts) != {"x", "cx", "ccx", "clean_c3x_mbu"}:
        raise AssertionError(f"{path.name}: malformed opcode histogram")
    if sum(counts.values()) != records:
        raise AssertionError(f"{path.name}: opcode histogram does not partition records")
    if report["executed_toffoli"] != counts["ccx"] + 2 * counts["clean_c3x_mbu"]:
        raise AssertionError(f"{path.name}: Toffoli arithmetic mismatch")
    reduction = report["reduction"]
    if reduction["schema"] != REDUCTION_SCHEMA or not reduction["fixed_point_verified"]:
        raise AssertionError(f"{path.name}: malformed reduction proof metadata")
    removed_by_kind = {
        key: int(value) for key, value in reduction["removed_by_kind"].items()
    }
    if set(removed_by_kind) != {"x", "cx", "ccx"}:
        raise AssertionError(f"{path.name}: malformed removed-by-kind")
    if reduction["source_records"] - reduction["removed"] != records:
        raise AssertionError(f"{path.name}: source/removal record mismatch")
    if reduction["removed"] != sum(removed_by_kind.values()):
        raise AssertionError(f"{path.name}: removal partition mismatch")
    if report["candidate"] or report["trusted_9024_validation"] or report["official_submission"]:
        raise AssertionError(f"{path.name}: sidecar overclaims evidence")

    committed_checks = {
        "file": path.name,
        "step_start": start,
        "step_end": end,
        "records": records,
        "counts": counts,
        "executed_toffoli": report["executed_toffoli"],
        "compressed_bytes": path.stat().st_size,
        "compressed_sha256": checks["compressed_sha256"],
        "raw_file_sha256": checks["raw_file_sha256"],
        "raw_record_sha256": checks["raw_record_sha256"],
        "source_records": reduction["source_records"],
        "source_compressed_sha256": reduction["source_compressed_sha256"],
        "removed": reduction["removed"],
        "removed_by_kind": removed_by_kind,
    }
    for key, expected in committed_checks.items():
        if committed.get(key) != expected:
            raise AssertionError(f"{path.name}: aggregate chunk {key} mismatch")
    return {
        "records": records,
        "counts": counts,
        "source_records": int(reduction["source_records"]),
        "removed": int(reduction["removed"]),
        "removed_by_kind": removed_by_kind,
    }, end + 1


def verify(
    directory: Path,
    word_auditor: Path,
    transformer: Path,
    scratch_root: Path,
    jobs: int = 1,
) -> dict[str, object]:
    directory = directory.resolve()
    scratch_root = scratch_root.resolve()
    scratch_root.mkdir(parents=True, exist_ok=True)
    sums_sha = verify_sha256sums(directory)
    aggregate_path = directory / "aggregate.json"
    if aggregate_path.read_bytes() != (directory / "aggregate_manifest.json").read_bytes():
        raise AssertionError("aggregate copies differ")
    aggregate = json.loads(aggregate_path.read_text(encoding="ascii"))
    contract = {
        "schema": AGGREGATE_SCHEMA,
        "scope_predicate": SCOPE,
        "model_attribution": "GPT-Codex",
        "python_candidate_sha256": PREFIX_SOURCE_SHA256,
        "source_module": "eea_circuit_s835_exactwidth_dirty12",
        "field_width": 256,
        "local_width": 573,
        "aux_size": 7,
        "schedule_steps": 1616,
        "chunk_count": 36,
    }
    for key, expected in contract.items():
        if aggregate.get(key) != expected:
            raise AssertionError(f"aggregate {key} mismatch")
    committed_rows = aggregate.get("chunks")
    paths = sorted(directory.glob("chunk-*.zst"))
    if not isinstance(committed_rows, list) or len(committed_rows) != len(paths):
        raise AssertionError("bundle chunk list mismatch")
    if len(paths) != 36:
        raise AssertionError("expected 36 bundle chunks")
    expected_starts: list[int] = []
    cursor = 1
    for path in paths:
        expected_starts.append(cursor)
        match = NAME.fullmatch(path.name)
        assert match is not None
        cursor = int(match.group(2)) + 1
    if cursor != 1617:
        raise AssertionError("incomplete schedule coverage")

    def task(item):
        index, path = item
        return verify_chunk(
            path, committed_rows[index], expected_starts[index],
            word_auditor, transformer, scratch_root,
        )[0]

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        rows = list(pool.map(task, enumerate(paths)))
    totals: Counter[str] = Counter()
    removed: Counter[str] = Counter()
    records = source_records = removed_total = 0
    for row in rows:
        records += int(row["records"])
        source_records += int(row["source_records"])
        removed_total += int(row["removed"])
        totals.update(row["counts"])
        removed.update(row["removed_by_kind"])
    computed = {
        "records_per_traversal": records,
        "primitive_counts": {
            gate: totals[gate] for gate in ("x", "cx", "ccx", "clean_c3x_mbu")
        },
        "executed_toffoli_per_traversal": totals["ccx"] + 2 * totals["clean_c3x_mbu"],
        "emitted_ops_per_traversal": records + 3 * totals["clean_c3x_mbu"],
    }
    computed["four_traversal_emitted_ops"] = 4 * computed["emitted_ops_per_traversal"]
    computed["four_traversal_executed_toffoli"] = 4 * computed["executed_toffoli_per_traversal"]
    for key, expected in computed.items():
        if aggregate.get(key) != expected:
            raise AssertionError(f"aggregate {key} arithmetic mismatch")
    reduction = aggregate["reduction"]
    if reduction["schema"] != REDUCTION_SCHEMA:
        raise AssertionError("wrong aggregate reduction schema")
    if reduction["source_records_per_traversal"] != source_records:
        raise AssertionError("aggregate source-record mismatch")
    if reduction["removed_per_traversal"] != removed_total:
        raise AssertionError("aggregate removed-count mismatch")
    expected_removed = {gate: removed[gate] for gate in ("x", "cx", "ccx")}
    if reduction["removed_by_kind_per_traversal"] != expected_removed:
        raise AssertionError("aggregate removed-by-kind mismatch")
    if source_records - removed_total != records:
        raise AssertionError("aggregate source/removal arithmetic mismatch")
    if not reduction["fixed_point_verified_per_shard"]:
        raise AssertionError("aggregate fixed-point flag missing")
    aggregate["bundle_sha256sums_sha256"] = sums_sha
    return aggregate


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--directory", type=Path, required=True)
    parser.add_argument("--word-auditor", type=Path, required=True)
    parser.add_argument("--transformer", type=Path, required=True)
    parser.add_argument("--scratch-root", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    result = verify(
        args.directory, args.word_auditor.resolve(), args.transformer.resolve(),
        args.scratch_root, args.jobs,
    )
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="ascii")
    print(
        "PASS prefix XOR bundle "
        f"records={result['records_per_traversal']} "
        f"toffoli={result['executed_toffoli_per_traversal']}",
        flush=True,
    )


if __name__ == "__main__":
    main()
