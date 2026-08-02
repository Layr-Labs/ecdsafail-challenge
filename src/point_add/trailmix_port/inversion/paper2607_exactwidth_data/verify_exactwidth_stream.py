#!/usr/bin/env python3
"""Verify a fixed-point-reduced Q819 paper2607 stream bundle."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import struct
import subprocess
import tempfile


MAGIC = b"P26EEA2\0"
FIELD_WIDTH = 256
LOCAL_WIDTH = 573
SCHEDULE_STEPS = 1616
SOURCE_MODULE = "eea_circuit_s835_exactwidth_dirty12"
AUX_SIZE = 7
CHUNK_COUNT = 36
NAME = re.compile(r"chunk-(\d{4})-(\d{4})\.zst$")
SIDE_SCHEMA = "paper2607-eea-primitive-stream-v5-xor-fixed-point"
AGGREGATE_SCHEMA = "paper2607-eea-primitive-stream-aggregate-v3-xor-fixed-point"
REDUCTION_SCHEMA = "ecdsafail-paper2607-bounded-xor-window-fixed-point-v1"
SCOPE = "open public ECDSA Fail reversible point-addition benchmark"
FIRST_PASS_REMOVED = {"x": 5_855_042, "cx": 154_130, "ccx": 111_464}


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb", buffering=0) as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read_exact(stream: object, size: int) -> bytes:
    value = stream.read(size)
    if len(value) != size:
        raise AssertionError(f"truncated stream: wanted {size}, got {len(value)}")
    return value


def verify_sha256sums(directory: Path) -> str:
    checksum_path = directory / "SHA256SUMS"
    raw = checksum_path.read_bytes()
    rows: dict[str, str] = {}
    for line in raw.decode("ascii").splitlines():
        digest, separator, name = line.partition("  ")
        if separator != "  " or not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise AssertionError(f"malformed SHA256SUMS line: {line!r}")
        if not name or "/" in name or name in rows or name == "SHA256SUMS":
            raise AssertionError(f"unsafe or duplicate SHA256SUMS name: {name!r}")
        rows[name] = digest
    actual = {path.name for path in directory.iterdir() if path.name != "SHA256SUMS"}
    allowed_unlisted = {"verify_exactwidth_stream.py"} & actual
    covered_actual = actual - allowed_unlisted
    if set(rows) != covered_actual:
        raise AssertionError(
            f"SHA256SUMS coverage mismatch: missing={sorted(covered_actual - set(rows))} "
            f"extra={sorted(set(rows) - covered_actual)}"
        )
    for name, expected in rows.items():
        observed = sha256_file(directory / name)
        if observed != expected:
            raise AssertionError(f"{name}: compressed/artifact SHA mismatch")
    return hashlib.sha256(raw).hexdigest()


def verify_chunk(
    path: Path,
    committed: dict[str, object],
    expected_start: int,
    word_auditor: Path,
    fixed_point_scanner: Path,
    scratch_directory: Path,
) -> tuple[dict[str, object], int]:
    match = NAME.fullmatch(path.name)
    if match is None:
        raise AssertionError(f"unexpected chunk name: {path.name}")
    name_start, name_end = map(int, match.groups())
    report_path = path.with_suffix(path.suffix + ".json")
    report = json.loads(report_path.read_text(encoding="ascii"))
    scratch_directory.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        prefix=path.name + ".", suffix=".raw", dir=scratch_directory, delete=False
    ) as raw_stream:
        raw_path = Path(raw_stream.name)
        process = subprocess.Popen(
            ["/usr/bin/zstd", "-q", "-dc", str(path)],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            bufsize=0,
        )
        assert process.stdout is not None and process.stderr is not None
        header = read_exact(process.stdout, 24)
        raw_stream.write(header)
        if header[:8] != MAGIC:
            raise AssertionError(f"{path.name}: wrong stream magic")
        field_width, local_width, start, end = struct.unpack("<IIII", header[8:])
        if (field_width, local_width) != (FIELD_WIDTH, LOCAL_WIDTH):
            raise AssertionError(f"{path.name}: wrong widths")
        if (start, end) != (name_start, name_end):
            raise AssertionError(f"{path.name}: header/name range mismatch")
        if start != expected_start or not start <= end <= SCHEDULE_STEPS:
            raise AssertionError(f"{path.name}: noncontiguous schedule range")

        body_digest = hashlib.sha256()
        full_digest = hashlib.sha256(header)
        body_bytes = 0
        while True:
            block = process.stdout.read(8 * 1024 * 1024)
            if not block:
                break
            raw_stream.write(block)
            body_digest.update(block)
            full_digest.update(block)
            body_bytes += len(block)
        stderr = process.stderr.read()
        return_code = process.wait()
        if return_code != 0:
            raise AssertionError(f"{path.name}: zstd exited {return_code}: {stderr!r}")
    try:
        if body_bytes % 8:
            raise AssertionError(f"{path.name}: partial primitive record")
        records = body_bytes // 8
        audited = subprocess.run(
            [str(word_auditor), str(raw_path)],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        ).stdout.strip()
        audit_match = re.fullmatch(
            r"value_width=(\d+) local_width=(\d+) step_start=(\d+) step_end=(\d+) "
            r"records=(\d+) x=(\d+) cx=(\d+) ccx=(\d+) kind7=(\d+)",
            audited,
        )
        if audit_match is None:
            raise AssertionError(f"{path.name}: malformed independent word audit")
        audit_values = tuple(map(int, audit_match.groups()))
        if audit_values[:5] != (FIELD_WIDTH, LOCAL_WIDTH, start, end, records):
            raise AssertionError(f"{path.name}: independent word-audit contract mismatch")
        audited_counts = dict(zip(("x", "cx", "ccx", "clean_c3x_mbu"), audit_values[5:]))

        with raw_path.open("rb", buffering=0) as scanner_input:
            scanner_input.seek(24)
            scan = subprocess.run(
                [str(fixed_point_scanner)],
                stdin=scanner_input,
                check=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            ).stdout.strip()
        scan_match = re.fullmatch(
            r"input=(\d+) output=(\d+) removed=(\d+) reordered=(\d+) "
            r"barriers=(\d+) examined=(\d+) max_scan=(\d+) "
            r"window_exhaustions=(\d+) x=(\d+) cx=(\d+) ccx=(\d+)",
            scan,
        )
        if scan_match is None:
            raise AssertionError(f"{path.name}: malformed fixed-point scan")
        scan_values = tuple(map(int, scan_match.groups()))
        if scan_values[0] != records or scan_values[1] != records:
            raise AssertionError(f"{path.name}: fixed-point scan record mismatch")
        if any(scan_values[index] != 0 for index in (2, 3, 8, 9, 10)):
            raise AssertionError(f"{path.name}: output is not a fixed point")
        if scan_values[4] != audited_counts["clean_c3x_mbu"]:
            raise AssertionError(f"{path.name}: fixed-point barrier mismatch")
    finally:
        raw_path.unlink(missing_ok=True)

    checks = {
        "schema": SIDE_SCHEMA,
        "n": FIELD_WIDTH,
        "qubits": LOCAL_WIDTH,
        "source_module": SOURCE_MODULE,
        "aux_size": AUX_SIZE,
        "step_start": start,
        "step_end": end,
        "schedule_end": SCHEDULE_STEPS,
        "measurement_uncompute": False,
        "records": records,
        "raw_record_sha256": body_digest.hexdigest(),
        "raw_file_sha256": full_digest.hexdigest(),
        "compressed_bytes": path.stat().st_size,
        "compressed_sha256": sha256_file(path),
        "scope_predicate": SCOPE,
        "model_attribution": "GPT-Codex",
    }
    for key, expected in checks.items():
        if report.get(key) != expected:
            raise AssertionError(
                f"{path.name}: sidecar {key}={report.get(key)!r}, expected {expected!r}"
            )

    counts = report.get("counts")
    if not isinstance(counts, dict) or set(counts) != {"x", "cx", "ccx", "clean_c3x_mbu"}:
        raise AssertionError(f"{path.name}: malformed primitive counts")
    counts = {key: int(value) for key, value in counts.items()}
    if any(value < 0 for value in counts.values()) or sum(counts.values()) != records:
        raise AssertionError(f"{path.name}: primitive counts do not partition records")
    if counts != audited_counts:
        raise AssertionError(f"{path.name}: sidecar/independent opcode histogram mismatch")
    if report.get("executed_toffoli") != counts["ccx"] + 2 * counts["clean_c3x_mbu"]:
        raise AssertionError(f"{path.name}: executed Toffoli mismatch")

    reduction = report.get("reduction")
    if not isinstance(reduction, dict) or reduction.get("schema") != REDUCTION_SCHEMA:
        raise AssertionError(f"{path.name}: malformed reduction proof metadata")
    removed_by_kind = reduction.get("removed_by_kind")
    if not isinstance(removed_by_kind, dict) or set(removed_by_kind) != {"x", "cx", "ccx"}:
        raise AssertionError(f"{path.name}: malformed removed-by-kind metadata")
    removed_by_kind = {key: int(value) for key, value in removed_by_kind.items()}
    removed = int(reduction["removed"])
    if removed != sum(removed_by_kind.values()):
        raise AssertionError(f"{path.name}: removal arithmetic mismatch")
    if int(reduction["source_records"]) - removed != records:
        raise AssertionError(f"{path.name}: source/output record mismatch")
    if int(reduction["reduction_passes"]) < 1:
        raise AssertionError(f"{path.name}: missing material reduction pass")
    if reduction.get("verification_zero_pass") is not True:
        raise AssertionError(f"{path.name}: missing fixed-point verification pass")

    chunk_keys = (
        "file", "step_start", "step_end", "records", "raw_record_sha256",
        "raw_file_sha256", "compressed_bytes", "compressed_sha256",
    )
    observed = {key: path.name if key == "file" else report[key] for key in chunk_keys}
    for key, value in observed.items():
        if committed.get(key) != value:
            raise AssertionError(f"{path.name}: aggregate chunk {key} mismatch")
    if int(committed["source_records"]) != int(reduction["source_records"]):
        raise AssertionError(f"{path.name}: aggregate source-record mismatch")
    if int(committed["removed"]) != removed:
        raise AssertionError(f"{path.name}: aggregate removal mismatch")
    if committed["removed_by_kind"] != removed_by_kind:
        raise AssertionError(f"{path.name}: aggregate removed-by-kind mismatch")
    if int(committed["reduction_passes"]) != int(reduction["reduction_passes"]):
        raise AssertionError(f"{path.name}: aggregate pass-count mismatch")
    return {"counts": counts, "reduction": reduction, "records": records}, end + 1


def verify(
    directory: Path,
    word_auditor: Path,
    fixed_point_scanner: Path,
    scratch_directory: Path,
) -> dict[str, object]:
    directory = directory.resolve()
    sha256sums_sha = verify_sha256sums(directory)
    aggregate_raw = (directory / "aggregate.json").read_bytes()
    if aggregate_raw != (directory / "aggregate_manifest.json").read_bytes():
        raise AssertionError("aggregate.json and aggregate_manifest.json differ")
    aggregate = json.loads(aggregate_raw)
    if aggregate.get("schema") != AGGREGATE_SCHEMA:
        raise AssertionError("wrong aggregate schema")
    contract = {
        "field_width": FIELD_WIDTH,
        "local_width": LOCAL_WIDTH,
        "source_module": SOURCE_MODULE,
        "aux_size": AUX_SIZE,
        "schedule_steps": SCHEDULE_STEPS,
        "chunk_count": CHUNK_COUNT,
        "scope_predicate": SCOPE,
        "model_attribution": "GPT-Codex",
    }
    for key, expected in contract.items():
        if aggregate.get(key) != expected:
            raise AssertionError(f"aggregate {key} mismatch")
    chunks = aggregate.get("chunks")
    if not isinstance(chunks, list) or len(chunks) != CHUNK_COUNT:
        raise AssertionError("wrong aggregate chunk list")
    paths = sorted(directory.glob("chunk-*.zst"))
    if len(paths) != CHUNK_COUNT:
        raise AssertionError("wrong compressed chunk count")

    totals: Counter[str] = Counter()
    removed: Counter[str] = Counter()
    expected_start = 1
    source_records = 0
    max_passes = 0
    for path, committed in zip(paths, chunks, strict=True):
        row, expected_start = verify_chunk(
            path,
            committed,
            expected_start,
            word_auditor,
            fixed_point_scanner,
            scratch_directory,
        )
        totals["records"] += int(row["records"])
        totals.update(row["counts"])
        reduction = row["reduction"]
        source_records += int(reduction["source_records"])
        removed.update({key: int(value) for key, value in reduction["removed_by_kind"].items()})
        max_passes = max(max_passes, int(reduction["reduction_passes"]))
    if expected_start != SCHEDULE_STEPS + 1:
        raise AssertionError("incomplete aggregate schedule")

    kind7 = totals["clean_c3x_mbu"]
    computed = {
        "records_per_traversal": totals["records"],
        "emitted_ops_per_traversal": totals["records"] + 3 * kind7,
        "executed_toffoli_per_traversal": totals["ccx"] + 2 * kind7,
        "four_traversal_emitted_ops": 4 * (totals["records"] + 3 * kind7),
        "four_traversal_executed_toffoli": 4 * (totals["ccx"] + 2 * kind7),
        "primitive_counts": {
            key: totals[key] for key in ("x", "cx", "ccx", "clean_c3x_mbu")
        },
    }
    for key, expected in computed.items():
        if aggregate.get(key) != expected:
            raise AssertionError(f"aggregate {key} arithmetic mismatch")
    reduction = aggregate.get("reduction")
    if not isinstance(reduction, dict) or reduction.get("schema") != REDUCTION_SCHEMA:
        raise AssertionError("wrong aggregate reduction metadata")
    if int(reduction["source_records_per_traversal"]) != source_records:
        raise AssertionError("aggregate source-record total mismatch")
    if source_records != 260_771_788:
        raise AssertionError("aggregate parent record count drift")
    if int(reduction["removed_per_traversal"]) != sum(removed.values()):
        raise AssertionError("aggregate removed total mismatch")
    if reduction["removed_by_kind_per_traversal"] != dict(removed):
        raise AssertionError("aggregate removed-by-kind total mismatch")
    if reduction["first_pass_removed_by_kind_per_traversal"] != FIRST_PASS_REMOVED:
        raise AssertionError("aggregate first-pass census lineage mismatch")
    if int(reduction["max_reduction_passes"]) != max_passes:
        raise AssertionError("aggregate max-pass mismatch")
    if reduction.get("verification_zero_pass_per_shard") is not True:
        raise AssertionError("aggregate fixed-point proof flag is absent")
    if source_records - sum(removed.values()) != totals["records"]:
        raise AssertionError("aggregate source/reduction/output identity mismatch")
    if totals["clean_c3x_mbu"] != 6_464:
        raise AssertionError("aggregate clean-C3X marker count drift")

    canonical = (json.dumps(aggregate, indent=2, sort_keys=True) + "\n").encode("ascii")
    if canonical != aggregate_raw:
        raise AssertionError("aggregate encoding is not canonical")
    aggregate["bundle_sha256sums_sha256"] = sha256sums_sha
    return aggregate


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--directory", type=Path, required=True)
    parser.add_argument("--word-auditor", type=Path, required=True)
    parser.add_argument("--fixed-point-scanner", type=Path, required=True)
    parser.add_argument("--scratch-directory", type=Path, required=True)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    aggregate = verify(
        args.directory,
        args.word_auditor.resolve(),
        args.fixed_point_scanner.resolve(),
        args.scratch_directory.resolve(),
    )
    aggregate.pop("bundle_sha256sums_sha256")
    encoded = json.dumps(aggregate, indent=2, sort_keys=True) + "\n"
    if args.out is not None:
        args.out.write_text(encoded, encoding="ascii")
    print(encoded, end="")


if __name__ == "__main__":
    main()
