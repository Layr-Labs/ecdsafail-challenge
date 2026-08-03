#!/usr/bin/env python3
"""Install a verified Aux10 stream and synchronize the Rust count constants."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil


EXPECTED_CHUNKS = 36
EXPECTED_STEPS = 1616
EXPECTED_LOCAL_WIDTH = 576
EXPECTED_AUX = 10
EXPECTED_GENERATOR_SHA256 = (
    "b00c0801921234a7b7c528988addda914c8b229548959ab5c0d5fd2aeee922be"
)
EXPECTED_SUPPORT_COMMIT = "ac1ecffee14b5a977421b75669c52db6b4033646"
EXPECTED_SUPPORT_SHA256 = (
    "067d363deeabb6532b52f42eba884b0d184c5b74aa14d2c0d33e5579f668d277"
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def replace_constant(source: str, name: str, value: int) -> str:
    pattern = re.compile(rf"^(const {re.escape(name)}: usize = )[0-9_]+;$", re.MULTILINE)
    updated, count = pattern.subn(rf"\g<1>{value:_};", source)
    if count != 1:
        raise AssertionError(f"{name}: expected one definition, replaced {count}")
    return updated


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--stream", type=Path, required=True)
    parser.add_argument("--source-root", type=Path, required=True)
    args = parser.parse_args()

    aggregate_path = args.stream / "aggregate.json"
    aggregate = json.loads(aggregate_path.read_text(encoding="utf-8"))
    assert aggregate["chunk_count"] == EXPECTED_CHUNKS
    assert aggregate["schedule_steps"] == EXPECTED_STEPS
    assert aggregate["local_width"] == EXPECTED_LOCAL_WIDTH
    assert aggregate["aux_size"] == EXPECTED_AUX
    identity = aggregate["source_identity"]
    assert identity == {
        "candidate_generator_sha256": EXPECTED_GENERATOR_SHA256,
        "support_commit": EXPECTED_SUPPORT_COMMIT,
        "support_source_sha256": EXPECTED_SUPPORT_SHA256,
    }
    generator = (
        args.source_root
        / "src/point_add/trailmix_port/inversion/paper2607_data"
        / "eea_circuit_s835_exactwidth_dirty12.py"
    )
    assert sha256(generator) == EXPECTED_GENERATOR_SHA256

    chunks = sorted(args.stream.glob("chunk-*.zst"))
    reports = sorted(args.stream.glob("chunk-*.zst.json"))
    assert len(chunks) == len(reports) == EXPECTED_CHUNKS

    destination = (
        args.source_root
        / "src/point_add/trailmix_port/inversion/paper2607_exactwidth_data"
    )
    for path in chunks + reports:
        shutil.copy2(path, destination / path.name)
    shutil.copy2(aggregate_path, destination / "aggregate.json")
    shutil.copy2(aggregate_path, destination / "aggregate_manifest.json")

    primitive = aggregate["primitive_counts"]
    markers = int(primitive["clean_c3x_mbu"])
    values = {
        "AUX_WIDTH": EXPECTED_AUX,
        "CORE_WIDTH": EXPECTED_LOCAL_WIDTH - 10,
        "STREAM_X_PER_TRAVERSAL": int(primitive["x"]),
        "STREAM_CX_PER_TRAVERSAL": int(primitive["cx"]),
        "STREAM_CCX_PER_TRAVERSAL": int(primitive["ccx"]) + 2 * markers,
        "STREAM_HMR_PER_TRAVERSAL": markers,
        "STREAM_CZ_PER_TRAVERSAL": markers,
    }
    rust_path = (
        args.source_root
        / "src/point_add/trailmix_port/inversion/paper2607_eea.rs"
    )
    source = rust_path.read_text(encoding="utf-8")
    for name, value in values.items():
        source = replace_constant(source, name, value)
    rust_path.write_text(source, encoding="utf-8")

    print(
        "PASS installed Aux10 stream "
        f"records={aggregate['records_per_traversal']} "
        f"toffoli={aggregate['executed_toffoli_per_traversal']} "
        f"local_width={aggregate['local_width']}"
    )


if __name__ == "__main__":
    main()
