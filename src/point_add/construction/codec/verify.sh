#!/usr/bin/env bash
set -euo pipefail
if [ "$#" -ne 2 ]; then echo 'Usage: bash verify.sh RAW_FILE GENERATED_SOURCE_DIR' >&2; exit 2; fi
srcdir=$(cd -- "$(dirname -- "$0")" && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/gateir-verify.XXXXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
if [ -f "$2/schedule.zst" ]; then
    "${RUSTC:-rustc}" -O --edition=2021 "$srcdir/verify-scheduled.rs" -o "$tmp/decode"
    "${ZSTD:-zstd}" -qdc -- "$2/schedule.zst" > "$tmp/plan"
    "${ZSTD:-zstd}" -qdc --long=30 -- "$2/gates.zst" | "$tmp/decode" "$1" "$tmp/plan" | cmp -- "$1" -
else
    "${RUSTC:-rustc}" -O --edition=2021 "$srcdir/verify-raw.rs" -o "$tmp/decode"
    "${ZSTD:-zstd}" -qdc --long=30 -- "$2/gates.zst" | "$tmp/decode" | cmp -- "$1" -
fi
sha256sum -- "$1" "$2/gates.zst"
