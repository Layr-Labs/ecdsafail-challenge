#!/usr/bin/env bash
set -euo pipefail
if [ "$#" -ne 3 ]; then echo 'Usage: bash pack-scheduled.sh TRACE SIDECAR_TSV EMPTY_OUTPUT_DIR' >&2;exit 2;fi
srcdir=$(cd -- "$(dirname -- "$0")" && pwd)
trace=$1; sidecar=$2; dest=$3
if [ -d "$dest" ] && [ -n "$(ls -A -- "$dest")" ];then echo "Output directory is not empty: $dest" >&2;exit 2;fi
mkdir -p -- "$dest"; dest=$(cd -- "$dest" && pwd)
stage=$(mktemp -d -- "$dest/.schedule-pack.XXXXXXXX");trap 'rm -rf -- "$stage"' EXIT
"${CXX:-c++}" -O3 -std=c++17 "$srcdir/schedule.cc" -o "$stage/schedule"
"${CXX:-c++}" -O3 -std=c++17 "$srcdir/encode.cc" -o "$stage/encode"
"$stage/schedule" "$trace" "$sidecar" "$stage/plan" "$stage/report" |
    "$stage/encode" "$stage/literals" |
    "${ZSTD:-zstd}" -q -T"${GIR_THREADS:-1}" -"${GIR_LEVEL:-15}" --long="${GIR_WINDOW:-27}" -f -o "$stage/gates.zst"
"${ZSTD:-zstd}" -q -15 -f "$stage/plan" -o "$stage/schedule.zst"
cat "$stage/report" >&2
awk '$1=="total"{print $2}' "$stage/report" > "$stage/gate_count.rs"
sed '/^pub fn build()/,$d' "$srcdir/mod.rs" > "$stage/mod.rs"
cat "$srcdir/scheduled-build.rs.in" >> "$stage/mod.rs"
cp "$srcdir/decoder.rs" "$srcdir/schedule.rs" "$stage/"
for f in decoder.rs schedule.rs mod.rs gate_count.rs gates.zst schedule.zst;do mv -- "$stage/$f" "$dest/$f";done
(cd -- "$dest" && wc -c gates.zst schedule.zst && sha256sum decoder.rs mod.rs schedule.rs gate_count.rs gates.zst schedule.zst)
