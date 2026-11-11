#!/usr/bin/env bash
# Exact windowed pair-cancellation peephole (tpeep.c), repeated until a pass removes nothing.
# Usage: bash tpeep-fixpoint.sh TRACE SIDECAR_TSV OUT_TRACE OUT_TSV [W=4096]
# Run after `node q650/point.cjs raw|spans` and before pack-scheduled.sh / verify.sh (both take OUT_TRACE, OUT_TSV).
set -euo pipefail
if [ "$#" -lt 4 ]; then echo 'Usage: bash tpeep-fixpoint.sh TRACE SIDECAR_TSV OUT_TRACE OUT_TSV [W]' >&2; exit 2; fi
srcdir=$(cd -- "$(dirname -- "$0")" && pwd)
in=$1; tsv=$2; out=$3; otsv=$4; W=${5:-4096}
tmp=$(mktemp -d "$(dirname -- "$out")/.tpeep.XXXXXXXX"); trap 'rm -rf -- "$tmp"' EXIT
"${CC:-cc}" -O2 -o "$tmp/tpeep" "$srcdir/tpeep.c"
cur=$in; curt=$tsv; n=0
while :; do
  n=$((n+1)); nxt="$tmp/p$n.u16le"; nxtt="$tmp/p$n.tsv"
  "$tmp/tpeep" "$cur" "$curt" "$nxt" "$nxtt" "$W" 2> "$tmp/log"
  cat "$tmp/log" >&2
  [ "$cur" != "$in" ] && rm -f -- "$cur" "$curt"
  cur=$nxt; curt=$nxtt
  grep -q ' removed 0 ' "$tmp/log" && break
  [ "$n" -ge 16 ] && { echo 'tpeep: no fixed point after 16 passes' >&2; exit 1; }
done
mv -- "$cur" "$out"; mv -- "$curt" "$otsv"
echo "tpeep-fixpoint: $n passes" >&2
