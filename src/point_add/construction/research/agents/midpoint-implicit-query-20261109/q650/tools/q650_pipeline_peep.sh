#!/usr/bin/env bash
# q650 end-to-end pipeline (+ optional PEEP=1 exact peephole after generation, papers): generator -> sha -> pack -> codec verify -> ops.bin -> fasteval (9024 shots).
# Usage: bash q650_pipeline.sh WORKTREE OUTDIR [ENTRY]
#   WORKTREE  repo root (e.g. /Users/akashbalasubramani/Desktop/ecdsafail-650mul)
#   OUTDIR    empty/new dir for trace (14.7 GB), ranges, rebuilt/, ops.bin (~4.2 GB), logs
#   ENTRY     generator entry relative to WORKTREE/src/point_add/construction (default q651/point.cjs)
# Env: INSTALL=1  copy rebuilt gates.zst/schedule.zst/gate_count.rs + TRACE-SHA256 into WORKTREE/src/point_add
#                 and cargo build the harness binaries (does NOT commit).
#      SKIP_VERIFY=1 skip the codec round trip (iteration only; ~13 min saved; never for a candidate).
#      KEEP_TRACE=0 delete trace.u16le at the end (default keep).
#      FE_THREADS (default 4). Never runs more than 2 heavy jobs at once.
set -euo pipefail
[ "$#" -ge 2 ] || { sed -n 2,11p "$0"; exit 2; }
tools="/private/tmp/claude-501/-Users-akashbalasubramani-Desktop-ecdsafail/a4ae7645-ba90-472e-b4df-919aabeea298/scratchpad/q650tools"
wt=$(cd -- "$1" && pwd); out=$2; entry=${3:-q651/point.cjs}
con="$wt/src/point_add/construction"
fasteval=/Users/akashbalasubramani/Desktop/fasteval/target/release/fasteval
t2o="$tools/trace2ops/target/release/trace2ops"
mkdir -p "$out"; out=$(cd -- "$out" && pwd)
[ -e "$out/trace.u16le" ] && { echo "OUTDIR already has a trace: $out" >&2; exit 2; }
log() { echo "[$(date +%H:%M:%S)] $*" | tee -a "$out/pipeline.log"; }
T() { local s=$SECONDS; "$@"; log "  ($(( SECONDS - s ))s) $*"; }

# trace2ops mapping must equal this worktree's committed record->Op mapping
awk '/^fn optional_bit/{p=1} p{print} p&&/^fn operation/{q=1} q&&/^}$/{exit}' "$wt/src/point_add/mod.rs" > "$out/.opmap"
sed -n '2,$p' "$tools/trace2ops/src/opmap.rs" | sed '$d' | cmp -s - "$out/.opmap" \
  || { echo "record->Op mapping in $wt/src/point_add/mod.rs differs from trace2ops; rebuild with trace2ops/gen.sh" >&2; exit 3; }

log "worktree $wt @ $(git -C "$wt" rev-parse --short HEAD) $(git -C "$wt" status --porcelain | wc -l | tr -d ' ') dirty paths; entry $entry"
log "1/6 generate raw + spans (parallel)"
s=$SECONDS
(cd "$con" && node "$entry" raw "$out/trace.u16le" > "$out/raw.json" 2> "$out/raw.err") & p1=$!
(cd "$con" && node "$entry" spans "$out/ranges.tsv" > "$out/spans.json" 2> "$out/spans.err") & p2=$!
wait $p1 || { log "raw generation FAILED"; tail "$out/raw.err"; exit 1; }
wait $p2 || { log "spans generation FAILED"; tail "$out/spans.err"; exit 1; }
log "  ($(( SECONDS - s ))s) generator"
ops=$(node -e 'console.log(JSON.parse(require("fs").readFileSync(process.argv[1])).ops)' "$out/raw.json")
width=$(node -e 'console.log(JSON.parse(require("fs").readFileSync(process.argv[1])).width)' "$out/raw.json")
log "  generator: ops=$ops width=$width"
if [ "$ops" -gt 2100000000 ]; then log "  !! ops > 2.1e9: likely OOM on the 128 GB grader (56 B/op resident)";
elif [ "$ops" -gt 1900000000 ]; then log "  ! ops > 1.9e9 self-imposed margin (56*ops = $(( ops*56/1000000000 )) GB resident on a 128 GB runner)"; fi

if [ "${PEEP:-0}" = 1 ]; then
  here=$(cd -- "$(dirname -- "$0")" && pwd); tpeep=${TPEEP:-$out/tpeep}
  [ -x "$tpeep" ] || cc -O2 -o "$tpeep" "$here/tpeep.c" || { log "tpeep build FAILED"; exit 1; }
  log "1b/6 tpeep (exact peephole, W=${PEEP_W:-4096}, passes=${PEEP_PASSES:-1})"
  s=$SECONDS
  cp "$out/ranges.tsv" "$out/ranges.orig.tsv"
  for p in $(seq 1 ${PEEP_PASSES:-1}); do
    "$tpeep" "$out/trace.u16le" "$out/ranges.tsv" "$out/trace.p.u16le" "$out/ranges.p.tsv" ${PEEP_W:-4096} 2>> "$out/tpeep.err" || { log "tpeep FAILED"; exit 1; }
    mv "$out/trace.p.u16le" "$out/trace.u16le"; mv "$out/ranges.p.tsv" "$out/ranges.tsv"
  done
  grep tpeep "$out/tpeep.err" | tee -a "$out/pipeline.log"
  ops=$(( $(stat -f %z "$out/trace.u16le") / 8 ))
  log "  ($(( SECONDS - s ))s) after tpeep: ops=$ops"
fi
log "2/6 sha256"
(cd "$out" && sha256sum trace.u16le ranges.tsv | tee "$out/TRACE-SHA256")

log "3/6 pack (schedule + encode + zstd)"
T bash -c "cd '$con' && GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh '$out/trace.u16le' '$out/ranges.tsv' '$out/rebuilt' > '$out/pack.out' 2> '$out/pack.err'"
grep -E '^total|^literal|^copied |sidecar coverage' "$out/pack.err" | tee -a "$out/pipeline.log"

log "4+5/6 codec round trip (verify.sh) || ops.bin (trace2ops)"
s=$SECONDS
if [ "${SKIP_VERIFY:-0}" = 1 ]; then echo "SKIPPED (SKIP_VERIFY=1)" > "$out/verify.out"; true & v=$!
else (cd "$con" && TMPDIR="$out" bash codec/verify.sh "$out/trace.u16le" "$out/rebuilt" > "$out/verify.out" 2>&1) & v=$!; fi
ZSTD_THREADS=3 "$t2o" "$out/trace.u16le" "$out/ops.bin" > /dev/null 2> "$out/t2o.err" & c=$!
wait $c || { log "trace2ops FAILED"; tail "$out/t2o.err"; exit 1; }
tail -1 "$out/t2o.err" | tee -a "$out/pipeline.log"
wait $v || { log "codec verify FAILED (rebuilt artifacts do not reproduce the trace)"; cat "$out/verify.out"; exit 1; }
log "  ($(( SECONDS - s ))s) verify+convert: codec round trip $(grep -q SKIPPED "$out/verify.out" && echo SKIPPED || echo OK)"

log "6/6 fasteval 9024 shots"
T bash -c "FE_THREADS=${FE_THREADS:-4} '$fasteval' '$out/ops.bin' > '$out/fe.out' 2> '$out/fe.err'"
cat "$out/fe.out" | tee -a "$out/pipeline.log"

if [ "${INSTALL:-0}" = 1 ]; then
  log "install rebuilt artifacts into $wt/src/point_add + cargo build"
  for f in gates.zst schedule.zst gate_count.rs; do cp "$out/rebuilt/$f" "$wt/src/point_add/$f"; done
  for f in mod.rs decoder.rs schedule.rs; do cmp -s "$out/rebuilt/$f" "$wt/src/point_add/$f" || { log "!! $f differs from committed codec copy"; exit 1; }; done
  cp "$out/TRACE-SHA256" "$wt/src/point_add/TRACE-SHA256"
  T bash -c "cd '$wt' && cargo build --release --locked --offline --bin build_circuit --bin eval_circuit > '$out/cargo.log' 2>&1"
fi
[ "${KEEP_TRACE:-1}" = 0 ] && rm -f "$out/trace.u16le"
grep -q 'ALL OK' "$out/fe.out" && log "PIPELINE PASS ops=$ops $(grep -o 'qubits [0-9]*' "$out/fe.out")" || { log "PIPELINE FAIL"; exit 1; }
