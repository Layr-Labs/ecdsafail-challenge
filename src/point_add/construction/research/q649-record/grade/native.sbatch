#!/bin/bash -l
#SBATCH --job-name=q649-private-native
#SBATCH --account=plgccaiautore2026-cpu
#SBATCH --partition=plgrid
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --time=00:40:00
#SBATCH --export=ALL
#SBATCH --output=native-%j.log
set -euo pipefail
umask 077
cd "$SLURM_SUBMIT_DIR"
sha256sum --quiet -c SOURCE-SHA256
module load GCCcore/15.2.0 nodejs/24.16.0
entry=research/q649-record/circuit.cjs
mkdir "native-$SLURM_JOB_ID"
out="$PWD/native-$SLURM_JOB_ID"
node "$entry" scheduled "$out/trace.u16le" "$out/ranges.tsv" >"$out/native.partial" &
emitter=$!
node "$entry" check forward 96 >"$out/forward.partial" &
forward=$!
node "$entry" check reverse 96 >"$out/reverse.partial" &
reverse=$!
wait "$emitter"
mv "$out/native.partial" "$out/native.json"
wait "$forward"
mv "$out/forward.partial" "$out/forward.json"
wait "$reverse"
mv "$out/reverse.partial" "$out/reverse.json"
python3 - "$out" <<'PY'
import hashlib,json,sys
from pathlib import Path
p=Path(sys.argv[1])
native=json.loads((p/'native.json').read_bytes())
assert native['width']==649 and native['spans']>0
assert (p/'trace.u16le').stat().st_size==8*native['ops']
for direction in ('forward','reverse'):
    r=json.loads((p/(direction+'.json')).read_bytes())
    assert r['width']==649 and r['points']==96
    assert r['shortForwardOracles']==r['shortInverseOracles']==r['historyOracles']==0
    if direction=='forward':
        assert r['ccx']==native['counts'][13] and r['hmr']==native['counts'][12]
    print(direction,r['expectedT'],r['ccx'],flush=True)
h=hashlib.sha256()
with (p/'trace.u16le').open('rb') as src:
    for block in iter(lambda:src.read(8<<20),b''):h.update(block)
assert h.hexdigest()==native['traceSha256']
print('Verified native source trace',native['ops'],native['traceSha256'])
PY
