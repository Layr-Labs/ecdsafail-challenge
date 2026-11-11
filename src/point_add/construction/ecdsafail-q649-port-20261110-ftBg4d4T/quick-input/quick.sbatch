#!/bin/bash -l
#SBATCH --job-name=q649-index
#SBATCH --account=plgccaiautore2026-cpu
#SBATCH --partition=plgrid
#SBATCH --ntasks=1
#SBATCH --export=ALL
#SBATCH --cpus-per-task=1
#SBATCH --mem=6G
#SBATCH --time=02:30:00
#SBATCH --output=quick-%A-%a.log
set -euo pipefail
umask 077
cd "$SLURM_SUBMIT_DIR"
sha256sum --quiet -c INPUT-SHA256
module load GCCcore/15.2.0 nodejs/24.16.0
id=$SLURM_ARRAY_TASK_ID
owner=construction/research/agents/midpoint-implicit-query-20261109/q651-ten-field
node port/check-window.cjs "$owner" > "window-$id.json"
variant=arith-code-rotate-digit-codetrans-prefix-crop-host-fast
case "$id" in
    0) mode=forward ;;
    1) variant+=-lease-leaseadd-f1-audit; mode=upperforward ;;
    2) variant+=-lease-leaseadd-f1-audit; mode=upperreverse ;;
    3) variant+=-lease-leaseadd-f1-virtualtop-physical; mode=count ;;
    4) variant+=-lease-leaseadd-f1-virtualtop; mode=forward ;;
    *) exit 2 ;;
esac
node port/price.cjs construction compiler "$variant" "$mode" fixtures/openssl-384.json 32 > "$id.partial"
mv "$id.partial" "$id.json"
sha256sum "$id.json" > "$id.sha256"
