#!/bin/bash -l
#SBATCH --job-name=q649-port
#SBATCH --account=plgccaiautore2026-cpu
#SBATCH --partition=plgrid
#SBATCH --ntasks=1
#SBATCH --export=ALL
#SBATCH --cpus-per-task=1
#SBATCH --mem=6G
#SBATCH --time=02:30:00
#SBATCH --output=price-%A-%a.log
set -euo pipefail
umask 077
cd "$SLURM_SUBMIT_DIR"
sha256sum --quiet -c INPUT-SHA256
module load GCCcore/15.2.0 nodejs/24.16.0
id=$SLURM_ARRAY_TASK_ID
variant=arith-code-rotate-digit
mode=forward
case "$id" in
    0) ;;
    1) mode=reverse ;;
    2) variant+=-physical ;;
    3) variant+=-physical; mode=reverse ;;
    4) variant+=-physical; mode=count ;;
    5) mode=count ;;
    6) variant+=-virtualtop-physical; mode=count ;;
    7) variant+=-virtualtop-physical ;;
    *) exit 2 ;;
esac
node port/price.cjs construction compiler "$variant" "$mode" fixtures/openssl-384.json 32 > "$id.partial"
mv "$id.partial" "$id.json"
sha256sum "$id.json" > "$id.sha256"
