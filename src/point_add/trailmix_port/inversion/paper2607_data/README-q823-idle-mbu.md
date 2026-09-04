# Q823 idle-R-MBU source reproduction

Attribution: gpt-5.

This package reproduces the candidate's 1,616 real Qiskit EEA steps. It makes
six source-call substitutions in the Q823 fused-R block, replacing borrowed
four-CCX cells with existing clean-helper measurement-uncompute markers. It
does not delete sampled gates or add workspace. It is source reproduction,
not a claim of whole-point-add correctness, canonical score, or acceptance.

The authenticated baseline source commit is
`5d3dedcda8a86e39b68b64e14cc12631d37b7045`. Its canonical generator path is
`src/point_add/trailmix_port/inversion/paper2607_data/eea_circuit_s835_exactwidth_dirty12.py`.
All local source filenames and exact hashes are listed in `source_manifest.json`.
The two support modules are supplied dependency sources that were absent from
that baseline tree. The existing upstream license is included unchanged.

## Generate

Use Python 3.11 and a dedicated environment:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
.venv/bin/python -B reproduce_q823_idle_mbu.py --output generated --workers 4
```

The output directory must not exist. The default produces 36 shards: 35 ranges
of 45 steps and a final range of 41. Failed or partial output is preserved and
never reused automatically. Each worker has a 512 MiB address-space limit and
a 180-second per-shard wall-clock limit; one to four workers are supported.
Source hashes and dependency versions are checked before and after generation.
All production LRU caches are cleared and checked empty after every step.

A bounded reproduction target is:

```sh
.venv/bin/python -B reproduce_q823_idle_mbu.py --output smoke-0226-0270 --start 226 --end 270 --workers 1
```

Its expected compressed shard SHA256 is
`f66d2ec71e8007b5215d555d8d90ddff2f1207d941e95710a6762580c4f4beb9`,
and its raw record-payload SHA256 is
`38fd42e880cb9d52eaa5d1b3b3a450d0fff1ddd423e5b2bca7bd1bac824e9a4d`.
Expected counts are 2,157,492 records and 1,173,316 raw lowered CCX. These are
reproduction targets, not a claim that a reader has already reproduced them.

The original `generate_eea_blob.py` is imported unchanged for recursive
flattening and eight-byte record packing. The wrapper builds the canonical
source under module label `q823_mbu_generation_source`, matching stream metadata.
Compressed and raw bytes should match independently generated candidate
streams; timing, source-manifest, and generator hashes in metadata truthfully
describe this wrapper and will differ from other generation wrappers.

## ABI and evidence boundary

Each shard starts with `P26EEA2\0`, then four little-endian 32-bit integers:
field width 256, local references 577, first step, last step. Each record is a
little-endian 64-bit word: four kind bits, four arity bits, then up to five
10-bit operand indices. Unused high bits are zero. The local ABI comprises 567
owned references and 10 borrowed dirty references; it is not the whole-circuit
Q count. Kind 7 is a clean-C3X MBU marker, lowered to two CCX, one HMR, and one
conditional CZ. Counting it as one Toffoli is incorrect.

The active Rust embedding directory is `paper2607_exactwidth_data`, not the
older `paper2607_data` shard directory. This wrapper only writes a fresh output
directory; it does not modify a solver, call a benchmark, submit anything, or
use credentials. Its aggregate explicitly records that full 9,024-shot
validation and Rust builder reduction have not run.

The window certificate here is the exact LF-normalized byte sequence expected
by the generator's embedded hash. The candidate source retains its original
CRLF bytes. Do not normalize either file incidentally. Proof or simulator
modules are not required to reproduce the primitive stream and are not
dependencies of this package.
