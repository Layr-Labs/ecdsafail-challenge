# Test-only TAIL_NONCE grinder

Implementation: `measurement/nonce_grinder.rs`, a child of the existing
`#[cfg(test)]` E1/E2 laboratory. No harness, manifest, dependency, production
configuration, or scored artifact is changed. These commands run **tests** in
the existing build binary, never its artifact-writing `main`.

## Exact acceptance, not a walk approximation

The current builder is called once per process. Its complete operation stream
is held read-only, with a private 96-operation replacement tail per candidate.
The tail must be 48 unconditional `X;X` pairs on q0/q1, outside every condition
stack. Only the low 48 nonce bits exist; ranges outside `[0, 2^48)` are rejected.
The nonce selects the target of each pair, never the circuit's mathematical
function. Setting `TAIL_NONCE` in the environment does **not** override the
production builder's pinned configuration.

SHAKE256 absorbs the harness's domain `quantum_ecc-fiat-shamir-v2`, the LE u64
operation count, and each operation's one-byte kind plus six LE u64 operands.
This is **not** the 56-byte on-disk framing. The hash state immediately before
the tail is cached and cloned for each nonce. The printed `baseline_xof32`
fingerprints the source-built stream, including its original nonce.

The harness attempts exactly **9,024** scalar pairs, each two 32-byte
little-endian integers. Infinity and equal-x inputs are skipped, not replaced;
thus accepted shots can theoretically be fewer than 9,024. Accepted inputs are
packed contiguously into batches of 64, normally **141 batches**.

For speed, the grinder:

1. Precomputes 32 tables of 256 generator multiples. Scalar multiplication uses
   at most 32 calls to the **original reference `curve.add`**, rather than
   roughly 384 calls in `curve.mul`. There is no new field implementation.
2. Clones the candidate XOF. One clone generates scalar pairs lazily; the other
   skips **all** `64 × attempted_shots` bytes before any simulation. This is
   essential: every R/Hmr random byte must match the harness even when later
   points have not yet been computed.
3. Runs the unchanged trusted `Simulator::apply_iter` and reuses E1's exact
   classical/phase/ancilla checks. It rejects only after an actual failing
   batch. No speculative walk prefilter can discard a genuinely passing nonce.
4. Distributes independent nonces across `std::thread` workers, sharing one
   immutable op allocation and the precomputed table.
5. Rechecks every apparent pass using E1's original `sample_points`
   (`curve.mul`), all batches, the trusted simulator, and literal evaluator
   cleanup checks. It asserts agreement on failures, checked shots, Toffoli/
   Clifford totals and final RNG position before printing `GRIND_PASS`.

This reproduces the **implemented** evaluator. It does not invent the
forward/reverse check or deterministic dirty-free assertion described in the
README but absent from this checkout's evaluator. There is no `src/main.rs`;
the actual trusted entry point is `src/bin/eval_circuit.rs`.

## Commands

Run the fast regression suite:

```sh
cargo test --release --bin build_circuit point_add::measurement:: -- --nocapture
```

Full positive/negative baseline cross-check, including byte-for-byte comparison
against the existing compressed artifact opened read-only:

```sh
GRIND_VERIFY_OPS=ops.bin cargo test --release --bin build_circuit \
  point_add::measurement::nonce_grinder::baseline_parity \
  -- --ignored --exact --nocapture
```

This last test requires that the source-built circuit's pinned nonce already
passes. Do not use it as a prerequisite for a newly modified, unground circuit.

Deliberately seeded rediscovery of the known baseline nonce:

```sh
GRIND_START=7978488 GRIND_END=7978496 GRIND_VERIFY_OPS=ops.bin \
  cargo test --release --bin build_circuit \
  point_add::measurement::nonce_grinder::search \
  -- --ignored --exact --nocapture
```

Independent throughput benchmark (all full-size candidate sets, early
rejections allowed):

```sh
GRIND_START=0 GRIND_END=128 GRIND_STOP_ON_PASS=0 \
  cargo test --release --bin build_circuit \
  point_add::measurement::nonce_grinder::search \
  -- --ignored --exact --nocapture
```

Search a **newly modified source-built stream**, without changing the grinder:

```sh
GRIND_START=0 GRIND_END=281474976710656 \
  cargo test --release --bin build_circuit \
  point_add::measurement::nonce_grinder::search \
  -- --ignored --exact --nocapture
```

Do not set `GRIND_VERIFY_OPS=ops.bin` for changed source unless that artifact
is intentionally expected to match. The grinder never reads `ops.bin` unless
this optional comparison is requested; it does not accidentally grind a stale
artifact. Recompile/restart after changes: a running process is an immutable
snapshot and does not watch source or automatically change streams.

### Configuration

| Environment variable | Default | Meaning |
|---|---:|---|
| `GRIND_START` | 0 | Inclusive nonce start |
| `GRIND_END` | 281474976710656 | Exclusive end; at most `2^48` |
| `GRIND_THREADS` | `available_parallelism()` | Positive worker count, at most available CPUs |
| `GRIND_SHOTS` | 9024 | Attempted scalar pairs, 1–9024; smaller runs are explicitly not harness-sized |
| `GRIND_STOP_ON_PASS` | 1 | 1 stops after a certified pass; 0 keeps searching |
| `GRIND_SECONDS` | 0 | Search wall-time budget; 0 is unlimited; in-flight candidates finish |
| `GRIND_LOG_SECONDS` | 10 | Positive progress-log interval |
| `GRIND_VERIFY_OPS` | unset | Optional read-only full stream comparison |

`GRIND_READY` logs setup time separately. Search throughput uses completed
candidate decisions divided by search elapsed time, **not** 9,024-shot full
evaluations per second. Early-rejected candidates typically simulate much
less than the full set. `checked_shots`/`batches` expose the actual work.
Finalist certification is included in search timing. A `search` test finishing
successfully does not mean it found a pass: inspect `GRIND_PASS` and
`GRIND_DONE passes=...`.

`next_nonce` is an assignment cursor, **not a safe crash-resume checkpoint**:
up to the worker count of earlier candidates can still be in flight. A clean
`GRIND_DONE` after a finite/time-limited run has no in-flight work; an interrupted
run should restart its original range if complete coverage matters.

## Persistent execution and redirection

Use a genuinely detached process only when the owner requests persistence.
The agent's detached Bash tool is suitable; ordinary session-attached async
execution is not enough. The active process's actual PID, snapshot executable,
log path and measurements are recorded in
`.squad/decisions/inbox/rust-eng-nonce-grinder.md`.

For manual builds, capture Cargo's executable path without relying on its hash:

```sh
cargo test --release --bin build_circuit --no-run --message-format=json \
  > target/nonce-grinder-build.jsonl
python3 - <<'PY'
import json
import shutil
from pathlib import Path
for line in Path("target/nonce-grinder-build.jsonl").read_text().splitlines():
    record = json.loads(line)
    if (record.get("reason") == "compiler-artifact"
            and record.get("target", {}).get("name") == "build_circuit"
            and record.get("profile", {}).get("test")
            and record.get("executable")):
        shutil.copy2(record["executable"], "target/nonce-grinder")
        break
else:
    raise SystemExit("test executable not found")
PY
```

Stop the **specific recorded PID** before replacing the snapshot executable or
redirecting it. Rebuild against the modified source, then launch that snapshot
with the same exact test selector and desired `GRIND_*` range. Findings are
printed to the log only: the tool never applies a found nonce to `mod.rs`,
writes `ops.bin`, scores, submits, or commits anything.

Nonce grinding is an owner-requested research workflow under the team's
accepted statistical-correctness regime. A ground pass is not evidence of a
lower fresh-input failure probability and is not a challenge-policy sign-off.
