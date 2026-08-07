#!/usr/bin/env python3
"""Measure whole-dialog rank bounds and the implemented terminal-suffix codec.

The production walk is deterministic on an input field element.  Therefore a
complete dialog uniquely identifies that input when the initial modulus is
fixed, giving an exact 256-bit whole-dialog rank bound.  The executable probe
also enumerates the terminal reverse tree at every tractable depth and measures
the existing 32-word tail codec on a deterministic uniform field sample.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
import re
import time
from pathlib import Path
from typing import Any

RESEARCH_DIR = Path(__file__).resolve().parent
REPO_ROOT = RESEARCH_DIR.parents[3]
GCD_SOURCE = REPO_ROOT / "src/point_add/trailmix_ludicrous/gcd.rs"
CODEC_SOURCE = REPO_ROOT / "src/point_add/trailmix_ludicrous/codec.rs"
SCHEDULE_SOURCE = REPO_ROOT / "src/point_add/trailmix_ludicrous/schedule.rs"
DEFAULT_OUTPUT = REPO_ROOT / ".autoresearch/measurements/y3-global-codec-v1/report.json"
FIELD_MODULUS = (1 << 256) - (1 << 32) - 977
FIXED_SEED = 0x5933C0DEC
FULL_VERIFIER_WALKS = 2 * 9_024


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while chunk := source.read(1 << 20):
            digest.update(chunk)
    return digest.hexdigest()


def parse_schedule() -> tuple[int, list[int]]:
    source = SCHEDULE_SOURCE.read_text(encoding="utf-8")
    iters_match = re.search(r"pub const ITERS: usize = (\d+);", source)
    schedule_match = re.search(r"SCHED_J2:.*?= &\[(.*?)\];", source, re.DOTALL)
    if iters_match is None or schedule_match is None:
        raise ValueError("could not parse production GCD schedule")
    iters = int(iters_match.group(1))
    schedule = [int(value) for value in schedule_match.group(1).split(",") if value.strip()]
    if len(schedule) != iters:
        raise ValueError(f"ITERS={iters}, but SCHED_J2 has {len(schedule)} entries")
    return iters, schedule


def parse_tail4_decoder() -> tuple[int, list[int], list[list[int]]]:
    source = CODEC_SOURCE.read_text(encoding="utf-8")
    bits_match = re.search(r"TAIL4_TOP32_CODE_BITS: usize = (\d+);", source)
    decoder_match = re.search(
        r"TAIL4_TOP32_DECODER_ANF: \[&\[u16\]; 12\] = \[(.*?)\n\];",
        source,
        re.DOTALL,
    )
    reorder_match = re.search(
        r"fn tail4_reordered_raw\(.*?\{.*?\[\s*(.*?)\s*\]\s*\}",
        source,
        re.DOTALL,
    )
    if bits_match is None or decoder_match is None or reorder_match is None:
        raise ValueError("could not parse the implemented tail4 decoder")
    terms = [
        [int(value) for value in body.split(",") if value.strip()]
        for body in re.findall(r"&\[(.*?)\]", decoder_match.group(1), re.DOTALL)
    ]
    reorder = [int(value) for value in re.findall(r"raw\[(\d+)\]", reorder_match.group(1))]
    if len(terms) != 12 or len(reorder) != 12 or sorted(reorder) != list(range(12)):
        raise ValueError("tail4 decoder shape changed")
    return int(bits_match.group(1)), reorder, terms


def decode_tail4_support() -> set[tuple[tuple[int, int, int], ...]]:
    code_bits, reorder, decoder_terms = parse_tail4_decoder()
    support: set[tuple[tuple[int, int, int], ...]] = set()
    for code in range(1 << code_bits):
        reordered_raw = []
        for terms in decoder_terms:
            value = 0
            for mask in terms:
                if code & mask == mask:
                    value ^= 1
            reordered_raw.append(value)
        raw = [0] * 12
        for wire_index, raw_index in enumerate(reorder):
            raw[raw_index] = reordered_raw[wire_index]
        support.add(tuple(tuple(raw[index : index + 3]) for index in range(0, 12, 3)))
    if len(support) != 1 << code_bits:
        raise ValueError("tail4 decoder is not injective on code words")
    return support


def current_tape_bits(iters: int, tail4: bool) -> int:
    tail_symbols = 5 if tail4 and iters >= 6 else 0
    codec_symbols = iters - 1 - tail_symbols
    triples = iters // 3
    while 3 * triples > codec_symbols:
        triples -= 1
    remainder = codec_symbols - 3 * triples
    bits = 2 + 7 * triples
    if remainder == 3 and triples > 0:
        bits += 7
    else:
        bits += 5 * (remainder // 2) + 3 * (remainder % 2)
    if tail_symbols:
        bits += 8
    return bits


def run_walk(value: int, schedule: list[int]) -> tuple[list[tuple[int, int, int]], str]:
    u = FIELD_MODULUS
    v = value
    dialog: list[tuple[int, int, int]] = []
    for index, width in enumerate(schedule):
        if u.bit_length() > width or v.bit_length() > width:
            return dialog, "schedule-overflow"
        if index == 0:
            first_shift = int(v & 1 == 0)
            if first_shift:
                v >>= 1
        else:
            v >>= 1
        second_shift = int(v & 1 == 0)
        if second_shift:
            v >>= 1
        subtract = v & 1
        swap = 0
        if subtract:
            swap = int(index == 0 or v < u)
            if swap:
                u, v = v, u
            v -= u
        dialog.append((subtract, swap, second_shift))
    return dialog, "terminal" if (u, v) == (1, 0) else "nonterminal"


def reverse_predecessors(
    state: tuple[int, int], width: int
) -> list[tuple[tuple[int, int], tuple[int, int, int]]]:
    u, v = state
    limit = 1 << width
    candidates = [
        ((u, 4 * v), (0, 0, 1)),
        ((u, 2 * (u + v)), (1, 0, 0)),
        ((u, 4 * (u + v)), (1, 0, 1)),
    ]
    if v > 0:
        candidates.extend(
            [
                ((u + v, 2 * u), (1, 1, 0)),
                ((u + v, 4 * u), (1, 1, 1)),
            ]
        )
    return [(prior, symbol) for prior, symbol in candidates if max(prior) < limit]


def enumerate_terminal_tree(schedule: list[int], state_cap: int) -> list[dict[str, Any]]:
    states = {(1, 0)}
    rows = []
    for depth, index in enumerate(range(len(schedule) - 1, 0, -1), start=1):
        next_states = {
            prior
            for state in states
            for prior, _ in reverse_predecessors(state, schedule[index])
        }
        unrestricted = (pow(5, depth) + 1) // 2
        rows.append(
            {
                "depth": depth,
                "start_iteration": index,
                "width": schedule[index],
                "reachable_states": len(next_states),
                "unrestricted_states": unrestricted,
                "rank_bits": max(1, (len(next_states) - 1).bit_length()),
            }
        )
        states = next_states
        if len(states) > state_cap:
            break
    return rows


def wilson_interval(successes: int, trials: int) -> tuple[float, float]:
    if trials == 0:
        return 0.0, 1.0
    z = 1.959963984540054
    probability = successes / trials
    denominator = 1 + z * z / trials
    centre = (probability + z * z / (2 * trials)) / denominator
    radius = z * math.sqrt(probability * (1 - probability) / trials + z * z / (4 * trials * trials)) / denominator
    return max(0.0, centre - radius), min(1.0, centre + radius)


def run(args: argparse.Namespace) -> dict[str, Any]:
    started = time.monotonic()
    iters, schedule = parse_schedule()
    tail4_support = decode_tail4_support()
    rng = random.Random(args.seed)
    suffix_counts: dict[int, dict[tuple[tuple[int, int, int], ...], int]] = {
        depth: {} for depth in range(1, args.max_suffix + 1)
    }
    outcomes = {"terminal": 0, "schedule-overflow": 0, "nonterminal": 0}
    tail4_misses = 0
    for _ in range(args.samples):
        dialog, outcome = run_walk(rng.randrange(1, FIELD_MODULUS), schedule)
        outcomes[outcome] += 1
        if outcome != "terminal":
            continue
        for depth, counts in suffix_counts.items():
            suffix = tuple(dialog[-depth:])
            counts[suffix] = counts.get(suffix, 0) + 1
        if tuple(dialog[-4:]) not in tail4_support:
            tail4_misses += 1

    terminal_samples = outcomes["terminal"]
    miss_lo, miss_hi = wilson_interval(tail4_misses, terminal_samples)
    miss_rate = tail4_misses / terminal_samples if terminal_samples else 1.0
    clean_seed_estimate = (1.0 - miss_rate) ** FULL_VERIFIER_WALKS
    current_bits = current_tape_bits(iters, tail4=False)
    tail4_bits = current_tape_bits(iters, tail4=True)
    full_dialog_count = FIELD_MODULUS - 1
    report = {
        "schema_version": 1,
        "verdict": "green" if current_bits - tail4_bits > 2 else "red",
        "scope": "Y3 whole-dialog rank bound plus production terminal-suffix probe",
        "production": {
            "iters": iters,
            "schedule_entries": len(schedule),
            "schedule_tail": schedule[-12:],
            "field_modulus_hex": hex(FIELD_MODULUS),
            "current_tape_bits": current_bits,
            "tail4_tape_bits": tail4_bits,
            "tail4_qubits_saved": current_bits - tail4_bits,
        },
        "exact_whole_dialog_bound": {
            "domain_elements": full_dialog_count,
            "rank_bits": (full_dialog_count - 1).bit_length(),
            "current_representation_bits": current_bits,
            "information_slack_qubits": current_bits - (full_dialog_count - 1).bit_length(),
            "proof": "With fixed initial u=p, the deterministic dialog plus terminal state reverses to exactly one input x; all x in 1..p-1 therefore give p-1 distinct complete dialogs in the exact walk.",
            "scope_warning": "The production circuit deliberately truncates a small-probability tail, so this is an exact-algorithm information bound, not a proof that a cheap streaming ranker exists for the approximate verifier circuit.",
        },
        "terminal_tree": enumerate_terminal_tree(schedule, args.state_cap),
        "monte_carlo": {
            "seed": args.seed,
            "requested_samples": args.samples,
            "outcomes": outcomes,
            "conditional_terminal_samples": terminal_samples,
            "tail4_decoder_words": len(tail4_support),
            "tail4_support_misses": tail4_misses,
            "tail4_support_miss_rate": miss_rate,
            "tail4_support_miss_rate_wilson95": [miss_lo, miss_hi],
            "estimated_clean_seed_probability_for_18048_walks": clean_seed_estimate,
            "suffixes": [
                {
                    "depth": depth,
                    "observed_distinct": len(counts),
                    "rank_bits": max(1, (len(counts) - 1).bit_length()),
                    "most_frequent": [
                        {"symbols": [list(symbol) for symbol in suffix], "count": count}
                        for suffix, count in sorted(counts.items(), key=lambda item: (-item[1], item[0]))[:8]
                    ],
                }
                for depth, counts in suffix_counts.items()
            ],
            "evidence_class": "deterministic Monte Carlo; ranking evidence only",
        },
        "rank_unrank_price": {
            "naive_endpoint_construction": "Run the existing reverse walk to map tape->x, copy x, then regenerate the tape before the apply traversal.",
            "naive_endpoint_peak_reduction_qubits": 0,
            "naive_endpoint_reason": "The apply traversal still requires the full tape beside the 256-bit coefficient register; regenerating it restores the binding live set and adds two GCD traversals.",
            "global_streaming_ranker_status": "unimplemented-and-unpriced",
            "bounded_tail4_status": "implemented reversible 12-to-5 payload codec; build-time artifact measurement must price its actual gate delta",
            "decision": "Measure tail4 as the only concrete >2-qubit Y3 operator; do not implement the 256-bit global rank bound without a streaming apply construction.",
        },
        "source_hashes": {
            str(path.relative_to(REPO_ROOT)): sha256_file(path)
            for path in (GCD_SOURCE, CODEC_SOURCE, SCHEDULE_SOURCE)
        },
        "wall_seconds": time.monotonic() - started,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--samples", type=int, default=1_000_000)
    parser.add_argument("--seed", type=int, default=FIXED_SEED)
    parser.add_argument("--max-suffix", type=int, default=12)
    parser.add_argument("--state-cap", type=int, default=1_000_000)
    args = parser.parse_args()
    if args.samples <= 0 or args.max_suffix < 4 or args.state_cap <= 0:
        parser.error("samples/state-cap must be positive and max-suffix must be at least four")
    report = run(args)
    print(json.dumps(report, sort_keys=True))
    return 0 if report["verdict"] == "green" else 1


if __name__ == "__main__":
    raise SystemExit(main())
