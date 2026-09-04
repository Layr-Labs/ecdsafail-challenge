#!/usr/bin/env python3
"""All-certified-window differential checks for the Q820 Aux8 prototype."""

from __future__ import annotations

import argparse
import gc
from pathlib import Path
import random

import verify_aux11_reductions as verify
import verify_q820_aux8 as common


def unique_windows(candidate, name, *, terminal=False):
    steps = range(4, 1617, 4) if terminal else range(1, 1617)
    return sorted(
        {
            tuple(candidate.safe_active_windows(256, step)[name])
            for step in steps
        }
    )


def clear_gate_cache(old, new, name):
    for module in (old, new):
        gate = getattr(module, name)
        if hasattr(gate, "cache_clear"):
            gate.cache_clear()
    gc.collect()


def check_r(old, new, cases):
    windows = unique_windows(new, "r_addsub")
    for index, (k, upper) in enumerate(windows, 1):
        width = upper - k + 1
        fields = [
            ("Ctrl", 1), ("Phase2", 1), ("Mode", 1), ("Sign", 1),
            ("Work1", width), ("Work2", width), ("l_t", 8), ("l_q", 9),
            ("l_s", 9), ("Dirty", 10),
        ]
        rng = random.Random(0x82010000 + k * 1024 + upper)
        values = common.random_common(fields, cases, rng)
        # The certified R gate omits cells outside [k, upper]. Its encoded
        # metadata fixes the represented dynamic interval:
        # lower=l_t+l_q+1=k and upper=259-l_s. Also, Ctrl is the folded live-R
        # predicate, so Ctrl=1 implies Mode=0. Preserve random interior work
        # words while enforcing these operational boundary conditions.
        mask = (1 << cases) - 1
        ctrl = values["Ctrl"][0] & mask
        values["Mode"] = [values["Mode"][0] & (mask ^ ctrl)]
        values["l_t"] = common.words_from_values(
            [(k - 2) % (1 << 8)] * cases, 8
        )
        values["l_q"] = common.words_from_values([511] * cases, 9)
        values["l_s"] = common.words_from_values(
            [(258 - upper) % 259] * cases, 9
        )
        common.compare_pair(
            label=f"R-{k}-{upper}",
            old_gate=old.compact_r_subrestore_fused_gate(n=256, k=k, K=upper),
            new_gate=new.compact_r_subrestore_fused_gate(n=256, k=k, K=upper),
            old_fields=fields + [("OldScratch", 8)],
            new_fields=fields + [("NewScratch", 2)],
            common_values=values,
            old_clean=["OldScratch"],
            new_clean=["NewScratch"],
            cases=cases,
        )
        clear_gate_cache(old, new, "compact_r_subrestore_fused_gate")
        if index % 20 == 0:
            print(f"PROGRESS R {index}/{len(windows)}", flush=True)
    print(f"PASS R unique_windows={len(windows)}", flush=True)


def check_lc(old, new, cases):
    windows = unique_windows(new, "swap")
    for index, (k, upper) in enumerate(windows, 1):
        width = upper - k + 1
        fields = [
            ("Ctrl", 1), ("Direction", 1), ("Sign", 1),
            ("Work1", width + 1), ("l_t", 8), ("l_q", 9),
            ("Dirty0", 1),
        ]
        rng = random.Random(0x82020000 + k * 1024 + upper)
        common.compare_pair(
            label=f"LC-{k}-{upper}",
            old_gate=old.compact_lc_swap_gate(k=k, K=upper),
            new_gate=new.compact_lc_swap_gate(k=k, K=upper),
            old_fields=fields + [("OldScratch", 9)],
            new_fields=fields + [("DirtyExtra", 3), ("NewScratch", 8)],
            common_values=common.random_common(fields, cases, rng),
            old_clean=["OldScratch"],
            new_clean=["NewScratch"],
            new_dirty=["DirtyExtra"],
            cases=cases,
        )
        clear_gate_cache(old, new, "compact_lc_swap_gate")
        if index % 20 == 0:
            print(f"PROGRESS LC {index}/{len(windows)}", flush=True)
    print(f"PASS LC unique_windows={len(windows)}", flush=True)


def check_tsub(old, new, cases):
    windows = unique_windows(new, "t_addsub")
    for index, (k, upper) in enumerate(windows, 1):
        width = upper - k + 1
        fields = [
            ("Ctrl", 1), ("Sign", 1), ("Work1", width),
            ("Work2", width), ("l_t", 8), ("Borrowed0", 1),
        ]
        old_gate = old.compact_prefix_addsub_gate(
            k=k, K=upper, mode="sub", sign_update=False,
            capture_borrow_sign=False, target="work2", name="OLD_TSUB",
        )
        new_gate = new.compact_prefix_addsub_gate(
            k=k, K=upper, mode="sub", sign_update=False,
            capture_borrow_sign=False, target="work2", name="NEW_TSUB",
        )
        base = sum(width for _, width in fields)
        old_scratch = old_gate.num_qubits - base
        new_scratch = new_gate.num_qubits - base - 1
        rng = random.Random(0x82030000 + k * 1024 + upper)
        common.compare_pair(
            label=f"Tsub-{k}-{upper}",
            old_gate=old_gate,
            new_gate=new_gate,
            old_fields=fields + [("OldScratch", old_scratch)],
            new_fields=fields
            + [("BorrowedExtra", 1), ("NewScratch", new_scratch)],
            common_values=common.random_common(fields, cases, rng),
            old_clean=["OldScratch"],
            new_clean=["NewScratch"],
            new_dirty=["BorrowedExtra"],
            cases=cases,
        )
        clear_gate_cache(old, new, "compact_prefix_addsub_gate")
        if index % 20 == 0:
            print(f"PROGRESS Tsub {index}/{len(windows)}", flush=True)
    print(f"PASS Tsub unique_windows={len(windows)}", flush=True)


def check_tadd(old, new, cases):
    windows = unique_windows(new, "t_addsub")
    for index, (k, upper) in enumerate(windows, 1):
        fields = [
            ("Ctrl", 1), ("Sign", 1), ("Tail", 1), ("Work1", 259),
            ("Work2", 259), ("l_t", 8), ("l_s", 9), ("l_rp", 8),
            ("Dirty", 10),
        ]
        rng = random.Random(0x82040000 + k * 1024 + upper)
        values = common.random_common(fields, cases, rng)
        values["l_s"] = common.words_from_values(
            [rng.randrange(259) for _ in range(cases)], 9
        )
        common.compare_pair(
            label=f"Tadd-{k}-{upper}",
            old_gate=old.compact_prefix_add_midtail_gate(
                n=256, k=k, K=upper
            ),
            new_gate=new.compact_prefix_add_midtail_gate(
                n=256, k=k, K=upper
            ),
            old_fields=fields + [("OldScratch", 8)],
            new_fields=fields + [("NewScratch", 7)],
            common_values=values,
            old_clean=["OldScratch"],
            new_clean=["NewScratch"],
            cases=cases,
        )
        clear_gate_cache(old, new, "compact_prefix_add_midtail_gate")
        if index % 20 == 0:
            print(f"PROGRESS Tadd {index}/{len(windows)}", flush=True)
    print(f"PASS Tadd unique_windows={len(windows)}", flush=True)


def check_terminal(old, new, cases):
    pairs = sorted(
        {
            (
                tuple(new.safe_active_windows(256, step)["len_update_lt"]),
                tuple(new.safe_active_windows(256, step)["len_update_lrp"]),
            )
            for step in range(4, 1617, 4)
        }
    )
    prefix = [
        ("Ctrl", 1), ("Work1", 259), ("Work2", 259),
        ("l_t", 8), ("l_rp", 8),
    ]
    mask = (1 << cases) - 1
    for index, ((k4, K4), (k5, K5)) in enumerate(pairs, 1):
        rng = random.Random(
            0x82050000 + k4 * 1_000_000 + K4 * 10_000 + k5 * 100 + K5
        )
        low_a, high_a = max(3, k5), min(258, K5)
        low_b, high_b = max(3, k4), min(258, K4)
        reachable = low_a <= high_a and low_b <= high_b
        values = common.random_common(prefix + [("Dirty0", 1)], cases, rng)
        if reachable:
            values["Ctrl"] = [mask]
            values["Extension"] = [0]
            a_values = [rng.randrange(low_a, high_a + 1) for _ in range(cases)]
            b_values = [rng.randrange(low_b, high_b + 1) for _ in range(cases)]
            values["l_t"] = common.words_from_values(
                [a - 3 for a in a_values], 8
            )
            values["l_rp"] = common.words_from_values(
                [258 - b for b in b_values], 8
            )
        else:
            values["Ctrl"] = [0]
            values["Extension"] = [rng.getrandbits(cases)]
        common.compare_pair(
            label=f"terminal-{k4}-{K4}-{k5}-{K5}",
            old_gate=old.compact_swap_work_and_len_gate(
                n=256, k4=k4, K4=K4, k5=k5, K5=K5
            ),
            new_gate=new.compact_swap_work_and_len_gate(
                n=256, k4=k4, K4=K4, k5=k5, K5=K5
            ),
            old_fields=prefix
            + [("Dirty0", 1), ("Extension", 1), ("OldScratch", 8)],
            new_fields=prefix
            + [
                ("Dirty0", 1), ("DirtyExtra", 7), ("Extension", 1),
                ("NewScratch", 7),
            ],
            common_values=values,
            old_clean=["OldScratch"],
            new_clean=["NewScratch"],
            new_dirty=["DirtyExtra"],
            cases=cases,
        )
        clear_gate_cache(old, new, "compact_swap_work_and_len_gate")
        clear_gate_cache(old, new, "compact_len_update_lt_gate")
        clear_gate_cache(old, new, "compact_len_update_lrp_gate")
        if index % 20 == 0:
            print(f"PROGRESS terminal {index}/{len(pairs)}", flush=True)
    print(f"PASS terminal unique_window_pairs={len(pairs)}", flush=True)


CHECKS = {
    "r": check_r,
    "lc": check_lc,
    "tsub": check_tsub,
    "tadd": check_tadd,
    "terminal": check_terminal,
}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--old", type=Path, required=True)
    parser.add_argument("--new", type=Path, required=True)
    parser.add_argument("--category", choices=sorted(CHECKS), required=True)
    parser.add_argument("--cases", type=int, default=8)
    args = parser.parse_args()
    old = verify.load_module(
        f"q821_aux9_{args.category}_reference", args.old.resolve()
    )
    new = verify.load_module(
        f"q820_aux8_{args.category}_candidate", args.new.resolve()
    )
    CHECKS[args.category](old, new, args.cases)
    print(f"PASS all-window category={args.category}", flush=True)


if __name__ == "__main__":
    main()
