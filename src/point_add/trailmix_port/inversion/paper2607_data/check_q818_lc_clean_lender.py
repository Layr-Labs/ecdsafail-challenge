#!/usr/bin/env python3
"""Certify the fixed-schedule Work1[0] lender for Q818 LC swaps."""

from __future__ import annotations

import json
from pathlib import Path


def main() -> None:
    certificate = json.loads(
        Path(__file__).with_name("active_windows_1616.json").read_text(
            encoding="utf-8"
        )
    )
    work_size = int(certificate["work_size"])
    nonnull = []
    null_steps = []
    for row in certificate["rows"]:
        step = int(row["step"])
        window = row["safe"]["quotient_swap"]
        if window is None:
            null_steps.append(step)
            continue
        k, K = map(int, window)
        if k <= 1:
            raise AssertionError(f"step {step}: Work1[0] enters [{k - 1}, {K}]")
        excluded = work_size - (K - k + 2)
        if excluded < 1:
            raise AssertionError(f"step {step}: no excluded Work1 lane")
        nonnull.append((step, k, K, excluded))

    print(
        "PASS q818-lc-lender "
        f"rows={len(certificate['rows'])} nonnull={len(nonnull)} "
        f"null={len(null_steps)} null_steps={null_steps} "
        f"min_excluded={min(row[3] for row in nonnull)} lender=Work1[0]"
    )


if __name__ == "__main__":
    main()
