#!/usr/bin/env python3
"""Verify and aggregate repaired Q813 Aux1 paper2607 primitive shards."""

from __future__ import annotations

from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "paper2607_data"))

import verify_q818_stream as q817_verifier


q817_verifier.verifier.LOCAL_WIDTH = 576
q817_verifier.verifier.AUX_SIZE = 1


if __name__ == "__main__":
    q817_verifier.verifier.main()
