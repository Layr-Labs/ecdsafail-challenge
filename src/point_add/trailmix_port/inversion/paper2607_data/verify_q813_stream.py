#!/usr/bin/env python3
"""Verify and aggregate repaired Q813 Aux1 paper2607 primitive shards."""

from __future__ import annotations

import verify_q818_stream as q817_verifier


q817_verifier.verifier.LOCAL_WIDTH = 567
q817_verifier.verifier.AUX_SIZE = 1


if __name__ == "__main__":
    q817_verifier.verifier.main()
