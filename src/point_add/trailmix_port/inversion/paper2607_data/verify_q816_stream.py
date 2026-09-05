#!/usr/bin/env python3
"""Verify and aggregate certified Q816 Aux4 paper2607 primitive shards."""

from __future__ import annotations

import verify_q818_stream as q817_verifier


q817_verifier.verifier.LOCAL_WIDTH = 570
q817_verifier.verifier.AUX_SIZE = 4


if __name__ == "__main__":
    q817_verifier.verifier.main()
