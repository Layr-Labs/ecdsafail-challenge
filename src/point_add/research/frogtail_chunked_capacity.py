#!/usr/bin/env python3
"""Expected-T resource model for the locally validated chunked Frogtail family.

Counts the budget-dependent additions, digit erases, normalizer zero tests,
absorption tests and products. The constant term is calibrated to emitted
gates at 1000 qubits; the full model matches the independently emitted 917,
933 and 1000 circuits exactly. It is not a generic GCD cost estimator.
Recalibrate after changes to the walk, arithmetic, or phase-correction policy.
"""
import argparse
import hashlib
import json
from pathlib import Path

FIXED_T = 1_395_828
SCHEDULE_SHA = "076a6a5da5d0d24f84e0f89473b727a5826e0afb4b90f1a40546ba0a9b6483aa"


def fits_chunk_plan(n, room, flag):
    for count in range(1, n + 1):
        last = room + 1 - int(flag) - (count - 1)
        if last <= 0 or any(room <= j for j in range(count - 1)):
            break
        if sum(room - j for j in range(count - 1)) + last >= n:
            return True
    return False


def add_cost(n, room, flag=False):
    if flag:
        assert fits_chunk_plan(n, room, True)
        return 2 * n + 1 + (n - room) / 2
    if room >= n - 1:
        return 2 * n - 1
    if fits_chunk_plan(n, room, False):
        return 2 * n - 1 + (n - room - 1) / 2
    return 3 * n - 2 - room


def mcx_cost(n, temps):
    if n < 2:
        return 0
    if temps >= n - 2:
        return n - 1
    return temps + 4 * (n - temps - 2)


def split_and_cost(n, temps):
    if n < 3 or n - 2 <= temps or n > 2 * temps:
        return mcx_cost(n, temps)
    na, nb = n - n // 2, n // 2
    return (na - 1) + (nb - 1) + 1 + (na - 2)


def schedule():
    path = Path(__file__).resolve().parents[1] / "frogtail_batch/sched_frogtail.txt"
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == SCHEDULE_SHA, "schedule changed; recalibrate"
    values = [int(x) for line in raw.decode().splitlines() if not line.startswith("#")
              for x in line.split()]
    assert values[:3] == [308, 308, 556]
    return [0] + values[3:]


def costs(q, c):
    assert q >= 917
    rf, ri, re = q - 886, q - 909, q - 910
    forward = 2 * sum(add_cost(w, rf) + add_cost(308 - w, rf) for w in c[1:557])
    inverse = 2 * sum(add_cost(w, ri) + add_cost(308 - w, ri) for w in c[1:557])
    erase = 556 * sum(add_cost(n, re) for n in range(2, 23))
    normalizer = 1112 * sum(split_and_cost(1 << i, ri) for i in range(5))
    absorption = 2 * sum(mcx_cost(2 + min(22, c[t]), q - 906) for t in range(485, 558))
    # Three 318-bit tail products, plus four 256-bit products/MACs and seven
    # coordinate additions. Carry-flag phase cleanup belongs to FIXED_T.
    products = 954 * add_cost(256, min(q - 841, 255), True)
    products += 1031 * add_cost(256, min(q - 770, 255), True)
    return dict(forward_adds=forward, inverse_adds=inverse, digit_erase_adds=erase,
                normalizer_tests=normalizer, absorption_tests=absorption,
                product_adds=products, fixed=FIXED_T)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--min-q", type=int, default=917)
    parser.add_argument("--max-q", type=int, default=1100)
    args = parser.parse_args()
    if not 917 <= args.min_q <= args.max_q:
        parser.error("require 917 <= min-q <= max-q")
    c = schedule()
    for q, expected in [(917, 4_718_933.5), (933, 4_470_791.5), (1000, 4_281_203)]:
        assert sum(costs(q, c).values()) == expected
    rows = []
    for q in range(args.min_q, args.max_q + 1):
        parts = costs(q, c)
        t = sum(parts.values())
        rows.append(dict(qubits=q, expected_average_t=t, expected_product=q * t, parts=parts))
    best = min(rows, key=lambda x: x["expected_product"])
    selected = [r for r in rows if r["qubits"] in [917, 925, 931, 932, 933, 934, 950, 1000, 1025, 1100]]
    print(json.dumps(dict(scope="This fixed arithmetic family; expected costs, not measured scores",
                          best_product_in_scanned_range=best, selected_points=selected), indent=2))


if __name__ == "__main__":
    main()
