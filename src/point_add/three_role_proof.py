"""Independent, exhaustive Boolean models for two three-owner identities.

This file imports or executes no contestant module, circuit generator,
evaluator, or benchmark. Each gate is a literal reversible controlled-X;
there are no relative phases or measurement assumptions. The inverse test
reverses exactly the same gate tape. This checks the local arithmetic
identities, not integration, total width, or the qualified parent's ranges.
"""

from itertools import product


def play(value, tape):
    for target, controls in tape:
        if all(((value >> q) & 1) == bit for q, bit in controls):
            value ^= 1 << target
    return value


def virtual_boundary(n, source_length, boundary):
    t = list(range(n + 1))
    s = list(range(n + 1, n + 1 + source_length))
    carry = n + 1 + source_length
    e, activity = carry + 1, carry + 2
    tape = []

    def gate(target, *controls):
        assert all(q != target for q, _ in controls)
        tape.append((target, tuple(controls)))

    def cell(i, inverse=False):
        x = carry if i == 0 else s[i - 1]
        seq = [(t[i], ((s[i], 1),)), (x, ((s[i], 1),)),
               (s[i], ((x, 1), (t[i], 1)))]
        tape.extend(reversed(seq) if inverse else seq)
        return x

    def undo(i):
        if i < source_length:
            return cell(i, True)
        return carry if i == 0 else s[i - 1]

    for q in t:
        gate(q)
    for i in range(source_length):
        cell(i)
    x = undo(n)
    for i in reversed(range(n + 1)):
        if i < n:
            gate(t[i], (activity, 1), (e, 1), (s[i], 1))
            gate(t[i], (activity, 1), (e, 1), (x, 1))
            if boundary == i + 1:
                gate(t[i], (activity, 1), (e, 1), (s[i], 0))
        previous = undo(i - 1) if i else None
        if boundary == i:
            or_terms = [[(t[i - 1], 1)], [(previous, 1)],
                        [(t[i - 1], 1), (previous, 1)]]
            gate(e, (activity, 1))
            for term in or_terms:
                gate(e, (activity, 1), (t[i], 1), *term)
            for term in or_terms:
                gate(t[i], (activity, 1), (e, 1), *term)
        if previous is not None:
            x = previous
    for q in t:
        gate(q)
    return tape, carry, e, activity


def fixed_top(n, first):
    t = list(range(n + 1))
    q = list(range(n + 1, 2 * n + 1))
    carry, e, activity = q[-1], 2 * n + 1, 2 * n + 2
    tape = []

    def gate(target, *controls):
        assert all(p != target for p, _ in controls)
        tape.append((target, tuple(controls)))

    def cell(i, inverse=False):
        x = carry if i == first else q[i - 1]
        seq = [(t[i], ((q[i], 1),)), (x, ((q[i], 1),)),
               (q[i], ((x, 1), (t[i], 1)))]
        tape.extend(reversed(seq) if inverse else seq)
        return x

    gate(carry)
    for p in t:
        gate(p)
    for i in range(first, n - 1):
        cell(i)
    or_terms = [[(t[n - 1], 1)], [(q[n - 2], 1)],
                [(t[n - 1], 1), (q[n - 2], 1)]]
    gate(e, (activity, 1))
    for term in or_terms:
        gate(e, (activity, 1), (t[n], 1), *term)
    for term in or_terms:
        gate(t[n], (activity, 1), (e, 1), *term)
    gate(t[n - 1], (activity, 1), (e, 1))
    gate(t[n - 1], (activity, 1), (e, 1), (q[n - 2], 1))
    for i in reversed(range(first, n - 1)):
        x = cell(i, True)
        gate(t[i], (activity, 1), (e, 1), (q[i], 1))
        gate(t[i], (activity, 1), (e, 1), (x, 1))
    for p in t:
        gate(p)
    gate(carry)
    return tape, e, activity


def check_variable():
    count = 0
    for n in range(1, 6):
        for source_length in (n, n + 1):
            for boundary in range(1, n + 1):
                tape, carry, e, activity = virtual_boundary(n, source_length, boundary)
                for source in range(1 << source_length):
                    divisor = (source & ((1 << (boundary - 1)) - 1)) | (1 << (boundary - 1))
                    for target in range(1 << (n + 1)):
                        d = target & ((1 << (boundary + 1)) - 1)
                        if d < 2 * divisor:
                            state = target | (source << (n + 1)) | (1 << activity)
                            got = play(state, tape)
                            quotient = int(d >= divisor)
                            want = (target - quotient * divisor) | (source << (n + 1))
                            want |= (1 << activity) | (quotient << e)
                            assert got == want, (n, source_length, boundary, source, target)
                            assert play(got, reversed(tape)) == state
                            count += 1
                        for c, flight in product((0, 1), repeat=2):
                            state = target | (source << (n + 1)) | (c << carry) | (flight << e)
                            assert play(state, tape) == state
                            count += 1
    return count


def check_fixed():
    count = 0
    for n in range(2, 7):
        for first in range(n):
            tape, e, activity = fixed_top(n, first)
            for source in range(1 << n):
                for target in range(1 << (n + 1)):
                    if source >> (n - 1) and source % (1 << first) == 0 and target < 2 * source:
                        state = target | (source << (n + 1)) | (1 << activity)
                        got = play(state, tape)
                        quotient = int(target >= source)
                        want = (target - quotient * source) | (source << (n + 1))
                        want |= (1 << activity) | (quotient << e)
                        assert got == want, (n, first, source, target)
                        assert play(got, reversed(tape)) == state
                        count += 1
                    for flight in (0, 1):
                        state = target | (source << (n + 1)) | (flight << e)
                        assert play(state, tape) == state
                        count += 1
    return count


if __name__ == "__main__":
    variable, fixed = check_variable(), check_fixed()
    print(f"PASS variable-boundary: {variable:,} states")
    print(f"PASS fixed-top: {fixed:,} states")
    print("Only local identities were tested; integration and peak width remain unverified.")
