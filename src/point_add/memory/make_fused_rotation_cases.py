#!/usr/bin/env python3
"""Reproduce the native test fixture from independent certified PZ/tail states."""
import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).parent
SUPPORT = HERE.parents[3] / 'tail-support-proof/src/point_add/memory/tail_support_certificate.py'
spec = importlib.util.spec_from_file_location('tail_support_certificate', SUPPORT)
model = importlib.util.module_from_spec(spec)
spec.loader.exec_module(model)
rows, certificates = [], []
selected_rounds = {0, 1, 2, 7, 31, 63, 127, 223}
for index in range(64):
    certificate = model.check_input(index)
    assert certificate['status'] == 'certificate_pass'
    certificates.append(certificate)
    x = int(certificate['x'], 16)
    a, b, ca, cb, q, parity, _ = model.pz(x)
    coefficients = [((-1 if parity else 1) * (ca + q * cb)) % model.P,
                    ((1 if parity else -1) * cb) % model.P]
    values = [a, b]
    for i in range(2):
        while values[i] % 2 == 0:
            values[i] //= 2
            coefficients[i] = coefficients[i] * model.INV2 % model.P
    for step in range(model.ROUNDS):
        target, source = 1 - step % 2, step % 2
        sign = ((values[0] ^ values[1]) >> 1) & 1
        old, addend = coefficients[target], coefficients[source]
        result = (old + (1 - 2 * sign) * addend) * model.INV2 % model.P
        literal, defect = model.signed_add_source(old, addend, sign)
        assert defect == 0 and model.half_source(literal) == result
        # Rotation-only phase identity, independently checked on every case.
        rotated = ((result << 1) % model.M) | (result >> 255)
        predicate = int((rotated ^ (sign * (model.M - 1))) < addend)
        carry = ((old ^ (sign * (model.M - 1))) + addend) >> 256
        assert predicate == carry
        if step in selected_rounds:
            rows.append(f'{old:064x} {addend:064x} {sign} {result:064x}')
        values[target] = (values[target] + (1 - 2 * sign) * values[source]) // 2
        coefficients[target] = result
packet = '\n'.join(rows) + '\n'
target = HERE.parent / 'trailmix_port/inversion/fused_rotation_cases.txt'
target.write_text(packet)
(HERE / 'fused_rotation_fixture_certificates.json').write_text(json.dumps(certificates, indent=2) + '\n')
summary = dict(cases=len(rows), inputs=64, rounds=sorted(selected_rounds),
    packet_sha256=hashlib.sha256(packet.encode()).hexdigest(),
    support_script_sha256=hashlib.sha256(SUPPORT.read_bytes()).hexdigest(),
    full_trajectory_rotation_comparisons=64 * model.ROUNDS,
    scope='Exact-transition classical certificates and literal phase predicate; actual native tests remain separate')
(HERE / 'fused_rotation_fixture_summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
