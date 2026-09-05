import sys, random
sys.path.insert(0, r"r:/Coding/shor/paper2607-support-ac1ecf")
sys.path.insert(0, ".")
from flatten import flatten, simulate_ops
import gen_base as base
import gen_patched as new

T     = int(sys.argv[1]) if len(sys.argv) > 1 else 800
NCASE = int(sys.argv[2]) if len(sys.argv) > 2 else 512

qb = base.build_step_circuit(256, T, T_max=1616, aux_size=1, measurement_uncompute=False)
qn = new.build_step_circuit(256, T, T_max=1616, aux_size=1, measurement_uncompute=False)
ob, on = flatten(qb), flatten(qn)
nq = qb.num_qubits
assert qn.num_qubits == nq, f"layout changed: {nq} vs {qn.num_qubits}"
print(f"step {T}: qubits {nq}  ops {len(ob):,} -> {len(on):,}  ({len(ob)/max(1,len(on)):.2f}x fewer)")

random.seed(7)
seed = {q: random.getrandbits(NCASE) for q in range(nq)}
for q in range(nq-9, nq): seed[q] = 0   # TAnc starts |0> in the real circuit
rb = simulate_ops(ob, nq, NCASE, dict(seed))
rn = simulate_ops(on, nq, NCASE, dict(seed))
diff = [q for q in range(nq) if rb[q] != rn[q]]
if diff:
    tot = sum(bin(rb[q] ^ rn[q]).count("1") for q in diff)
    print(f"RESULT step {T}: FAIL  {len(diff)} qubits differ (first {diff[:12]}), {tot} case-bits wrong of {nq*NCASE}")
else:
    print(f"RESULT step {T}: PASS  0 mismatches over {NCASE} random basis cases x {nq} qubits")
