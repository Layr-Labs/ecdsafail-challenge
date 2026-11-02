#!/usr/bin/env python3
"""Export the SKY-COF design's per-tick public widths and model room (public layout, H_k0w64, eps=1e-4)
from the design's own assembly (barrier/skycof-deciders/assemble.py, scd_n10M_s20261001 tables), for the
tick's cost measurement. Columns: t rail cof H live cap A model_rails model_cof.
Usage: python design_widths.py OUT.tsv [eps]"""
import sys, importlib.util
D = r"R:/Coding/shor2/barrier/skycof-deciders"
sys.path.insert(0, D)
sys.argv_saved = sys.argv[:]
out = sys.argv[1]; eps = float(sys.argv[2]) if len(sys.argv) > 2 else 1e-4
sys.argv = ["assemble.py", D + "/scd_n10M_s20261001"]
spec = importlib.util.spec_from_file_location("assemble", D + "/assemble.py")
A = importlib.util.module_from_spec(spec); spec.loader.exec_module(A)
from lowroom_prims import cadd
v = A.variant("public", "H_k0w64", eps, 0, 64)
o = [x for x in A.opt if x["layout"] == "public" and x["H"] == "H_k0w64" and abs(float(x["eps"]) - eps) / eps < 1e-6 and x["railfield"] == "srail"][0]
mr, mc, mh = int(o["m_rail"]), int(o["m_cof"]), int(o["m_H"])
R = A.R
rail = [A.B["srail"][t] + mr for t in range(R)]
cof = [min(A.B["kcof"][t] + mc, 256) for t in range(R)]
H = [A.B["H_k0w64"][t] + mh for t in range(R)]
live = [2 * rail[t] + 2 * cof[t] + H[t] + A.PASS + A.SMALL for t in range(R)]
cap = v["cap"]
with open(out, "w") as f:
    f.write(f"# public H_k0w64 eps={eps:g} margins rail/cof/H {mr}/{mc}/{mh} CAP {cap} PASS {A.PASS} SMALL {A.SMALL} FLAGS {A.FLAGS}\n")
    f.write("t\trail\tcof\tH\tlive\tcap\tA\tmodel_rails\tmodel_cof\n")
    tr = tc = 0.0
    for t in range(R):
        a = max(0, cap - live[t] - A.FLAGS)
        mrl = 2 * rail[t]; mcf = cof[t] + cadd(cof[t], a)
        tr += mrl; tc += mcf
        f.write(f"{t}\t{rail[t]}\t{cof[t]}\t{H[t]}\t{live[t]}\t{cap}\t{a}\t{mrl}\t{mcf:.1f}\n")
print(f"CAP {cap} walk_peak {v['walk_peak']} model per traversal rails {tr/1e3:.1f}k cof {tc/1e3:.1f}k (assemble: rails {v['T']['rails']/1e3:.1f}k cof {v['T']['cof']/1e3:.1f}k)")
