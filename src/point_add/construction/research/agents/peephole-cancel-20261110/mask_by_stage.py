#!/usr/bin/env python3
"""Attribute deleted Toffolis of a deletion mask to generator stages (innermost span).
usage: mask_by_stage.py TRACE.u16le RANGES.tsv MASK OUT.tsv"""
import sys
import numpy as np
trace, ranges, maskf, out = sys.argv[1:5]
t = np.memmap(trace, dtype='<u2', mode='r')
kind = np.asarray(t[0::4])
n = kind.shape[0]
ccx = kind == 13
del kind
m = np.unpackbits(np.fromfile(maskf, dtype=np.uint8), bitorder='little')[:n].astype(bool)
pd = np.zeros(n + 1, dtype=np.int64); np.cumsum(m & ccx, out=pd[1:])
pc = np.zeros(n + 1, dtype=np.int64); np.cumsum(ccx, out=pc[1:])
ids, par, st, en, names, flags = [], [], [], [], [], []
with open(ranges) as f:
    for line in f:
        p = line.rstrip('\n').split('\t')
        if not p[0].lstrip('-').isdigit():
            continue
        ids.append(int(p[0])); par.append(int(p[1])); st.append(int(p[2])); en.append(int(p[3])); names.append(p[4]); flags.append(p[5] if len(p) > 5 else '')
ids = np.array(ids); par = np.array(par); st = np.array(st); en = np.array(en)
incl_d = pd[en] - pd[st]; incl_c = pc[en] - pc[st]
idx = {int(i): k for k, i in enumerate(ids)}
self_d = incl_d.copy(); self_c = incl_c.copy()
for k in range(len(ids)):
    p = idx.get(int(par[k]))
    if p is not None:
        self_d[p] -= incl_d[k]; self_c[p] -= incl_c[k]
agg = {}
for k in range(len(ids)):
    a = agg.setdefault(names[k], [0, 0, 0])
    a[0] += 1; a[1] += int(self_c[k]); a[2] += int(self_d[k])
rows = sorted(agg.items(), key=lambda kv: -kv[1][2])
with open(out, 'w') as f:
    f.write('name\tinstances\tself_ccx\tdeleted_ccx\tpct\n')
    for name, (c, sc, sd) in rows:
        f.write(f'{name}\t{c}\t{sc}\t{sd}\t{100.0 * sd / max(sc, 1):.2f}\n')
print('total ccx', int(pc[-1]), 'deleted', int(pd[-1]), 'in spans', int(self_d.sum()))
