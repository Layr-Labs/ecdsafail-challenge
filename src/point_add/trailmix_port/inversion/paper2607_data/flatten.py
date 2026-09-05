def flatten(qc):
    out=[]
    def rec(circ, qmap):
        for ci in circ.data:
            op=ci.operation; name=op.name
            gids=[qmap[circ.find_bit(q).index] for q in ci.qubits]
            if name in ("x","cx","ccx","swap","cz","z","h","u","measure","reset","barrier","delay"):
                out.append((name,gids))
            else:
                d=op.definition
                if d is None: raise ValueError("leaf "+name)
                rec(d, {i:gids[i] for i in range(len(gids))})
    rec(qc, {i:i for i in range(qc.num_qubits)})
    return out

def simulate_ops(ops, nq, ncase, seed_assign):
    lanes=[0]*nq
    ALL=(1<<ncase)-1
    for q,mask in seed_assign.items(): lanes[q]=mask
    for name,qids in ops:
        if name=="x": lanes[qids[0]]^=ALL
        elif name=="cx": lanes[qids[1]]^=lanes[qids[0]]
        elif name=="ccx": lanes[qids[2]]^=lanes[qids[0]]&lanes[qids[1]]
        elif name=="swap": lanes[qids[0]],lanes[qids[1]]=lanes[qids[1]],lanes[qids[0]]
        elif name in ("barrier","delay"): pass
        else: raise ValueError("sim cannot handle "+name)
    return lanes
