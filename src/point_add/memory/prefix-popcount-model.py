"""Lightweight exact-integer metadata audit, not a quantum/support certificate."""
from pathlib import Path
import hashlib,json
P=2**256-2**32-977
BITS=6

def run(p,x,steps):
    a,b,ca,cb,q=p,min(x,p-x),0,1,0
    C=0; trace=[]; peak=0
    for _ in range(steps):
        if a==0 and b==1 and q==0: break
        role=int(a<b)
        before=C
        C+=1-2*role
        if role:
            j=(q&-q).bit_length()-1
            assert j>=0 and q>>j&1
            q^=1<<j;ca+=cb<<j
        if ca<cb:
            j=a.bit_length()-b.bit_length()
            if a<b<<j:j-=1
            assert j>=0 and not(q>>j&1)
            a-=b<<j;q^=1<<j
        assert int(ca<cb)==1-role
        assert C==q.bit_count() and 0<=C<1<<BITS
        assert (C==0)==(q==0)
        assert C-1+2*role==before
        peak=max(peak,C)
        trace.append((before,C,role,q))
        if q==0 and a!=0:a,b,ca,cb=b,a,cb,ca
        assert a*cb+b*(ca+q*cb)==p
    # The q-preserving cut conversion gives the exact original tail ABI.
    erased=C-sum((q>>j)&1 for j in range(q.bit_length()))
    assert erased==0 and erased+q.bit_count()==C
    for old,new,role,q_after in reversed(trace):
        assert new==q_after.bit_count()
        assert new-1+2*role==old
    return len(trace),peak,C

small=sum(run(p,x,100)[0] for p in [31,61,127,251] for x in range(1,p))
rows=[]
for i in range(128):
    x=1+int.from_bytes(hashlib.shake_256(f'prefix-popcount-20260910:{i}'.encode()).digest(32),'little')%(P-1)
    rows.append(run(P,x,360))
def layer_id(x):
    layer=0;total=0
    while total<=x:
        total+=(1<<layer)+1;layer+=1
    return layer-1

def start_layer(i): return sum((1<<j)+1 for j in range(i))
def anc_count(n):
    if n<=1:return 0
    t=layer_id(n-1)+1
    return 1 if t<=2 else 2+anc_count(t)
def layers(q,initial):
    if len(q)==1:return [[[],0],[[q[0]],0]]
    n=len(q);last=layer_id(n-1);out=[[[],0]];targets=[];anc=[initial[0]]
    for level in range(last+1):
        st=start_layer(level);en=min(n,start_layer(level+1))
        out.append([targets+[q[st]],0])
        for i in range(st+1,en):
            offset=i-st;t=anc[-offset]
            out.append([targets+[t],1])
        size=en-st
        targets.append(anc[1-size])
        off=2-size
        if off<0:off=len(anc)+off
        anc=anc[off:]+q[st:en]
    if len(targets)<=2:return out
    out.append([[],0]);prefix=layers(targets,initial[2:])
    for level in range(1,last+1):
        st=start_layer(level);en=min(n,start_layer(level+1));ctrls,cost=prefix[level]
        out[st+1][1]+=cost
        temp=ctrls[0] if len(ctrls)==1 else initial[1]
        if len(ctrls)==2:out[st+1][1]+=1
        for i in range(st,en):out[i+1][0]=[temp,out[i+1][0][-1]]
        if len(ctrls)==2:out[en+1][1]+=1
    return out

# Exact small static expansion of the existing cinc KG control-layer shape.
# This counts emitted CCXs, not a quantum simulation or compiler optimization.
shape=layers(list(range(BITS)),list(range(100,100+anc_count(BITS))))
inc_raw=2*sum(row[1] for row in shape)+sum(len(row[0])==2 for i,row in enumerate(shape) if i<BITS+1 and i!=0)
assert inc_raw==12

report=dict(scope='Exact integer metadata transitions only; no original thin-width/approximate-compare or quantum-phase validation.',small_transitions=small,secp_inputs=len(rows),secp_transitions=sum(r[0] for r in rows),max_observed_popcount=max(r[1] for r in rows),max_observed_cut_popcount=max(r[2] for r in rows),all_update_swap_inverse_and_cut_invariants=True,increment_raw_ccx=inc_raw,increment_ancilla_upper_bound=anc_count(BITS),ideal_predicate_cost_screen={str(n):dict(raw_per_boundary_saved=2*n-3-(2*BITS-3)-inc_raw,expected_per_boundary_saved=1.5*n-2-(1.5*BITS-2)-inc_raw) for n in [12,14,18,24,31]},capacity_proof='Configured quotient width<64 implies popcount<=63. Added bits are fresh zero bits, removed bits are one, so valid updates never wrap six bits.')
Path(__file__).with_name('prefix-popcount-model-results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
