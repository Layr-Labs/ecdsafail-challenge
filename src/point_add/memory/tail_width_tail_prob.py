"""For a cut, estimate per-round exceedance rates of the tail value width against a table.
usage: python tail_width_tail_prob.py CUT TABLE_FILE N_PER_WORKER WORKERS ROUNDS_TO_CHECK"""
import sys, random, multiprocessing as mp, re
from midq_tail_width_model import pz_prefix, bl, sw, P
def one(args):
    seed,n,cut,tab,R=args
    rng=random.Random(seed); exc1=[0]*R; exc2=[0]*R; tot=0
    for _ in range(n):
        x=rng.randrange(1,P); a,b,q,t=pz_prefix(x,cut)
        if t or a==0: continue
        if a%2==0: a>>=(a&-a).bit_length()-1
        if b%2==0: b>>=(b&-b).bit_length()-1
        tot+=1; pair=[a,b]
        for r in range(R):
            w=max(sw(pair[0]),sw(pair[1]))
            t_=1 if r%2==0 else 0; s_=1-t_
            sign=((pair[s_]^pair[t_])>>1)&1
            ssum=pair[t_]+(-pair[s_] if sign else pair[s_])
            w=max(w,sw(ssum))
            if w>tab[r]-1: exc1[r]+=1
            if w>tab[r]-2: exc2[r]+=1
            pair[t_]=ssum>>1
    return exc1,exc2,tot
if __name__=='__main__':
    cut=int(sys.argv[1]); t=open(sys.argv[2]).read()
    m=re.search(r'MIDQ_TAIL_VALUE_WIDTH: \[u8; MIDQ_TAIL_ROUNDS \+ 1\] = \[(.*?)\];',t,re.S)
    tab=[int(x) for x in re.findall(r'\d+',m.group(1))]
    n=int(sys.argv[3]); W=int(sys.argv[4]); R=int(sys.argv[5])
    with mp.Pool(W) as pool: res=pool.map(one,[(5000+i,n,cut,tab,R) for i in range(W)])
    tot=sum(r[2] for r in res)
    print("samples",tot)
    for r in range(R):
        e1=sum(x[0][r] for x in res); e2=sum(x[1][r] for x in res)
        print(f"round {r:3d} table {tab[r]}  P(w>table-1)={e1/tot:.2e} ({e1})  P(w>table-2)={e2/tot:.2e} ({e2})")
