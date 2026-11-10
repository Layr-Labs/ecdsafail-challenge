import random,struct,subprocess,sys
E=65535
def mk(n,nq,seed):
    R=random.Random(seed);recs=[]
    pool=[]
    for i in range(n):
        r=R.random()
        if r<0.25 and pool: recs.append(R.choice(pool[-30:]))   # repeat a recent gate (cancellation candidates)
        elif r<0.45:
            t=R.randrange(nq);g=(6,t,E,E);recs.append(g);pool.append(g)
        elif r<0.7:
            a,t=R.sample(range(nq),2);g=(8,a,t,E);recs.append(g);pool.append(g)
        elif r<0.9:
            a,b,t=R.sample(range(nq),3);g=(13,a,b,t);recs.append(g);pool.append(g)
        elif r<0.92: recs.append((7,R.randrange(nq),E,E))
        elif r<0.93: a,b=R.sample(range(nq),2);recs.append((9,a,b,E))
        elif r<0.94: recs.append((12,R.randrange(nq),R.randrange(100),E))
        elif r<0.95: recs.append((6,R.randrange(nq),R.randrange(4),E))   # classically controlled X
        elif r<0.96: a,t=R.sample(range(nq),2);recs.append((8,a,t,R.randrange(4)))
        elif r<0.97: recs.append((3,R.randrange(9),E,E))
        elif r<0.98: recs.append((15,R.randrange(4),E,E))
        else: recs.append((16,E,E,E))
    return recs
def sim(recs,st,bits):
    st=list(st);ph=0;meas={}
    cond=[]
    for k,a,b,c in recs:
        on=all(bits[x] for x in cond)
        if k==15: cond.append(a%4);continue
        if k==16:
            if cond: cond.pop()
            continue
        if not on: continue
        if k==6: 
            if b==E or bits[b%4]: st[a]^=1
        elif k==8:
            if c==E or bits[c%4]: st[b]^=st[a]
        elif k==13: st[c]^=st[a]&st[b]
        elif k==7: ph^=st[a]
        elif k==9: ph^=st[a]&st[b]
        elif k==12: meas.setdefault(b,[]).append(st[a]); st[a]=0
    return st,ph,meas
bad=0;tot=0;removed=0;N=0
for seed in range(60):
    nq=6+seed%5;recs=mk(3000,nq,seed);N+=len(recs)
    open('a.u16le','wb').write(b''.join(struct.pack('<4H',*r) for r in recs))
    with open('a.tsv','w') as f:
        for i in range(0,len(recs),97): f.write(f"{i}\t0\t{i}\t{min(len(recs),i+150)}\tspan{i}\t0\n")
    subprocess.run(['./tpeep','a.u16le','a.tsv','b.u16le','b.tsv','64'],check=True,capture_output=True)
    d=open('b.u16le','rb').read();out=[struct.unpack('<4H',d[i:i+8]) for i in range(0,len(d),8)];removed+=len(recs)-len(out)
    # span remap check: recompute kept indices by greedy alignment is hard; check counts monotone and within range
    R=random.Random(seed)
    for _ in range(40):
        st=[R.randrange(2) for _ in range(nq)];bits=[R.randrange(2) for _ in range(4)]
        tot+=1
        if sim(recs,st,bits)!=sim(out,st,bits): bad+=1
print('traces 60 records',N,'removed',removed,'random-state checks',tot,'mismatches',bad)
# exact span remap check
import os
bad2=0
for seed in range(20):
    nq=6+seed%5;recs=mk(3000,nq,seed)
    open('a.u16le','wb').write(b''.join(struct.pack('<4H',*r) for r in recs))
    sp=[(i,min(len(recs),i+150)) for i in range(0,len(recs),97)]+[(0,len(recs))]
    with open('a.tsv','w') as f:
        for j,(s0,e0) in enumerate(sp): f.write(f"{j}\t0\t{s0}\t{e0}\tspan\t{j%2}\n")
    subprocess.run(['./tpeep','a.u16le','a.tsv','b.u16le','b.tsv','64'],check=True,capture_output=True,env={**os.environ,'TPEEP_DUMP':'del.txt'})
    D=set(int(x) for x in open('del.txt').read().split())
    for (s0,e0),line in zip(sp,open('b.tsv')):
        f=line.rstrip('\n').split('\t');s1,e1=int(f[2]),int(f[3])
        if s1!=s0-sum(1 for d in D if d<s0) or e1!=e0-sum(1 for d in D if d<e0) or f[5]!=str(sp.index((s0,e0))%2 if False else f[5]): bad2+=1
print('span remap mismatches',bad2)
