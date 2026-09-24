from pathlib import Path
import json,datetime,hashlib
R=Path(__file__).resolve().parent.parent
def t(k):return 0 if k<2 else 2*k-3
def base(lo,hi,n):
    cost=0
    for v in range(n-1):
        if not lo<=v<hi:continue
        h=v//64;l=max(lo,h*64);r=min(hi,(h+1)*64)
        k=sum(l>>b!=(r-1)>>b for b in range(6))
        cost+=t(k+(0 if lo//64==(hi-1)//64 else [1,2,3,3][h]))
    return 2*cost
def general(z):
    _,block,lo,hi,n,fixed,fv,wire,split,old,new,*_=z
    assert old==base(lo,hi,n)
    if not fixed>>wire&1:return
    trace=[];last=None
    for v in range(n-1):
        if not lo<=v<min(hi,252):continue
        h=v//64;l=max(lo,h*64);r=min(hi,252,(h+1)*64)
        lows=[(b+5,bool(v>>b&1))for b in range(6)if l>>b!=(r-1)>>b]
        high=[(4,False)] if h==0 else [(4,True),(3,False)] if h==1 else [(4,True),(3,True),(2,h==3)]
        high=[x for x in high if not fixed>>x[0]&1]
        producer=tuple(high+[x for x in lows if x[0]>=5+split])
        assert all(w!=wire for w,_ in producer+tuple(lows))
        if last!=producer:
            if last is not None:trace.append(len(last))
            trace.append(len(producer));last=producer
        trace.append(1+sum(b<5+split for b,_ in lows))
    if last is not None:trace.append(len(last))
    assert new==2*sum(t(k)for k in trace),(block,new,trace)
def c1(z):
    _,block,lo,hi,n,_,_,s1,s2,old,new,*_=z
    trace=[];one=None;two=None;last_h=None;baseline=0;high=lo//64!=(hi-1)//64
    for v in range(n-1):
        if not lo<=v<hi:continue
        h=v//64;l=max(lo,h*64);r=min(hi,(h+1)*64)
        bits=[b for b in range(6)if l>>b!=(r-1)>>b]
        baseline+=t(len(bits)+high)
        first=tuple((b,bool(v>>b&1))for b in bits if b>=s1)+(((6,True),)if high else ())
        if one!=first or high and last_h!=h:
            if two is not None:trace.append(len(two));two=None
            if one is not None:trace.append(len(one))
            trace.append(len(first));one=first;last_h=h
        if s2==7:trace.append(1+sum(b<s1 for b in bits));continue
        second=tuple((b,bool(v>>b&1))for b in bits if s2<=b<s1)+((6,True),)
        if two!=second:
            if two is not None:trace.append(len(two))
            trace.append(len(second));two=second
        trace.append(1+sum(b<s2 for b in bits))
    assert old==2*baseline and new==2*sum(t(k)for k in trace),(block,old,new)
selected={};checked=0
for name,fn in [('general',general),('c1',c1)]:
    file='lifetime-scores-r01.tsv' if name=='general' else 'c1-lifetime-scores-r01.tsv'
    rows=[list(map(int,l.split()))for l in (R/'gpu'/file).read_text().splitlines()]
    best=[]
    for b in range(202):
        row=min((z for z in rows if z[1]==b),key=lambda z:(z[10],z[7],z[8]))
        fn(row);checked+=1
        if row[10]<row[9]:best.append(row)
    selected[name]=best
with (R/'gpu/selected-lifetimes-r01.json').open('x') as f:json.dump(selected,f,indent=2)
dest=R/'workspace/src/point_add/trailmix_port/inversion/q792_lifetime_plans_r01.rs'
with dest.open('x') as f:
    f.write('// GPU-selected lifetimes; CPU independently checked selected scores.\n')
    for name in ['general','c1']:
        seen={}
        for z in selected[name]:
            _,b,lo,hi,n,fixed,value,x,y,old,new,*_=z
            data=(fixed,value,x,y) if name=='general' else (x,y)
            key=(lo,hi,n)
            assert key not in seen or seen[key]==data
            seen[key]=data
        if name=='general':
            f.write('const GENERAL:&[(usize,usize,usize,usize,usize,usize,usize)]=&[\n')
        else:f.write('const C1:&[(usize,usize,usize,usize,usize)]=&[\n')
        for key,data in sorted(seen.items()):f.write('('+','.join(map(str,key+data))+'),\n')
        f.write('];\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
proof={'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'GPU_SELECTED_INDEPENDENT_COST_CHECK_PASS','both_B50_used':True,'GPU_candidates':15554+5656,'CPU_selected_cost_checks':checked,'general_improving_blocks':len(selected['general']),'C1_improving_blocks':len(selected['c1']),'predicted_gain_general':32*sum(z[9]-z[10]for z in selected['general']),'predicted_gain_C1':32*sum(z[9]-z[10]for z in selected['c1']),'whole_circuit_gain_measured':False,'emitted_plan_path':str(dest.relative_to(R/'workspace')),'emitted_plan_sha256':sha(dest),'hashes':{p.name:sha(p)for p in (R/'gpu').glob('*')if p.is_file() and p.name!='selected-proof-r01.json'}}
with (R/'gpu/selected-proof-r01.json').open('x') as f:json.dump(proof,f,indent=2)
print(json.dumps({k:v for k,v in proof.items()if k!='hashes'},indent=2))
