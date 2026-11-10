import sys
def top(p):
    out=[]
    for l in open(p):
        f=l.rstrip('\n').split('\t')
        if len(f)>=5 and f[1]=='0' and f[4].split('.')[0] in ('upper','short','history'): out.append((f[4]+('(rev)' if f[5]=='1' else ''),int(f[2]),int(f[3])))
    return out
a,b=top(sys.argv[1]),top(sys.argv[2]);tot=0;agg={}
print(f"{'stage':28}{'ops before':>14}{'ops after':>14}{'saved':>12}{'%':>7}")
for (n,s,e),(n2,s2,e2) in zip(a,b):
    assert n==n2; d=(e-s)-(e2-s2); tot+=d; agg[n]=agg.get(n,0)+d
    print(f"{n:28}{e-s:14,}{e2-s2:14,}{d:12,}{100*d/(e-s):7.2f}")
print('stage total saved',f"{tot:,}");print({k:f"{v:,}" for k,v in agg.items()})
