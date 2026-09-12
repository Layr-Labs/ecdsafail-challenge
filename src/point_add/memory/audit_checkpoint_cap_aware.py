"""Local gate-template and scratch-bound checks; actual Rust native tests are remote."""
from pathlib import Path
import hashlib,json

def naf(value,width):
    terms=[];i=0
    while value:
        if value&1:
            digit=-1 if value&3==3 else 1
            if i<width:terms.append((i,digit))
            value-=digit
        value>>=1;i+=1
    return terms

def add(ops,g,a,b):
    n=len(a)
    if n==1:ops.append((a[0],g,b[0]));return
    for i in range(1,n):ops.append((a[i],b[i]))
    for i in reversed(range(1,n-1)):ops.append((b[i+1],b[i]))
    for i in range(n-1):ops.append((b[i+1],a[i],b[i]))
    for i in reversed(range(n-1)):
        ops.append((a[i+1],g,b[i+1]));ops.append((b[i+1],a[i],b[i]))
    for i in range(1,n-1):ops.append((b[i+1],b[i]))
    ops.append((a[0],g,b[0]))
    for i in range(1,n):ops.append((a[i],b[i]))

def kernel(n,value,subtract):
    ops=[];g=2*n;a=list(range(n));donor=list(range(n,2*n))
    for start,digit in naf(value,n):
        word=a[start:];source=donor[:len(word)]
        if len(word)==1:ops.append((word[0],g));continue
        increment=(digit>0)!=subtract
        if increment:ops.extend((i,)for i in word)
        add(ops,g,word,source);ops.extend((i,)for i in source)
        add(ops,g,word,source);ops.extend((i,)for i in source)
        if increment:ops.extend((i,)for i in word)
    assert all(all(0<=i<2*n+1 for i in op)for op in ops)
    return ops

def run(ops,words):
    r=words.copy();mask=(1<<64)-1
    for op in ops:
        if len(op)==1:r[op[0]]^=mask
        elif len(op)==2:r[op[0]]^=r[op[1]]
        else:r[op[0]]^=r[op[1]]&r[op[2]]
    return r

cases=0
for n in range(1,7):
    values=range(1<<n)if n<=5 else [0,1,3,5,9,17,39,0x1000003d1]
    states=1<<(2*n+1);mask=(1<<n)-1
    for value in values:
        assert sum((1<<i)*d for i,d in naf(value,n))&mask==value&mask
        for subtract in [False,True]:
            ops=kernel(n,value,subtract)
            for first in range(0,states,64):
                inputs=[(first+i)%states for i in range(64)]
                words=[sum(((v>>bit)&1)<<lane for lane,v in enumerate(inputs))for bit in range(2*n+1)]
                actual=run(ops,words)
                expected=[]
                for v in inputs:
                    a=v&mask;enabled=(v>>(2*n))&1
                    z=(a+enabled*(-value if subtract else value))&mask
                    expected.append((v&~mask)|z)
                want=[sum(((v>>bit)&1)<<lane for lane,v in enumerate(expected))for bit in range(2*n+1)]
                assert actual==want;cases+=64

full_cases=0;prices=[]
for n,value in [(255,0x800001e8),(256,0x1000003d1)]:
    rows=[];mask=(1<<n)-1
    for index in range(64):
        raw=hashlib.shake_256(f'checkpoint-cap-audit-{n}-{index}'.encode()).digest(64)
        a=int.from_bytes(raw[:32],'little')&mask;d=int.from_bytes(raw[32:],'little')&mask
        rows.append(a|(d<<n)|((index&1)<<(2*n)))
    words=[sum(((v>>bit)&1)<<lane for lane,v in enumerate(rows))for bit in range(2*n+1)]
    for subtract in [False,True]:
        ops=kernel(n,value,subtract);actual=run(ops,words)
        expected=[(v&~mask)|(((v&mask)+((v>>(2*n))&1)*(-value if subtract else value))&mask)for v in rows]
        want=[sum(((v>>bit)&1)<<lane for lane,v in enumerate(expected))for bit in range(2*n+1)]
        assert actual==want;full_cases+=64
    raw_T=sum(len(op)==3 for op in kernel(n,value,False))
    bound=sum(6*(n-i)-4 for i,_ in naf(value,n)if n-i>=2)
    assert raw_T==bound
    prices.append(dict(width=n,constant=value,terms=naf(value,n),raw_T=raw_T,extra_clean=0,reference_compact_raw_T=3*n-4))
report=dict(status='PASS local reversible gate-template and source scratch bounds',
    small_word_cases=cases,full_width_cases=full_cases,prices=prices,
    only_gates=['X','CX','CCX'],phase='No phase gates or measurements in the zero-clean fallback; source restored exactly.',
    native_rust_execution=False,whole_circuit_cap_enforced=False)
out=Path(__file__).with_name('CHECKPOINT_CAP_LOCAL_RESULTS.json');out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
