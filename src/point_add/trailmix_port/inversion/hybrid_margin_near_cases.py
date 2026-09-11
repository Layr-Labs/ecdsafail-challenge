"""Generate synthetic LOCAL algebraic test cases, not PZ-reachability evidence.

Expected outputs use integer field arithmetic independently of the fused kernel.
The literal old word fold/rotate maps and their overflow predicates are checked
separately before writing the fixture. No benchmark or nonce inputs are read.
"""
from pathlib import Path
M=1<<256;F=(1<<32)+977;P=M-F;MASK=M-1;K=(F-1)//2;LOW=(1<<255)-1
B=(1<<200)+(1<<135)

def add(a,b,sigma):
    total=(a^ (MASK if sigma else 0))+b;carry=total>=M
    folded=((total&MASK)+(F if carry else 0))&MASK
    return folded^(MASK if sigma else 0),carry,folded

def halve_word(x):
    return (((x>>1)-K*(x&1))&LOW)+((x&1)<<255)

def double_word(y):
    return ((((y<<1)&MASK)|(y>>255))+(F-1)*(y>>255))&MASK

def record(w,kind,offset,a,b,sigma):
    d=2*((1<<32)+1)*(1<<w);vmin=P//d+1;drop={97:125,109:113}[w]
    z=(a+(-1 if sigma else 1)*b)%P
    y=(z+(z&1)*P)//2
    literal,kf,_=add(a,b,sigma)
    assert literal==z and halve_word(literal)==y
    rotated=((y<<1)&MASK)|(y>>255)
    flhs=rotated^(MASK if sigma else 0)
    doubled=(2*y)%P
    assert double_word(y)==doubled
    inverse,ki,ilhs=add(doubled,b,not sigma)
    assert inverse==a and (2*y-(-1 if sigma else 1)*b)%P==a
    for c in[a,b,y,doubled]:assert 0<c<P and min(c,P-c)>=vmin
    assert abs(flhs-b)>1<<drop and abs(ilhs-b)>1<<drop
    assert (flhs<b)==kf and (ilhs<b)==ki
    assert ((flhs>>drop)<(b>>drop))==kf and ((ilhs>>drop)<(b>>drop))==ki
    fbad=((flhs>>136)<(b>>136))!=kf;ibad=((ilhs>>136)<(b>>136))!=ki
    return (w,kind,offset,a,b,int(sigma),y,int(kf),flhs,int(ki),ilhs,int(fbad),int(ibad))

rows=[]
for w in[97,109]:
    vmin=P//(2*((1<<32)+1)*(1<<w))+1
    for offset in range(12):
        v=vmin+offset
        for high in[False,True]:
            for sigma in[False,True]:rows.append(record(w,'forward-high'if high else'forward-low',offset,P-v if high else v,B,sigma))
    for offset in range(16):
        u=(vmin|1)+2*offset
        a=P+u-B
        row=record(w,'inverse-double',offset,a,B,False)
        assert row[6]==(P+u)//2 and row[-1]==1
        rows.append(row)
    group=[r for r in rows if r[0]==w]
    assert len(group)==64 and sum(r[-2]for r in group)==24 and sum(r[-1]for r in group)==16
    print(f'W{w}:64 local cases, newdrop{ {97:125,109:113}[w]}, old136 defects forward24 inverse16')
lines=['# LOCAL algebraic fixtures; no PZ-reachability claim.',
       '# w family offset a b sign canonical_y forward_carry forward_lhs inverse_carry inverse_lhs old136_forward_bad old136_inverse_bad']
for r in rows:
    w,kind,offset,a,b,sigma,y,kf,flhs,ki,ilhs,fbad,ibad=r
    lines.append(f'{w} {kind} {offset} {a:064x} {b:064x} {sigma} {y:064x} {kf} {flhs:064x} {ki} {ilhs:064x} {fbad} {ibad}')
Path(__file__).with_suffix('.txt').write_text('\n'.join(lines)+'\n')
print('PASS128 independent local algebraic cases; expected field arithmetic and old word semantics agree')
