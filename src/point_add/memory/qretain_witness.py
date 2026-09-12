"""One recorded scalar regression, no circuit or sample generation."""
import json
P=(1<<256)-(1<<32)-977
factor=int('a886fa97a6d9e5c7eb7f824b9302db27992d9862334845a199a1f8f4152dbc63',16)
x=min(factor,P-factor)
a,b,ca,cb,q,parity=P,x,0,1,0,1
old_widths=[22,22,22,22,22,18,18,22,22,22,20,22,21,21,21,20]
rows=[]
for step in range(338):
    before=q
    if 322<=step<=337:
        width=old_widths[step-322]
        rows.append(dict(step=step,q_before=hex(q),old_width=width,
            old_discarded=hex(q&~((1<<width)-1)),fixed_width=32,
            fixed_discarded=hex(q&~((1<<32)-1))))
    assert q>>32==0
    if a<b and q:
        j=(q&-q).bit_length()-1
        assert j<=31
        q^=1<<j;ca+=cb<<j
    if ca<cb:
        delta=a.bit_length()-b.bit_length()
        offset=int(delta>=0 and a<(b<<delta))
        j=delta-offset
        if j>=0:
            assert delta<=31 and j<=31
            a-=b<<j;q^=1<<j
    if q==0 and a!=0:a,b,ca,cb=b,a,cb,ca;parity^=1
    assert a*cb+b*(ca+q*cb)==P
    sign=-1 if parity else 1
    assert (a-sign*(ca+q*cb)*x)%P==0 and (b+sign*cb*x)%P==0
    assert q>>32==0
    if 322<=step<=337:rows[-1]['q_after']=hex(q)
assert rows[0]['q_after']=='0x200000'
assert all(int(r['q_before'],16)&(1<<21) for r in rows[1:])
assert rows[-1]['q_after']=='0x0'
first=next(r for r in rows if int(r['old_discarded'],16))
assert (first['step'],first['q_before'],first['old_discarded'])==(327,'0x232400','0x200000')
assert all(r['fixed_discarded']=='0x0' for r in rows)
print(json.dumps(dict(status='PASS scalar witness only',shot=1465,factor=hex(factor),
    first_old_loss=first,rows=rows,no_quantum_simulation=True,
    no_general_profile_success_claim=True),indent=2))
