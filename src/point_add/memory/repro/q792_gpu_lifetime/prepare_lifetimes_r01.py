from pathlib import Path
import re,json,datetime,hashlib
R=Path(__file__).resolve().parent.parent
W=R/'workspace/src/point_add/trailmix_port/inversion'
text=(W/'metadata_entry_head5.rs').read_text().split('const A_SUPPORTS:',1)[1]
supports=[tuple(map(int,x))for x in re.findall(r'\((\d+),(\d+)\)',text)][:202]
text=(W/'shared_step.rs').read_text().split('const SCHEDULE_SUPPORTS:',1)[1]
steps=[tuple(map(int,x))for x in re.findall(r'\((\d+),\s*(\d+)\)',text)][:202]
assert len(supports)==len(steps)==202
ts=[(a,c,s)for a in range(4)for c in range(4)for s in range(4)if a+c+s<=4]
assert len(ts)==32
# Exact mapping of every admitted original rank under the existing A-high chart.
next_code=[0,16,24,28];mapping={}
for i,t in enumerate(ts):
    if sum(t)==4 and (t[1]==0 or t[2]==0):continue
    mapping[t]=next_code[t[0]];next_code[t[0]]+=1
assert next_code==[13,24,28,29]
rows=[];proof=[]
for block,((lo,hi),(_,end)) in enumerate(zip(supports,steps)):
    states=[]
    for a in range(lo,min(hi,252)):
        for t,code in mapping.items():
            if t[0]!=a//64:continue
            # There exists C>=2,S>=3 in these coarse bins iff their minima fit.
            if a+max(2,t[1]*64)+max(3,t[2]*64)<=256:states.append(code|((a&63)<<5))
    assert states
    fixed=2047;value=states[0]
    for x in states:fixed&=~(x^value)
    value&=fixed
    proof.append({'block':block,'support':[lo,hi],'end':min(end,254),'admitted_metadata_states':len(states),'fixed_mask':fixed,'fixed_value':value,'free_wires':[i for i in range(11)if fixed>>i&1]})
    for wire in range(11):
        for split in range(7):rows.append((block,lo,hi,min(end,254),fixed,value,wire,split))
with (R/'gpu/lifetime-input-r01.txt').open('x') as f:
    f.write(str(len(rows))+'\n')
    for row in rows:f.write(' '.join(map(str,row))+'\n')
with (R/'gpu/lifetime-domain-proof-r01.json').open('x') as f:json.dump({'status':'EXACT_ADMITTED_STATE_CENSUS','assumptions':['general T10: C>=2,S>=3,A+C+S<=256','analytic A_SUPPORTS','existing exact A-high chart'],'states':proof,'candidate_scores_evaluated_on_CPU':False},f,indent=2)
print(json.dumps({'jobs':len(rows),'blocks_with_clean_rail':sum(bool(x['fixed_mask'])for x in proof),'total_admitted_states':sum(x['admitted_metadata_states']for x in proof),'candidates_evaluated':False}))
