"""Exact inverse-coordinate Boolean differences across arbitrary NCT interiors.
All inputs arbitrary. The accumulating target must not be read by the interior.
"""
from pathlib import Path
import array,collections,datetime,hashlib,json,struct,ast
R=Path(__file__).resolve().parent;F=Path(json.loads((R/'PLAN.json').read_text())['base'])/'gpu/fixtures-r01-whole-step';O=R/'incremental-r20';O.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def toggle(s,v):
 if v in s:s.remove(v)
 else:s.add(v)
def update(poly,op):
 k,t,a,b=op;v=1<<t;term=0 if k==0 else(1<<a)if k==1 else(1<<a)|(1<<b)
 out=poly.copy()
 for m in poly:
  if m&v:toggle(out,(m^v)|term)
 if len(out)>128 or any(x.bit_count()>12 for x in out):raise OverflowError
 return out
def mul(a,b):
 out=set()
 for x in a:
  for y in b:toggle(out,x|y)
 if len(out)>512:raise OverflowError
 return out
def positions(x):
 while x:
  b=x&-x;yield b.bit_length()-1;x^=b
stats=collections.Counter();candidates=[];census=[]
for j in range(4):
 ops=list(struct.iter_unpack('<4I',(F/f'j{j}-ops.bin').read_bytes()));lastread=[-1]*564;recent=[[]for _ in range(564)];pairs=[]
 for i,(k,t,a,b)in enumerate(ops):
  if k>=1:lastread[a]=i
  if k==2:lastread[b]=i
  if k==2:
   prior=[p for p in recent[t]if p>lastread[t] and i-p<=8192];recent[t]=prior[-8:]
   picks=set(prior[-1:])
   equal=[p for p in prior if set(ops[p][2:])=={a,b}]
   if equal:picks.add(equal[-1])
   for p in sorted(picks):pairs.append((p,i))
   recent[t].append(i)
 local=collections.Counter();eligible=[]
 for pos,(first,last)in enumerate(pairs):
  k,p,a,b=ops[first];_,_,c,d=ops[last];left={1<<a};right={1<<b};same={a,b}=={c,d};local['pairs']+=1;local['same_control_pairs']+=same
  if last-first>128:local['beyond128_pairs']+=1
  nonlinear=False
  try:
   for op in ops[first+1:last]:
    assert not(op[0]>=1 and op[2]==p or op[0]==2 and op[3]==p)
    if op[0]==2 and any(m>>op[1]&1 for m in left|right):nonlinear=True
    left=update(left,op);right=update(right,op)
   delta=mul(left,right);toggle(delta,(1<<c)|(1<<d))
  except OverflowError:local['symbolic_budget_exceeded']+=1;continue
  local['exact_deltas']+=1;local['nonlinear_input_updates']+=nonlinear
  degree=max((x.bit_count()for x in delta),default=0);local['delta_degree_'+str(degree)]+=1
  eligible.append((first,last))
  if degree>2:continue
  support=0
  for m in delta:support|=m
  ids=list(positions(support));n=len(ids)
  if n>64:local['over64_delta_support']+=1;continue
  idx={q:i for i,q in enumerate(ids)};matrix=[0]*64;lin=0
  for m in delta:
   bs=list(positions(m))
   if len(bs)==2:u,v=map(idx.get,bs);matrix[u]^=1<<v;matrix[v]^=1<<u
   elif bs:lin^=1<<idx[bs[0]]
   else:lin^=1<<n
  candidates.append({'clock':j,'first':first,'last':last,'span':last-first+1,'target':p,'old_controls':[a,b],'new_controls':[c,d],'same_controls':same,'nonlinear_input_update':nonlinear,'left':sorted(left),'right':sorted(right),'delta':sorted(delta),'ids':ids,'n':n,'matrix':matrix,'linear':lin})
 # Interval disjoint repeated pairs: a conservative count without double counting gates.
 end=-1;disjoint=0;allendpoints=set()
 for first,last in eligible:
  allendpoints.update((first,last))
  if first>end:disjoint+=1;end=last
 local['exact_delta_unique_endpoint_T']=len(allendpoints);local['interval_disjoint_pair_count']=disjoint;local['interval_disjoint_pair_T']=2*disjoint
 local['template_T']=sum(o[0]==2 for o in ops);local['template_N']=len(ops)
 census.append({'clock':j,**local});stats.update(local);print('CLOCK',j,dict(local),flush=True)
(O/'quadratic-candidates.json').write_text(json.dumps(candidates,separators=(',',':')))
for j in range(4):
 rows=[r for r in candidates if r['clock']==j];data=array.array('Q')
 for r in rows:data.extend([r['n'],1]+r['matrix']+[0]*(7*64))
 assert rows
 (O/f'j{j}-matrices.bin').write_bytes(data.tobytes())
result={'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'base_Q':792,'base_T':910644642,'source_fixtures':{p.name:sha(p)for p in F.glob('*ops.bin')},'script_sha256':sha(Path(__file__)),'class':'pairs of CCX accumulation endpoints; no reads of accumulation target in interior; up to8192 distance,8 recent endpoint history; exact inverse-coordinate polynomials','proof':'all inputs, no clean-wire/reachability premise, full-state D preserved; delta=f_old(D^-1(y)) XOR f_new(y)','scope':'four full-width templates, not whole circuit','quadratic_candidates':len(candidates),'stats':dict(stats),'by_clock':census,'status':'CENSUS_ONLY_GPU_SCORING_PENDING'}
(O/'census.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
