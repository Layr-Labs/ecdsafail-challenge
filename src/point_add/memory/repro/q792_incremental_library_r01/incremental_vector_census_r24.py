from pathlib import Path
import ast,array,collections,datetime,hashlib,json,struct
R=Path(__file__).resolve().parent;F=Path(json.loads((R/'PLAN.json').read_text())['base'])/'gpu/fixtures-r01-whole-step';O=R/'incremental-vector-r24';O.mkdir();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
tree=ast.parse((R/'incremental_census_r20.py').read_text());exec(compile(ast.Module(body=[x for x in tree.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'r20-pure-functions','exec'))
def add(e,t,v):
 z=e.get(t,set())^v
 if z:e[t]=z
 elif t in e:del e[t]
def bound(e):
 if len(e)>24 or sum(map(len,e.values()))>256:raise OverflowError
 if any(len(z)>128 or any(m.bit_count()>12 for m in z)for z in e.values()):raise OverflowError
stats=collections.Counter();candidates=[];byclock=[]
for j in range(4):
 ops=list(struct.iter_unpack('<4I',(F/f'j{j}-ops.bin').read_bytes()));lastread=[-1]*564;recent=[[]for _ in range(564)];pairs=[]
 for i,(k,t,a,b)in enumerate(ops):
  if k>=1:lastread[a]=i
  if k==2:lastread[b]=i
  if k==2:
   recent[t]=[p for p in recent[t]if i-p<=512][-8:];picks=set(recent[t][-1:]);equal=[p for p in recent[t]if set(ops[p][2:])=={a,b}]
   if equal:picks.add(equal[-1])
   for p in sorted(picks):
    if lastread[t]>p:pairs.append((p,i))
   recent[t].append(i)
 local=collections.Counter();local['pairs_with_target_read']=len(pairs)
 for first,last in pairs:
  _,p,a,b=ops[first];e={p:{(1<<a)|(1<<b)}}
  try:
   for k,t,a,b in ops[first+1:last]:
    if k==1:add(e,t,e.get(a,set()))
    elif k==2:
     ea=e.get(a,set());eb=e.get(b,set());v=mul({1<<a},eb)^mul({1<<b},ea)^mul(ea,eb);add(e,t,v)
    e={q:z for q,poly in e.items()if(z:=update(poly,(k,t,a,b)))};bound(e)
   _,p,a,b=ops[last];add(e,p,mul({1<<a}^e.get(a,set()),{1<<b}^e.get(b,set())));bound(e)
  except OverflowError:local['symbolic_budget_exceeded']+=1;continue
  local['exact_vector_deltas']+=1
  degree=max((m.bit_count()for z in e.values()for m in z),default=0);local['degree_'+str(degree)]+=1
  if degree>2:continue
  quads={tuple(sorted(m for m in z if m.bit_count()==2))for z in e.values()};quads.discard(())
  if len(quads)>1:local['multiple_quadratic_components_no_one_T']+=1;continue
  support=sum(1<<q for q in e)
  for z in e.values():
   for m in z:support|=m
  ids=list(positions(support));n=len(ids)
  if not n:ids=[p];n=1
  if n>64:local['support_over64']+=1;continue
  idx={q:i for i,q in enumerate(ids)};matrix=[0]*64;u=0;c=0;linear=[1<<i for i in range(n)];normalized_delta={}
  for q,z in e.items():
   at=idx[q];normalized_delta[at]=sorted(sum(1<<idx[i]for i in positions(m))for m in z)
   if any(m.bit_count()==2 for m in z):u|=1<<at
   for m in z:
    if m.bit_count()==1:linear[at]^=1<<idx[m.bit_length()-1]
    elif m==0:c^=1<<at
  for m in next(iter(quads),()):
   a,b=[idx[q]for q in positions(m)];matrix[a]^=1<<b;matrix[b]^=1<<a
  candidates.append({'clock':j,'first':first,'last':last,'span':last-first+1,'target':p,'n':n,'ids':ids,'delta':normalized_delta,'matrix':matrix,'direction':u,'linear':linear,'constant':c,'premise':'all inputs arbitrary; target reads allowed; full vector correction propagated symbolically through each interior NCT'})
 byclock.append({'clock':j,**local});stats.update(local);print('CLOCK',j,dict(local),flush=True)
(O/'quadratic-candidates.json').write_text(json.dumps(candidates,separators=(',',':')))
for j in range(4):
 rows=[r for r in candidates if r['clock']==j];data=array.array('Q')
 for r in rows:data.extend([r['n'],1]+r['matrix']+[0]*(7*64))
 assert rows;(O/f'j{j}-matrices.bin').write_bytes(data.tobytes())
result={'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'VECTOR_CENSUS_GPU_PENDING','base_T':910644642,'base_Q':792,'stats':dict(stats),'by_clock':byclock,'quadratic_candidates':len(candidates),'script_sha256':sha(Path(__file__)),'source_fixtures':{p.name:sha(p)for p in F.glob('*ops.bin')},'scope':'four full-width templates; not whole circuit'};(O/'census.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
