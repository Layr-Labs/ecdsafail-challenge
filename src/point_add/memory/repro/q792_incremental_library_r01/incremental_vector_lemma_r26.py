from pathlib import Path
import ast,datetime,hashlib,json,random
R=Path(__file__).resolve().parent;O=R/'incremental-vector-proof-r26';O.mkdir()
for name in ['incremental_census_r20.py','incremental_vector_census_r24.py']:
 tree=ast.parse((R/name).read_text());exec(compile(ast.Module(body=[x for x in tree.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),name,'exec'))
def evaluate(ops,x):
 for k,t,a,b in ops:
  if k==0 or ((x>>a&1)and(k==1 or(x>>b&1))):x^=1<<t
 return x
def value(poly,x):return sum((x&m)==m for m in poly)%2
rng=random.Random(7922026091326);cases=0;programs=0;read_cases=0
for case in range(1024):
 n=4+case%3;p=rng.randrange(n);a,b=rng.sample([i for i in range(n)if i!=p],2);c,d=rng.sample([i for i in range(n)if i!=p],2);D=[]
 for _ in range(1+case%24):
  k=rng.randrange(3);t,a1,b1=rng.sample(range(n),3);D.append((k,t,a1,b1))
 e={p:{(1<<a)|(1<<b)}}
 for k,t,a1,b1 in D:
  if k==1:add(e,t,e.get(a1,set()))
  elif k==2:add(e,t,mul({1<<a1},e.get(b1,set()))^mul({1<<b1},e.get(a1,set()))^mul(e.get(a1,set()),e.get(b1,set())))
  e={q:z for q,poly in e.items()if(z:=update(poly,(k,t,a1,b1)))}
 add(e,p,mul({1<<c}^e.get(c,set()),{1<<d}^e.get(d,set())))
 full=[(2,p,a,b)]+D+[(2,p,c,d)]
 for x in range(1<<n):
  y=evaluate(D,x);z=y
  for q,poly in e.items():z^=value(poly,y)<<q
  assert evaluate(full,x)==z;assert evaluate(full[::-1],z)==x;cases+=1
 programs+=1;read_cases+=any(k>=1 and a1==p or k==2 and b1==p for k,t,a1,b1 in D)
result={'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','programs':programs,'exhaustive_full_state_cases':cases,'programs_reading_initial_target':read_cases,'inverse':True,'initial_state':'arbitrary all wires, no clean premise','phase':'NCT only','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};(O/'result.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
