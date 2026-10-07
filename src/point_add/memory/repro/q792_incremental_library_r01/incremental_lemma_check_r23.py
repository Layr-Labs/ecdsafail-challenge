from pathlib import Path
import ast,datetime,hashlib,json,random
R=Path(__file__).resolve().parent;O=R/'incremental-proof-r23';O.mkdir();tree=ast.parse((R/'incremental_census_r20.py').read_text());exec(compile(ast.Module(body=[x for x in tree.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'r20-pure-functions','exec'))
def evaluate(ops,x):
 for k,t,a,b in ops:
  if k==0 or ((x>>a&1)and(k==1 or(x>>b&1))):x^=1<<t
 return x
def poly(poly,x):return sum((x&m)==m for m in poly)%2
example=[[2,2,0,1],[1,0,3,0],[2,2,0,1]];replacement=[[1,0,3,0],[2,2,3,1]]
for x in range(16):assert evaluate(example,x)==evaluate(replacement,x)
rng=random.Random(7922026091323);cases=0
for case in range(512):
 n=4+case%5;p=n-1;a,b=rng.sample(range(p),2);c,d=rng.sample(range(p),2);D=[]
 for _ in range(1+case%40):
  k=rng.randrange(3);cs=rng.sample(range(p),2);targets=[q for q in range(n)if q not in cs];t=rng.choice(targets);D.append((k,t,*cs))
 left={1<<a};right={1<<b}
 for op in D:left=update(left,op);right=update(right,op)
 delta=mul(left,right);toggle(delta,(1<<c)|(1<<d));full=[(2,p,a,b)]+D+[(2,p,c,d)]
 for x in range(1<<n):
  y=evaluate(D,x);z=y^(poly(delta,y)<<p);assert evaluate(full,x)==z;assert evaluate(full[::-1],z)==x;cases+=1
result={'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','example_all_inputs':16,'independent_direct_simulation_programs':512,'exhaustive_full_state_cases':cases,'inverse':True,'premise':'p is never a control in D, arbitrary initial p and every other wire','phase':'NCT permutations, no phase gates','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};(O/'result.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
