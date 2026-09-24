from pathlib import Path
import array,ast,bisect,collections,datetime,hashlib,json,os,struct,subprocess,random
R=Path(__file__).resolve().parent;O=R/'incremental-r20';F=Path(json.loads((R/'PLAN.json').read_text())['base'])/'gpu/fixtures-r01-whole-step';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Copy only pure proved algebra and emitter functions; do not import a trial driver.
source=R/'synthesize_joint_r01.py';tree=ast.parse(source.read_text());names={'bits','quad_product','rank','factor','emit','cancel','eval_ops'}
exec(compile(ast.Module(body=[x for x in tree.body if isinstance(x,ast.FunctionDef)and x.name in names],type_ignores=[]),str(source),'exec'))
env=os.environ.copy();lr=R.parent/'intel-runtime/root/usr/lib/x86_64-linux-gnu';env['LD_LIBRARY_PATH']=str(lr)+':'+str(lr/'intel-opencl');env['OCL_ICD_VENDORS']=str(R.parent/'q792-gpu-20260912.sd8khklc/gpu/vendors')
with(O/'gpu-rank.log').open('x')as f:p=subprocess.run(['prlimit','--as=4000000000','timeout','180s',str(R/'gpu_joint_r01'),str(O),str(O)],env=env,stdout=f,stderr=subprocess.STDOUT)
assert p.returncode==0;assert 'BOTH_B50'in(O/'gpu-rank.log').read_text();print((O/'gpu-rank.log').read_text(),flush=True)
candidates=json.loads((O/'quadratic-candidates.json').read_text());accepted=[];stats=collections.Counter()
def multiply(a,b):
 out=set()
 for x in a:
  for y in b:
   m=x|y
   if m in out:out.remove(m)
   else:out.add(m)
 return out
def prove_synthesis(ops,n,delta):
 state=[{1<<i}for i in range(n)]
 for k,t,a,b in ops:state[t]^=({0}if k==0 else state[a]if k==1 else multiply(state[a],state[b]))
 for i in range(n):assert state[i]==({1<<i}^delta if i==n-1 else{1<<i}),(i,ops,delta)
for j in range(4):
 rows=[r for r in candidates if r['clock']==j];weights=array.array('I');weights.frombytes((O/f'j{j}-weights.bin').read_bytes());assert len(weights)==256*len(rows)
 for ix,r in enumerate(rows):
  n=r['n'];q=sum(v<<(n*i)for i,v in enumerate(r['matrix'][:n]));cost=weights[ix*256+1];assert rank(q,n)//2==cost;stats['GPU_CPU_rank_agreements']+=1
  if cost>=2:stats['no_T_gain']+=1;continue
  fs,lin=factor(q,n);assert len(fs)==cost;lin^=r['linear'];ids=r['ids']+[r['target']];nn=n+1
  # Last coordinate is the accumulation target; it is not in delta support.
  assert r['target']not in r['ids'];new=[]
  for a,b in fs:new.extend(emit((a,b,1<<n),nn))
  for i in bits(lin):new.append([0,n,0,0]if i==n else[1,n,i,0])
  new=cancel(new);nd=len(new)-2
  if nd>64:stats['N_cap_rejected']+=1;continue
  idx={q:i for i,q in enumerate(ids)};delta={sum(1<<idx[b]for b in bits(m))for m in r['delta']}
  prove_synthesis(new,nn,delta);stats['CPU_full_state_proofs']+=1
  normalized=new;new=[[k,ids[t],ids[a]if k else 0,ids[b]if k==2 else 0]for k,t,a,b in new]
  accepted.append({**r,'new':new,'normalized_new':normalized,'new_T':cost,'saving_T':2-cost,'N_delta':nd,'proof':'Exact inverse-coordinate ANF through every interior gate; accumulation target not read; CPU full symbolic synthesis state equality incl all restored controls; GPU/CPU exact quadratic rank equality'})
print('ACCEPTED',len(accepted),dict(stats),flush=True)
(O/'proved-replacements.json').write_text(json.dumps(accepted,separators=(',',':')))
D=O/'rewritten';D.mkdir();selected=[];metrics=[]
for j in range(4):
 rows=sorted([r for r in accepted if r['clock']==j],key=lambda r:(r['last']+1,r['first']));ends=[r['last']+1 for r in rows];best=[(0,0)];back=[]
 for i,r in enumerate(rows):
  pred=bisect.bisect_right(ends,r['first'],0,i);take=(best[pred][0]+r['saving_T'],best[pred][1]-r['N_delta']);use=take>best[-1];best.append(take if use else best[-1]);back.append((use,pred))
 chosen=[];i=len(rows)
 while i:
  use,pred=back[i-1]
  if use:chosen.append(rows[i-1]);i=pred
  else:i-=1
 chosen.sort(key=lambda r:r['first']);selected.extend(chosen);ops=list(struct.iter_unpack('<4I',(F/f'j{j}-ops.bin').read_bytes()));out=[];pos=0
 for r in chosen:out.extend(ops[pos:r['first']]);out.extend(ops[r['first']+1:r['last']]);out.extend(r['new']);pos=r['last']+1
 out.extend(ops[pos:]);(D/f'j{j}-ops.bin').write_bytes(b''.join(struct.pack('<4I',*o)for o in out));(D/f'j{j}-cases.bin').write_bytes((F/f'j{j}-cases.bin').read_bytes())
 metrics.append({'clock':j,'selected':len(chosen),'saving_T':sum(o[0]==2 for o in ops)-sum(o[0]==2 for o in out),'N_delta':len(out)-len(ops),'same_control_pairs':sum(r['same_controls']for r in chosen),'nonlinear_input_update_pairs':sum(r['nonlinear_input_update']for r in chosen),'beyond128_pairs':sum(r['span']>128 for r in chosen)})
(O/'selected-replacements.json').write_text(json.dumps(selected,separators=(',',':')))
result={'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'EXACT_SYMBOLIC_PROVED_GPU_MATERIALIZATION_PENDING','script_sha256':sha(Path(__file__)),'algebra_source_sha256':sha(source),'census_sha256':sha(O/'census.json'),'rank_GPU_log_sha256':sha(O/'gpu-rank.log'),'stats':dict(stats),'proved_replacements':len(accepted),'selected':len(selected),'metrics':metrics,'saving_T':sum(r['saving_T']for r in metrics),'N_delta':sum(r['N_delta']for r in metrics),'whole_gain':'UNMEASURED','extra_qubits':0}
(O/'synthesis-result.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2),flush=True)
with(O/'rewritten-gpu.log').open('x')as f:p=subprocess.run(['prlimit','--as=4000000000','timeout','180s',str(F.parent/'phase_routing_assess_r01'),str(D)],env=env,stdout=f,stderr=subprocess.STDOUT)
assert p.returncode==0;log=(O/'rewritten-gpu.log').read_text();print(log,flush=True);assert log.count('errors=0')==4 and 'both_B50=true'in log
result.update(status='EXACT_SYMBOLIC_AND_BOTH_B50_FULL_TEMPLATE_PASS',GPU_cases=43008,GPU_errors=0,rewritten_GPU_log_sha256=sha(O/'rewritten-gpu.log'))
(O/'result.json').write_text(json.dumps(result,indent=2))
