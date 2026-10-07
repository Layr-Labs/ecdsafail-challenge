from pathlib import Path
import array,collections,datetime,hashlib,json,struct,random,bisect
R=Path(__file__).resolve().parent;O=R/'trial-r01';groups=json.loads((O/'groups.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def bits(x):
 while x:
  b=x&-x;yield b.bit_length()-1;x^=b
def commute(p,q):
 a,b,u=p;c,d,v=q
 return not ((a&v).bit_count()%2 or (b&v).bit_count()%2 or (c&u).bit_count()%2 or (d&u).bit_count()%2)
def quad_product(a,b,n):
 mask=(1<<n)-1;av=a&mask;bv=b&mask;q=0
 for i in bits(av|bv):q|=(((bv if av>>i&1 else 0)^(av if bv>>i&1 else 0))&~(1<<i))<<(n*i)
 l=(av&bv)^(bv if a>>n else 0)^(av if b>>n else 0)^((1<<n)if a>>n and b>>n else 0)
 return q,l
def rank(q,n):
 rows=[(q>>(n*i))&((1<<n)-1)for i in range(n)];piv={}
 for x in rows:
  while x and x.bit_length()-1 in piv:x^=piv[x.bit_length()-1]
  if x:piv[x.bit_length()-1]=x
 return len(piv)
def factor(q,n):
 result=[];lin=0;mask=(1<<n)-1
 while q:
  i=next(i for i in range(n)if q>>(n*i)&mask);b=q>>(n*i)&mask;j=next(bits(b));a=q>>(n*j)&mask
  z,l=quad_product(a,b,n);q^=z;lin^=l;result.append((a,b))
 return result,lin
def emit(p,n):
 a,b,u=p
 if not u:return []
 assert not ((a&u).bit_count()%2 or(b&u).bit_count()%2)
 r=next(bits(u));frame=[];mask=(1<<n)-1
 for i in bits(u^(1<<r)):
  frame.append([1,i,r,0]);a^=((a>>i)&1)<<r;b^=((b>>i)&1)<<r
 assert not(a>>r&1 or b>>r&1)
 av=a&mask;bv=b&mask;ca=a>>n;cb=b>>n;one=None
 if not av:
  if not ca:return []
  one=b
 elif not bv:
  if not cb:return []
  one=a
 elif av==bv:
  if ca!=cb:return []
  one=a
 middle=[]
 if one is not None:
  if one&mask:
   p=next(bits(one&mask))
   for i in bits((one&mask)^(1<<p)):frame.append([1,p,i,0])
   middle.append([1,r,p,0])
  if one>>n:middle.append([0,r,0,0])
 else:
  p=next(bits(av))
  for i in bits(av^(1<<p)):
   frame.append([1,p,i,0]);b^=((b>>p)&1)<<i
  q=next(bits((b&mask)&~(1<<p)))
  for i in bits((b&mask)^(1<<q)):frame.append([1,q,i,0])
  if ca:middle.append([0,p,0,0])
  if cb:middle.append([0,q,0,0])
  middle.append([2,r,p,q])
  if cb:middle.append([0,q,0,0])
  if ca:middle.append([0,p,0,0])
 return frame+middle+frame[::-1]
def cancel(ops):
 n=max(max(o[1:])for o in ops)+1 if ops else 0;rd=[[]for _ in range(n)];wr=[[]for _ in range(n)];same=collections.defaultdict(list);alive=[True]*len(ops)
 def last(s):
  while s and not alive[s[-1]]:s.pop()
  return s[-1]if s else -1
 for i,(k,t,a,b)in enumerate(ops):
  cs=tuple(sorted(([a]if k else[])+([b]if k==2 else[])));key=(k,t,cs);p=last(same[key])
  if p>=0 and last(rd[t])<p and all(last(wr[q])<p for q in cs):alive[p]=alive[i]=False
  else:
   same[key].append(i);wr[t].append(i)
   for q in cs:rd[q].append(i)
 return [o for i,o in enumerate(ops)if alive[i]]
def eval_ops(ops,x):
 for k,t,a,b in ops:x^=(1 if k==0 else(x>>a&1)if k==1 else((x>>a&1)&(x>>b&1)))<<t
 return x
weights={}
for j in range(4):
 vals=array.array('I');vals.frombytes((O/f'j{j}-weights.bin').read_bytes());indices=json.loads((O/f'j{j}-indices.json').read_text())
 for i,ix in enumerate(indices):weights[ix]=vals[i*256:i*256+256]
accepted=[];stats=collections.Counter();rng=random.Random(79220260913)
for ix,r in enumerate(groups):
 n=r['n'];d=r['d'];qs=r['basis'];projections=[];lookup={0:0}
 for co in range(1,1<<d):
  low=co&-co;q=lookup[co^low]^qs[low.bit_length()-1];lookup[co]=q;projections.append((weights[ix][co],q))
 piv={};chosen=[]
 for cost,q in sorted(projections):
  x=q
  while x and x.bit_length()-1 in piv:x^=piv[x.bit_length()-1]
  if x:piv[x.bit_length()-1]=x;chosen.append((q,cost))
 if sum(cost for _,cost in chosen)>=r['old_group_T']:stats['no_T_gain']+=1;continue
 piv={}
 for i,(q,cost)in enumerate(chosen):
  assert rank(q,n)==2*cost,'independent CPU rank must equal GPU selected weight'
  x=q;co=1<<i
  while x and x.bit_length()-1 in piv:
   y,z=piv[x.bit_length()-1];x^=y;co^=z
  assert x;piv[x.bit_length()-1]=(x,co)
 us=[0]*len(chosen)
 for out,q in enumerate(r['quad']):
  x=q;co=0
  while x:
   y,z=piv[x.bit_length()-1];x^=y;co^=z
  for i in bits(co):us[i]^=1<<out
 new=[];linear=r['lin'][:]
 for i,(q,cost)in enumerate(chosen):
  fs,l=factor(q,n);assert len(fs)==cost
  new.extend((a,b,us[i])for a,b in fs)
  for out in bits(us[i]):linear[out]^=l
 linear_groups=collections.defaultdict(int)
 for out,l in enumerate(linear):
  if l:linear_groups[l]^=1<<out
 new.extend((1<<n,l,u)for l,u in linear_groups.items())
 # Symbolic proof of every output polynomial, with constant and diagonal terms.
 checkq=[0]*n;checkl=[0]*n
 for a,b,u in new:
  q,l=quad_product(a,b,n)
  for out in bits(u):checkq[out]^=q;checkl[out]^=l
 assert checkq==r['quad'] and checkl==r['lin']
 if any(not commute(p,q)for p in new for q in new):stats['noncommuting_factorization']+=1;continue
 members=set(r['members']);end=max(members);ps=r['products']
 assert all(commute(ps[i],ps[j])for i in members for j in range(i+1,end+1))
 result=[]
 for i,p in enumerate(ps):
  if i==end:
   for z in new:result.extend(emit(z,n))
  elif i not in members:result.extend(emit(p,n))
 result.extend(r['linear']);result=cancel(result);new_T=sum(o[0]==2 for o in result)
 if new_T>=r['original_T']:stats['materialized_no_gain']+=1;continue
 ids=r['ids'];idx={q:i for i,q in enumerate(ids)};original=[[k,idx[t],idx[a]if k else 0,idx[b]if k==2 else 0]for k,t,a,b in r['original']]
 # Algebra above is the proof; directed and random checks guard emitter errors.
 inputs=list(range(1<<n))if n<=10 else [0,(1<<n)-1]+[1<<i for i in range(n)]+[rng.getrandbits(n)for _ in range(128)]
 for x in inputs:
  y=eval_ops(original,x);assert eval_ops(result,x)==y,(ix,n,x);assert eval_ops(result[::-1],y)==x
 stats['proved_positive_windows']+=1;stats['unrestricted_window_T_gain']+=r['original_T']-new_T
 if len(result)>len(original)+len(original)//3+16:stats['N_cap_rejected']+=1;continue
 row={'group_index':ix,'clock':r['clock'],'first':r['first'],'width':r['width'],'n':n,'members':r['members'],'old_T':r['original_T'],'new_T':new_T,'saving_T':r['original_T']-new_T,'N_delta':len(result)-len(original),'replacement':[[k,ids[t],ids[a]if k else 0,ids[b]if k==2 else 0]for k,t,a,b in result],'normalized_replacement':result,'proof':'exact affine conjugation; all intervening commutations; full Boolean quadratic vector identity including diagonal/linear/constants; mutually commuting synthesis; independent CPU selected-rank confirmation','guard_checks':len(inputs)}
 accepted.append(row)
(O/'proved-replacements.json').write_text(json.dumps(accepted,separators=(',',':')))
F=Path(json.loads((R/'PLAN.json').read_text())['base'])/'gpu/fixtures-r01-whole-step';D=O/'rewritten';D.mkdir();selected=[];metrics=[]
for j in range(4):
 rows=sorted([r for r in accepted if r['clock']==j],key=lambda r:(r['first']+r['width'],r['first']));ends=[r['first']+r['width']for r in rows];best=[(0,0)];back=[]
 for i,r in enumerate(rows):
  pred=bisect.bisect_right(ends,r['first'],0,i);take=(best[pred][0]+r['saving_T'],best[pred][1]-r['N_delta']);use=take>best[-1];best.append(take if use else best[-1]);back.append((use,pred))
 chosen=[];i=len(rows)
 while i:
  use,pred=back[i-1]
  if use:chosen.append(rows[i-1]);i=pred
  else:i-=1
 chosen.sort(key=lambda r:r['first']);selected.extend(chosen);ops=list(struct.iter_unpack('<4I',(F/f'j{j}-ops.bin').read_bytes()));out=[];pos=0
 for r in chosen:out.extend(ops[pos:r['first']]);out.extend(r['replacement']);pos=r['first']+r['width']
 out.extend(ops[pos:]);(D/f'j{j}-ops.bin').write_bytes(b''.join(struct.pack('<4I',*o)for o in out));(D/f'j{j}-cases.bin').write_bytes((F/f'j{j}-cases.bin').read_bytes())
 metrics.append({'clock':j,'selected':len(chosen),'saving_T':sum(o[0]==2 for o in ops)-sum(o[0]==2 for o in out),'N_delta':len(out)-len(ops)})
(O/'selected-replacements.json').write_text(json.dumps(selected,separators=(',',':')))
result={'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'SYMBOLIC_PROVED_GPU_MATERIALIZATION_PENDING','script_sha256':sha(Path(__file__)),'groups_sha256':sha(O/'groups.json'),'GPU_log_sha256':sha(O/'gpu.log'),'stats':dict(stats),'proved_replacements':len(accepted),'nonoverlapping':len(selected),'four_template_metrics':metrics,'saving_T':sum(r['saving_T']for r in metrics),'N_delta':sum(r['N_delta']for r in metrics),'whole_gain':'UNMEASURED','extra_qubits':0}
(O/'synthesis-result.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
