from pathlib import Path
import json,struct,hashlib,collections,datetime
S=Path(__file__).resolve().parent;R=S.parent;O=S/'unconditional-r09';I=S/'fragments-r06';rows=json.loads((I/'windows.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();library={};rejected=[];eligible=0

def factor(q,n):
 products=[]
 while True:
  edges=[m for m in range(1<<n)if m.bit_count()==2 and(q>>m&1)]
  if not edges:break
  e=edges[0];i=(e&-e).bit_length()-1;j=(e^(1<<i)).bit_length()-1
  a=sum(1<<k for k in range(n)if k!=j and q>>((1<<j)|(1<<k))&1);b=sum(1<<k for k in range(n)if k!=i and q>>((1<<i)|(1<<k))&1)
  product=0
  for x in range(n):
   for y in range(n):
    if a>>x&1 and b>>y&1:product^=1<<((1<<x)|(1<<y))
  q^=product;products.append((a,b));assert len(products)<=n//2
 return products,sum(((q>>(1<<i))&1)<<i for i in range(n))
def linear_reduce(columns,n):
 rows=[sum(((columns[j]>>i)&1)<<j for j in range(n))for i in range(n)];ops=[]
 for i in range(n):
  pivot=next((j for j in range(i,n)if rows[j]>>i&1),None)
  if pivot is None:return None
  if pivot!=i:
   for t,a in [(i,pivot),(pivot,i),(i,pivot)]:rows[t]^=rows[a];ops.append([1,t,a,0])
  for j in range(n):
   if j!=i and rows[j]>>i&1:rows[j]^=rows[i];ops.append([1,j,i,0])
 assert rows==[1<<i for i in range(n)];return ops

def transvection(a,b,v,n):
 assert (a&v).bit_count()%2==0 and(b&v).bit_count()%2==0
 r=(v&-v).bit_length()-1;frame=[]
 for i in range(n):
  if i!=r and v>>i&1:
   frame.append([1,i,r,0]);a^=((a>>i)&1)<<r;b^=((b>>i)&1)<<r
 assert not(a>>r&1 or b>>r&1)
 p=(a&-a).bit_length()-1
 for i in range(n):
  if i!=p and a>>i&1:frame.append([1,p,i,0]);b^=((b>>p)&1)<<i
 q=next(i for i in range(n)if i!=p and b>>i&1)
 for i in range(n):
  if i!=q and b>>i&1:frame.append([1,q,i,0])
 return frame+[[2,r,p,q]]+frame[::-1]
def eval_ops(ops,x):
 for k,t,a,b in ops:x^=(1 if k==0 else(x>>a&1)if k==1 else((x>>a&1)&(x>>b&1)))<<t
 return x
for j in range(4):
 data=(O/f'j{j}-classification.bin').read_bytes();vals=struct.unpack('<'+str(len(data)//4)+'I',data);indices=json.loads((I/f'j{j}-indices.json').read_text())
 for k,ri in enumerate(indices):
  record=vals[k*516:(k+1)*516];n,old_t,ok,u=record[:4]
  if not ok:continue
  eligible+=1;truth=list(record[4:4+(1<<n)]);anf=record[260:260+(1<<n)];q=sum(1<<m for m in range(1<<n)if m.bit_count()==2 and anf[m]);products,lin=factor(q,n);columns=[anf[1<<i]^(u if lin>>i&1 else 0)for i in range(n)];red=linear_reduce(columns,n)
  if red is None:rejected.append([ri,'singular_linear_part']);continue
  v=u
  for _,t,a,_ in red:v^=((v>>a)&1)<<t
  if any((a&v).bit_count()%2 or(b&v).bit_count()%2 for a,b in products):rejected.append([ri,'product_changes_own_controls']);continue
  candidate=[]
  for a,b in products:candidate.extend(transvection(a,b,v,n))
  candidate.extend(red[::-1]);candidate.extend([0,i,0,0]for i in range(n)if anf[0]>>i&1)
  # Exact adjacent cancellations do not use reachability.
  stack=[]
  for op in candidate:
   if stack and stack[-1]==op:stack.pop()
   else:stack.append(op)
  candidate=stack;new_t=sum(o[0]==2 for o in candidate)
  if new_t>=old_t:rejected.append([ri,'no_T_gain']);continue
  original=rows[ri]['pattern'][1]
  assert [eval_ops(original,x)for x in range(1<<n)]==truth,'GPU truth disagrees with independent CPU'
  assert [eval_ops(candidate,x)for x in range(1<<n)]==truth,'synthesis all-state mismatch'
  assert [eval_ops(candidate[::-1],truth[x])for x in range(1<<n)]==list(range(1<<n))
  key=json.dumps({'n':n,'roles':['arbitrary_inout']*n,'contract':True,'truth':truth},separators=(',',':'));digest=hashlib.sha256(key.encode()).hexdigest();entry=library.get(digest)
  if entry is None:entry={'key':json.loads(key),'full_key_sha256':digest,'replacement':candidate,'new_T':new_t,'new_N':len(candidate),'observed_instances':[],'proof':'independent complete truth and inverse, every wire included','GPU_replacement_assessment':'PENDING'};library[digest]=entry
  entry['observed_instances'].append({'window_index':ri,'clock':j,'op_index':rows[ri]['occurrence'][1],'old_T':old_t,'saving_T':old_t-new_t})
with(O/'library-cpu-confirmed.json').open('x')as f:json.dump(library,f,indent=2)
result={'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'eligible':eligible,'unique_functions':len(library),'proved_instances':sum(len(v['observed_instances'])for v in library.values()),'rejected':rejected,'source_sha256':sha(Path(__file__)),'GPU_original_function_log_sha256':sha(O/'gpu.log'),'library_sha256':sha(O/'library-cpu-confirmed.json'),'replacement_GPU_assessment':'PENDING','whole_gain':'UNMEASURED'}
with(O/'synthesis-result.json').open('x')as f:json.dump(result,f,indent=2)
print(json.dumps({k:v for k,v in result.items()if k!='rejected'},indent=2));print('REJECTIONS',collections.Counter(r[1]for r in rejected))
