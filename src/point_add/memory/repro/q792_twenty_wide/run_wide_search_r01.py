from pathlib import Path
import hashlib,json,subprocess,os,datetime,collections
G=Path(__file__).resolve().parent;R=G.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert json.loads((R/'s02-wide-census.result.json').read_text())['status']=='PASS'
files=sorted((G/'wide-census-r01').glob('*.txt'));rows=[]
for p in files:
 lines=p.read_text().splitlines();n,k=map(int,lines[0].split());truth=lines[1];cubes=[tuple(map(int,x.split())) for x in lines[2:]];assert len(truth)==1<<n
 rows.append({'file':p.name,'n':n,'k':k,'truth':truth,'old_cubes':cubes})
inp=G/'wide-input-r01.txt'
with inp.open('x')as f:f.write(str(len(rows))+'\n'+'\n'.join(f"{x['n']} {x['k']} {x['truth']}" for x in rows)+'\n')
env=os.environ.copy();lib=R.parent/'intel-runtime/root/usr/lib/x86_64-linux-gnu';env['LD_LIBRARY_PATH']=str(lib)+':'+str(lib/'intel-opencl');env['OCL_ICD_VENDORS']=str(R.parent/'q792-gpu-20260912.sd8khklc/gpu/vendors')
manifest={'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sources':{str(p.relative_to(R)):sha(p) for p in files+[inp,G/'wide_search_r01.cpp',G/'wide_search_r01',R/'s02-wide-census.result.json',R/'s02-wide-census.manifest.json']},'functions':len(rows),'candidates':sum(1<<x['n'] for x in rows),'n_histogram':dict(collections.Counter(x['n'] for x in rows)),'policy':'both B50 score every polarity on full truth; CPU only validates selected output after GPU; no seed/EEA case inputs','environment':{k:env[k]for k in ['LD_LIBRARY_PATH','OCL_ICD_VENDORS']}}
with (G/'wide-search-manifest-r01.json').open('x') as f:json.dump(manifest,f,indent=2)
with (G/'wide-search-r01.log').open('x')as f:r=subprocess.run(['prlimit','--as=6000000000','timeout','600s',str(G/'wide_search_r01'),str(inp),str(G/'wide-scores-r01.txt')],env=env,stdout=f,stderr=subprocess.STDOUT)
assert r.returncode==0
log=(G/'wide-search-r01.log').read_text();assert 'both_B50=true' in log;print(log,flush=True)
scores=collections.defaultdict(list)
for line in (G/'wide-scores-r01.txt').read_text().splitlines():j,p,t,o=map(int,line.split());scores[j].append((t,o,p))
def cost(cubes,k):
 t=o=0
 for m,v in cubes:
  c=k+m.bit_count();a=0 if c<2 else 2*c-3;t+=a;o+=max(1,a)+2*(m^v).bit_count()
 return t,o
selected=[]
for j,x in enumerate(rows):
 old=cost(x['old_cubes'],x['k']);best=min(scores[j]);t,o,p=best
 a=[int(x['truth'][i^p]) for i in range(1<<x['n'])]
 for b in range(x['n']):
  for i in range(len(a)):
   if i>>b&1:a[i]^=a[i^(1<<b)]
 cubes=[(i,i&~p) for i,v in enumerate(a) if v];assert cost(cubes,x['k'])==(t,o)
 for addr,v in enumerate(x['truth']):assert sum((addr&m)==bits for m,bits in cubes)%2==int(v)
 if (t,o)<old and o<=old[1]*1.1+8:selected.append({**x,'polarity':p,'cubes':cubes,'old_T':old[0],'new_T':t,'old_proxy_ops':old[1],'new_proxy_ops':o})
proof={'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'GPU_POLARITY_SEARCH_AND_EXHAUSTIVE_SELECTED_TRUTH_PASS','both_B50':True,'functions':len(rows),'candidates':manifest['candidates'],'selected_count':len(selected),'selected':selected,'all_selected_full_truth_CPU_agreement':True,'manifest_sha256':sha(G/'wide-search-manifest-r01.json'),'scores_sha256':sha(G/'wide-scores-r01.txt'),'whole_gain':'UNMEASURED'}
with (G/'wide-selected-proof-r01.json').open('x')as f:json.dump(proof,f,indent=2)
print(json.dumps({k:v for k,v in proof.items()if k!='selected'},indent=2))
