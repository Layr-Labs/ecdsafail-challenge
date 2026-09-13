from pathlib import Path
import re,json,hashlib,datetime,collections
G=Path(__file__).resolve().parent;R=G.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
z=json.loads((R/'s04-census.result.json').read_text());assert z['status']=='PASS'
log=R/'s04-census.log';rows=[]
for m,ds in re.findall(r'C1_CODEC_CENSUS meta=(\d+) widths=(\[[^\n]*\])',log.read_text()):
 ds=json.loads(ds);assert all(0<=d<32 for d in ds);h=collections.Counter(ds);rows.append([int(m)]+[h[d]for d in range(32)])
rows=sorted(set(map(tuple,rows)));assert len(rows)>1
p=G/'c1-codec-input-r01.txt'
with p.open('x')as f:f.write(str(len(rows))+'\n'+'\n'.join(' '.join(map(str,row))for row in rows)+'\n')
z={'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PRE_EXECUTION_IDENTITIES','jobs':len(rows),'candidates_per_group':3,'rule':'C1 C4/C5 clean across codec; factor or direct MCX with one clean rail; arbitrary outside-C1 codec U cancels literal inverse around identity arithmetic','hashes':{str(p.relative_to(R)):sha(p)for p in [G/'c1_codec_search_r01.cpp',G/'c1_codec_search_r01',G/'c1-codec-input-r01.txt',R/'s04-census.log',R/'s04-census.manifest.json',R/'s04-census.result.json']}}
with (G/'c1-codec-search-manifest-r01.json').open('x')as f:json.dump(z,f,indent=2)
print('PREPARED',len(rows),'groups')
