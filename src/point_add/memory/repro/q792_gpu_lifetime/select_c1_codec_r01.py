from pathlib import Path
import json,hashlib,datetime
G=Path(__file__).resolve().parent;R=G.parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((G/'c1-codec-search-manifest-r01.json').read_text());assert all(sha(R/n)==h for n,h in m['hashes'].items())
cc=lambda n:0 if n==0 else 1 if n==1 else 4 if n==2 else 2*n
tof=lambda n:0 if n<2 else 2*n-3
selected=[];n=0
for line in (G/'c1-codec-scores-r01.tsv').read_text().splitlines():
 v=list(map(int,line.split()));assert len(v)==38;i=v[0];meta=v[1];hist=v[2:34];old,new,policy,cached=v[34:];widths=[d for d,k in enumerate(hist)for _ in range(k)]
 # Independently verify GPU costs and chosen minimum, never substitute CPU choices.
 costs=[min(sum(cc(meta+d) for d in widths),2*cc(meta)+2*sum(tof(1+d) for d in widths)),2*tof(1+meta)+sum(tof(1+d)for d in widths),sum(tof(1+meta+d)for d in widths)]
 assert costs[0]==old and costs[policy]==new==min(costs) and costs[1]==cached;n+=1
 if policy:selected.append((meta,widths,policy,old,new))
p=R/'workspace/src/point_add/trailmix_port/inversion/q792_c1_codec_plans_r01.rs'
with p.open('x')as f:
 f.write('//! GPU-selected codec policy on C1-clean C4/C5, including preparation and restoration.\npub(super) const POLICIES:&[(usize,&[usize],u8)]=&[\n')
 for meta,ds,policy,old,new in selected:f.write(f'({meta},&{ds},{policy}), // {old} -> {new} T\n')
 f.write('];\n')
z={'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'GPU_SELECTED_INDEPENDENT_COST_CHECK_PASS','both_B50_used':True,'GPU_groups':n,'GPU_candidates':3*n,'CPU_selected_checks':n,'improving_groups':len(selected),'unweighted_gain':sum(x[3]-x[4]for x in selected),'whole_gain_measured':False,'emitted_plan_path':str(p.relative_to(R/'workspace')),'emitted_plan_sha256':sha(p),'hashes':{p.name:sha(p)for p in [G/'c1_codec_search_r01.cpp',G/'c1_codec_search_r01',G/'c1-codec-input-r01.txt',G/'c1-codec-scores-r01.tsv',G/'c1-codec-search-manifest-r01.json',G/'c1-codec-search-r01.log']}}
with (G/'c1-codec-selected-proof-r01.json').open('x')as f:json.dump(z,f,indent=2)
print(json.dumps(z,indent=2))
