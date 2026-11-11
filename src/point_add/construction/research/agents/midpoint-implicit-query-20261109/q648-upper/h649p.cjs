'use strict';
// Upper-stage harness over the q651 (or patched) upper source and its runFold oracle.
// usage: node harness.cjs <q651dir> <fwd|rev> <stress|field|few> [ban=652,651] [patch=a.js,b.js] [out=file] [dump=file]
// env FAST=w,..   per (row, wire) touch counts
// env CENSUS=w,.. per (row, window label) touch counts
// env LIVE=w      live-interval idle census: for each interval where w is nonzero (all-lane view), list wires zero/one at
//                 entry and untouched until w returns to zero.
const path=require('path'),fs=require('fs'),Module=require('module');
const [Q,dir,mode,...rest]=process.argv.slice(2);
const opt=Object.fromEntries(rest.map(a=>a.split('=')));
// h649: Q = their q651-ten-field dir. SINK=1 applies their peephole sink (op counts as emitted); default is pre-sink (census/occupancy).
const {joined}=require(path.join(Q,'../field128-height-experiment/pinned.cjs'));
const f=path.join(joined,'checkpoint/centered-point.cjs');
const U649=require(path.join(Q,process.env.UENTRY||'u-upper-649.cjs'));
let src=require(path.join(Q,'upper.cjs')).upper(fs.readFileSync(f,'utf8'));
src=process.env.SINK?U649.upper(src):U649.sourceUpper(src);
if(process.env.UEXTRA)for(const pf of process.env.UEXTRA.split(','))src=require(path.resolve(pf)).upper(src);
const one=(s,a,b,w)=>{if(s.split(a).length!==2)throw Error('harness anchor '+(w||'')+' '+a.slice(0,80));return s.replace(a,()=>b);};
if(opt.patch)for(const pf of opt.patch.split(','))for(const e of require(path.resolve(pf))){const [a,b]=e.length===3?e.slice(1):e;src=one(src,a,b,'extra '+pf);}
src=one(src,'out(a,b,t){\n        const g=this.one,cv=x=>x>g?x-1:x;','out(a,b,t){\n        if(globalThis.__H)globalThis.__H(a,b,t,undefined,this);const g=this.one,cv=x=>x>g?x-1:x;');
src=one(src,'this.physical.out(a===NONE?NONE:cv(a),b===NONE?NONE:cv(b),cv(t));\n    }\n    mc(cs,t,dirty){super.mc(cs.filter(q=>q!==this.one),t,dirty);}',
 'this.physical.out(a===NONE?NONE:cv(a),b===NONE?NONE:cv(b),cv(t));if(globalThis.__A)globalThis.__A(t,this);\n    }\n    mc(cs,t,dirty){super.mc(cs.filter(q=>q!==this.one),t,dirty);}');
src=one(src,'hmr(q){return this.physical.hmr(this.cq(q));}','hmr(q){if(globalThis.__H)globalThis.__H(q,1023,q,"hmr",this);const r=this.physical.hmr(this.cq(q));if(globalThis.__A)globalThis.__A(q,this);return r;}');
src=one(src,'z(q){this.physical.z(this.cq(q));}','z(q){if(globalThis.__H)globalThis.__H(q,1023,q,"z",this);this.physical.z(this.cq(q));}');
src=one(src,'const row=new UnguardedGeneral(m,delta,k,logical);\n        if(k>0&&k<m/2-1){const unit=new EarlyUnit(m,delta,k,logical);ops.push(rv=>unit.emit(tape,rv));}\n        ops.push(rv=>row.emit(tape,rv),',
 'const row=new UnguardedGeneral(m,delta,k,logical);\n        if(k>0&&k<m/2-1){const unit=new EarlyUnit(m,delta,k,logical);ops.push(rv=>{globalThis.__K="u"+k;unit.emit(tape,rv);});}\n        ops.push(rv=>{globalThis.__K=k;row.emit(tape,rv);},');
src=one(src,'function runFold(m,delta,logical,inputs,seed,back,policy=\'random\'){',fs.readFileSync(path.join(__dirname,'round_inj.js'),'utf8').replace('stepList(ops,true,fn=>fn(true));','globalThis.__RV=1;stepList(ops,true,fn=>fn(true));')+'function runFold(m,delta,logical,inputs,seed,back,policy=\'random\'){');
src=one(src,'return {pointReference,exceptionTable,','globalThis.__C={MixedArithmetic,WordArithmetic,UnitPreparation,UniversalGeneral,TruncatedGeneral,AlignedGeneral,SingleAffineGeneral,EarlyGeneral,OddEstimateGeneral,UnguardedGeneral,EarlyUnit,Tape,FoldTape};\nreturn {pointReference,exceptionTable,');
src=src.replace('return {pointReference,exceptionTable,','return {runRound,pointReference,exceptionTable,');
if(opt.dump)fs.writeFileSync(opt.dump,src);
const m=new Module(f,module);m.filename=f;m.paths=module.paths;m._compile(src,f);const L=m.exports;
const list=s=>new Set((s||'').split(',').filter(Boolean).map(Number));
const ban=list(opt.ban),cen=list(process.env.CENSUS),fast=list(process.env.FAST);
Error.stackTraceLimit=80;
const SKIP=/^(stepList|perform|fn|mc|out|Array|forEach|<anonymous>|runFold|__H|__A|label|ops|seq|steps|rv|rr)$/;
const label=(d)=>{const st=new Error().stack.split('\n').slice(2).map(l=>(l.match(/at (?:Object\.|new |[\w$]+\.)?([\w$.<>]+) /)||[])[1]).filter(x=>x&&!SKIP.test(x)).reverse();
  const i=st.indexOf('emit');return (i>=0?st.slice(i+1):st).slice(0,d||+(process.env.DEPTH||7)).join('>');};
globalThis.__K='pre';
const win=new Map(),fc=new Map();let hits=0;
const LIVE=process.env.LIVE?Number(process.env.LIVE):null,ivs=[];let cur=null;
const state=(tape,q)=>{const B=tape.physical.batches,x=q>tape.one?q-1:q;let o=0,a=-1;for(const r of B){o|=r[x];a&=r[x];}return o===0?0:(a>>>0)===0xffffffff?1:2;};
const banCheck=(a,b,t,kind)=>{if(ban.has(a)||ban.has(b)||ban.has(t))throw Error('BAN hit '+[a,b,t,kind||'g']+' row '+globalThis.__K+' at '+label());};
if(LIVE!==null){
  globalThis.__H=(a,b,t,kind,tape)=>{
    banCheck(a,b,t,kind);
    if(cur){cur.touch.add(a);cur.touch.add(b);cur.touch.add(t);cur.n++;return;}
    if(t===LIVE){
      const z=[],o=[];for(let q=0;q<657;q++){if(q===tape.one)continue;const v=state(tape,q);if(v===0)z.push(q);else if(v===1)o.push(q);}
      cur={k:globalThis.__K,label:label(4),zero:z,one:o,touch:new Set([a,b,t]),n:1};
    }
  };
  globalThis.__A=(t,tape)=>{if(cur&&t===LIVE&&state(tape,LIVE)===0){cur.end=label(4);ivs.push(cur);cur=null;}};
}else if(process.env.RELAY){
  // relay feasibility for wire R: within each live interval of R, cover it by idle-zero gaps of candidate wires.
  const R=Number(process.env.RELAY),cand=q=>q!==R&&!(q>=385&&q<641)&&!(q>=652&&q<=656)&&q!==641&&q!==649;
  let iv=null,idx=0,ord=0;const res=[];const FA=process.env.FAILAT?JSON.parse(fs.readFileSync(process.env.FAILAT)).map(x=>x.fail):null;
  const zeroAll=tape=>{const z=new Uint8Array(657);for(let q=0;q<657;q++)if(q!==tape.one)z[q]=state(tape,q)===0?1:0;return z;};
  globalThis.__H=(a,b,t,kind,tape)=>{
    banCheck(a,b,t,kind);
    if(!iv&&t===R){iv={k:globalThis.__K,label:label(4),entry:zeroAll(tape),touch:new Map(),n:0,ord:ord++};idx=0;}
    if(!iv)return;
    if(FA&&FA[iv.ord]!==null&&FA[iv.ord]!==undefined&&(idx===FA[iv.ord]||idx===FA[iv.ord]-1)){const z=zeroAll(tape),busy=[];for(let q=0;q<657;q++)if(cand(q)&&!z[q]&&!(q<385))busy.push(q);(iv.at=iv.at||[]).push({idx,gate:[a,b,t],where:label(12),busyHelpers:busy});}
    for(const w of [a,b,t]){if(w===1023||!cand(w))continue;let l=iv.touch.get(w);if(!l){l=[];iv.touch.set(w,l);}l.push(idx,-1);}
    iv.n++;
  };
  globalThis.__A=(t,tape)=>{
    if(!iv)return;
    if(cand(t)){const l=iv.touch.get(t);if(l&&l[l.length-2]===idx)l[l.length-1]=state(tape,t)===0?1:0;}
    idx++;
    if(t===R&&state(tape,R)===0){
      // build gaps: for wire w, idle-zero ranges [s,e) of gate positions (move point p means between gate p-1 and p)
      const N=idx,gaps=[];
      for(let w=0;w<657;w++){if(!cand(w))continue;const l=iv.touch.get(w)||[];let z=iv.entry[w],s=0;
        for(let i=0;i<l.length;i+=2){const g=l[i];if(z&&g>s)gaps.push([s,g,w]);else if(z&&g===s){} // empty
          if(l[i+1]!==-1)z=l[i+1];s=g+1;}
        if(z&&N>s)gaps.push([s,N,w]);}
      // gaps: t1 hosted on w over positions [s,e]; a move at position p needs both gaps to contain p (s<=p<=e)
      gaps.sort((x,y)=>x[0]-y[0]);let pos=0,moves=0,fail=null,gi=0,bestEnd=-1,bestW=-1;const used=new Map();
      // interval cover: running max end over gaps with start<=pos
      while(true){
        while(gi<gaps.length&&gaps[gi][0]<=pos){if(gaps[gi][1]>bestEnd){bestEnd=gaps[gi][1];bestW=gaps[gi][2];}gi++;}
        if(bestEnd<pos||bestEnd<0){fail=pos;break;}
        moves++;used.set(bestW,(used.get(bestW)||0)+1);
        if(bestEnd>=N)break;
        if(bestEnd===pos){fail=pos;break;}
        pos=bestEnd;
      }
      res.push({k:iv.k,ord:iv.ord,at:iv.at,label:iv.label,n:N,moves,fail,used:[...used.entries()].sort((a,b)=>b[1]-a[1]).slice(0,8)});
      iv=null;
    }
  };
  process.on('exit',()=>fs.writeFileSync(opt.out||'relay.json',JSON.stringify(res)));
}else if(process.env.OCC){
  // helper occupancy: number of helpers nonzero (any lane) after each gate; per row-window max and where.
  const Hs=(process.env.OCCH||'256,642,643,644,645,646,647,648,650,651').split(',').map(Number),nz=new Map(Hs.map(q=>[q,0]));let occ=0;const best=new Map();
  globalThis.__H=(a,b,t,kind,tape)=>{banCheck(a,b,t,kind);};
  globalThis.__A=(t,tape)=>{if(!nz.has(t))return;const v=state(tape,t)===0?0:1;if(v!==nz.get(t)){occ+=v?1:-1;nz.set(t,v);}
    if(occ>=+process.env.OCC){const key=globalThis.__K+'\t'+label(9);const e=best.get(key);if(!e||occ>e.occ)best.set(key,{occ,zero:Hs.filter(q=>!nz.get(q))});}};
  process.on('exit',()=>fs.writeFileSync(opt.out||'occ.tsv',[...best.entries()].map(([k,v])=>k+'\t'+v.occ+'\t'+v.zero.join(',')).join('\n')+'\n'));
}else if(fast.size)globalThis.__H=(a,b,t)=>{for(const x of [a,b,t])if(fast.has(x)){const key=globalThis.__K+'\t'+x+(x===t?'T':'C');fc.set(key,(fc.get(key)||0)+1);}};
else if(ban.size||cen.size)globalThis.__H=(a,b,t,kind)=>{
  banCheck(a,b,t,kind);
  if(cen.size&&(cen.has(a)||cen.has(b)||cen.has(t))){hits++;const w=[a,b,t].filter(x=>cen.has(x));
    const key=globalThis.__K+' | '+w.join(',')+(cen.has(t)?' T':' C')+' | '+label();win.set(key,(win.get(key)||0)+1);}
};

// WIN=method,... : per call of these prototype methods, record ops, helper wires zero-at-entry and untouched (incl. loans)
if(process.env.WIN){
  const names=process.env.WIN.split(','),C=globalThis.__C,stats=new Map();let cur=null;
  const HS=[256,642,643,644,645,646,647,648,650,651];
  const oldH=globalThis.__H;
  globalThis.__H=(a,b,t,kind,tape)=>{if(oldH)oldH(a,b,t,kind,tape);if(cur){cur.touch.add(a);cur.touch.add(b);cur.touch.add(t);cur.n++;}};
  for(const cls of Object.values(C))for(const nm of names){
    if(!cls.prototype||!Object.prototype.hasOwnProperty.call(cls.prototype,nm))continue;
    const orig=cls.prototype[nm];
    cls.prototype[nm]=function(tape,...rest){
      if(cur)return orig.call(this,tape,...rest);
      const z=HS.filter(q=>state(tape,q)===0);cur={touch:new Set(),n:0};
      try{return orig.call(this,tape,...rest);}finally{
        const free=z.filter(q=>!cur.touch.has(q)),key=nm+'\t'+globalThis.__K+'\t'+label(5);
        const e=stats.get(key)||{calls:0,ops:0,freeCalls:0,freeOps:0,hosts:{}};
        e.calls++;e.ops+=cur.n;if(free.length){e.freeCalls++;e.freeOps+=cur.n;for(const q of free)e.hosts[q]=(e.hosts[q]||0)+1;}
        stats.set(key,e);cur=null;}
    };
  }
  process.on('exit',()=>fs.writeFileSync(opt.out||'win.json',JSON.stringify([...stats.entries()])));
}

if(process.env.EVER){
  const nz=new Uint8Array(657),no=new Uint8Array(657);let seen=null,entry=null;
  const upd=(tape,q)=>{const v=state(tape,q);if(v!==0)nz[q]=1;if(v!==1)no[q]=1;};
  const oldA=globalThis.__A;
  globalThis.__A=(t,tape)=>{if(oldA)oldA(t,tape);if(!entry){entry=1;for(let q=0;q<657;q++)if(q!==tape.one)upd(tape,q);}upd(tape,t);};
  process.on('exit',()=>{const out=[];for(let q=0;q<657;q++){if(q===641)continue;out.push([q,nz[q]?(no[q]?'varies':'always1'):'always0']);}
    fs.writeFileSync(opt.out||'ever.json',JSON.stringify(out));});
}
if(process.env.CHK){let bad=0;globalThis.__CHK=(tape,q,k,mt)=>{const v=state(tape,q);if(v!==0&&bad++<5)console.error('CHK f1 nonzero row',k,'mt',mt,'state',v,'cond',tape.physical.current!==null,label(9));};}

// OWN: owner (method stack at the 0->nonzero transition) of each helper at every 10/10 occupancy point
if(process.env.OWN){
  const ST=[];globalThis.__ST=ST;const C=globalThis.__C;
  const SKIPM=new Set(['constructor','out','mc','loan','toggle','cnotList','constBelow','equal','increment','inc','permute','gatedSwap','get','ab']);
  for(const cls of Object.values(C)){const pr=cls.prototype;if(!pr)continue;
    for(const nm of Object.getOwnPropertyNames(pr)){if(SKIPM.has(nm))continue;const dsc=Object.getOwnPropertyDescriptor(pr,nm);if(!dsc||typeof dsc.value!=='function')continue;
      const orig=dsc.value;pr[nm]=function(...a){ST.push(nm);try{return orig.apply(this,a);}finally{ST.pop();}};}}
  const HS=(process.env.OCCH||'256,642,643,644,645,646,647,648,650,651').split(',').map(Number),NM={256:'b256',642:'pick',643:'carry',644:'f1',645:'q0',646:'q1',647:'f2',648:'take',650:'t0',651:'t1'};
  const nz=new Map(HS.map(q=>[q,0])),own=new Map();let occ=0;const agg=new Map();
  const D=+(process.env.ODEPTH||5);
  const ctx=()=>{const i=ST.lastIndexOf('core');return ST.slice(i>=0?i+1:0).join('>');};
  globalThis.__H=(a,b,t,kind,tape)=>{banCheck(a,b,t,kind);};
  globalThis.__A=(t,tape)=>{if(!nz.has(t))return;const v=state(tape,t)===0?0:1;
    if(v!==nz.get(t)){occ+=v?1:-1;nz.set(t,v);if(v)own.set(t,ctx());}
    if(occ===HS.length){const w=ctx().split('>').slice(0,D).join('>'),k=globalThis.__K,kk=typeof k==='number'?(k<=112?'0-112':'113+'):String(k);
      const key=kk+' | '+w;let e=agg.get(key);if(!e){e={n:0,roles:{}};agg.set(key,e);}e.n++;
      for(const q of HS){const r=NM[q]+' <- '+(own.get(q)||'?').split('>').slice(0,7).join('>');e.roles[r]=(e.roles[r]||0)+1;}}};
  process.on('exit',()=>fs.writeFileSync(opt.out||'own.json',JSON.stringify([...agg.entries()])));
}

// DEAD: late-HMR lead indicator. A helper's dead span = (last gate using it as a control or phase, gate returning it to all-zero].
// Counts 9/9 gates (all OCCH helpers nonzero on some lane) covered by at least one helper's dead span, per window label.
if(process.env.DEAD){
  const ST=[];const C=globalThis.__C;
  const SKIPM=new Set(['constructor','out','mc','loan','toggle','cnotList','constBelow','equal','increment','inc','permute','gatedSwap','get','ab']);
  for(const cls of Object.values(C)){const pr=cls.prototype;if(!pr)continue;
    for(const nm of Object.getOwnPropertyNames(pr)){if(SKIPM.has(nm))continue;const dsc=Object.getOwnPropertyDescriptor(pr,nm);if(!dsc||typeof dsc.value!=='function')continue;
      const orig=dsc.value;pr[nm]=function(...a){ST.push(nm);try{return orig.apply(this,a);}finally{ST.pop();}};}}
  const HS=(process.env.OCCH||'256,642,643,644,645,646,647,648,650').split(',').map(Number),hset=new Set(HS);
  const nz=new Map(HS.map(q=>[q,0])),lastCtl=new Map(HS.map(q=>[q,-1])),spans=[];let occ=0,g=0;
  const runs=[],labId=new Map(),labs=[];let curRun=null;
  const ctx=()=>{const i=ST.lastIndexOf('core');const w=ST.slice(i>=0?i+1:0).slice(0,+(process.env.DDEPTH||3)).join('>');const kk=typeof globalThis.__K==='number'?(globalThis.__K<=63?'0-63':globalThis.__K<=112?'64-112':'113+'):String(globalThis.__K);const key=kk+' | '+w;let id=labId.get(key);if(id===undefined){id=labs.length;labs.push(key);labId.set(key,id);}return id;};
  globalThis.__H=(a,b,t,kind,tape)=>{banCheck(a,b,t,kind);
    if(kind){if(hset.has(a))lastCtl.set(a,g);return;}            // hmr / z read the value
    if(hset.has(a))lastCtl.set(a,g);if(hset.has(b))lastCtl.set(b,g);};
  globalThis.__A=(t,tape)=>{
    if(hset.has(t)){const v=state(tape,t)===0?0:1;if(v!==nz.get(t)){occ+=v?1:-1;nz.set(t,v);
        if(v)lastCtl.set(t,g);else spans.push([lastCtl.get(t)+1,g,t]);}}
    if(occ===HS.length){const L=ctx();if(curRun&&curRun[1]===g&&curRun[2]===L)curRun[1]=g+1;else{curRun=[g,g+1,L];runs.push(curRun);}}
    g++;};
  process.on('exit',()=>{
    // union of all dead spans (any helper) -> merged intervals; coverage of each 9/9 run = measure of intersection
    spans.sort((x,y)=>x[0]-y[0]);const merged=[];for(const [a,b,h] of spans){if(b<=a)continue;const last=merged[merged.length-1];if(last&&a<=last[1])last[1]=Math.max(last[1],b);else merged.push([a,b]);}
    const tot=new Map(),cov=new Map();let mi=0;
    for(const [a,b,lid] of runs){const L=labs[lid];tot.set(L,(tot.get(L)||0)+(b-a));
      while(mi<merged.length&&merged[mi][1]<=a)mi++;let c=0;for(let j=mi;j<merged.length&&merged[j][0]<b;j++)c+=Math.max(0,Math.min(b,merged[j][1])-Math.max(a,merged[j][0]));
      cov.set(L,(cov.get(L)||0)+c);}
    // per helper coverage (top windows)
    const by=new Map();const perH=new Map();for(const [a,b,h] of spans){if(b>a){if(!perH.has(h))perH.set(h,[]);perH.get(h).push([a,b]);}}
    for(const [h,list] of perH){let k=0;for(const [a,b,lid] of runs){while(k<list.length&&list[k][1]<=a)k++;let c=0;for(let j=k;j<list.length&&list[j][0]<b;j++)c+=Math.max(0,Math.min(b,list[j][1])-Math.max(a,list[j][0]));if(c){const key=labs[lid]+' #'+h;by.set(key,(by.get(key)||0)+c);}}}
    const out=[...tot.entries()].sort((a,b)=>b[1]-a[1]).map(([L,n])=>[L,n,cov.get(L)||0]);
    fs.writeFileSync(opt.out||'dead.json',JSON.stringify({windows:out,byHelper:[...by.entries()].sort((a,b)=>b[1]-a[1]).slice(0,60)}));});
}

// PCEN (papers): 8/8 census split by direction; per (dir,row-bucket,ctx) count, helper owner roles, and sampled all-lane-zero non-helper wires
if(process.env.PCEN){
  const ST=[];const C=globalThis.__C;
  const SKIPM=new Set(['constructor','out','mc','loan','toggle','cnotList','constBelow','equal','increment','inc','permute','gatedSwap','get','ab']);
  for(const cls of Object.values(C)){const pr=cls.prototype;if(!pr)continue;
    for(const nm of Object.getOwnPropertyNames(pr)){if(SKIPM.has(nm))continue;const dsc=Object.getOwnPropertyDescriptor(pr,nm);if(!dsc||typeof dsc.value!=='function')continue;
      const orig=dsc.value;pr[nm]=function(...a){ST.push(nm);try{return orig.apply(this,a);}finally{ST.pop();}};}}
  const HS=(process.env.OCCH||'256,642,643,644,645,646,647,648').split(',').map(Number),NM={256:'b256',642:'pick',643:'carry',644:'f1',645:'q0',646:'q1',647:'f2',648:'take',650:'t0',651:'t1'};
  const hset=new Set(HS),nz=new Map(HS.map(q=>[q,0])),own=new Map();let occ=0,n88=0;const agg=new Map();
  const D=+(process.env.ODEPTH||6),SAMP=+(process.env.SAMP||4000);
  const ctx=()=>{const i=ST.lastIndexOf('core');return ST.slice(i>=0?i+1:0).join('>');};
  const lastTouch=new Map();let g=0;
  globalThis.__H=(a,b,t,kind,tape)=>{banCheck(a,b,t,kind);};
  globalThis.__A=(t,tape)=>{g++;if(nz.has(t)){const v=state(tape,t)===0?0:1;
    if(v!==nz.get(t)){occ+=v?1:-1;nz.set(t,v);if(v)own.set(t,ctx());}}
    if(occ===HS.length){n88++;const k=globalThis.__K,kk=(globalThis.__RV?'R':'F')+' '+(typeof k==='number'?(k<=63?'0-63':k<=112?'64-112':'113+'):String(k));
      const key=kk+' | '+ctx().split('>').slice(0,D).join('>');let e=agg.get(key);if(!e){e={n:0,roles:{},zs:{},ns:0};agg.set(key,e);}e.n++;
      if(e.n%64===1)for(const q of HS){const r=NM[q]+' <- '+(own.get(q)||'?').split('>').slice(0,6).join('>');e.roles[r]=(e.roles[r]||0)+1;}
      if(e.n%SAMP===1){e.ns++;for(let q=0;q<657;q++){if(q===tape.one||hset.has(q))continue;if(state(tape,q)===0)e.zs[q]=(e.zs[q]||0)+1;}}}};
  process.on('exit',()=>{const out=[...agg.entries()].sort((a,b)=>b[1].n-a[1].n);fs.writeFileSync(opt.out||'pcen.json',JSON.stringify({n88,out}));});
}

if(process.env.PROF){
  const ST=[];const C=globalThis.__C;
  const SKIPM=new Set(['constructor','out','mc','loan','get','ab']);
  for(const cls of Object.values(C)){const pr=cls.prototype;if(!pr)continue;
    for(const nm of Object.getOwnPropertyNames(pr)){if(SKIPM.has(nm))continue;const dsc=Object.getOwnPropertyDescriptor(pr,nm);if(!dsc||typeof dsc.value!=='function')continue;
      const orig=dsc.value;pr[nm]=function(...a){ST.push(nm);try{return orig.apply(this,a);}finally{ST.pop();}};}}
  const agg=new Map(),D=+(process.env.PDEPTH||2);
  globalThis.__A=(t,tape)=>{const k=globalThis.__K;if(globalThis.__RV||typeof k!=='number'||k>63)return;
    let i=ST.indexOf('u6DoubleSign');if(i<0)i=ST.indexOf('u648FourSign');if(i<0)i=ST.indexOf('u9ThreeSign');if(i<0)return;
    const key=ST.slice(i+1,i+1+D).join('>');agg.set(key,(agg.get(key)||0)+1);};
  process.on('exit',()=>fs.writeFileSync(opt.out||'prof.json',JSON.stringify([...agg.entries()].sort((a,b)=>b[1]-a[1]))));
}

// LCEN=w: touches of wire w (gate operand, incl. loans) per (dir,row-bucket,ctx) -- window-local ban check
if(process.env.LCEN){
  const W=+process.env.LCEN,ST=[];const C=globalThis.__C;
  for(const cls of Object.values(C)){const pr=cls.prototype;if(!pr)continue;
    for(const nm of Object.getOwnPropertyNames(pr)){if(nm==='constructor'||nm==='out'||nm==='mc')continue;const dsc=Object.getOwnPropertyDescriptor(pr,nm);if(!dsc||typeof dsc.value!=='function')continue;
      const orig=dsc.value;pr[nm]=function(...a){ST.push(nm);try{return orig.apply(this,a);}finally{ST.pop();}};}}
  const agg=new Map(),D=+(process.env.LDEPTH||6);
  globalThis.__H=(a,b,t,kind,tape)=>{banCheck(a,b,t,kind);if(a!==W&&b!==W&&t!==W)return;const k=globalThis.__K;
    const kk=(globalThis.__RV?'R':'F')+' '+(typeof k==='number'?(k<=63?'0-63':k<=112?'64-112':'113+'):String(k));
    const i=ST.lastIndexOf('core');const key=kk+' | '+ST.slice(i>=0?i+1:0,(i>=0?i+1:0)+D).join('>');agg.set(key,(agg.get(key)||0)+1);};
  process.on('exit',()=>fs.writeFileSync(opt.out||'lcen.json',JSON.stringify([...agg.entries()].sort((a,b)=>b[1]-a[1]))));
}
const back=dir==='rev',t0=Date.now();
const xs=mode==='field'?L.fieldInputs():mode==='few'?L.fieldInputs().slice(0,32):L.fieldStress();
const r=dir==='round'?L.runRound(256,(1n<<32n)+977n,657,xs,0x334b312e):L.runFold(256,(1n<<32n)+977n,657,xs,back?0x9a4dedcd:0x334b312e,back);
r.secs=(Date.now()-t0)/1000;r.hits=hits;
console.log(JSON.stringify(r));
if(fast.size)fs.writeFileSync(opt.out||'fast.tsv',[...fc.entries()].map(([k,v])=>k+'\t'+v).join('\n')+'\n');
if(cen.size)fs.writeFileSync(opt.out||'census.tsv',[...win.entries()].sort().map(([k,v])=>v+'\t'+k).join('\n')+'\n');
if(LIVE!==null){if(cur)ivs.push(Object.assign(cur,{end:'OPEN'}));
  fs.writeFileSync(opt.out||'live.json',JSON.stringify(ivs.map(v=>({k:v.k,label:v.label,end:v.end,n:v.n,zeroIdle:v.zero.filter(q=>!v.touch.has(q)),oneIdle:v.one.filter(q=>!v.touch.has(q))}))));}
