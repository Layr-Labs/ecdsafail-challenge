'use strict';
// Differential test of the grouped alpha against the ungrouped one, at generator level (local wires).
// usage: node alpha-diff.cjs Q651_DIR PASSES [variant]   (variant letters: c = remainder below half the divisor (the real precondition), C = above half, o = heights 1/127/128 only, k = output register random below the height, g = random gap cell,
//        u = coefficient not reduced below the divisor, j = random output register)
// Both versions of outerloadJ (heights 2..n-2) are recorded once and replayed on random states, 32 per
// pass. Each state has a divisor of a chosen height h (2..n-2), cycling through all heights.
const fs=require('fs'),path=require('path'),crypto=require('crypto');
const [qdir,passesArg,variant='']=process.argv.slice(2);const passes=+passesArg;
// Both generators are compiled through the real overlay loader, so every helper is the shipped one.
const {patched}=require(path.join(qdir,'overlay.cjs'));
Object.assign(process.env,{R35_WIDTH:'651'});
const tail=[["d+'\\nreturn inverseField;'","d+'\\nglobalThis.__DIV={outerloadJ};return inverseField;'"]];
const lists=f=>require(path.join(qdir,f));
const baseList=[...lists('p-field652.js'),...lists('mul/p-mul651.js'),...lists('p-divide-d4.js'),...lists('p-stage-map.js')];
const grpList=lists('p-field651.js');
if(grpList.length!==baseList.length+1)throw Error('unexpected patch list');
patched('q653-next/backend.cjs',[...baseList,...tail]);const base=globalThis.__DIV;
patched('q653-next/backend.cjs',[...grpList,...tail]);const grp=globalThis.__DIV;
if(base===grp||String(base.outerloadJ)===String(grp.outerloadJ))throw Error('patch not applied');
const n=128,terms=[[256,1],[32,-1],[10,-1],[5,1],[4,1],[0,-1]];
let w=0;const vec=k=>Array.from({length:k},()=>w++);
const M=vec(n),lp=vec(2),rm=vec(n),rp0=w++,Q=vec(n),sign=w++,H=vec(n),C=vec(n),spare=vec(3);
const L=[...M,...lp],R=[...rm,rp0,rm[0]],loan=[...H,...C],e=rm[1];
const v=Array.from({length:n},(_,j)=>R[n+1-j]),u=Array.from({length:n},(_,j)=>L[n+1-j]);
function record(f){const parts=[];let cur=new Int16Array(3<<22),k=0,cnt=[0,0,0,0];
  const sink=(kind,g)=>{if(kind!=='nct')throw Error('kind '+kind);for(const r of g){if(r.length<1||r.length>3)throw Error('row '+r.length);if(k===cur.length){parts.push(cur);cur=new Int16Array(3<<22);k=0;}
    cnt[r.length]++;cur[k]=r.length===3?r[0]:-1;cur[k+1]=r.length>=2?r[r.length-2]:-1;cur[k+2]=r[r.length-1];k+=3;}};
  f(sink);parts.push(cur.subarray(0,k));return{parts,cnt};}
const t0=Date.now();
const A=record(s=>base.outerloadJ(n,terms,L,R,Q,sign,loan,[e,spare[0],spare[1],L[0]],s,2,n-2));
const B=record(s=>{for(let t=2;t<n-1;t++)grp.outerloadJ(n,terms,L,R,Q,sign,loan,[e,spare[0],spare[1],L[0]],s,t,t);});
console.log('recorded base X/CX/CCX',A.cnt.slice(1).join('/'),'grouped',B.cnt.slice(1).join('/'),((Date.now()-t0)/1000).toFixed(0)+'s');
function run(rec,st){for(const p of rec.parts)for(let i=0;i<p.length;i+=3){const a=p[i],b=p[i+1],c=p[i+2];if(a>=0)st[c]^=st[a]&st[b];else if(b>=0)st[c]^=st[b];else st[c]^=0xffffffff;}}
const rnd=k=>{const b=crypto.randomBytes(Math.ceil(k/8));let x=0n;for(const y of b)x=(x<<8n)|BigInt(y);return x&((1n<<BigInt(k))-1n);};
const stat=new Map();let baseDirty=0,ok=0,bad=0,total=0,changed=0,next=0;
const heights=[];for(let h=2;h<=n-2;h++)heights.push(h);if(variant.includes('o')){heights.length=0;heights.push(1,127,128);}
for(let pass=0;pass<passes;pass++){
  const st=new Uint32Array(w),hs=[];
  for(let lane=0;lane<32;lane++){
    const h=heights[next++%heights.length];hs.push(h);
    const set=(q,bit)=>{if(bit)st[q]|=(1<<lane)>>>0;};
    for(let q=0;q<w;q++)set(q,crypto.randomBytes(1)[0]&1);              // everything random first
    const clr=q=>{st[q]&=~((1<<lane)>>>0);};
    const V=rnd(h-1)|(1n<<BigInt(h-1));let U=rnd(h);if(!variant.includes('u'))U%=V;if(variant.includes('c'))U=rnd(h)%((V+1n)/2n);if(variant.includes('C'))U=(V+1n)/2n+rnd(h)%(V-(V+1n)/2n||1n);
    for(let j=0;j<n;j++){clr(v[j]);set(v[j],Number((V>>BigInt(j))&1n));}
    for(let j=0;j<h;j++){clr(u[j]);set(u[j],Number((U>>BigInt(j))&1n));}
    if(!variant.includes('g')&&h<n)clr(u[h]);                                   // gap cell of the true height
    if(!variant.includes('j')&&!variant.includes('o'))for(let j=variant.includes('k')?h:0;j<n-2;j++)clr(Q[j]);
    clr(e);
  }
  const s1=st.slice(),s2=st.slice();run(A,s1);run(B,s2);
  for(let lane=0;lane<32;lane++){let diff=0,ch=0;for(let q=0;q<w;q++){if(((s1[q]^s2[q])>>>lane)&1)diff++;if(((s1[q]^st[q])>>>lane)&1)ch++;}
    const h=hs[lane],r=stat.get(h)||[0,0];r[0]++;if(diff){r[1]++;bad++;if(bad<=8){const cat=(nm,ws)=>{const k=ws.filter(q=>((s1[q]^s2[q])>>>lane)&1).length;return k?nm+':'+k:'';};const bit=q=>(st[q]>>>lane)&1;
      console.log('MISMATCH h',h,'diff',diff,[cat('J',Q),cat('u',u),cat('v',v),cat('Llow',L.slice(0,n+2)),cat('loan',loan),cat('sign',[sign]),cat('e',[e])].filter(x=>x).join(' '),'sign',bit(sign),'v0',bit(v[0]),'u0',bit(u[0]),'Jdiff',Q.map((q,i)=>(((s1[q]^s2[q])>>>lane)&1)?i:-1).filter(i=>i>=0).slice(0,6).join(','),'..',Q.map((q,i)=>(((s1[q]^s2[q])>>>lane)&1)?i:-1).filter(i=>i>=0).slice(-2).join(','));}}
    else if(ok<4){ok++;const bit=q=>(st[q]>>>lane)&1;console.log('match h',h,'sign',bit(sign),'v0',bit(v[0]),'u0',bit(u[0]));}stat.set(h,r);total++;if(ch)changed++;
    if((s1[e]>>>lane)&1)console.log('flag not cleared, height',h);if([...u,...v,...loan,sign,e].some(q=>((s1[q]^st[q])>>>lane)&1))baseDirty++;}
}
const badH=[...stat].filter(([h,r])=>r[1]).map(([h,r])=>h+':'+r[1]+'/'+r[0]);
console.log('variant ['+variant+'] states',total,'heights covered',stat.size,'min per height',Math.min(...[...stat.values()].map(r=>r[0])),'states changed by base',changed,'mismatching states',bad,badH.length?'heights '+badH.join(' '):'');
console.log('states where the ungrouped circuit itself changes u/v/loan/sign/e:',baseDirty);console.log(bad?'RESULT FAIL':'RESULT PASS',((Date.now()-t0)/1000).toFixed(0)+'s');
