// per-block free wires in THEIR scale (and park): zero (all lanes, random Y) at block entry and exit, untouched by the block
const S='/Users/akashbalasubramani/Desktop/ecdsafail-649rg/src/point_add/construction/research/agents/midpoint-implicit-query-20261109/q650/regen/';
const {cases}=require(S+'sim.cjs');const {load,EDITS}=require('./r648-load.cjs');const crypto=require('crypto');
const B=load(EDITS);const n=128,W=+(process.env.W||8),lanes=32*W;const LAB=process.env.LAB||'scale';
const cs=cases(lanes,+(process.env.SEED||4),'mix');const Sx=new Uint32Array(1024*W);const put=(w,l,b)=>{if(b)Sx[w*W+(l>>5)]|=1<<(l&31);};
for(let l=0;l<lanes;l++){const c=cs[l];for(let i=0;i<n;i++){put(129-i,l,Number((c.r>>BigInt(i))&1n));put(259-i,l,Number((c.v>>BigInt(i))&1n));}}
for(let q=389;q<645;q++)for(let w=0;w<W;w++)Sx[q*W+w]=crypto.randomBytes(4).readUInt32LE(0);for(let w=0;w<W;w++)Sx[645*W+w]=0xffffffff;
const zero=()=>{const z=new Uint8Array(1024);for(let q=0;q<1024;q++){let ok=1;for(let w=0;w<W;w++)if(Sx[q*W+w]){ok=0;break;}z[q]=ok;}return z;};
const fm=a=>{const r=[];for(let i=0;i<a.length;){let j=i;while(j+1<a.length&&a[j+1]===a[j]+1)j++;r.push(i===j?''+a[i]:a[i]+'-'+a[j]);i=j+1;}return r.join(',');};
let stage=-1,bi=0,pend=null;const rows=[];globalThis.__rgStage=i=>{stage=i;bi=0;};
const fin=()=>{if(!pend)return;const z=zero();const f=[];for(let q=0;q<651;q++){if(q>=389&&q<645)continue;if(pend.z[q]&&z[q]&&!pend.t.has(q))f.push(q);}rows.push(pend.s+'#'+pend.i+' n='+pend.n+' free '+fm(f));pend=null;};
globalThis.__rgBlock=(lab,block,gates)=>{fin();if(lab!==LAB)return;const t=new Set();for(const x of gates){t.add(x>>>20);t.add((x>>>10)&1023);t.add(x&1023);}pend={s:stage,i:bi++,n:gates.length,z:zero(),t};};
B.emitRegenerateSparse(chunk=>{for(let k=0;k<chunk.length;k++){const zz=chunk[k],a=zz>>>20,b=(zz>>>10)&1023,t=(zz&1023)*W;
  if(a===1023){for(let w=0;w<W;w++)Sx[t+w]^=0xffffffff;}else if(b===1023){const A=a*W;for(let w=0;w<W;w++)Sx[t+w]^=Sx[A+w];}else{const A=a*W,B2=b*W;for(let w=0;w<W;w++)Sx[t+w]^=Sx[A+w]&Sx[B2+w];}}},false);fin();
let prev='';for(const r of rows){const k=r.replace(/#\d+ n=\d+/,'');if(k!==prev)console.log(r);prev=k;}
