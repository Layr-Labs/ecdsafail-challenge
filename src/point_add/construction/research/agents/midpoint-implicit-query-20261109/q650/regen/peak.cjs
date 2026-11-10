'use strict';
// Exact per-gate peak of simultaneously possibly-nonzero helpers (OR over lanes), per stage.
const {loadRegen}=require('./load.cjs');const {cases}=require('./sim.cjs');
const [patch,N='256',seed='9',W0='8']=process.argv.slice(2);const W=+W0;
const H=(process.env.H||'0,1,130,131,388,646,647,648,649,650').split(',').map(Number);
const cs=cases(+N,+seed,process.env.MODE||'mix');const {emitRegenerateSparse}=loadRegen(patch);
const n=128,S=new Uint32Array(1024*W),lanes=32*W;const put=(w,l,b)=>{if(b)S[w*W+(l>>5)]|=1<<(l&31);};const cr=require('crypto');
for(let l=0;l<lanes;l++){const c=cs[l%cs.length];for(let i=0;i<n;i++){put(129-i,l,Number((c.r>>BigInt(i))&1n));put(259-i,l,Number((c.v>>BigInt(i))&1n));}const y=cr.randomBytes(32);for(let i=0;i<256;i++)put(389+i,l,(y[i>>3]>>(i&7))&1);}
for(let w=0;w<W;w++)S[645*W+w]=0xffffffff;
const idx=new Int16Array(1024).fill(-1);H.forEach((q,i)=>idx[q]=i);
const nz=new Uint8Array(H.length);let cnt=0;
const isnz=q=>{for(let w=0;w<W;w++)if(S[q*W+w])return 1;return 0;};
let cur=-1;const res={};let blk=0;
globalThis.__rgStage=(i,l)=>{cur=i;blk=0;res[i]={label:l,peak:0,hist:new Array(H.length+1).fill(0),peakBlocks:[]};};
emitRegenerateSparse(chunk=>{const r=res[cur];let bp=0;
  for(const z of chunk){const a=z>>>20,b=(z>>>10)&1023,tq=z&1023,t=tq*W;
    if(a===1023){for(let w=0;w<W;w++)S[t+w]^=0xffffffff;}else if(b===1023){const A=a*W;for(let w=0;w<W;w++)S[t+w]^=S[A+w];}else{const A=a*W,B=b*W;for(let w=0;w<W;w++)S[t+w]^=S[A+w]&S[B+w];}
    const k=idx[tq];if(k>=0){const v=isnz(tq);if(v!==nz[k]){cnt+=v-nz[k];nz[k]=v;}}
    r.hist[cnt]++;if(cnt>bp)bp=cnt;}
  if(bp>r.peak){r.peak=bp;r.peakBlocks=[];}if(bp===r.peak&&r.peakBlocks.length<12)r.peakBlocks.push(blk);blk++;},false);
for(const i of Object.keys(res)){const r=res[i];console.log(`stage ${i} ${r.label} peak=${r.peak} gate-hist(count:gates)=${r.hist.map((x,j)=>x?j+':'+x:'').filter(Boolean).join(' ')} first-peak-blocks=${r.peakBlocks.join(',')}`);}
