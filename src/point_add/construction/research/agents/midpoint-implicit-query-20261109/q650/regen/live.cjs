'use strict';
// Block-boundary liveness of helpers: per stage, run-length string of state at each block start: 0 all-zero, 1 all-one, x mixed.
// Also "zero over whole block" (z) if zero at all gates in the block on all lanes.
const {loadRegen}=require('./load.cjs');const {cases}=require('./sim.cjs');
const [patch,N='512',seed='9',W0='16',onlyStage]=process.argv.slice(2);const W=+W0;
const H=(process.env.H||'0,1,130,131,388,646,647,648,649,650').split(',').map(Number);
const cs=cases(+N,+seed,process.env.MODE||'mix');
const {emitRegenerateSparse}=loadRegen(patch);
const n=128,S=new Uint32Array(1024*W),lanes=32*W;
const put=(wire,lane,bit)=>{if(bit)S[wire*W+(lane>>5)]|=1<<(lane&31);};
const cr=require('crypto');
for(let l=0;l<lanes;l++){const c=cs[l%cs.length];for(let i=0;i<n;i++){put(129-i,l,Number((c.r>>BigInt(i))&1n));put(259-i,l,Number((c.v>>BigInt(i))&1n));}
  const y=cr.randomBytes(32);for(let i=0;i<256;i++)put(389+i,l,(y[i>>3]>>(i&7))&1);}
for(let w=0;w<W;w++)S[645*W+w]=0xffffffff;
const st=q=>{let o=0,a=0xffffffff;for(let w=0;w<W;w++){o|=S[q*W+w];a&=S[q*W+w];}return o===0?'0':a===0xffffffff?'1':'x';};
let cur=-1;const out={};
globalThis.__rgStage=(i,label)=>{cur=i;out[i]={label,s:H.map(()=>[])};};
emitRegenerateSparse(chunk=>{const o=out[cur];
  const ever=new Uint32Array(H.length*W);
  for(let h=0;h<H.length;h++)for(let w=0;w<W;w++)ever[h*W+w]=S[H[h]*W+w];
  const idx=new Int16Array(1024).fill(-1);H.forEach((q,i)=>idx[q]=i);
  for(const z of chunk){const a=z>>>20,b=(z>>>10)&1023,tq=z&1023,t=tq*W;
    if(a===1023){for(let w=0;w<W;w++)S[t+w]^=0xffffffff;}
    else if(b===1023){const A=a*W;for(let w=0;w<W;w++)S[t+w]^=S[A+w];}
    else{const A=a*W,B=b*W;for(let w=0;w<W;w++)S[t+w]^=S[A+w]&S[B+w];}
    const k=idx[tq];if(k>=0)for(let w=0;w<W;w++)ever[k*W+w]|=S[t+w];}
  for(let h=0;h<H.length;h++){let e=0;for(let w=0;w<W;w++)e|=ever[h*W+w];o.s[h].push(e===0?'z':st(H[h]));}
},false);
const rle=a=>{const r=[];let p=null,c=0;for(const x of a){if(x===p)c++;else{if(p!==null)r.push(p+(c>1?c:''));p=x;c=1;}}r.push(p+(c>1?c:''));return r.join(' ');};
for(const i of Object.keys(out)){if(onlyStage!==undefined&&+onlyStage!==+i)continue;const o=out[i];console.log(`stage ${i} ${o.label} blocks=${o.s[0].length}`);
  H.forEach((q,h)=>console.log(`  ${q}: ${rle(o.s[h])}`));}
