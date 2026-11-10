'use strict';
// For each small-V class (by bit length), find wires transparent to walk6 for every state of the class.
const {loadRegen}=require('./load.cjs');
const [patch,VLO,VHI]=process.argv.slice(2);
const gcd=(a,b)=>{while(b){[a,b]=[b,a%b];}return a;};
const states=[];for(let v=+VLO;v<=+VHI;v++)for(let r=0;r<v;r++)if(gcd(r,v)===1||v===1)states.push([BigInt(r),BigInt(v)]);
const cands=[];for(let q=0;q<650;q++)if(q!==645&&!(q>=389&&q<645))cands.push(q); // Y is a dirty pool: skip
const per=cands.length+1,lanes=states.length*per,W=Math.ceil(lanes/32);
const {emitRegenerateSparse}=loadRegen(patch);
const S=new Uint32Array(1024*W);
const put=(w,l,b)=>{if(b)S[w*W+(l>>5)]|=1<<(l&31);else S[w*W+(l>>5)]&=~(1<<(l&31));};
const get=(w,l)=>(S[w*W+(l>>5)]>>>(l&31))&1;
for(let l=0;l<lanes;l++){const [r,v]=states[Math.floor(l/per)];for(let i=0;i<128;i++){put(129-i,l,Number((r>>BigInt(i))&1n));put(259-i,l,Number((v>>BigInt(i))&1n));}}
for(let w=0;w<W;w++)S[645*W+w]=0xffffffff;
let cur=-1;const pre=new Map();
globalThis.__rgStage=(i)=>{cur=i;if(i===2)for(let l=0;l<lanes;l++){const c=l%per;for(const q of (process.env.TT||"261,262").split(",").map(Number))put(q,l,0);if(c>0){const q=cands[c-1];put(q,l,1-get(q,l));}}};
emitRegenerateSparse(chunk=>{if(cur>2)return;for(const z of chunk){const a=z>>>20,b=(z>>>10)&1023,t=(z&1023)*W;
  if(a===1023){for(let w=0;w<W;w++)S[t+w]^=0xffffffff;}else if(b===1023){const A=a*W;for(let w=0;w<W;w++)S[t+w]^=S[A+w];}else{const A=a*W,B=b*W;for(let w=0;w<W;w++)S[t+w]^=S[A+w]&S[B+w];}}},false);
const ok=cands.filter((q,ci)=>states.every((st,si)=>{const base=si*per,l=base+ci+1;for(let w=0;w<1024;w++)if(get(w,l)!==(get(w,base)^(w===q?1:0)))return false;return true;}));
console.log(`V in [${VLO},${VHI}] (${states.length} states): transparent`,ok.filter(q=>q<261||q>388).join(','),'| T wires:',ok.filter(q=>q>=261&&q<=388).length);
