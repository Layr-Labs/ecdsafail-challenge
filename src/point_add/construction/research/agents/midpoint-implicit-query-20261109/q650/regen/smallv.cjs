'use strict';
// Small-V exhaustive check of walk6 sensitivity to wires holding parked quotient bits.
// For every V in [1,VMAX], every rm<V coprime, and every assignment of the listed wires at walk6 entry,
// walk6's result on all other wires must not depend on the assignment, and the listed wires must be preserved.
const {loadRegen}=require('./load.cjs');
const [patch,VMAX='7',wl='261,262']=process.argv.slice(2);const WS=wl.split(',').map(Number);
const gcd=(a,b)=>{while(b){[a,b]=[b,a%b];}return a;};
const states=[];for(let v=+(process.env.VMIN||1);v<=+VMAX;v++)for(let r=0;r<v;r++)if(gcd(r,v)===1||v===1)states.push([BigInt(r),BigInt(v)]);
const combos=1<<WS.length,lanes=states.length*combos,W=Math.ceil(lanes/32);
const {emitRegenerateSparse}=loadRegen(patch);
const S=new Uint32Array(1024*W);
const put=(w,l,b)=>{if(b)S[w*W+(l>>5)]|=1<<(l&31);else S[w*W+(l>>5)]&=~(1<<(l&31));};
const get=(w,l)=>(S[w*W+(l>>5)]>>>(l&31))&1;
for(let l=0;l<lanes;l++){const [r,v]=states[Math.floor(l/combos)];for(let i=0;i<128;i++){put(129-i,l,Number((r>>BigInt(i))&1n));put(259-i,l,Number((v>>BigInt(i))&1n));}}
for(let w=0;w<W;w++)S[645*W+w]=0xffffffff;
let cur=-1;
globalThis.__rgStage=(i)=>{cur=i;if(i===2)for(let l=0;l<lanes;l++){const c=l%combos;WS.forEach((q,j)=>put(q,l,(c>>j)&1));}};
emitRegenerateSparse(chunk=>{if(cur>2)return;for(const z of chunk){const a=z>>>20,b=(z>>>10)&1023,t=(z&1023)*W;
  if(a===1023){for(let w=0;w<W;w++)S[t+w]^=0xffffffff;}else if(b===1023){const A=a*W;for(let w=0;w<W;w++)S[t+w]^=S[A+w];}else{const A=a*W,B=b*W;for(let w=0;w<W;w++)S[t+w]^=S[A+w]&S[B+w];}}},false);
let bad=0;
for(let l=0;l<lanes;l++){const base=l-(l%combos),c=l%combos;
  for(let q=0;q<1024;q++){if(WS.includes(q)){if(get(q,l)!==((c>>WS.indexOf(q))&1)){bad++;break;}continue;}if(get(q,l)!==get(q,base)){bad++;break;}}}
console.log('states',states.length,'lanes',lanes,'sensitive lanes',bad);
