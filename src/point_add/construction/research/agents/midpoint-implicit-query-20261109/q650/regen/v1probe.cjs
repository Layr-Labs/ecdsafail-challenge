'use strict';
// V=1: walk6's bank input is fixed (V=1, rm=0). Flip one candidate wire per lane at walk6 entry and check walk6 is
// then identity on that wire and unchanged elsewhere (exhaustive for V=1: walk6 touches only banks, helpers, T[0]).
const {loadRegen}=require('./load.cjs');
const W=+process.argv[3]||8,lanes=32*W,patch=process.argv[2];
const cands=(process.env.CANDS||"").split(",").filter(Boolean).map(Number);if(!cands.length)for(let q=0;q<650;q++)if(q!==645)cands.push(q); // bank data wires except aux/tst
const {emitRegenerateSparse}=loadRegen(patch);
const S=new Uint32Array(1024*W);
const put=(w,l,b)=>{if(b)S[w*W+(l>>5)]|=1<<(l&31);else S[w*W+(l>>5)]&=~(1<<(l&31));};
const get=(w,l)=>(S[w*W+(l>>5)]>>>(l&31))&1;
const R=0x123456789abcdef0fedcba9876543210n;
for(let l=0;l<lanes;l++){for(let i=0;i<128;i++){put(129-i,l,Number((R>>BigInt(i))&1n));}put(259,l,1);}
for(let w=0;w<W;w++)S[645*W+w]=0xffffffff;
let cur=-1,snap0=null;
globalThis.__rgStage=(i)=>{cur=i;if(i===2){for(let l=1;l<lanes&&l-1<cands.length;l++)put(cands[l-1],l,1-get(cands[l-1],l));snap0=S.slice();}};
emitRegenerateSparse(chunk=>{if(cur>2)return;for(const z of chunk){const a=z>>>20,b=(z>>>10)&1023,t=(z&1023)*W;
  if(a===1023){for(let w=0;w<W;w++)S[t+w]^=0xffffffff;}else if(b===1023){const A=a*W;for(let w=0;w<W;w++)S[t+w]^=S[A+w];}else{const A=a*W,B=b*W;for(let w=0;w<W;w++)S[t+w]^=S[A+w]&S[B+w];}}},false);
// after stage 2 (S now = state after walk6, since stages >2 skipped)
const ok=[];
for(let l=1;l<lanes&&l-1<cands.length;l++){const w=cands[l-1];let same=true;
  for(let q=0;q<1024;q++){const ref=get(q,0)^(q===w?1:0);if(get(q,l)!==ref){same=false;break;}}
  if(same)ok.push(w);}
console.log('V=1 walk6-transparent candidate wires:',ok.length?ok.join(','):'none');
