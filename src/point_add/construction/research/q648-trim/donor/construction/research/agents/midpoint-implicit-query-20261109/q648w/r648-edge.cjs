'use strict';
// Directed cases for the scale case split and park top bit. usage: node edge.cjs PATCH [seed] [W] [extra-random-per-clz]
const {midpoint,p}=require('/Users/akashbalasubramani/Desktop/ecdsafail-649rg/src/point_add/construction/research/agents/midpoint-implicit-query-20261109/q650/regen/sim.cjs');const {runCases}=require('./r648-sim.cjs');const run=(patch,cs,o)=>runCases(cs,o.W,o.seed);
const cr=require('crypto');
const [patch,seed='1',W='16',per='2']=process.argv.slice(2);
const rnd=bits=>bits<=0?0n:BigInt('0x'+cr.randomBytes(Math.ceil(bits/8)).toString('hex'))&((1n<<BigInt(bits))-1n);
const gcd=(a,b)=>{while(b){[a,b]=[b,a%b];}return a;};
const egcd=(a,b)=>{let [r0,r1,s0,s1]=[a,b,1n,0n];while(r1){const q=r0/r1;[r0,r1]=[r1,r0-q*r1];[s0,s1]=[s1,s0-q*s1];}return [r0,s0];};
const inv=(a,m)=>{const [g,s]=egcd(((a%m)+m)%m,m);if(g!==1n)throw Error('ni');return ((s%m)+m)%m;};
const mk=(r,v)=>({r,v,u:v===1n?0n:p*inv(r%v,v)%v});
const cs=[];const coprimeR=(v,r)=>{if(v===1n)return r;while(gcd(r,v)!==1n)r=(r+1n)&((1n<<128n)-1n);return r;};
const M128=(1n<<128n)-1n;
// fixed specials
for(const v of [1n,2n,3n,4n,5n,(1n<<126n),(1n<<126n)+1n,(1n<<127n)-1n,(1n<<127n),(1n<<127n)+1n,(1n<<127n)+3n,M128,M128-1n])
  for(const r of [0n,1n,2n,(1n<<127n)-1n,1n<<127n,M128,M128-1n,v>0n?v-1n:0n,v,v+1n,rnd(128)]){if(r>M128)continue;const rr=coprimeR(v,r);if(rr===0n&&v!==1n)continue;cs.push(mk(rr,v));}
// every V bit length, R forcing b=1 (R >= V<<clz) and b=0, plus random
for(let bits=1;bits<=128;bits++)for(let j=0;j<+per;j++){
  const v=(rnd(bits-1))|(1n<<BigInt(bits-1)),clz=128-bits,vn=v<<BigInt(clz);
  const hi=vn+rnd(128)%((M128-vn)+1n); // >= V<<clz : top quotient bit 1
  cs.push(mk(coprimeR(v,hi),v));cs.push(mk(coprimeR(v,rnd(128)%v),v));cs.push(mk(coprimeR(v,rnd(128)),v));}
// genuine midpoints
for(let i=0;i<256;i++)cs.push((()=>{const m=midpoint(rnd(256)%(p-1n)+1n);return {r:m.r,v:m.v,u:m.u};})());
// small-x midpoints (v=1)
for(let i=0;i<16;i++){const m=midpoint(rnd(1+Number(rnd(7)))+1n);cs.push({r:m.r,v:m.v,u:m.u});}
let total=0,bad=0;const Wn=+W,lanes=32*Wn;
for(let off=0;off<cs.length;off+=lanes){const chunk=cs.slice(off,off+lanes);const res=run(patch,chunk,{W:Wn,seed:+seed+off});
  // lanes beyond chunk wrap (duplicates) - count unique
  total+=chunk.length;bad+=res.bad;if(res.bad||res.dirty.length)console.log('chunk',off,JSON.stringify(res).slice(0,600));}
console.log('edge cases',total,'bad lanes',bad);
