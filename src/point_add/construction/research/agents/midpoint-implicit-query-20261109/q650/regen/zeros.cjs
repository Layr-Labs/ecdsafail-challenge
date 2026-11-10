'use strict';
// Per stage: wires that are zero on every lane at every point of the stage (sampled support, not proof).
const {loadRegen}=require('./load.cjs');const {cases}=require('./sim.cjs');
const [patch,N='256',seed='3',W0='8']=process.argv.slice(2);const W=+W0;
const cs=cases(+N,+seed,'mix');
// reuse sim run but with gate hook: reimplement minimal
const {emitRegenerateSparse}=loadRegen(patch);
const n=128,S=new Uint32Array(1024*W),lanes=32*W;
const put=(wire,lane,bit)=>{if(bit)S[wire*W+(lane>>5)]|=1<<(lane&31);};
let s=12345n;const cr=require("crypto");const g=()=>BigInt("0x"+cr.randomBytes(8).toString("hex"));
for(let l=0;l<lanes;l++){const c=cs[l%cs.length];for(let i=0;i<n;i++){put(129-i,l,Number((c.r>>BigInt(i))&1n));put(259-i,l,Number((c.v>>BigInt(i))&1n));}
  for(let i=0;i<256;i+=64){const y=g();for(let j=0;j<64;j++)put(389+i+j,l,Number((y>>BigInt(j))&1n));}}
for(let w=0;w<W;w++)S[645*W+w]=0xffffffff;
let ever=null,cur=-1;const res=[];
const fin=()=>{if(cur<0)return;const nz=[];for(let q=0;q<1024;q++){let o=0;for(let w=0;w<W;w++)o|=ever[q*W+w];if(o)nz.push(q);}res.push([cur,nz]);};
globalThis.__rgStage=(i)=>{fin();cur=i;ever=S.slice();};
emitRegenerateSparse(chunk=>{for(const z of chunk){const a=z>>>20,b=(z>>>10)&1023,t=(z&1023)*W;
  if(a===1023){for(let w=0;w<W;w++){S[t+w]^=0xffffffff;ever[t+w]|=S[t+w];}}
  else if(b===1023){const A=a*W;for(let w=0;w<W;w++){S[t+w]^=S[A+w];ever[t+w]|=S[t+w];}}
  else{const A=a*W,B=b*W;for(let w=0;w<W;w++){S[t+w]^=S[A+w]&S[B+w];ever[t+w]|=S[t+w];}}}},false);
fin();
const all=new Set();for(let i=0;i<645;i++)all.add(i);for(let i=646;i<=650;i++)all.add(i);
const rng=a=>{const o=[];let st=null,pr=null;for(const x of a){if(st===null){st=pr=x;}else if(x===pr+1)pr=x;else{o.push(st===pr?''+st:st+'-'+pr);st=pr=x;}}if(st!==null)o.push(st===pr?''+st:st+'-'+pr);return o.join(',');};
for(const [i,nz] of res){const z=new Set(nz);console.log('stage',i,'always-zero:',rng([...all].filter(q=>!z.has(q))));}
