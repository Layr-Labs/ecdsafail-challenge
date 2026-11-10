'use strict';
// Per-stage-window census of logical wires touched by emitRegenerateSparse (non-erase = the emitted mode).
// usage: node census.cjs PATCHFILE [wires...]
const {loadRegen}=require('./load.cjs');
const pf=process.argv[2],H=process.argv.slice(3).map(Number);
const helpers=H.length?H:[0,1,130,131,388,646,647,648,649,650];
const {emitRegenerateSparse}=loadRegen(pf);
let cur=-1;const st=[];
globalThis.__rgStage=(i,l,nb)=>{cur=i;st[i]={label:l,blocks:nb,ops:0,ccx:0,ctl:new Map(),tgt:new Map(),maxw:0};};
const inc=(m,k)=>m.set(k,(m.get(k)||0)+1);
emitRegenerateSparse(chunk=>{const s=st[cur];for(const z of chunk){const a=z>>>20,b=(z>>>10)&1023,t=z&1023;s.ops++;if(a!==1023&&b!==1023)s.ccx++;
  if(a!==1023)inc(s.ctl,a);if(b!==1023)inc(s.ctl,b);inc(s.tgt,t);s.maxw=Math.max(s.maxw,t,a===1023?0:a,b===1023?0:b);}},process.env.ERASE==='1');
let T=0,C=0;
for(const [i,s] of st.entries()){T+=s.ops;C+=s.ccx;
  console.log(`stage ${i} ${s.label} blocks=${s.blocks} ops=${s.ops} ccx=${s.ccx} maxwire=${s.maxw}`);
  console.log('   '+helpers.map(w=>`${w}:${s.ctl.get(w)||0}/${s.tgt.get(w)||0}`).join(' '));
}
console.log('total ops',T,'ccx',C);
// any wires >=646 or others not in data
const data=new Set();for(let i=2;i<130;i++)data.add(i);for(let i=132;i<260;i++)data.add(i);for(let i=260;i<388;i++)data.add(i);for(let i=389;i<645;i++)data.add(i);
const other=new Set();for(const s of st)for(const m of [s.ctl,s.tgt])for(const k of m.keys())if(!data.has(k))other.add(k);
console.log('non-data wires touched:',[...other].sort((a,b)=>a-b).join(','));
