// Per-window census of jackylee's regen R6 (q651-ten-field/r6-regen649.cjs), raw (pre-peep), erase=false.
const Q='/Users/akashbalasubramani/Desktop/ecdsafail-648w/src/point_add/construction/research/agents/midpoint-implicit-query-20261109/q651-ten-field/';
const fs=require('fs'),path=require('path'),Module=require('module');
const file=path.join(Q,'regen.cjs'),patches=require(Q+'r6-p-r649-final.js');
const edit=(s,a,b)=>{if(s.split(a).length!==2)throw Error('anchor '+a.slice(0,80));return s.replace(a,()=>b);};
let s=fs.readFileSync(file,'utf8');s=edit(s,'m.adjust=adjust;','m.adjust=s=>module.applyR42(adjust(s));');
const m=new Module(file,module);m.filename=file;m.paths=Module._nodeModulePaths(Q);
const HOOK=process.env.HOOK||'for(const [g,blocks,back] of stages){';
m.applyR42=s=>{for(const [a,b]of patches)s=edit(s,a,b);
  const n=s.split(HOOK).length-1;if(n!==1)throw Error('hook count '+n);
  return s.replace(HOOK,'let __si=0;'+HOOK+'if(globalThis.__rgStage)globalThis.__rgStage(__si++,g===walk?"walk":g===walk6?"walk6":g===park?"park":"scale",blocks.length);');};
m._compile(s,file);
const H=(process.env.H||'0,1,130,131,388,646,647,648,649,650,651,129,259').split(',').map(Number);
let cur=-1;const st=[];globalThis.__rgStage=(i,l,nb)=>{cur=i;st[i]={l,nb,ops:0,ctl:new Map(),tgt:new Map()};};
const inc=(mp,k)=>mp.set(k,(mp.get(k)||0)+1);
m.exports.emitRegenerateSparse(gs=>{const x=st[cur];if(!x)return;for(const z of gs){const a=z>>>20,b=(z>>>10)&1023,t=z&1023;x.ops++;if(a!==1023)inc(x.ctl,a);if(b!==1023)inc(x.ctl,b);inc(x.tgt,t);}},false);
let T=0;for(const [i,x] of st.entries()){T+=x.ops;console.log(`stage ${i} ${x.l} blocks=${x.nb} ops=${x.ops}`);console.log('   '+H.map(w=>`${w}:${x.ctl.get(w)||0}/${x.tgt.get(w)||0}`).join(' '));}
console.log('total',T);
