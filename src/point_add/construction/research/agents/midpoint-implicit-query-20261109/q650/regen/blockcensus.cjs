'use strict';
// For a stage index and wires, list per-block touches. usage: node blockcensus.cjs PATCH STAGE w1 w2 ...
const {loadRegen}=require('./load.cjs');
const [pf,si,...ws]=process.argv.slice(2);const W=ws.map(Number);
const {emitRegenerateSparse}=loadRegen(pf);
let cur=-1,blk=0;globalThis.__rgStage=(i)=>{cur=i;blk=0;};
emitRegenerateSparse(chunk=>{if(cur!==+si)return;const c=new Map();const used=new Set();
  for(const z of chunk){const a=z>>>20,b=(z>>>10)&1023,t=z&1023;for(const q of [a,b,t])if(q!==1023)used.add(q);for(const w of W){if(a===w||b===w)c.set(w+'c',(c.get(w+'c')||0)+1);if(t===w)c.set(w+'t',(c.get(w+'t')||0)+1);}}
  if(c.size)console.log('block',blk,'ops',chunk.length,[...c].map(x=>x.join('=')).join(' '),'| helpers used:',[0,1,130,131,388,646,647,648,649,650].filter(h=>used.has(h)).join(','));blk++;});
