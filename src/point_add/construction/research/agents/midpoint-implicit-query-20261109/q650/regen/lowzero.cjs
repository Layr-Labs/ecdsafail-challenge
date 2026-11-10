'use strict';
// Exactness of the masked low bits in the single scale core. Emit the core UNMASKED (Q650_NOMASK=1): M's low bits
// are then ordinary wires 0,1. Abstract interpretation from w0=w1=0: a gate targeting w keeps it zero only if one of
// its controls is a known-zero w. If w0,w1 stay zero for the whole core, every gate touching them is the identity in
// that run, so deleting them (the G=0 masked circuit) equals the core with low bits 0, for any contents of w0,w1.
process.env.Q650_NOMASK='1';
const {loadRegen}=require('./load.cjs');
const {emitRegenerateSparse}=loadRegen(process.argv[2]);
const W=[0,1];const blocks=[];
globalThis.__q650blk=(inst,g)=>{if(inst.lo&&inst.constructor.name==='Core')blocks.push(g.slice());};
emitRegenerateSparse(()=>{},false);
// core blocks are the Bc blocks that are not norms: norms touch tags (incl. wires 0,1) legitimately, so isolate:
const k=7,core=blocks.slice(k,-k).flat();
let zero=[true,true],touch=0,bad=0;
for(const z of core){const a=z>>>20,b=(z>>>10)&1023,t=z&1023;const ia=W.indexOf(a),ib=W.indexOf(b),it=W.indexOf(t);
  if(ia>=0||ib>=0||it>=0)touch++;
  if(it>=0){const killed=(ia>=0&&zero[ia])||(ib>=0&&zero[ib]);if(!killed){zero[it]=false;bad++;}}}
// norms/denorms must not touch M's low bits except as tags (they do not read M[0..1] wires 0,1 as modulus)
const Gt=core.filter(z=>(z&1023)===132).length;console.log('G=M[127] as target in core',Gt);console.log('blocks',blocks.length,'core gates',core.length,'gates touching low wires',touch,'zero-breaking targets',bad,'final known-zero',zero);
