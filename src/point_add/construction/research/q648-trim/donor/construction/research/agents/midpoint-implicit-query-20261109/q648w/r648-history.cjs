'use strict';
// Drop-in history module (stage-config "historyModule") for jackylee0424's 649 tree: their R6 regeneration
// (q651-ten-field/r6-regen649.cjs, byte-identical gates when Q648_REGEN is unset) or, with Q648_REGEN=1, ledger's
// seven-site regeneration (sites 0,1,130,131,646,647,648; logical 388 never touched), or with Q648_REGEN=save649 the
// 8-site TstRelay(5) stage-4 saving. See r648-regen.cjs.
// Same interface and the same W4096 commute peep sink as r6-regen649.cjs.
const path=require('path');
const {load}=require('./r648-load.cjs');
// Q648_REGEN: unset = their R6; '1' = seven sites; 'save649' = 8 sites with the TstRelay(5) stage-4 walk (-13.5M/call).
const mode=process.env.Q648_REGEN||'';if(!['','1','1k','1kr','save649'].includes(mode))throw Error('Q648_REGEN must be unset, 1, 1k, 1kr or save649');
const RG=require('./r648-regen.cjs');const B=load(mode==='1'?RG.EDITS:mode==='1k'?RG.EDITS_1K:mode==='1kr'?RG.EDITS_1KR:mode==='save649'?RG.EDITS_SAVE649:[]);
const Q=path.join(__dirname,'../q651-ten-field');
module.exports={emitRegenerateSparseRaw:B.raw,emitRegenerateSparse(sink,erase=false){
  let batch=[];const flush=()=>{if(batch.length){sink(batch);batch=[];}};
  const p=require(path.join(Q,'r6-peep.cjs')).createPeep((a,b,t)=>{batch.push((a<<20)|(b<<10)|t);if(batch.length===65536)flush();},{mode:'commute',window:4096});
  B.raw(gs=>{for(const x of gs)p.gate(x>>>20&1023,x>>>10&1023,x&1023);},erase);p.flush();flush();}};
