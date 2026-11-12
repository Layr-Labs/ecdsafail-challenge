'use strict';
// Algebraic NCT transforms only; no clean-site or input-value assumptions.
const path=require('path');
const root=__dirname;
function createPeep(out,options={}){
 const index=require(path.join(root,'i9-multiply-s3-u-peep-index.cjs')).createPeep(out,{window:65536});
 const frame=require(path.join(root,'i9-multiply-s3-u-peep-frame2.cjs')).createPeep(index.gate,{window:4096});
 const swap=require(path.join(root,'i9-multiply-s3-u-peep-swap.cjs')).createPeep(frame.gate,{window:4096,mode:'commute'});
 return {gate:swap.gate,flush(){swap.flush();frame.flush();index.flush();}};
}
function wrapSparse(sink,options){let batch=[];const send=()=>{if(batch.length){sink('packed',batch);batch=[];}};
 const p=createPeep((a,b,t)=>{batch.push((a<<20)|(b<<10)|t);if(batch.length===65536)send();},options);
 return {sink(k,d){if(k==='packed')for(const x of d)p.gate(x>>>20&1023,x>>>10&1023,x&1023);else if(k==='nct')for(const r of d)p.gate(r.length>1?r[0]:1023,r.length>2?r[1]:1023,r.at(-1));else{p.flush();send();sink(k,d);}},flush(){p.flush();send();}};
}
module.exports={createPeep,wrapSparse};
