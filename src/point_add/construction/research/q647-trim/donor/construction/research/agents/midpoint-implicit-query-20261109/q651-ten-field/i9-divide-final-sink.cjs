'use strict';
// Compatible S4 subset: NOT frames and indexed cancellation BEFORE one W4096 sink.
// No symbolic zero assumptions; flush every frame at every metadata boundary.
function wrapSparse(sink){
 const final=require('./i9-divide-peep.cjs').wrapSparse(sink,{mode:'commute',window:4096});
 let batch=[];const send=()=>{if(batch.length){final.sink('packed',batch);batch=[];}};
 const index=require('./i9-divide-s3-u-peep-index.cjs').createPeep((a,b,t)=>{batch.push((a<<20)|(b<<10)|t);if(batch.length===65536)send();},{window:65536});
 const frame=require('./i9-divide-s3-u-peep-frame2.cjs').createPeep(index.gate,{window:4096});
 const flush=()=>{frame.flush();index.flush();send();final.flush();};
 return {sink(k,d){if(k==='packed')for(const x of d)frame.gate(x>>>20&1023,x>>>10&1023,x&1023);else if(k==='nct')for(const r of d)frame.gate(r.length>1?r[0]:1023,r.length>2?r[1]:1023,r.at(-1));else{flush();sink(k,d);}},flush};
}
module.exports={wrapSparse};
