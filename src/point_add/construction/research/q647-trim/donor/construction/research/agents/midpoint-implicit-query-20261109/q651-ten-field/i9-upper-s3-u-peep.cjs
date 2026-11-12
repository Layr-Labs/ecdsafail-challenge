'use strict';
// R43 S2: reversible permutation frame -> S1 -> NOT frame -> indexed cancellation.
// Bodies are embedded so the existing upper source overlay remains self-contained.
function combined(out,options={}){
 const stats={input:0,output:0,inputCCX:0,outputCCX:0,removed:0,removedCCX:0};
 const final=INDEX((a,b,z)=>{if(b===1023){b=a;a=1023;}out(a,b,z);stats.output++;if(a!==1023&&b!==1023)stats.outputCCX++;},{window:65536});
 const frame=FRAME(final.gate,{window:4096});
 const first=SWAP(frame.gate,{mode:'commute',window:4096});
 const values=VALUE(first.gate);
 function gate(a,b,z){stats.input++;if(a!==1023&&b!==1023)stats.inputCCX++;values.gate(a,b,z);}
 function flush(){first.flush();frame.flush();final.flush();stats.removed=stats.input-stats.output;stats.removedCCX=stats.inputCCX-stats.outputCCX;}
 return {gate,flush,stats,stage:values.stage,hmr:values.hmr,push:values.push,pop:values.pop};
}
const createPeep=Function('return '+combined.toString().replace('INDEX(', '('+require('./i9-upper-s3-u-peep-index.cjs').createPeep.toString()+')(').replace('FRAME(', '('+require('./i9-upper-s3-u-peep-frame2.cjs').createPeep.toString()+')(').replace('SWAP(', '('+require('./i9-upper-s3-u-peep-swap.cjs').createPeep.toString()+')(').replace('VALUE(', '('+require('./i9-upper-s3-u-value-pass.cjs').create.toString()+')('))();
function wrapSparse(sink,options){const p=createPeep((a,b,z)=>sink('nct',[a===1023?(b===1023?[z]:[b,z]):b===1023?[a,z]:[a,b,z]]),options);function wrapped(kind,data){if(kind==='nct')for(const r of data)p.gate(r.length===3?r[0]:1023,r.length>=2?r.at(-2):1023,r.at(-1));else if(kind==='packed')for(const x of data)p.gate(x>>>20&1023,x>>>10&1023,x&1023);else{p.flush();sink(kind,data);}}return {sink:wrapped,flush:p.flush,stats:p.stats};}
module.exports={createPeep,wrapSparse};
