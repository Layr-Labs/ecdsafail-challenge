'use strict';
function create(out){
 const N=1023,WORD=262144,LIMIT=65536;
 const Values=VALUECLASS;
 let v=new Values(1023,1023);
 return {gate:(a,b,t)=>v.gate(a,b,t,out),flush(){v=new Values(1023,1023);},
 stage(){v=new Values(1023,1023);for(const q of [512,641,642,643,644,645,646,647])v.put(q,0);},
 hmr(q){v.put(q,0);},push(){v.push();},pop(){v.pop();}};
}
exports.create=Function('return '+create.toString().replace('VALUECLASS',require('./i7-upper-s3-values.cjs').Values.toString()))();
