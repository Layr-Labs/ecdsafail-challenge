'use strict';
module.exports={tags:4,native641Free:true,name:'D22 dear four-tag virtual-test',emit(pub,w,L,R,ws,dirty,back,sink){
 if(back)throw Error('D24 inner direction');
 require('./i9-divide-walk-small.cjs').install(w,pub.dirtyDigit,{rot:true,pair:true,select:true});
 require('./i9-divide-one-predicate-relay.cjs').install(w,pub.dirtyDigit);
 let buf=[];const flush=()=>{if(buf.length){sink('packed',buf);buf=[];}};
 const map=q=>q===ws.fire?ws.tst:q;
 const a=require('./i9-divide-anf-eliminate.cjs').make(ws.tst,r=>{const qs=r.map(map);if(qs.includes(641)||new Set(qs).size!==qs.length)throw Error('D24 inner alias/641');buf.push(((qs.length>1?qs[0]:1023)<<20)|((qs.length>2?qs[1]:1023)<<10)|qs.at(-1));if(buf.length>=16384)flush();},{cap:10000,loan:dirty,cubes:true});
 pub.emitWalk(w,L,R,ws,dirty,back,a.sink);a.finish();flush();
}};
