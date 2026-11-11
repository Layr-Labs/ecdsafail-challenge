'use strict';
function wrap(pub){return function(w,L,R,ws,dirty,back,sink){
 require('./i9-divide-walk-small.cjs').install(w,pub.dirtyDigit,{rot:true,pair:true,select:true});
 const inner=ws.aux===-1&&!back;
 if(ws.aux===-1)require(inner?'./i9-divide-hosted-test.cjs':'./i9-divide-multi-relay.cjs').install(w,pub.dirtyDigit);
 const next=inner?{...ws,fire:ws.tst,tst:-1}:ws;
 const result=pub.emitWalk(w,L,R,next,dirty,back,(k,g)=>{
  for(const x of g)for(const q of [x>>>20&1023,x>>>10&1023,x&1023])if([643,644,645].includes(q)||(inner&&q===641))throw Error('D23 inner ban '+q);
  sink(k,g);
 });
 if(inner)w.d23virtual.finish();
 return result;
};}
module.exports={wrap};

