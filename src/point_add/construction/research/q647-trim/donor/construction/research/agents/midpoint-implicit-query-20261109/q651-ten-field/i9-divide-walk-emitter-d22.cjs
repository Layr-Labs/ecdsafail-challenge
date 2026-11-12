'use strict';
// Composable with any D5-compatible carrier overlay that supplies the original
// 3-tag inner / 4-tag reverse classes, fire641/test642 and fire642/testL129.
function wrap(pub){return function(w,L,R,ws,dirty,back,sink){
 require('./i9-divide-walk-small.cjs').install(w,pub.dirtyDigit,{rot:true,pair:true,select:true});
 if(ws.aux===-1)require('./i9-divide-multi-relay.cjs').install(w,pub.dirtyDigit);
 return pub.emitWalk(w,L,R,ws,dirty,back,(k,g)=>{
  for(const x of g)if([x>>>20&1023,x>>>10&1023,x&1023].some(q=>q===643||q===644||q===645))throw Error('D18 whole-walk ban643/644/645');
  sink(k,g);
 });
};}
module.exports={wrap};
