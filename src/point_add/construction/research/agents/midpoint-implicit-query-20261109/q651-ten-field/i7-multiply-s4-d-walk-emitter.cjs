'use strict';
// Composable with any D5-compatible carrier overlay that supplies the original
// 3-tag inner / 4-tag reverse classes, fire642/test643 and fire643/testL129.
function wrap(pub){return function(w,L,R,ws,dirty,back,sink){
 require('./i7-multiply-d14-walk-small.cjs').install(w,pub.dirtyDigit,{rot:true,pair:true,select:true});
 if(ws.aux===-1)require('./i7-multiply-s4-d-relay-cancel.cjs').install(w,pub.dirtyDigit);
 return pub.emitWalk(w,L,R,ws,dirty,back,(k,g)=>{
  for(const x of g)if([x>>>20&1023,x>>>10&1023,x&1023].some(q=>q===644||q===645))throw Error('D10 whole-walk ban644/645');
  sink(k,g);
 });
};}
module.exports={wrap};
