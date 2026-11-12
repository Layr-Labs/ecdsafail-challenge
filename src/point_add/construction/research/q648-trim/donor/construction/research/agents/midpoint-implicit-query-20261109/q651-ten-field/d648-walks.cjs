'use strict';
// Q648_DIV walk dispatch (evict): 7-site D14 walks from ledger's q648w (3bfbb91 / bf48182). Logical 643 is never emitted.
//   inner  : D2Canonical(n,3) relay -> TstRelay1E(n)       on {641 tag, 642 fire}
//   rev    : D2ReducedImpl(n,4) relay -> TstRelayRE(n,4)   on {641, L[n+1]=650 tags, 642 fire}
//   outer  : Reduced(n,7) tag2 643 -> Q121 (zero, untouched by the walk; count is parked in Q0..Q5)
//   rek    : same port layout, TstRelayKRE(n,2) (ledger 853885c; cheaper)
// Q648_DIV is a comma list of parts (inner,rev,...) or 'all'.
const parts=()=>{const s=(process.env.Q648_DIV||'').split(',').map(x=>x.trim()).filter(Boolean);return p=>s.includes('all')||s.includes(p);};
function wrapEmit(raw,wrapped){
 const on=parts();if(!on('inner')&&!on('rev')&&!on('rek')&&!on('outer'))return wrapped;
 const {TstRelay1E,TstRelayKRE}=require('../q648w/walkt1.cjs'),{TstRelayRE}=require('../q648w/walktf.cjs');
 const small=v=>{if(on('rot'))require('./d14-walk-small.cjs').install(v,raw.dirtyDigit,{rot:true,pair:false,select:false});};
 return function(w,L,R,ws,dirty,back,sink){
  const nm=w.constructor.name,n=w.n;
  if(on('inner')&&nm==='D2Canonical'&&!back){
   const v=new TstRelay1E(n,{dirtyDigit:raw.dirtyDigit,maxRelay:+(process.env.Q648_IMR||5),...(on('ra')?{relayAt:require('../q648w/relayAt-inner1.json')}:{})});small(v);
   return raw.emitWalk(v,L,R,{sign:ws.sign,tag:[ws.tag[0],-1],fire:ws.fire,tst:-1,aux:-1},dirty,back,sink);
  }
  if((on('rev')||on('rek'))&&nm==='D2ReducedImpl'&&back){
   const v=on('rek')?new TstRelayKRE(n,2,{dirtyDigit:raw.dirtyDigit,maxRelay:+(process.env.Q648_RMR||4),...(on('ra')?{relayAt:require('../q648w/relayAt-revKR2.json')}:{})}):new TstRelayRE(n,4,{dirtyDigit:raw.dirtyDigit});small(v);
   return raw.emitWalk(v,L,R,{...ws,tag:[ws.tag[0],L[n+1],-1],fire:ws.tag[1],tst:-1,aux:-1},dirty,back,sink);
  }
  if(on('outer')&&nm==='SectorReduced'&&!back){
   // count bits sit in Q0..Q5 during the outer walk; Q6..Q121 are zero and untouched by it, so tag2 moves 643 -> Q121.
   const q121=L[0]+3*n+121;if(L[0]!==0||!ws.tag.includes(643))throw Error('d648 outer layout');
   return wrapped(w,L,R,{...ws,tag:ws.tag.map(q=>q===643?q121:q)},dirty,back,sink);
  }
  return wrapped(w,L,R,ws,dirty,back,sink);
 };
}
module.exports={wrapEmit,parts};
