'use strict';
const base=require('./i9-multiply-s4-m-prep-dirty-alt.cjs');
const def=`
function m6powerSweep(n,M,X,s,J,e,dirty,i,kappa) {
 const groupBit=M[n-1],guard=gt(s,i,e,null,dirty);
 // i>=1 enabled implies s>=2, hence original M[0:2]=0.
 // Even divisor: the low dividend digit is unchanged by compare/subtract.
 let gates=guard.concat(dirtyDigit(M.slice(2),X.slice(1,-1),X[n-1],e,dirty[0]),[[groupBit]]);
 const prefix=k=>{if(k===0)return [[groupBit]];if(k>=n)return [];const cs=M.slice(2,k);return negate(cs,MCX(cs,groupBit,dirty),cs.map(()=>false));};
 const interval=1<<J.length;let previous=[];
 for(let base=0;base<n-1;base+=interval){const a=base===0?0:base+1,b=base+interval+1,current=[a,b].filter(k=>k<n);
  for(const k of previous)if(!current.includes(k))gates=gates.concat(prefix(k));for(const k of current)if(!previous.includes(k))gates=gates.concat(prefix(k));previous=current;
  for(let j=base;j<Math.min(n-1,base+interval);j++){const pattern=eq_bits(J,j),ctrl=[e,groupBit,...J],sgn=[true,true,...pattern];
   gates=gates.concat(negate(ctrl.concat(X[j]),MCX(ctrl.concat(X[j]),X[n-1],dirty),sgn.concat(true)));
   if(i<=j&&((kappa>>BigInt(j-i))&1n))gates=gates.concat(negate(ctrl,MCX(ctrl,X[n-1],dirty),sgn));
  }
 }
 for(const k of previous)gates=gates.concat(prefix(k));gates.push([groupBit]);
 for(let j=n-1;j>0;j--)gates.push(...fr(e,X[j],X[j-1]));return gates.concat(guard.slice().reverse());
}
function m6powerParts(n,T,H,S,en,L,kappa,extra){
 const extra2=[];for(let l=2;l<n;l++)if((l-1)&2){const word=T.slice(2,l+1);extra2.push(...negate(word,MCX(word,T[1],L),word.map((_,j)=>j===word.length-1)));}
 return [()=>extra,()=>one_stage(n,null,T,H,S,[T[0]],en,en,L,0,kappa),()=>extra2,
  ...Array.from({length:n-2},(_,j)=>()=>m6powerSweep(n,T,H,S,[T[0],T[1]],en,L,j+1,kappa)),
  ()=>extra2.slice().reverse(),()=>extra.slice().reverse()];
}
`;
module.exports={source:base.source,f:s=>{s=base.f(s);const a='function power(back){run(vp);run(extra);for(let k=0;k<127;k++)run(one_stage(128,outer,T,H,S,index,en,tmp,L,back?126-k:k,kappa),back);run(extra,true);run(vp,true);}';
 if(s.split(a).length!==2)throw Error('power host anchor');return def+s.replace(a,'function power(back){const parts=m6powerParts(128,T,H,S,en,L,kappa,extra);if(back)parts.reverse();for(const part of parts)run(part(),back);}');}};
