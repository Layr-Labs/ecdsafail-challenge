'use strict';
module.exports=s=>{
 s=require('./upper-partial.cjs').upper(s);
 const anchor='return {pointReference,exceptionTable,shellWithFieldOracles,';
 if(s.split(anchor).length!==2)throw Error('I upper instrumentation anchor');
 const hooks=`
let irow=null,iwindow=null;
for(const [cn,C] of Object.entries({UnitPreparation,UniversalGeneral,TruncatedGeneral,AlignedGeneral,SingleAffineGeneral,EarlyUnit,EarlyGeneral,OddEstimateGeneral,UnguardedGeneral}))for(const name of Object.getOwnPropertyNames(C.prototype)){
 const d=Object.getOwnPropertyDescriptor(C.prototype,name),isWindow=['trial','affine','signProbe','estimate','removeDebt'].includes(name);
 if(typeof d.value!=='function'||(!isWindow&&name!=='emit'))continue;
 const fn=d.value;C.prototype[name]=function(...args){const old=irow,ow=iwindow;
  if(name==='emit')irow={kind:cn==='EarlyUnit'||this instanceof UnitPreparation?'U':'G',k:this.k};
  if(isWindow&&!iwindow){iwindow={...irow,name,target:name==='signProbe'?args[1]:null};if(globalThis.__iUpperWindow)globalThis.__iUpperWindow(iwindow);}
  try{return fn.apply(this,args);}finally{if(isWindow&&!ow&&globalThis.__iUpperWindow)globalThis.__iUpperWindow(null);irow=old;iwindow=ow;}
 };
}
`;
 return s.replace(anchor,hooks+anchor);
};
