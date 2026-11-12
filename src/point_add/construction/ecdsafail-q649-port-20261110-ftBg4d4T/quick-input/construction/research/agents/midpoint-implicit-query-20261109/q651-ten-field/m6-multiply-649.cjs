// M6: eight-helper short.multiply; fixed five power-host digits, W4096 commute.
'use strict';
const published=require('./public-backend.cjs');
const {sharedDigit}=require('./shared-digit.cjs');
const pub=published.withDigit(sharedDigit);
const {replace}=require('../q653-next/parts.cjs');
const {emitDivideSparse}=require('./divide.cjs').build(pub);
let f=replace(pub.f,'vp=val_low(T,idx,tmp,L);',`vp=val_low(T,idx,tmp,L),index=idx.concat(T[0]),extra=[];
    for(let l=2;l<128;l++)if((l-1)&4){
        const word=T.slice(1,l+1),pol=word.map((_,j)=>j===word.length-1);
        extra.push(...negate(word,MCX(word,T[0],L),pol));
    }`);
f=replace(f,'function power(back){run(vp);','function power(back){run(vp);run(extra);');
f=replace(f,'T,H,S,idx,en,tmp,L,back?126-k:k,kappa),back);run(vp,true);',
    'T,H,S,index,en,tmp,L,back?126-k:k,kappa),back);run(extra,true);run(vp,true);');
const sweep=Function('dirtyDigit','return ('+
    replace(pub.lowValuationSweep.toString(),'const cs=M.slice(0,k)','const cs=M.slice(1,k)')+');')(pub.dirtyDigit);
const alt=published.withDigit(require('./m6-alternating.cjs').alternatingDigit);
const Host=require('./m6-host-walk.cjs')(alt,5);
class Walk extends Host{constantDigit(...args){return require('./m6-constant-fast.cjs').apply(this,args);}}
f=require('./m6-power-final.cjs').f(f);
const mul=Function('module','Replacement','dirtyDigit','lowValuationSweep','plusOneMod',f+'\nreturn emitForward128;')(
    {exports:{}},Walk,pub.dirtyDigit,sweep,pub.plusOneMod);
function emitMultiplySparse(sink){
 const mapped=pub.mapped(sink,false),guard=(kind,d)=>{const check=q=>{if(q!==1023&&(q===648||q>=649))throw Error('M6 whole-stage ban '+q);};
  if(kind==='nct')for(const r of d)for(const q of r)check(q);else if(kind==='packed')for(const x of d){check(x>>>20&1023);check(x>>>10&1023);check(x&1023);}else check(d[0]);mapped(kind,d);
 };
 const p=require('./m6-peep.cjs').wrapSparse(guard,{window:4096,mode:'commute'});mul(p.sink);p.flush();
}
module.exports={emitMultiplySparse,emitDivideSparse};
