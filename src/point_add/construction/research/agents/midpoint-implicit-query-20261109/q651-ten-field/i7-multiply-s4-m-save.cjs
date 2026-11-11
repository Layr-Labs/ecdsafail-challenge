// M7 seven-helper short.multiply. S1 donor composition, W4096 once.
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
const alt=published.withDigit(require('./i7-multiply-s4-m-alternating.cjs').alternatingDigit);
const Host=require('./i7-multiply-s4-m-walk-relay.cjs')(alt,5);
class Walk extends Host{constantDigit(a,b,h,e){
 const self=this,tape={loan(used,n){const block=new Set(used),out=self.y.filter(q=>!block.has(q)).slice(0,n);if(out.length!==n)throw Error('S4 digit loans');return out;},out(x,y,t){self.raw(x===1023?-1:x,y===1023?-1:y,t);}};
 require('./i7-multiply-s3-implicit-top.cjs').implicitTopDigit(tape,[...b,h],[...a,-1001],[e],false);
}}
require('./i7-multiply-s3-field-rotate.cjs').adapt(new Walk(128));
f=require('./i7-multiply-s4-m-m7-transform.cjs')(f);
const mul=Function('module','Replacement','dirtyDigit','lowValuationSweep','plusOneMod',f+'\nreturn emitForward128;')(
    {exports:{}},Walk,pub.dirtyDigit,sweep,pub.plusOneMod);
function emitMultiplySparse(sink){
 const mapped=pub.mapped(sink,false),guard=(kind,d)=>{const check=q=>{if(q!==1023&&q>=647)throw Error('M7 whole-stage ban '+q);};
 if(kind==='nct')for(const r of d)for(const q of r)check(q);else if(kind==='packed')for(const x of d){check(x>>>20&1023);check(x>>>10&1023);check(x&1023);}else check(d[0]);mapped(kind,d);};
 const p=require('./i7-multiply-s4-sink.cjs').wrapSparse(guard,{window:4096,mode:'commute'});mul(p.sink);p.flush();
}
module.exports={emitMultiplySparse,emitDivideSparse,mul,Walk,f};
