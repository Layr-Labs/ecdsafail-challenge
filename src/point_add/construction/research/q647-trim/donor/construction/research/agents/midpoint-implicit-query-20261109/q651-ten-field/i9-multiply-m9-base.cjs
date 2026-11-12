// M8 PARTIAL: six-helper walks, seven-helper surrounding windows. S1 composition; one final sink.
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
const alt=published.withDigit(require('./i9-multiply-s4-m-alternating.cjs').alternatingDigit);
const Host=require('./i9-multiply-m8-walk-relay.cjs')(alt,6);
class Walk extends Host{constantDigit(a,b,h,e){
 const self=this,tape={loan(used,n){const block=new Set(used),out=self.y.filter(q=>!block.has(q)).slice(0,n);if(out.length!==n)throw Error('S4 digit loans');return out;},out(x,y,t){self.raw(x===1023?-1:x,y===1023?-1:y,t);}};
 require('./i9-multiply-s3-implicit-top.cjs').implicitTopDigit(tape,[...b,h],[...a,-1001],[e],false);
}}
require('./i9-multiply-s3-field-rotate.cjs').adapt(new Walk(128));
f=require('./i9-multiply-s4-m-m7-transform.cjs')(f);
f=replace(f,'m[W.L[n]]=646;m[W.R[n]]=644;m[W.tst]=642;m[W.fire]=645;','m[W.L[n]]=645;m[W.R[n]]=643;m[W.tst]=641;m[W.fire]=644;');
f=replace(f,'m[W.sign]=643;m[W.aux]=644;','m[W.sign]=642;m[W.aux]=643;');
f=replace(f,'if(q===G.tag.at(-3)&&block.extraPort','if(q===G.tag.at(-4)&&block.thirdPort!==null&&block.thirdPort!==undefined)q=block.thirdPort;else if(q===G.tag.at(-3)&&block.extraPort');
f=replace(f,'tg=W.tag.slice(0,-1)','tg=[]');f=replace(f,"if(641+tg.length>646)throw Error('walk sites');",'m[W.tag.at(-2)]=640;');f=replace(f,'else if(q===G.tag.at(-2))q=block.tagPort;',''); // D22 lowers every non-top tag before unitMap.
const mul=Function('module','Replacement','dirtyDigit','lowValuationSweep','plusOneMod',f+'\nreturn emitForward128;')(
    {exports:{}},Walk,pub.dirtyDigit,sweep,pub.plusOneMod);
function emitMultiplySparse(sink){
 const mapped=pub.mapped(sink,false),guard=(kind,d)=>{const check=q=>{if(q!==1023&&q>=647)throw Error('M7 whole-stage ban '+q);};
 if(kind==='nct')for(const r of d)for(const q of r)check(q);else if(kind==='packed')for(const x of d){check(x>>>20&1023);check(x>>>10&1023);check(x&1023);}else check(d[0]);mapped(kind,d);};
 const p=require('./i9-multiply-s4-sink.cjs').wrapSparse(guard,{window:4096,mode:'commute'});mul(p.sink);p.flush();
}
module.exports={emitMultiplySparse,emitDivideSparse,mul,Walk,f,status:'PARTIAL:646 still used outside walks'};
