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
const Walk=require('./multiply-nine.cjs').walk(pub);
f=require('./multiply-nine.cjs')(f);
const mul=Function('module','Replacement','dirtyDigit','lowValuationSweep','plusOneMod',f+'\nreturn emitForward128;')(
    {exports:{}},Walk,pub.dirtyDigit,sweep,pub.plusOneMod);
function emitMultiplySparse(sink){const out=pub.mapped(sink,false);mul((kind,data)=>{const ban=q=>{if(q===648||q>=650&&q!==1023)throw Error('multiply-nine forbidden '+q);};if(kind==='packed'){for(const x of data){ban(x>>>20&1023);ban(x>>>10&1023);ban(x&1023);}}else if(kind==='nct'){for(const r of data)for(const q of r)ban(q);}else ban(data[0]);out(kind,data);});}
module.exports={emitMultiplySparse,emitDivideSparse};
