'use strict';
const fs=require('node:fs'),path=require('node:path'),Module=require('node:module');
const {replace}=require('./base.cjs');
const seed=path.join(__dirname,'backend.cjs');
let text=fs.readFileSync(seed,'utf8');
function tune(f){
    f=replace(f,'vp=val_low(T,idx,tmp,L);',`vp=val_low(T,idx,tmp,L),index=idx.concat(T[0]),extra=[];
      for(let l=2;l<128;l++)if((l-1)&4){
        const word=T.slice(1,l+1),pol=word.map((_,j)=>j===word.length-1);
        extra.push(...negate(word,MCX(word,T[0],L),pol));
      }`);
    f=replace(f,'function power(back){run(vp);','function power(back){run(vp);run(extra);');
    f=replace(f,'T,H,S,idx,en,tmp,L,back?126-k:k,kappa),back);run(vp,true);',
        'T,H,S,index,en,tmp,L,back?126-k:k,kappa),back);run(extra,true);run(vp,true);');
    return f;
}
const sweep=require('./base.cjs').lowValuationSweep.toString();
if(!sweep.includes('const cs=M.slice(0,k)'))throw Error('Valuation prefix changed');
const pinned=require('../q653-next/parts.cjs').dirtyDigit;
const sweepWithPackedIndex=Function('dirtyDigit','return ('+
    sweep.replace('const cs=M.slice(0,k)','const cs=M.slice(1,k)')+');')(pinned);
function thinAtLowerCost(d){
    let out=require('./divide-port.cjs').thinDivide(d);
    out=replace(out,'new Reduced(n,5),L,R,ws,loan,false,sink);put([[S[4],R[1]],[R[1],S[4]],[S[4],R[1]]]);',
        'new Reduced(n,6),L,R,{...ws,sign:Q[n-1]},loan,false,sink);put([[Q[n-1],R[1]],[R[1],Q[n-1]],[Q[n-1],R[1]]]);');
    return out;
}
text=replace(text,"const multiply=Function('module'","f=module.tune(f);const multiply=Function('module'");
text=replace(text,'SectorCanonical,dirtyDigit,lowValuationSweep,plusOneMod,require(',
    'SectorCanonical,dirtyDigit,module.sweep,plusOneMod,require(');
text=replace(text,"require('./divide-port.cjs').thinDivide(d)","module.thin(d)");
const m=new Module(seed,module);m.filename=seed;m.paths=module.paths;m.tune=tune;m.sweep=sweepWithPackedIndex;m.thin=thinAtLowerCost;
m._compile(text,seed);module.exports=m.exports;
