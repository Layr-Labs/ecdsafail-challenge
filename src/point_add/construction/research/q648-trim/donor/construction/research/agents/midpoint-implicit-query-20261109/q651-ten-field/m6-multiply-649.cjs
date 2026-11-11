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
// q648 (papers): Q648_WALK=1 uses ledger's TstRelayD (q648-walks @ 1e6557a, ../q648w/walktf.cjs) at 7 sites, 647 free.
// Q648_WALKK=1 (with Q648_WALK=1): ledger's TstRelayK (q648-walks @ c3bafc1, ../q648w/walkt1.cjs), same 7-site layout.
const WalkD=process.env.Q648_WALK==='1'?class extends (process.env.Q648_WALKK==='1'?require('../q648w/walkt1.cjs').TstRelayK:require('../q648w/walktf.cjs').TstRelayD){constructor(n){super(n,[647,648,649],654,{dirtyDigit:alt.dirtyDigit});}}:null;
class Walk extends Host{constantDigit(...args){return require('./m6-constant-fast.cjs').apply(this,args);}}
f=require('./m6-power-final.cjs').f(f);
// q648 (papers): multiply non-walk windows on 7 helpers (logical 647 free outside the walk). Q648_MUL=1 enables.
if(process.env.Q648_MUL==='1')for(const m of ['./q648/p648-power.cjs','./q648/p648-lift.cjs','./q648/p648-colour2.cjs','./q648/p648-colour1.cjs'])f=require(m).f(f);
if(process.env.Q648_WALK==='1'){
 f=replace(f,'function unitMap(n,W,K){','function unitMap(n,W,K){if(W.direct){const m=[];for(let j=0;j<n;j++){m[W.L[j]]=j;m[W.R[j]]=3*n+j;}for(let j=0;j<2*n;j++)m[W.y[j]]=n+j;m[W.L[n]]=643;m[W.R[n]]=645;m[W.fire]=646;W.tag.forEach((q,j)=>{m[q]=640+j;});m[W.sign]=644;if(W.tag.length!==3)throw Error("direct walk tags");return m;}');
 f=replace(f,"if(map){const top=G.tag.at(-1),tr=q=>{if(q===1023)return q;if(q===top){","if(map){const top=G.tag.at(-1),tr=q=>{if(q===1023)return q;if(G.direct){const z=map[q];if(!(z>=0))throw Error('unbound direct port '+q);return z;}if(q===top){");
}
const mul=Function('module','Replacement','dirtyDigit','lowValuationSweep','plusOneMod',f+'\nreturn emitForward128;')(
    {exports:{}},process.env.Q648_WALK==='1'?WalkD:Walk,pub.dirtyDigit,sweep,pub.plusOneMod);
function emitMultiplySparse(sink){
 const mapped=pub.mapped(sink,false),guard=(kind,d)=>{const check=q=>{if(q!==1023&&(q===648||q>=649||(process.env.Q648_MULBAN==='1'&&q===647)))throw Error('M6 whole-stage ban '+q);};
  if(kind==='nct')for(const r of d)for(const q of r)check(q);else if(kind==='packed')for(const x of d){check(x>>>20&1023);check(x>>>10&1023);check(x&1023);}else check(d[0]);mapped(kind,d);
 };
 const p=require('./m6-peep.cjs').wrapSparse(guard,{window:4096,mode:'commute'});mul(p.sink);p.flush();
}
module.exports={emitMultiplySparse,emitDivideSparse};
