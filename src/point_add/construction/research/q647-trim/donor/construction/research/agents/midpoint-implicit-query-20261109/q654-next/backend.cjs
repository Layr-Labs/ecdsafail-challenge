'use strict';
const {f:oldF,d:oldD,replace,lowValuationSweep,plusOneMod,dirtyDigit}=require('./prior.cjs');
const {CanonicalUnit}=require('../field128-height-experiment/walks.cjs');
const {Reduced,SectorCanonical,emitWalk}=require('./walks.cjs');
let f=replace(oldF,'idx=vec(5,649)','idx=vec(4,649)');
f=replace(f,'if(back)run(inc);const loc=[4,5,10,32,256]','if(back)for(let i=0;i<15;i++)run(inc,true);const loc=[5,10,32,256]');
f=replace(f,'idx,[4,1,0],[3,2]),back);if(!back)run(inc,true);','idx,[3,0],[2,1]),back);if(!back)for(let i=0;i<15;i++)run(inc);');
f=replace(f,'m[W.tst]=m[W.L[n+1]];return m;','m[W.tst]=m[W.L[n+1]];m[W.fire]=m[W.R[n+1]];return m;');
const mult=Function('module','Replacement','dirtyDigit','lowValuationSweep','plusOneMod',f+'\nreturn emitForward128;')({exports:{}},CanonicalUnit,dirtyDigit,lowValuationSweep,plusOneMod);

function donor(used){const avoid=new Set(used);for(let q=0;q<640;q++)if(!avoid.has(q))return q;throw Error('no disjoint dirty loan');}
function dirtyTriples(g,t,loan){
  const out=[];
  for(let j=0;j<g.length;j++){
    const a=g[j];if(!a.includes(t)){out.push(a);continue;}
    const b=g[j+1],c=g[j+2];
    if(a.length!==3||a[2]!==t||b.length!==3||b[0]!==t||c.length!==3||a.some((v,i)=>v!==c[i]))throw Error('unexpected clean-product primitive');
    const x=[a[0],a[1],loan],y=[loan,b[1],b[2]];out.push(x,y,x,y);j+=2;
  }
  return out;
}
function dirtyMdg(M,A,B,h,e,lib){
  const loan=donor([...M,...A,...B,h,e]),t=1000;
  return dirtyTriples(lib.plus(A,B,h,e,t),t,loan).concat(dirtyDigit(M,B,h,e,loan),dirtyTriples(lib.ltg(A,B,h,e,t),t,loan));
}
function dirtyBlock(n,k,M,J,e){
  const loan=donor([...M,...J,e]);let g=[];
  for(let j=k-1;j>=0;j--)g=g.concat(dirtyDigit(M,J.slice(j,j+n),J[j+n],e,loan));
  return g;
}
let d=replace(oldD,'function mdg(M,A,B,h,e,t){return [...plus(A,B,h,e,t),...digit(M.length,M,B,h,e,t),...ltg(A,B,h,e,t)];}',
  'function mdg(M,A,B,h,e,t){return dirtyMdg(M,A,B,h,e,{plus,ltg});}');
d=replace(d,'const [e,t,D]=ws,put=g=>','const [e,t]=ws,D=t,put=g=>');
d=replace(d,'[e,tmp,sp,pad]=ws;for(let t=1;','[e,tmp]=ws,sp=tmp;for(let t=1;');
d=replace(d,'const g=fusedblock(d,t,L.slice(0,d),w,sel,tmp);','const g=dirtyBlock(d,t,L.slice(0,d),w,sel);');
d=replace(d,'e=act+6,t=act+7,x=act+8','e=act+6,t=lp[0],x=act+8');
d=replace(d,'ws={sign:sig,tag:S,fire:e,tst:t,aux:L[n+1]}','ws={sign:sig,tag:S,fire:e,tst:S[6],aux:L[n+1]}');
d=replace(d,'Wstream(G,n,false,L,R,ws,loan,sink);','emitWalk(new Reduced(n),L,R,ws,loan,false,sink);');
d=replace(d,'Wstream(G,n,true,L,R,ws,loan,sink);','emitWalk(new Reduced(n),L,R,ws,loan,true,sink);');
d=replace(d,'const wi={sign:L[1],tag:S,fire:e,tst:t,aux:x};virtualStream(n,[...vt,R[1],R[1]],[...Q,L[0],L[0]],wi,loan,sink);',
  'const wi={sign:L[1],tag:S,fire:e,tst:S[5],aux:S[6]};emitWalk(new SectorCanonical(n),[...vt,R[1],R[1]],[...Q,L[0],L[0]],wi,loan,false,sink);');
const div=Function('module','dirtyMdg','dirtyBlock','emitWalk','Reduced','SectorCanonical',d+'\nreturn inverseField;')({exports:{}},dirtyMdg,dirtyBlock,emitWalk,Reduced,SectorCanonical);
function mapped(sink,back){
  const omit=back?[648,652,655,656]:[648,653,654,656];
  const ids=new Int16Array(1024);ids.fill(-1);ids[1023]=1023;
  for(let i=0;i<657;i++)if(!omit.includes(i))ids[i]=i===(back?654:655)?(back?652:653):i;
  const q=i=>{if(ids[i]<0||ids[i]===undefined)throw Error('live removed '+[back,i]);return ids[i];};
  return(kind,data)=>{
    if(kind==='packed'){
      const g=new Uint32Array(data.length);for(let i=0;i<data.length;i++){
        const x=data[i];g[i]=(q(x>>>20&1023)<<20)|(q(x>>>10&1023)<<10)|q(x&1023);
      }sink(kind,g);
    }else if(kind==='nct')sink(kind,data.map(row=>row.map(q)));
    else sink(kind,data.map((v,i)=>i===data.length-1?v:q(v)));
  };
}
function emitMultiplySparse(sink){mult(mapped(sink,false));}
function emitDivideSparse(sink){div(128,null,null,mapped(sink,true));}
module.exports={emitMultiplySparse,emitDivideSparse};
