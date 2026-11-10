'use strict';
const path=require('path');
const {checkedSource}=require('../field128-height-experiment/pinned.cjs');
const {CanonicalUnit,ReducedGcdWalk}=require('../field128-height-experiment/walks.cjs');
const previous=checkedSource(path.join(__dirname,'../field656-clean-lease/index.cjs'),
  '28d817c8e1a9ecd89f2569af62b1f0867ebf5acd99c4b6b6d6c30faac9777612');
const parent=Function('require','module',previous+'\nreturn {f,d,replace};')(require,{exports:{}});
const replace=parent.replace;

// A controlled restoring digit with arbitrary target h and no clean product
// scratch. Each 3-control gate restores the same arbitrary dirty wire.
function dirtyDigit(A,B,h,e,loan) {
  const n=A.length, last=n-1, out=[];
  const X=x=>out.push([x]), C=(a,b)=>out.push([a,b]), T=(a,b,c)=>out.push([a,b,c]);
  function three(a,b,c,d) {
    T(a,b,loan);T(loan,c,d);T(a,b,loan);T(loan,c,d);
  }
  if(n===1){X(B[0]);three(e,A[0],B[0],h);X(B[0]);C(e,h);three(e,h,A[0],B[0]);return out;}
  for(const q of B)X(q);
  for(let i=1;i<n;i++)C(A[i],B[i]);
  T(e,A[last],h);
  for(let i=n-2;i>=1;i--)C(A[i],A[i+1]);
  for(let i=0;i<n-1;i++)T(B[i],A[i],A[i+1]);
  three(e,A[last],B[last],h);C(e,h);
  three(e,h,A[last],B[last]);
  for(let i=n-2;i>=0;i--){T(B[i],A[i],A[i+1]);three(e,h,A[i],B[i]);}
  for(let i=1;i<n-1;i++)C(A[i],A[i+1]);
  for(let i=1;i<n;i++)C(A[i],B[i]);
  for(const q of B)X(q);
  return out;
}

let f=replace(parent.f,'en=655,tmp=656','en=655,tmp=655');
f=replace(f,'function one_stage(n,outer,M,X,s,J,e,t,dirty,i,kappa){',
  'function one_stage(n,outer,M,X,s,J,e,unused,dirty,i,kappa){const t=M[n-1];');
f=replace(f,'...digit(n-1,M.slice(1),X.slice(0,-1),X[n-1],e,t)',
  '...dirtyDigit(M.slice(1),X.slice(0,-1),X[n-1],e,dirty[0]),[t]');
f=replace(f,'g=g.concat([...high].reverse());for(let j=n-1;',
  'g=g.concat([...high].reverse(),[[t]]);for(let j=n-1;');
const nativeForward=Function('module','Replacement','dirtyDigit',f+'\nreturn emitForward128;')({exports:{}},CanonicalUnit,dirtyDigit);

// After the general walk, raw rm[0] is zero. It becomes V's lowest bit
// through the final cyclic right-rail shift and is restored during rewind.
let d=replace(parent.d,'R=[...rm,...rp]','R=[...rm,rp[0],rm[0]]');
d=replace(d,'const wi={sign:R[1],tag:S','const wi={sign:L[1],tag:S');
d=replace(d,'[...vt,R[0],R[1]],[...Q,L[0],L[1]],wi',
  '[...vt,R[1],R[1]],[...Q,L[0],L[0]],wi');
const nativeInverse=Function('module',d+'\nreturn inverseField;')({exports:{}});

// Both sparse exports preserve the two original virtual sites q648 and q656.
// For dense standalone use, the q648 hole is removed and q656 is past the end.
function mapSink(sink,divide,dense) {
  const ports=new Int16Array(1024);ports.fill(-1);ports[1023]=1023;
  for(let q=0;q<=656;q++){
    if(q===648||q===(divide?652:656))continue;
    const v=divide&&q===656?652:q;
    ports[q]=dense&&v>648?v-1:v;
  }
  function physical(q){const p=ports[q];if(p===undefined||p<0)throw Error('leased wire is live: '+q);return p;}
  return (kind,data)=>{
    if(kind==='packed') {
      const out=new Uint32Array(data.length);
      for(let i=0;i<data.length;i++){const x=data[i];out[i]=(physical(x>>>20&1023)<<20)|(physical(x>>>10&1023)<<10)|physical(x&1023);}
      sink(kind,out);
    }else if(kind==='nct')sink(kind,data.map(row=>row.map(physical)));
    else sink(kind,data.map((q,i)=>i===data.length-1?q:physical(q)));
  };
}
function emitMultiply655(sink){nativeForward(mapSink(sink,false,true));}
function emitDivide655(sink){nativeInverse(128,ReducedGcdWalk,CanonicalUnit,mapSink(sink,true,true));}
function emitMultiplySparse(sink){nativeForward(mapSink(sink,false,false));}
function emitDivideSparse(sink){nativeInverse(128,ReducedGcdWalk,CanonicalUnit,mapSink(sink,true,false));}
module.exports={emitMultiply655,emitDivide655,emitMultiplySparse,emitDivideSparse,dirtyDigit};
