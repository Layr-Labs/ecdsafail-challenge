'use strict';
const path=require('path'),nine=require('./i7-multiply-s4-m-multiply-nine.cjs');
const edit=(s,a,b)=>{if(s.split(a).length!==2)throw Error('M5 anchor '+a);return s.replace(a,()=>b);};
function patch(s){
 s=nine(s);
 // Five tags: three permanent, one on tst/r0, one on R[m].
 s=edit(s,'m[W.R[n]]=649;','m[W.R[n]]=645;');
 s=edit(s,'m[W.tst]=644;','m[W.tst]=643;');
 // One total valuation digit, parked on T[0]. All modulo-2 sectors emitted.
 s=edit(s,'idx=vec(1,649)','idx=vec(0,649)');
 s=edit(s,'if((l-1)&2)','if((l-1)&1)');
 // Exact independent count-bit erasure from gcd(T,H)=2^s.
 s=edit(s,'function prod(back){const low=[...T.slice(0,64),...H.slice(0,64)],erase=negate(low,MCX(low,S[6],L),low.map(()=>false));run(erase);run(r36prod(128,T,H,C,L,[649,S[6]]),back);run(erase);}',
 `function prod(back){const pred=(j,b)=>{const lo=[...T.slice(0,j),...H.slice(0,j)];return negate(lo,MCX(lo,S[b],L),lo.map(()=>false));},erase=[...pred(32,5),...pred(64,5),...pred(96,5),...pred(64,6)];run(erase);run(r36prod(128,T,H,C,L,[S[5],S[6]]),back);run(erase,true);}`);
 // Park the canonicalization record on normalized T's known-one top.
 s=edit(s,'mad=madd(T,C,H,649)',
 'mad=[[T[127]],...fr(1023,color,T[127]),...r36madd([...T.slice(0,-1),1001],C,H,color),...fr(1023,color,T[127]),[T[127]]]');
 // fr expects a control; sentinel 1023 is supported by packed output but not nct tests.
 s=s.replaceAll('...fr(1023,color,T[127])','[color,T[127]],[T[127],color],[color,T[127]]');
 return s;
}
module.exports={f:patch,source:(s,e)=>e(s,'class Walk extends pub.D2Canonical{constructor(n){super(n,6);}}',`const Walk=require(${JSON.stringify(path.join(__dirname,'host-walk.cjs'))})(pub,5);`)};
