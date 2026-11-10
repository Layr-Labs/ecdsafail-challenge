'use strict';
// Incremental [from,to] list AFTER q651/mul/p-mul651.js. Evict logical 650 from short.multiply.
//  walk : the 651 divide's aux-free sector walk D2Canonical(128,5) (same permutation on unit-walk entries);
//         aux is unbound and R[n] takes aux's old slot 645; rotations with >=2 controls use mulopt.rot2
//  whole stage: exact peephole pair cancellation on the emitted stream (mulopt.peepSink)
//  lifts: cin-free arithmetic (nasqret's ancilla-free plus/lt; increment via complemented dirty word)
//  power: one valuation tag (residue mod 2, interval width 2); all 64 valuation intervals are emitted; the
//         two prefix toggles between intervals share one dirty V-chain (tap2)
//  prep : madd scratch hosted on the normalized T[127] (constant-top r36madd), as the 651 product does
//  prod : S is cleared around the product (S = tz(T|X) there) and th is hosted on S[0]=640
const A='const multiply=Function(';
const inner=(a,b)=>[A,'f=replace(f,'+JSON.stringify(a)+','+JSON.stringify(b)+');\n'+A];
const helpers=String.raw`
// H ^= e & [A > B]; ancilla-free (nasqret's lt) with only the two H-toggling gates controlled.
function ltc(A,B,H,e,dirty){const n=A.length,last=n-1,g=[];const X=a=>g.push([a]),CX=(a,b)=>g.push([a,b]),T=(a,b,c)=>g.push([a,b,c]);
 const loan=dirty.filter(q=>q!==H&&q!==e&&!A.includes(q)&&!B.includes(q));
 for(const w of B)X(w);if(n===1){g.push(...MCX([e,A[0],B[0]],H,loan));X(B[0]);return g;}
 for(let i=1;i<n;i++)CX(A[i],B[i]);T(e,A[last],H);for(let i=n-2;i>=1;i--)CX(A[i],A[i+1]);for(let i=0;i<n-1;i++)T(B[i],A[i],A[i+1]);g.push(...MCX([e,B[last],A[last]],H,loan));
 for(let i=n-2;i>=0;i--)T(B[i],A[i],A[i+1]);for(let i=1;i<n-1;i++)CX(A[i],A[i+1]);for(let i=1;i<n;i++)CX(A[i],B[i]);for(const w of B)X(w);return g;}
// Given S = tz(T|X) (T,X same width, T|X nonzero), clears S; T and X are restored. Reverse list restores S.
// = [rotate T,X right by S] followed by the inverse of the trailing-zero normalization of (T,X).
// t ^= AND(c[0..k1)) ^ AND(c[0..k2)) for 3<=k1<k2=c.length with ONE dirty V-chain (the shorter AND is tapped on the
// way up in both passes); v restored. Costs about the k2-control MCX instead of two MCX.
function tap2(c,k1,t,v){const u=c.length;if(!(k1>=3&&k1<u&&u>=4&&v.length>=u-2))throw Error('tap2 args');
 const A=[c[0],c[1],v[0]],M=j=>[c[j],v[j-2],v[j-1]],Z=k=>[c[k-1],v[k-3],t];
 const pass=()=>{const g=[A];if(k1===3)g.push(Z(3));for(let j=2;j<=u-2;j++){g.push(M(j));if(j===k1-2)g.push(Z(k1));}g.push(Z(u));for(let j=u-2;j>=2;j--)g.push(M(j));return g;};
 return [...pass(),...pass()];}
// nasqret's (fused) lowValuationSweep; the two commuting prefix toggles applied between intervals share one ladder.
function lvs2(n,M,X,s,J,e,dirty,i,kappa){
  const groupBit=M[n-1],guard=gt(s,i,e,null,dirty);
  let gates=guard.concat(dirtyDigit(M.slice(1),X.slice(0,-1),X[n-1],e,dirty[0]),[[groupBit]]);
  const prefix=k=>{if(k===0)return [[groupBit]];if(k>=n)return [];const cs=M.slice(0,k);return negate(cs,MCX(cs,groupBit,dirty),cs.map(()=>false));};
  const toggle=ks=>{ks=ks.filter(k=>k<n).sort((a,b)=>a-b);
    if(ks.length===2&&ks[0]>=3){const cs=M.slice(0,ks[1]);return negate(cs,tap2(cs,ks[0],groupBit,dirty),cs.map(()=>false));}
    let g=[];for(const k of ks)g=g.concat(prefix(k));return g;};
  const interval=1<<J.length;let previous=[];
  for(let base=0;base<n-1;base+=interval){
    const a=base===0?0:base+1,b=base+interval+1;
    const current=[a,b].filter(k=>k<n);gates=gates.concat(toggle([...previous.filter(k=>!current.includes(k)),...current.filter(k=>!previous.includes(k))]));previous=current;
    for(let j=base;j<Math.min(n-1,base+interval);j++){
      const pattern=eq_bits(J,j),ctrl=[e,groupBit,...J],sgn=[true,true,...pattern];
      gates=gates.concat(negate(ctrl.concat(X[j]),MCX(ctrl.concat(X[j]),X[n-1],dirty),sgn.concat(true)));
      if(i<=j&&((kappa>>BigInt(j-i))&1n))gates=gates.concat(negate(ctrl,MCX(ctrl,X[n-1],dirty),sgn));
    }
  }
  gates=gates.concat(toggle(previous));
  gates.push([groupBit]);
  for(let j=n-1;j>0;j--)gates.push(...fr(e,X[j],X[j-1]));
  return gates.concat(guard.slice().reverse());
}
function tzclear(T,X,S,dirty){const n=T.length,g=[];
 const rot=(j,right)=>{const d=1<<j;for(const [a,b] of rotleft(n,right?n-d:d)){g.push(...fr(S[j],T[a],T[b]));g.push(...fr(S[j],X[a],X[b]));}};
 const test=j=>{const d=1<<j,cs=[...T.slice(0,d),...X.slice(0,d)];g.push(...negate(cs,MCX(cs,S[j],dirty),cs.map(()=>false)));};
 for(let j=S.length-1;j>=1;j--)rot(j,true);
 test(0);for(let j=1;j<S.length;j++){rot(j,false);test(j);}
 return g;}
`;
module.exports=[
 // D2Canonical is defined later in this module by q651/p-divide-d4.js; it is resolved at emission time.
 ['class R35UnitWalk extends SectorCanonical{constructor(n){super(n,5);}}',
  "const Q650M=require('../q650/mul/mulopt.cjs');function R35UnitWalk(n){const w=new D2Canonical(n,5);w.rot=function(c,A,s){return c.length>=2?Q650M.rot2.call(this,c,A,s):D2Canonical.prototype.rot.call(this,c,A,s);};return w;}"],
 // Exact peephole over the whole emitted multiply stream (mulopt.cjs). Q650_PEEP=0 disables it (diagnostics only).
 ['function emitMultiplySparse(sink){multiply(mapped(sink,false));}',
  "function emitMultiplySparse(sink){if(process.env.Q650_PEEP==='0'){multiply(mapped(sink,false));return;}const P=Q650M.peepSink(mapped(sink,false));multiply(P);P.flush();}"],
 inner('m[W.L[n]]=647;m[W.R[n]]=650;m[W.tst]=649;m[W.fire]=646;for(let j=0;j<tg.length;j++)m[tg[j]]=640+j;m[W.sign]=640+tg.length;m[W.aux]=641+tg.length;',
       'm[W.L[n]]=647;m[W.tst]=649;m[W.fire]=646;for(let j=0;j<tg.length;j++)m[tg[j]]=640+j;m[W.sign]=640+tg.length;m[W.R[n]]=641+tg.length;'),
 inner('idx=vec(2,649),en=647,tmp=647;','idx=vec(1,649),en=647,tmp=647;'),
 inner('const hole=649,sc=650,R=[...L,hole]','const hole=649,R=[...L,hole]'),
 inner('md=madd(T,R.slice(0,128),H,sc),G=','md=[[127],...r36madd([...T.slice(0,127),1001],R.slice(0,128),H,127),[127]],G='),
 inner('function shprod(n,M,X,C,R,P){',helpers+'\nfunction shprod(n,M,X,C,R,P){'),
 inner('function one_stage(n,outer,M,X,s,J,e,t,dirty,i,kappa){return lowValuationSweep(n,M,X,s,J,e,dirty,i,kappa,{gt,negate,MCX,eq_bits,fr});}',
       'function one_stage(n,outer,M,X,s,J,e,t,dirty,i,kappa){return lvs2(n,M,X,s,J,e,dirty,i,kappa);}'),
 inner('function prod(back){run(r36prod(128,T,H,C,L,[649,650]),back);}',
       'function prod(back){const P=r36prod(128,T,H,C,L,[649,640]),Z=tzclear(T,H,S,L);if(back){run(Z);run(P,true);}else{run(P);run(Z,true);}}'),
 inner('incmod(){this.raw(-1,-1,this.cin);this.add([],this.incWord,this.modw,this.cin,null);this.raw(-1,-1,this.cin);this.reverse(()=>this.add([],this.incWord,this.modw,this.cin,null));}',
       'incmod(){const g=this.incWord,x=this.modw,P=[...plus(g,x,null)].reverse(),N=g.map(q=>[q]);this.emitg([...N,...P,...N,...P]);}emitg(gs){for(const z of gs)this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));}'),
 inner('this.add([b],M,U,this.cin,null);this.op([active],b);this.lt([active],M,U,b);',
       'this.emitg(plus(M,U,null,b));this.op([active],b);this.emitg(ltc(M,U,b,active,this.y));'),
 // Ban: logical 650 is not a multiply site.
 [':[648,651,652,653,654,655,656],move=back?653:-1;',':[648,650,651,652,653,654,655,656],move=back?653:-1;'],
];
