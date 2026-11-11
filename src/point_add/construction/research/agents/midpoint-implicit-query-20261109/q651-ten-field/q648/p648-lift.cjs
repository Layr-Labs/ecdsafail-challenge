'use strict';
// q648 (papers): M6 lifts without the enable wire `on` (logical 647). Choice stays on S6 (their count-host trick).
// active_i = [S>i] = ~M[127] on every lift state at step start (M = T << min(i,S)); where M[127] is intact the enable is
// read from it, elsewhere it is expanded into the disjoint S-products of [S>i] (as in p648-power):
//   b ^= active (i >= 63)             -> CX from ~M127 (step start, M intact)
//   tick, incmod^-1, tick, incmod     -> Horner chain on U' (b ^= ~M127 & XOR_{j<=tz(M)} U'_j), M read-only
//   plus rows controlled by b (i>=63) -> one MCX per S-product (plus modifies M, so ~M127 is not usable there)
//   op([active],b)                    -> CX from ~M127 (plus restores M)
//   lt([active],M,U,b)                -> 127-bit ltc2 under ~M127 & ~U127 (on active lanes M127 = 0)
//   rot([active],M,1)                 -> its swap chain with the CCX(active,..) rows product-expanded
//   b ^= active after the rotation    -> product-expanded (M has moved)
// Q648_LIFT=0 keeps their lifts.
const LTC2=`
function ltc2(A,B,H,es,dirty){const n=A.length,last=n-1,g=[];const X=a=>g.push([a]),CX=(a,b)=>g.push([a,b]),T=(a,b,c)=>g.push([a,b,c]);
 const loan=dirty.filter(q=>q!==H&&!es.includes(q)&&!A.includes(q)&&!B.includes(q));
 for(const w of B)X(w);if(n===1){g.push(...MCX([...es,A[0],B[0]],H,loan));X(B[0]);return g;}
 for(let i=1;i<n;i++)CX(A[i],B[i]);g.push(...MCX([...es,A[last]],H,loan));for(let i=n-2;i>=1;i--)CX(A[i],A[i+1]);for(let i=0;i<n-1;i++)T(B[i],A[i],A[i+1]);g.push(...MCX([...es,B[last],A[last]],H,loan));
 for(let i=n-2;i>=0;i--)T(B[i],A[i],A[i+1]);for(let i=1;i<n-1;i++)CX(A[i],A[i+1]);for(let i=1;i<n;i++)CX(A[i],B[i]);for(const w of B)X(w);return g;}
`;
const NEW=` lifts(K){const a=[],n=this.n,U=this.dat,M=this.modw,H=this.outerTag,b=H.at(-1),half=n/2,t=M[n-1],y=this.y,active=this.on;
  const F=new Set((process.env.Q648L||'start,horner,plus,op,lt,rot,end').split(',')),keep=process.env.Q648KEEP==='1'||!['start','horner','plus','op','lt','rot','end'].every(x=>F.has(x));
  const flip=U.filter((_,j)=>Boolean((K>>BigInt(j))&1n));
  const zero=d=>this.zer([],M.slice(n-d),b),X1=q=>this.raw(-1,-1,q);
  const prods=i=>{const P=[];for(let j=0;j<H.length;j++)if(!((i>>j)&1)){const yes=[H[j]],no=[];for(let k=j+1;k<H.length;k++)(((i>>k)&1)?yes:no).push(H[k]);P.push({yes,no});}return P;};
  const pe=(i,cs,z)=>{for(const p of prods(i)){const ctl=[...cs,...p.yes,...p.no],pool=y.filter(q=>q!==z&&!ctl.includes(q));
    for(const q of p.no)X1(q);this.rows(MCX(ctl,z,pool));for(const q of p.no)X1(q);}};
  for(let i=0;i<n-1;i++)a.push({rev:false,fn:()=>{
   if(keep)this.less([],H,i,active);
   if(i<half-1)zero(half-i);else if(F.has('start')){X1(t);this.raw(t,-1,b);X1(t);}else this.op([active],b);
   if(F.has('horner')){for(const z of flip)X1(z);for(let j=0;j<n-1;j++)X1(M[j]);for(let j=n-2;j>=0;j--)this.raw(M[j],U[j+1],U[j]);
   X1(t);this.raw(t,U[0],b);X1(t);for(let j=0;j<=n-2;j++)this.raw(M[j],U[j+1],U[j]);for(let j=0;j<n-1;j++)X1(M[j]);for(const z of flip)X1(z);}
   else{for(const z of flip)X1(z);this.tick(active,U,M,b);this.reverse(()=>this.incmod());this.tick(active,U,M,b);this.incmod();for(const z of flip)X1(z);}
   const g=plus(M,U,null,b);
   for(const r of g){const cs=r.slice(0,-1),z=r.at(-1);
    if(i>=half-1&&cs.includes(b)){if(F.has('plus'))pe(i,cs,z);else this.rows(MCX([active,...cs],z,y));}
    else this.raw(r.length>1?r[0]:-1,r.length>2?r[1]:-1,z);}
   if(F.has('op')){X1(t);this.raw(t,-1,b);X1(t);}else this.op([active],b);
   if(F.has('lt')){X1(t);X1(U[n-1]);this.rows(ltc2(M.slice(0,n-1),U.slice(0,n-1),b,[t,U[n-1]],y));X1(U[n-1]);X1(t);}else this.lt([active],M,U,b);
   // the closing b ^= active commutes with the rotation (disjoint wires, same control): do it first, while M is intact
   // b back to S6 BEFORE the rotation (M still unrotated): i>=63 by b ^= active (= ~M127 here), i<63 by the start-of-step
   // erase predicate zero(half-i) again (it equals S6 on M_i). The rotation's S-products then read the true S6 on wire b.
   // (Both closings commute with the rotation or replace their post-rotation twin: after it b = S6 either way.)
   if(i>=half-1){if(F.has('end')){X1(t);this.raw(t,-1,b);X1(t);}else this.op([active],b);}else if(F.has('rot'))zero(half-i);
   if(F.has('rot')){for(let j=1;j<n;j++){this.raw(M[0],-1,M[j]);pe(i,[M[j]],M[0]);this.raw(M[0],-1,M[j]);}}else this.rot([active],M,1);
   if(i<half-1&&!F.has('rot'))zero(half-i-1);
   if(keep)this.less([],H,i,active);
  }});return a;
 }
`;
module.exports={f:s=>{
  if(process.env.Q648_LIFT==='0')return s;
  const A=' lifts(K){const a=[],n=this.n,U=this.dat,M=this.modw,H=this.outerTag,active=this.on,b=H.at(-1),half=n/2;';
  const a=s.indexOf(A);if(a<0||s.indexOf(A,a+1)>=0)throw Error('q648 lift anchor');
  const e=s.indexOf('}});return a;\n }',a);if(e<0)throw Error('q648 lift end');
  return LTC2+s.slice(0,a)+NEW+s.slice(e+'}});return a;\n }'.length);
}};
