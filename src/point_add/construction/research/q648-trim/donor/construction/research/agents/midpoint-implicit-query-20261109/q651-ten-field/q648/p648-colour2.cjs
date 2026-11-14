'use strict';
// q648 (papers): colour off 647 in the prod bracket. At prod (after power) gcd(T,H)=2^s, so S4 = bit 4 of s =
// XOR_{k=1..7} [low 16k bits of T and H all zero] (their S5/S6 erase, one bit lower). Erase S4 before can2, put can2's
// colour on S4's wire, restore after can2^-1. Q648_COLOUR2=0 disables.
const mk=w=>"globalThis.__mark&&globalThis.__mark('"+w+"');";
module.exports={f:s=>{if(process.env.Q648_COLOUR2==='0')return s;
 const AM='power(false);'+mk('can2')+'run(can);'+mk('prod-')+'prod(true);'+mk('ph')+"for(let i=0;i<n;i++)sink('phase',[C[i],i]);"+mk('prod')+'prod(false);'+mk('can2-')+'run(can,true);'+mk('power-')+'power(true);';
 if(s.split(AM).length===2){const BM='power(false);{const pr=(j,b)=>{const lo=[...T.slice(0,j),...H.slice(0,j)];return negate(lo,MCX(lo,S[b],L),lo.map(()=>false));},e4=[1,2,3,4,5,6,7].flatMap(k=>pr(16*k,4)),can4=digit(n,T,C,S[4]);'+
   mk('can2')+'run(e4);run(can4);'+mk('prod-')+'prod(true);'+mk('ph')+"for(let i=0;i<n;i++)sink('phase',[C[i],i]);"+mk('prod')+'prod(false);'+mk('can2-')+'run(can4,true);run(e4,true);}'+mk('power-')+'power(true);';
  return s.replace(AM,()=>BM);}
 const A='power(false);run(can);prod(true);for(let i=0;i<n;i++)sink(\'phase\',[C[i],i]);prod(false);run(can,true);power(true);';
 if(s.split(A).length!==2)throw Error('q648 colour2 anchor');
 const B='power(false);{const pr=(j,b)=>{const lo=[...T.slice(0,j),...H.slice(0,j)];return negate(lo,MCX(lo,S[b],L),lo.map(()=>false));},e4=[1,2,3,4,5,6,7].flatMap(k=>pr(16*k,4)),can4=digit(n,T,C,S[4]);'+
   'run(e4);run(can4);prod(true);for(let i=0;i<n;i++)sink(\'phase\',[C[i],i]);prod(false);run(can4,true);run(e4,true);}power(true);';
 return s.replace(A,()=>B);}};
