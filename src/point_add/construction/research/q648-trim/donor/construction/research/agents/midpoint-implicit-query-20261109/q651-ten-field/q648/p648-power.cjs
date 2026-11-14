'use strict';
// q648 (papers): M6 power steps without the step-enable wire (logical 647). Each enabled step i has e = [s>i], which is
// a disjoint union of products of S literals (one per zero bit j of i: s_j=1 and s_b=i_b for b>j, the same cubes gt()
// writes). The guard that computed e is dropped and every e-controlled row of the step body is replaced by one MCX per
// product (S literals as controls, dirty borrows from L). Disjoint products => the replacement toggles exactly when e=1.
// Applies to f (the multiply text) via an anchor; Q648_POWER=0 keeps the original.
const HELP=`
function q648expand(g,s,i,e,dirty,glen){
 if(process.env.Q648_POWER==='0')return g;
 const head=g.slice(0,glen),tail=g.slice(g.length-glen),body=g.slice(glen,g.length-glen);
 if(JSON.stringify(head)!==JSON.stringify(gt(s,i,e,null,dirty))||JSON.stringify(tail)!==JSON.stringify(gt(s,i,e,null,dirty).slice().reverse()))throw Error('q648 power guard shape');
 const P=[];for(let j=0;j<s.length;j++)if(!((i>>j)&1)){const yes=[s[j]],no=[];for(let b=j+1;b<s.length;b++)(((i>>b)&1)?yes:no).push(s[b]);P.push({yes,no});}
 const out=[];
 for(const r of body){if(!r.includes(e)){out.push(r);continue;}const t=r[r.length-1];if(t===e)throw Error('q648 power: e target in body');
  const cs=r.slice(0,-1).filter(q=>q!==e);
  for(const p of P){const ctl=[...cs,...p.yes,...p.no],pool=dirty.filter(q=>q!==t&&!ctl.includes(q));
   for(const q of p.no)out.push([q]);out.push(...MCX(ctl,t,pool));for(const q of p.no)out.push([q]);}}
 return out;
}
`;
const A='function m6powerSweep(n,M,X,s,J,e,dirty,i,kappa) {';
const B='function m6powerSweep(n,M,X,s,J,e,dirty,i,kappa){const g=m6powerSweep0(n,M,X,s,J,e,dirty,i,kappa);return q648expand(g,s,i,e,dirty,gt(s,i,e,null,dirty).length);}\n'+HELP+'\nfunction m6powerSweep0(n,M,X,s,J,e,dirty,i,kappa) {';
module.exports={f:s=>{if(s.split(A).length!==2)throw Error('q648 power anchor');return s.replace(A,()=>B);}};
