'use strict';
// Grouped terminal widths for the lower alpha classes of the ten-helper (Q651) divide.
//
// This is nasqret's "grouped winding heights" idea (submission 3db0b38c, file
// ../q653-grouped/backend.cjs, function groupWindingHeights; reused in 53d21251) ported onto the
// Q651 divide source as it stands after div10-rewrite.cjs and p-divide-d4.js.
//
// In the Q651 divide the alpha step is D2Alpha: heights n-1 and n have their own code (they must
// move the hosted count bits c5/c6 out of J[n-2]/J[n-1]); every height t < n-1 is delegated
// literally to outerloadJ(...,t,t). Only that delegated part is grouped here, so the hosted bits
// in J[n-2], J[n-1] are never inside a = J.slice(0,t) (t <= n-2).
//
// One group (lo..t) is compiled once at width t. Its flag e is set when the divisor height h is in
// [lo,t]. The divisor is zero-extended to t bits for free (its cells above h are zero). The
// coefficient cells u[h..t-1] and the gap cell u[t] hold the packed other remainder; they are
// swapped, under e and the height test, with the zero divisor cells v[t+j-lo] (j = lo..t), which
// needs 2t-lo <= n-1. After the width-t arithmetic the swaps are undone.
//
// Difference from nasqret's table: heights 125 and 126 form one group (126:125), which the same
// bound allows (2*126-125 = 127).
const GROUPS='{2:2,64:3,96:65,112:97,120:113,124:121,126:125,127:127,128:128}';
module.exports=function(source){
  const rep=(s,a,b)=>{if(s.split(a).length!==2)throw Error('group-alpha anchor: '+a.slice(0,60));return s.replace(a,()=>b);};
  const start=source.indexOf('function outerloadJ('),end=source.indexOf('function mulG(',start);
  if(start<0||end<=start)throw Error('group-alpha: outerloadJ not found');
  let body=source.slice(start,end);
  body=rep(body,"const m=v.slice(0,t),a=J.slice(0,t),gap=L[n+1-t],cls=flagHeight(v,t,e,loan),put=g=>sink('nct',g);",
`const groups=${process.env.G651_GROUPS||GROUPS},lo=groups[t];
  if(lo===undefined)continue;
  if(2*t-lo>n-1&&lo<t)throw Error('group-alpha: no zero divisor cells for group '+lo+'..'+t);
  const m=v.slice(0,t),a=J.slice(0,t),gap=L[n+1-t],put=g=>sink('nct',g);
  const zero=(word,dest)=>mcN(word,word.map(()=>false),dest,loan);
  const cls=lo===t?flagHeight(v,t,e,loan):zero(v.slice(t),e).concat(zero(v.slice(lo-1),e)),park=[];
  if(lo<t)for(let j=lo;j<=t;j++){
    const stash=v[t+j-lo],tail=v.slice(j,t),test=[e,...tail,stash],match=[true,...tail.map(()=>false),true];
    const cell=j===t?gap:u[j];
    if(stash===undefined)throw Error('group-alpha: no divisor padding');
    park.push([cell,stash],...mcN(test,match,cell,loan),[cell,stash]);
  }`);
  body=rep(body,'put(cls);if(t===n)','put(cls);put(park);if(t===n)');
  body=rep(body,'neg();cond();neg();cond();put([...cls].reverse());','neg();cond();neg();cond();put(park.slice().reverse());put([...cls].reverse());');
  return source.slice(0,start)+body+source.slice(end);
};
