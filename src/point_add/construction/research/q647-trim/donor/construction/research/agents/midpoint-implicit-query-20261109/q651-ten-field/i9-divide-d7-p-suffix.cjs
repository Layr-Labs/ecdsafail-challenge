'use strict';
// AFTER p-partial. At preF, M is the original nonzero modulus and c3 is
// a function of it. Erase c3 on644, use the unchanged field product, then
// regenerate c3 on clean649. This frees644 throughout F's body and completion.
// The erasing handoff still addresses644; qsplit/preF remain open.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D7 suffix '+a);s=s.replace(a,()=>b);};
 one('const count4=[];for(let shift=16;',`const count3=dest=>{const out=[];for(let shift=8;shift<n;shift+=8){const w=M.slice(n-shift);out.push(...mcN(w,w.map(()=>false),dest,C));}return out;};put(count3(S[3]));
const count4=[];for(let shift=16;`);
 one("put(rev(count4));tap('F');", "put(rev(count4));S[3]=L[n];put(count3(S[3]));tap('F');");
 return s;
};
