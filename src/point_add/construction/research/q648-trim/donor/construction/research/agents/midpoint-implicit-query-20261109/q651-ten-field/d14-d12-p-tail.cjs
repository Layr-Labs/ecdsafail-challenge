'use strict';
// AFTER D7 (independent of p-alpha). No644 from reverse-outer completion onward.
// Delay count3 recovery until reverse split/high frees a second helper.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D12 tail anchor '+a);s=s.replace(a,()=>b);};
 one('for(let j=0;j<S.length;j++){const low=M.slice(0,j+1)',
     'for(let j=0;j<S.length;j++){if(n===128&&off===7&&S.length===7&&j===3)continue;const low=M.slice(0,j+1)');
 one('S[bits-3]=Htop;for(let j=0;j<n-1;j++){',`S[bits-3]=Htop;
 S[3]=t;
 {const z=mcN(M.slice(0,4),[false,false,false,false],e,C);put(z);put([[e,Q[3],t],[e,rm[3],t]]);put(rev(z));sink('phase',[t,bits+3]);put([[t,Q[3]]]);}
 for(let j=0;j<n-1;j++){`);
 one('put(digit(n-1-j,M.slice(j+1),Q.slice(0,n-1-j),Q[n-1-j],e,t));',
     'put(D2F.dirtyDigit(M.slice(j+1),Q.slice(0,n-1-j),Q[n-1-j],e,C[0]));');
 const oracle='const count3=dest=>{const out=[];for(let shift=8;shift<n;shift+=8){const w=M.slice(n-shift);out.push(...mcN(w,w.map(()=>false),dest,C));}return out;};';
 one(oracle+'put(count3(S[3]));','');
 one("for(let i=0;i<n;i++){const q=gt(S,n-i-1,e,null,C);put(q);put(fr(e,Q[i],t));sink('hmr',[t,2*bits+i]);put(rev(q));}put(rot(M,-1));tap('preF');",
 `put(rot(M,-1));
 ${oracle}
 const c3oracle=count3(t);put(c3oracle);
 for(let i=0;i<n;i++){
  const q=gt(S,n-i-1,e,null,C);
  put(c3oracle);put(q);put(rev(c3oracle));
  put(fr(e,Q[i],t));sink('hmr',[t,2*bits+i]);
  put(c3oracle);put(rev(q));put(rev(c3oracle));
 }tap('preF');`);
 return s;
};
