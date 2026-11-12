'use strict';
// RESEARCH INTERFACE ONLY. Emits an encoded alpha output, not parkInner's ABI.
// Apply after D7, instead of p-alpha; do not install before an unchanged middle.
module.exports=s=>{
 s=require('./i9-divide-d12-p-alpha.cjs')(s);
 const a='D12DecodeAlpha(n,L,R,Q,loan,rm[1],base+4,sink);';
 if(s.split(a).length!==2)throw Error('D12 xor anchor');
 s=s.replace(a,'D12FoldSeed(n,L,R,Q,loan,rm[1],sink);');
 return s+`
// Convert the additive seed into an XOR on Q3 while preserving canonical Q<V.
// V divisible16 makes an XOR on bit3 range-preserving. Count3 is the affine
// form Q3+U3+Q1+U1; no physical count3 wire is required at this interface.
function D12FoldSeed(n,L,R,J,loan,e,sink){
 const v=Array.from({length:n},(_,j)=>R[n+1-j]),u=Array.from({length:n},(_,j)=>L[n+1-j]);
 const put=g=>sink('nct',g),raw=(cs,ps,z)=>mcN(cs,ps,z,loan.filter(w=>w!==z&&!cs.includes(w)));
 for(const t of [n-3,n-2,n-1,n]){
  const hc=v.slice(t-1),hp=hc.map((_,i)=>i===0),cs=[...hc,...v.slice(0,4)],ps=[...hp,false,false,false,false];
  const h=v[t-1],a=J.slice(0,t),implicit=[...v.slice(0,t-1),1001],add8=[];
  add8.push(...raw([e,...a.slice(3)],[true,...a.slice(3).map(()=>true)],h));add8.push(...incReg(a.slice(3),loan,e));
  eliminate(D2F.dirtyDigit(implicit,a,h,e,loan[0]),1001,1,(c,z)=>add8.push(...MCX(c,z,loan.filter(w=>w!==z&&!c.includes(w)))));
  add8.push(...raw([e,...a.slice(3)],[true,...a.slice(3).map(()=>false)],h));
  for(const orientation of [0,1]){
   const terms=orientation?[[J[1]],[u[1]]]:[[J[3]],[u[3]]];
   for(const x of [J[3],u[3]])for(const y of [J[1],u[1]])terms.push([x,y]);
   const pred=[];for(const term of terms)pred.push(...raw([...cs,...term],[...ps,...term.map(()=>true)],e));
   put(pred);put([[h]]);put(orientation?[...add8].reverse():add8);put([[h]]);put([[e,J[3]]]);put([...pred].reverse());
  }
 }
}
// Test/observer reconnect. Never part of the encoded production interface.
function D12DecodeXor(n,L,R,J,loan,e,dst,sink){
 const v=Array.from({length:n},(_,j)=>R[n+1-j]),u=Array.from({length:n},(_,j)=>L[n+1-j]),put=g=>sink('nct',g);
 const low=mcN(v.slice(n-4),v.slice(n-4).map(()=>false),e,loan);put(low);put(fr(e,J[n-4],dst));put([...low].reverse());
 for(const t of [n-3,n-2,n-1,n]){
  const hc=v.slice(t-1),hp=hc.map((_,i)=>i===0),cs=[...hc,...v.slice(0,4)],ps=[...hp,false,false,false,false];
  for(const w of [J[3],u[3],J[1],u[1]])put(mcN([...cs,w],[...ps,true],dst,loan));
  const cl=flagHeight(v,t,e,loan);put(cl);put([[e,dst,J[3]]]);put([...cl].reverse());
 }
}
`;
};
