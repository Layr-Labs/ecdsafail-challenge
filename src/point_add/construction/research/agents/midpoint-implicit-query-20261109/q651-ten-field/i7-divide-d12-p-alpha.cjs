'use strict';
// AFTER D7. New alpha carriers, followed by an explicit research reconnect.
// This overlay is NOT an eight-helper divider. Decode still writes native644.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D12 alpha anchor '+a);s=s.replace(a,()=>b);};
 one('if(t===n-3)put([[J[n-4],5*n+4],[5*n+4,J[n-4]],[J[n-4],5*n+4]]);','');
 one('if(t< n-2){ // D1: top-three classes get explicit count routing.',`if(t>=n-3){put(cls);put(D2F.fr(e,J[n-4],J[3]));put([...cls].reverse());}
 if(t< n-2){ // D1: top-three classes get explicit count routing.`);
 one('S[4]=base+5;T6[4]=base+5;tap(\'alpha\');',`D12DecodeAlpha(n,L,R,Q,loan,rm[1],base+4,sink);
 S[4]=base+5;T6[4]=base+5;tap('alpha');`);
 return s+`
// Reconnect only: original Q and the old external count3 restored exactly.
// Delete this call (not the function) to inspect the ban-clean encoded alpha.
function D12DecodeAlpha(n,L,R,J,loan,e,dst,sink){
 const v=Array.from({length:n},(_,j)=>R[n+1-j]),u=Array.from({length:n},(_,j)=>L[n+1-j]);
 const put=g=>sink('nct',g),raw=(cs,ps,z)=>mcN(cs,ps,z,loan.filter(w=>w!==z&&!cs.includes(w)));
 const low=raw(v.slice(n-4),v.slice(n-4).map(()=>false),e);
 put(low);put(fr(e,J[n-4],dst));put([...low].reverse());
 for(const t of [n-3,n-2,n-1,n]){
  const hc=v.slice(t-1),hp=hc.map((_,i)=>i===0),cs=[...hc,...v.slice(0,4)],ps=[...hp,false,false,false,false];
  // p=-1 mod16; c3=1 implies V divisible16. The lower two bits
  // determine original orientation even when c4 occupies physical sign.
  for(const w of [J[3],u[3],J[1],u[1]])put(raw([...cs,w],[...ps,true],dst));
  const h=v[t-1],a=J.slice(0,t),implicit=[...v.slice(0,t-1),1001],add8=[];
  add8.push(...raw([e,...a.slice(3)],[true,...a.slice(3).map(()=>true)],h));
  add8.push(...incReg(a.slice(3),loan,e));
  const dg=D2F.dirtyDigit(implicit,a,h,e,loan[0]);
  eliminate(dg,1001,1,(c,z)=>add8.push(...MCX(c,z,loan.filter(w=>w!==z&&!c.includes(w)))));
  add8.push(...raw([e,...a.slice(3)],[true,...a.slice(3).map(()=>false)],h));
  for(const orientation of [0,1]){
   const pred=[];if(!orientation)pred.push(...raw([...cs,dst],[...ps,true],e));
   for(const w of [J[1],u[1]])pred.push(...raw([...cs,dst,w],[...ps,true,true],e));
   put(pred);put([[h]]);put(orientation?[...add8].reverse():add8);put([[h]]);put([...pred].reverse());
  }
 }
}
`;
};
