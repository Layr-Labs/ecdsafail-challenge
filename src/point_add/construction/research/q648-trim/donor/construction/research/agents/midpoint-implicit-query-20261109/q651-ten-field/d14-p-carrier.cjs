'use strict';
// D5 source overlay, after the complete D3 chain. All gates are input-independent.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D5 anchor '+a);s=s.replace(a,()=>b);};
 one('for(let c=1;c<n-2;c++)cl(c,fr(e,Q[n-3],S[4]));',
     'for(let c=1;c<n-2;c++)cl(c,D5SignLease(n,L,V,Q,sg,e,loan,c,false,4));');
 one("if(c<n-2)put(fr(R[1],S[4],T6[0]));", 
     'if(c<n-2)put(D5SignLease(n,L,vt,Q,sig,R[1],loan,c,true,4,T6[0]));');
 one("sink('nct',cls);sink('nct',park);sink('nct',rot);",
     "sink('nct',cls);sink('nct',D5Relay(n,L,V,Q,sel,loan,c,false,4));sink('nct',park);sink('nct',rot);");
 one("sink('nct',body.reverse());\n  sink('nct',[...park].reverse());",
     "sink('nct',body.reverse());\n  sink('nct',D5Relay(n,L,V,Q,sel,loan,c,true,4));sink('nct',[...park].reverse());");
 one("put([...pp].reverse());sink('phase',[S[j],off+j]);put([[S[j],Q[j]]]);",
 `put([...pp].reverse());sink('phase',[S[j],off+j]);
 if(n===128&&off===7&&S.length===7&&j===4){
  // The c4 copy was a move into the known-zero Q4 when 32|g.
  // Its S0 measurement was zero; suppress the otherwise spurious repair.
  const z=[...M.slice(0,5),...rem.slice(0,5)],a=mcN(z,z.map(()=>false),tmp,loan);
  put(a);sink('cphase',[S[j],tmp,off+j]);put([...a].reverse());
 }
 put([[S[j],Q[j]]]);`);
 return s+`
// The actual gcd has size n+1-c. U1 is L[n]. For V divisible8,
// p=3 mod4, U,J odd, sign=J1 XOR U1. At exit Q=g*J, so
// J1=Q[k+1] XOR g[k+1] for k=v2(g). Missing gcd bits are zero.
function D5SignLease(n,L,V,Q,sign,e,loan,c,back,bit=4,destination){
 const size=n+1-c,rows=[],dst=destination===undefined?Q[n-3]:destination;
 const guardBits=Math.min(3,(1<<bit)-bit);
 const raw=(cs,ps,z)=>mcN(cs,ps,z,loan.filter(w=>w!==z&&!cs.includes(w)));
 for(let k=0;k<=bit&&k<size;k++){
  const cs=[e,...V.slice(0,guardBits),...L.slice(0,k+1)],ps=[true,...Array(guardBits).fill(false),...Array(k).fill(false),true];
  const sw=[];for(const r of fr(e,dst,sign)){
   const cc=r.slice(0,-1).filter(w=>w!==e);sw.push(...raw([...cs,...cc],[...ps,...cc.map(()=>true)],r.at(-1)));
  }
  const toggle=[];
  for(const w of [Q[back?k+1:1],L[n],...(back&&k+1<size?[L[k+1]]:[])])toggle.push(...raw([...cs,w],[...ps,true],sign));
  rows.push(...(back?[...sw,...toggle]:[...toggle,...sw]));
 }
 return rows;
}
// c4 -> V[c] before multiplication; V[c] -> Q[bit] afterwards.
// Selector e stays live throughout. All V suffix bits restore before unselect.
function D5Relay(n,L,V,Q,e,loan,c,back,bit=4){
 const size=n+1-c;if(c>=n-2||size<=bit+1)return [];
 const cs=[e,...L.slice(0,bit+1)],ps=[true,...Array(bit+1).fill(false)],rows=[];
 for(const r of fr(e,V[c],Q[back?bit:n-3])){
  const cc=r.slice(0,-1).filter(w=>w!==e);
  rows.push(...mcN([...cs,...cc],[...ps,...cc.map(()=>true)],r.at(-1),loan));
 }
 return rows;
}
`;
};
