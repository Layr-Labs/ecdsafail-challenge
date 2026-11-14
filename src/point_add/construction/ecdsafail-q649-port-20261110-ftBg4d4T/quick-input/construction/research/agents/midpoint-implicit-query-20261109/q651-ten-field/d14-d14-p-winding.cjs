'use strict';
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D14 winding anchor '+a);s=s.replace(a,()=>b);};
 one("D2Winding(n,L,R,Q,loan,sink);tap('winding');",
     "D14BeforeWinding(n,L,R,Q,loan,sink);D2Winding(n,L,R,Q,loan,sink);tap('winding');");
 one('parkOuter(n,M,rm,Q,T6.slice(0,1),p,bits,R[1],loan,sink);',
     'parkOuter(n,M,rm,Q,T6.slice(0,1),p,bits,R[1],loan,sink);D14ParkCount(n,L,R,Q,loan,T6[0],bits+3,sink);');
 one("sink('nct',cls);sink('nct',D5Relay(n,L,V,Q,sel,loan,c,false,4));",
     "sink('nct',cls);sink('nct',D14Relay(n,L,V,Q,sel,loan,c,false));sink('nct',D5Relay(n,L,V,Q,sel,loan,c,false,4));");
 one("sink('nct',D5Relay(n,L,V,Q,sel,loan,c,true,4));sink('nct',[...park].reverse());",
     "sink('nct',D5Relay(n,L,V,Q,sel,loan,c,true,4));sink('nct',D14Relay(n,L,V,Q,sel,loan,c,true));sink('nct',[...park].reverse());");
 one("for(let j=1;j<4;j++){put([[T6[j],Q[j]]]);sink('hmr',[T6[j],bits+j]);}",
     "for(let j=1;j<3;j++){put([[T6[j],Q[j]]]);sink('hmr',[T6[j],bits+j]);}");
 // Q3 is now count-encoded. Only k=2's old orientation oracle reads it.
 // Odd multiplication modulo8 has bit2(a*b)=bit2(a) XOR bit2(b).
 one('for(const w of [Q[back?k+1:1],L[n],...(back&&k+1<size?[L[k+1]]:[])])',
     'const qb=back&&k===2?2:1;for(const w of [Q[back?k+qb:1],L[n+1-qb],...(back&&k+qb<size?[L[k+qb]]:[])])');
 one('for(const w of [Q[k+1],L[n]])put(mcN([...cs,w],[...ps,true],sig,loan));',
     'const qb=k===2?2:1;for(const w of [Q[k+qb],L[n+1-qb]])put(mcN([...cs,w],[...ps,true],sig,loan));');
 one('if(g>>(k+1)&1)put(mcN(cs,ps,sig,loan));','if(g>>(k+qb)&1)put(mcN(cs,ps,sig,loan));');
 return s+`
function D14Raw(cs,ps,z,loan){
 const m=new Map();for(let i=0;i<cs.length;i++){if(m.has(cs[i])&&m.get(cs[i])!==ps[i])return [];m.set(cs[i],ps[i]);}
 if(m.has(z))throw Error('D14 winding alias '+z);
 return mcN([...m.keys()],[...m.values()],z,loan.filter(w=>w!==z&&!m.has(w)));
}
function D14BeforeWinding(n,L,R,Q,loan,sink){
 const V=Array.from({length:n},(_,j)=>R[n+1-j]),U=Array.from({length:n},(_,j)=>L[n+1-j]),e=R[1],put=g=>sink('nct',g);
 // Low heights: use U3 when gcd has valuation <4 and V is divisible16.
 // Under count3=1, this guard necessarily holds unless 16 divides gcd.
 for(let c=5;c<=n-5;c++)for(let k=0;k<4;k++){
  const hc=V.slice(c-1),cs=[...hc,...V.slice(0,4),...L.slice(0,k+1)],ps=[...hc.map((_,i)=>i===0),false,false,false,false,...Array(k).fill(false),true];
  for(const w of [Q[3],Q[2],U[1]])put(D14Raw([...cs,w],[...ps,true],U[3],loan));
  const pred=D14Raw(cs,ps,e,loan);put(pred);put(fr(e,Q[n-4],U[3]));put([...pred].reverse());
 }
 // The only high class with a gcd divisible16 is n-4 (g=16).
 // Return that count to the zero Q padding for the independent winding relay.
 {const c=n-4,hc=V.slice(c-1),cs=[...hc,...V.slice(0,4),...L.slice(0,4)],ps=[...hc.map((_,i)=>i===0),false,false,false,false,false,false,false,false];
  const pred=D14Raw(cs,ps,e,loan);put(pred);put(fr(e,U[3],Q[n-4]));put([...pred].reverse());
  for(const w of [Q[3],Q[2],U[1]])put(D14Raw([...cs,w],[...ps,true],U[3],loan));
 }
}
function D14Relay(n,L,V,Q,e,loan,c,back){
 if(c>n-4)return [];
 const cs=[e,...L.slice(0,4)],ps=[true,false,false,false,false],rows=[];
 for(const r of fr(e,V[c+1],Q[back?3:n-4])){
  const cc=r.slice(0,-1).filter(w=>w!==e);rows.push(...D14Raw([...cs,...cc],[...ps,...cc.map(()=>true)],r.at(-1),loan));
 }
 return rows;
}
function D14ParkCount(n,L,R,Q,loan,port,record,sink){
 const V=Array.from({length:n},(_,j)=>R[n+1-j]),U=Array.from({length:n},(_,j)=>L[n+1-j]),e=R[1],put=g=>sink('nct',g);
 for(let c=1;c<=n-4;c++){
  const hc=V.slice(c-1),cs=[...hc,...L.slice(0,4)],ps=[...hc.map((_,i)=>i===0),false,false,false,false];
  const pred=D14Raw(cs,ps,e,loan);put(pred);put(fr(e,Q[3],port));put([...pred].reverse());
 }
 // c3 in U3. Restore U3 using J=(Q/g) mod16 and
 // After inner inversion, U3=J3 XOR J2 XOR U1.
 // Missing high gcd bits are constants0.
 for(let c=5;c<=n;c++)for(let k=0;k<4&&k<n+1-c;k++){
  const size=n+1-c,hc=V.slice(c-1),cs=[...hc,...V.slice(0,4),...(c===n?[]:L.slice(0,k+1))],ps=[...hc.map((_,i)=>i===0),false,false,false,false,...(c===n?[]:[...Array(k).fill(false),true])];
  put(D14Raw([...cs,U[3]],[...ps,true],port,loan));
  put(D14Raw([...cs,port],[...ps,true],U[3],loan));
  put(D14Raw([...cs,U[1]],[...ps,true],U[3],loan));
  for(let odd=1;odd<16;odd+=2){
   if((odd>>Math.min(4,size-k))!==0)continue;
   const gb=L.slice(k+1,Math.min(k+4,size)),gp=gb.map((_,j)=>!!(odd>>(j+1)&1));
   let inv=1;while((inv*odd)%16!==1)inv+=2;
   for(let q=1;q<16;q+=2){const j=q*inv%16;if(((j>>3)^(j>>2))&1){
    const qb=Q.slice(k+1,k+4),qp=qb.map((_,i)=>!!(q>>(i+1)&1));put(D14Raw([...cs,...gb,...qb],[...ps,...gp,...qp],U[3],loan));
   }}
  }
 }
 put([[port,Q[3]]]);sink('hmr',[port,record]);
}
`;
};
