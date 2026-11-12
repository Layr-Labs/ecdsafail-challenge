'use strict';
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D17 winding anchor '+a);s=s.replace(a,()=>b);};
 one('D14BeforeWinding(n,L,R,Q,loan,sink);', 'D17BeforeWinding(n,L,R,Q,loan,sink);D14BeforeWinding(n,L,R,Q,loan,sink);');
 one("sink('nct',cls);sink('nct',D14Relay", "sink('nct',cls);sink('nct',D17Relay(n,L,V,Q,sel,loan,c,false));sink('nct',D14Relay");
 one("sink('nct',D14Relay(n,L,V,Q,sel,loan,c,true));sink('nct',[...park].reverse());", "sink('nct',D14Relay(n,L,V,Q,sel,loan,c,true));sink('nct',D17Relay(n,L,V,Q,sel,loan,c,true));sink('nct',[...park].reverse());");
 one("put([[T6[0],Q[4]]]);sink('hmr',[T6[0],bits+4]);", "put([[T6[0],Q[4]]]);sink('hmr',[T6[0],bits+4]);D17ParkCount(n,L,R,Q,loan,T6[0],bits+2,sink);");
 one('for(let j=1;j<3;j++){put([[T6[j],Q[j]]]);', 'for(let j=1;j<2;j++){put([[T6[j],Q[j]]]);');
 return s+`
function D17BeforeWinding(n,L,R,Q,loan,sink){
 const V=Array.from({length:n},(_,j)=>R[n+1-j]),U0=L[n+1],e=R[1],put=g=>sink('nct',g);
 const cs=[...V.slice(n-6),V[0]],ps=cs.map(()=>false),p=D17Raw(cs,ps,e,loan);
 put(p);put([[e,U0]]);put(fr(e,Q[n-5],U0));put([...p].reverse());
}
function D17Relay(n,L,V,Q,e,loan,c,back){
 if(c>n-4)return [];
 // At height1 the winding parks count5 into V0 until the row exits.
 // Oddness is already known from height1; do not read the parked V0.
 const cs=[e,...(c===1?[]:[V[0]]),...L.slice(0,4)],ps=[true,...(c===1?[]:[true]),false,false,false,false],rows=[],src=back?Q[2]:Q[c<=n-6?n-5:n-3];
 for(const r of fr(e,V[c+2],src)){const rest=r.slice(0,-1).filter(w=>w!==e);rows.push(...D17Raw([...cs,...rest],[...ps,...rest.map(()=>true)],r.at(-1),loan));}
 return rows;
}
function D17ParkCount(n,L,R,Q,loan,port,record,sink){
 const V=Array.from({length:n},(_,j)=>R[n+1-j]),U0=L[n+1],e=R[1],put=g=>sink('nct',g);
 put(D17Raw([V[0],U0],[false,true],port,loan));
 put(D17Raw([V[0],port],[false,true],U0,loan));put(D17Raw([V[0]],[false],U0,loan));
 for(let c=1;c<=n-4;c++){
  const hc=V.slice(c-1),cs=[...hc,V[0],...L.slice(0,4)],ps=[...hc.map((_,i)=>i===0),true,false,false,false,false],p=D17Raw(cs,ps,e,loan);
  put(p);put(fr(e,Q[2],port));put([...p].reverse());
 }
 put([[port,Q[2]]]);sink('hmr',[port,record]);
}
`;
};
