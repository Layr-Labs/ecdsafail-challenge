 'use strict';
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D26 reverse-host anchor '+a);s=s.replace(a,()=>b);};
 one('const logic=(...a)=>rev?legacyLogic(...a):d26Logic(...a);','const logic=(...a)=>d26Logic(...a);');
 let a=s.indexOf('function d26Gather(port){'),b=s.indexOf("// Enumerate the third carrier's disjoint branches",a);if(a<0||b<0)throw Error('D26 gather span');
 s=s.slice(0,a)+`function d26Gather(port,back=false){
 const rows=[],out=g=>rows.push(...g),mv=(cs,ps,a,b)=>{out(raw([...cs,a],[...ps,true],b));out(raw([...cs,b],[...ps,true],a));},sw=(cs,ps,a,b)=>{for(const r of fr(1022,a,b)){const rr=r.filter(q=>q!==1022);out(raw([...cs,...rr.slice(0,-1)],[...ps,...rr.slice(0,-1).map(()=>true)],rr.at(-1)));}};
 d26Branches((c,v,cs,ps)=>{
 if(c===n&&v===1)return;mv(cs,ps,d26Host(c,v),port);
 if(c===n-6&&v===0)out(raw(cs,ps,U[0]));
 if(c>=n-5&&v===0){sw(cs,ps,U[0],U[2]);for(const q of [Q[2],Q[1],U[1]])out(raw([...cs,q],[...ps,true],U[2]));out(raw([...cs,D,S[1]],[...ps,false,true],U[2]));out(raw([...cs,D,U[0]],[...ps,false,true],U[2]));}
 });put(back?rows.reverse():rows);
}
function d26BeforeReverse(c){
 if(c<=n-7){d26Move([e],[true],Q[n-7],V[c+3]);return;}
 if(c===n-6){d26Move([e,V[0]],[true,false],U[0],V[c+3]);put(raw([e,V[0]],[true,false],U[0]));d26Move([e,V[0]],[true,true],Q[n-3],V[c+3]);return;}
 if(c<=n-4){d26Not8((a,b)=>d26Move(a,b,Q[n-3],V[c+3]));return;}
 if(c===n-3||c===n-2)d26Not8((a,b)=>d26Move(a,b,Q[n-3],V[n-1]));
 if(c===n-1){d26Move([e,V[0]],[true,true],Q[n-3],S[1]);d26Move([e,V[0],V[1]],[true,false,true],Q[n-3],U[0]);d26Move([e,...V.slice(0,3)],[true,false,false,true],Q[n-3],U[0]);}
 if(c===n){d26Move([e,V[0],V[1]],[true,false,true],Q[n-3],U[0]);d26Move([e,...V.slice(0,3)],[true,false,false,true],Q[n-3],U[0]);}
}
function d26AfterReverse(c){
 if(c<=n-6){d26Move([e],[true],V[c+3],Q[n-6]);return;}
 if(c<=n-4){d26Not8((a,b)=>d26Move(a,b,V[c+3],Q[c]));return;}
 if(c===n-3||c===n-2)d26Not8((a,b)=>d26Move(a,b,V[n-1],Q[c]));
 if(c===n-1){d26Move([e,V[0]],[true,true],S[1],Q[c]);d26Move([e,V[0],V[1]],[true,false,true],U[0],Q[c]);d26Move([e,...V.slice(0,3)],[true,false,false,true],U[0],Q[c]);}
}
`+s.slice(b);
 one('const reverseBefore=c=>[','const legacyReverseBefore=c=>[');
 one('const reverseAfter=c=>{','const legacyReverseAfter=c=>{');
 one('const reconnectAfter=()=>{',`const reverseBefore=c=>{d26BeforeReverse(c);return legacyReverseBefore(c);};
 const reverseAfter=c=>{put(legacyReverseAfter(c));d26AfterReverse(c);return [];};
 const reconnectAfter=()=>{`);
 one('put([[S[0],count0Host],[count0Host,S[0]]]);S[0]=count0Host;extractBit(6,S[6]);','d26Gather(S[0],true);S[0]=count0Host;extractBit(6,S[6]);');
 one('D25WindEncode(n,L,R,Q,loan,base+1,sink);','D26PreWind(n,L,R,Q,loan,R[1],sink);D25WindEncode(n,L,R,Q,loan,R[1],sink);');
 return s+`
function D26PreWind(n,L,R,Q,loan,port,sink){
 const V=Array.from({length:n},(_,j)=>R[n+1-j]),U=Array.from({length:n},(_,j)=>L[n+1-j]),put=g=>sink('nct',g),raw=(cs,ps,z)=>D17Raw(cs,ps,z,loan);
 const mv=(cs,ps,a,b)=>{put(raw([...cs,a],[...ps,true],b));put(raw([...cs,b],[...ps,true],a));};
 const low=V.slice(n-6);mv(low,low.map(()=>false),Q[n-6],port);
 for(let c=n-5;c<=n;c++){
  const hc=V.slice(c-1),hp=hc.map((_,j)=>j===0),eight=[...hc,...V.slice(0,3)],ep=[...hp,false,false,false];
  mv(eight,ep,U[0],port);
  for(const r of fr(1022,U[0],U[2])){const rr=r.filter(q=>q!==1022);put(raw([...eight,...rr.slice(0,-1)],[...ep,...rr.slice(0,-1).map(()=>true)],rr.at(-1)));}
  for(const q of [Q[2],Q[1],U[1]])put(raw([...eight,q],[...ep,true],U[2]));
  const host=c===n?U[0]:c===n-2?L[3]:Q[c];
  if(c<n)mv([...hc,V[0]],[...hp,true],host,port);
  mv([...hc,V[0],V[1]],[...hp,false,true],host,port);
  mv([...hc,...V.slice(0,3)],[...hp,false,false,true],host,port);
 }
}
`;
};
