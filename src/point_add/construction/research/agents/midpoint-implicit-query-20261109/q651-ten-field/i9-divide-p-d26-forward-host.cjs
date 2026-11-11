 'use strict';
// Research candidate only: consume D25 alpha's conditional c0 without native641.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D26 forward-host anchor '+a);s=s.replace(a,()=>b);};
 one('D25Connect(n,L,R,Q,loan,base+1,sink);parkInner(n,L,R,Q,T6,sig,p,0,temps,loan,sink,false);','parkInner(n,L,R,Q,T6,sig,p,0,temps,loan,sink,false);');
 one('const logic=(cs,pol,z,markIndex=-1)=>{','const legacyLogic=(cs,pol,z,markIndex=-1)=>{');
 const anchor="// Enumerate the third carrier's disjoint branches; high odd c2 is identically0.";
 one(anchor,`
const c0=S[0],c5=S[5];
function d26Branches(fn){
 const lo=V.slice(n-7);fn(n-7,-1,lo,lo.map(()=>false));
 for(let c=n-6;c<=n;c++){
  const hc=V.slice(c-1),hp=hc.map((_,j)=>j===0);
  if(c===n-6){for(const odd of [0,1])fn(c,odd,[...hc,V[0]],[...hp,!!odd]);}
  else{fn(c,1,[...hc,V[0]],[...hp,true]);for(const v of [0,2,4,6])fn(c,v,[...hc,...V.slice(0,3)],[...hp,...[0,1,2].map(j=>!!(v>>j&1))]);}
 }
}
function d26Host(c,v){return c===n-7?Q[n-7]:c===n-6?v===0?U[0]:Q[n-3]:v===0?U[0]:Q[n-3];}
function d26Logic(cs,pol,z,markIndex=-1){
 const roles=[c5,c2,c3,c4,c0];if(!roles.some(q=>cs.includes(q)||z===q))return raw(cs,pol,z);
 const rows=[];d26Branches((c,v,hc,hp)=>{
  if(markIndex>=0&&c>n-6&&markIndex>=n-c)return;
  const odd=v===1,deep=c>=n-5&&v===0;
  if(deep&&z===U[2]&&cs.includes(c2))return; // Fuse the c2 mask at carrier release.
  const h0=d26Host(c,v),hosts=[c5,c<=n-6?low2:deep?U[2]:!odd?U[0]:lowHost,c<=n-5?low3:host3,c<=n-4?lowHost:c===n?sg:L[n-c],h0];
  const absent=[h0===c5,c>=n-3&&odd,false,c>n-6&&c<=n-4&&odd,c===n&&odd];
  function lower(a,p,t,g,gp,i){if(i===roles.length){rows.push(...raw([...hc,...g,...a],[...hp,...gp,...p],t));return;}
   const q=roles[i],host=hosts[i],bits=i===2&&c>n-5?4:i===3&&c===n?3:0,guard=V.slice(0,bits),ps=guard.map(()=>false);
   if(t===q){if(!absent[i])lower(a,p,host,[...g,...guard],[...gp,...ps],i+1);return;}
   const ix=a.indexOf(q);if(ix<0){lower(a,p,t,g,gp,i+1);return;}
   const rest=a.filter((_,j)=>j!==ix),rp=p.filter((_,j)=>j!==ix);if(!p[ix])lower(rest,rp,t,g,gp,i+1);
   if(!absent[i])lower([...rest,host],[...rp,true],t,[...g,...guard],[...gp,...ps],i+1);
  }lower(cs,pol,z,[],[],0);
 });return rows;
}
const logic=(...a)=>rev?legacyLogic(...a):d26Logic(...a);
const d26Move=(cs,ps,a,b)=>{put(raw([...cs,a],[...ps,true],b));put(raw([...cs,b],[...ps,true],a));};
const d26Swap=(cs,ps,a,b)=>{for(const r of fr(1022,a,b)){const rr=r.filter(q=>q!==1022);put(raw([...cs,...rr.slice(0,-1)],[...ps,...rr.slice(0,-1).map(()=>true)],rr.at(-1)));}};
const d26Not8=(fn)=>{fn([e,V[0]],[true,true]);fn([e,V[0],V[1]],[true,false,true]);fn([e,...V.slice(0,3)],[true,false,false,true]);};
function d26Prepare(c){
 if(c<=n-6){d26Move([e],[true],Q[n-6],V[c+3]);return;}
 if(c<=n-4){const cs=[e,...V.slice(0,3)],ps=[true,false,false,false];
  for(const q of [Q[2],Q[1],U[1]])put(raw([...cs,q],[...ps,true],U[2]));d26Swap(cs,ps,U[0],U[2]);d26Move(cs,ps,Q[c],U[0]);
  d26Not8((a,b)=>d26Move(a,b,Q[c],V[c+3]));return;
 }
 if(c===n-3||c===n-2)d26Not8((a,b)=>d26Move(a,b,Q[c],V[n-1]));
 if(c===n-1){d26Move([e,V[0]],[true,true],Q[c],S[1]);d26Move([e,V[0],V[1]],[true,false,true],Q[c],U[0]);d26Move([e,...V.slice(0,3)],[true,false,false,true],Q[c],U[0]);}
}
function d26After(c){
 if(c<=n-7){d26Move([e],[true],V[c+3],Q[n-7]);return;}
 if(c===n-6){put(raw([e,V[0]],[true,false],U[0]));d26Move([e,V[0]],[true,false],V[c+3],U[0]);d26Move([e,V[0]],[true,true],V[c+3],Q[n-3]);return;}
 if(c<=n-4){d26Not8((a,b)=>d26Move(a,b,V[c+3],Q[n-3]));return;}
 if(c===n-3||c===n-2)d26Not8((a,b)=>d26Move(a,b,V[n-1],Q[n-3]));
 if(c===n-1){d26Move([e,V[0]],[true,true],S[1],Q[n-3]);d26Move([e,V[0],V[1]],[true,false,true],U[0],Q[n-3]);d26Move([e,...V.slice(0,3)],[true,false,false,true],U[0],Q[n-3]);}
 if(c===n){d26Move([e,V[0],V[1]],[true,false,true],U[0],Q[n-3]);d26Move([e,...V.slice(0,3)],[true,false,false,true],U[0],Q[n-3]);}
}
function d26Gather(port){d26Branches((c,v,cs,ps)=>{
 if(c===n&&v===1)return;
 d26Move(cs,ps,d26Host(c,v),port);
 if(c===n-6&&v===0)put(raw(cs,ps,U[0]));
 if(c>=n-5&&v===0){d26Swap(cs,ps,U[0],U[2]);for(const q of [Q[2],Q[1],U[1]])put(raw([...cs,q],[...ps,true],U[2]));put(raw([...cs,D,S[1]],[...ps,false,true],U[2]));put(raw([...cs,D,U[0]],[...ps,false,true],U[2]));}
 });}
`+anchor);
 one('const forwardBefore=c=>{','const legacyForwardBefore=c=>{');
 one('const forwardAfter=c=>[','const legacyForwardAfter=c=>[');
 one('const reverseBefore=c=>[',`const forwardBefore=c=>{d26Prepare(c);return legacyForwardBefore(c);};
 const forwardAfter=c=>{put(legacyForwardAfter(c));d26After(c);return [];};
 const reverseBefore=c=>[`);
 one('put([[S[0],S[6]],[S[6],S[0]]]);S[0]=S[6];swap02();','d26Gather(S[6]);S[0]=S[6];swap02();');
 return s;
};
