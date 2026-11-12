'use strict';
// Third count carrier. Apply to D16 source; walks unchanged.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D17 alpha anchor '+a);s=s.replace(a,()=>b);};
 one('if(t===n-7)put([[J[n-5],5*n+3],[5*n+3,J[n-5]],[J[n-5],5*n+3]]);','');
 one('S[2]=base+3;T6[2]=base+3;', 'S[2]=base+3;T6[2]=base+3;');
 one('120:113,124:121,125:125,126:126','120:113,122:121,123:123,124:124,125:125,126:126');
 one('if(t>=n-3){put(cls);', 'if(t>=n-5)D17AlphaEnter(n,L,R,J,sign,loan,e,t,sink);\n if(t>=n-3){put(cls);');
 one('outerloadJ(n,terms,L,R,J,sign,loan,ws,sink,t,t);continue;',
     'outerloadJ(n,terms,L,R,J,sign,loan,ws,sink,t,t);if(t>=n-5)D17AlphaExit(n,L,R,J,sign,loan,e,t,sink);continue;');
 one('if(t===n){\n  // Q = orientation', 'D17AlphaExit(n,L,R,J,sign,loan,e,t,sink);\n if(t===n){\n  // Q = orientation');
 return s+`
function D17Raw(cs,ps,z,loan){
 const m=new Map();for(let i=0;i<cs.length;i++){if(m.has(cs[i])&&m.get(cs[i])!==ps[i])return [];m.set(cs[i],ps[i]);}
 if(m.has(z))throw Error('D17 alias '+z);
 return mcN([...m.keys()],[...m.values()],z,loan.filter(w=>w!==z&&!m.has(w)));
}
function D17AlphaEnter(n,L,R,J,sign,loan,e,t,sink){
 const V=Array.from({length:n},(_,j)=>R[n+1-j]),hc=V.slice(t-1),hp=hc.map((_,i)=>i===0),put=g=>sink('nct',g);
 const even=D17Raw([...hc,V[0]],[...hp,false],e,loan);put(even);put(fr(e,J[n-5],J[0]));put([...even].reverse());
 if(t<=n-4){const odd=D17Raw([...hc,V[0]],[...hp,true],e,loan);put(odd);put(fr(e,J[n-5],J[n-3]));put([...odd].reverse());}
}
function D17AlphaExit(n,L,R,J,sign,loan,e,t,sink){
 const V=Array.from({length:n},(_,j)=>R[n+1-j]),U=Array.from({length:n},(_,j)=>L[n+1-j]),hc=V.slice(t-1),hp=hc.map((_,i)=>i===0),put=g=>sink('nct',g);
 const guard=[...hc,V[0]],pol=[...hp,false],raw=(cs,ps,z)=>D17Raw(cs,ps,z,loan);
 // For even V, U0=1 and J0=1 XOR c2. Preserve c2 in U0.
 put(raw([...guard,J[0]],[...pol,true],U[0]));
 const h=V[t-1],a=J.slice(0,t),implicit=[...V.slice(0,t-1),1001],add1=[];
 add1.push(...raw([e,...a],[true,...a.map(()=>true)],h));add1.push(...incReg(a,loan,e));
 eliminate(D2F.dirtyDigit(implicit,a,h,e,loan[0]),1001,1,(cs,z)=>add1.push(...MCX(cs,z,loan.filter(w=>w!==z&&!cs.includes(w)))));
 add1.push(...raw([e,...a],[true,...a.map(()=>false)],h));
 for(const orientation of [0,1]){const pred=raw([...guard,U[0],sign],[...pol,true,!!orientation],e);
  put(pred);put([[h]]);put(orientation?[...add1].reverse():add1);put([[h]]);put([...pred].reverse());}
}
function D17DecodeAlpha(n,L,R,Q,loan,e,dst,sink){
 const V=Array.from({length:n},(_,j)=>R[n+1-j]),U=Array.from({length:n},(_,j)=>L[n+1-j]),put=g=>sink('nct',g);
 const low=D17Raw(V.slice(n-6),V.slice(n-6).map(()=>false),e,loan);put(low);put(fr(e,Q[n-5],dst));put([...low].reverse());
 for(let c=n-5;c<=n;c++){
  const hc=V.slice(c-1),hp=hc.map((_,i)=>i===0),even=D17Raw([...hc,V[0]],[...hp,false],e,loan);
  put(even);put(fr(e,U[0],dst));put([[e,U[0]]]);put([...even].reverse());
  if(c<=n-4){const odd=D17Raw([...hc,V[0]],[...hp,true],e,loan);put(odd);put(fr(e,Q[n-3],dst));put([...odd].reverse());}
 }
}
`;
};
