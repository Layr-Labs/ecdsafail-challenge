'use strict';
// Experimental second carrier. Applied after D12 XOR alpha + tail.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D14 anchor '+a);s=s.replace(a,()=>b);};
 one('D12FoldSeed(n,L,R,Q,loan,rm[1],sink);','D12FoldSeed(n,L,R,Q,loan,rm[1],sink);D14AlphaHost(n,L,R,Q,loan,rm[1],sink);');
 const a=s.indexOf('const logic=(cs,pol,z,markIndex=-1)=>{'),b=s.indexOf('\nfunction greater(',a);
 if(a<0||b<0)throw Error('logic span');
 s=s.slice(0,a)+`
const c3=S[3],host3=U[3],low3=Q[n-5];
const logic=(cs,pol,z,markIndex=-1)=>{
 if(!cs.includes(c4)&&z!==c4&&!cs.includes(c3)&&z!==c3)return raw(cs,pol,z);
 const rows=[];
 for(let cls=n-5;cls<=n;cls++){
  if(markIndex>=0&&cls>n-5&&markIndex>=n-cls)continue;
  const hc=cls===n-5?V.slice(cls):V.slice(cls-1),hp=hc.map((_,i)=>cls!==n-5&&i===0);
  const h3=cls===n-5?low3:host3,h4=cls<=n-4?lowHost:cls===n?sg:L[n-cls];
  function lower(c,p,target,guards,gpol,which){
   if(which===2){rows.push(...raw([...hc,...guards,...c],[...hp,...gpol,...p],target));return;}
   const virtual=which===0?c3:c4,host=which===0?h3:h4;
   const gb=which===0?(cls>n-5?4:0):(cls===n?3:0),g=V.slice(0,gb),gp=g.map(()=>false);
   if(target===virtual){lower(c,p,host,[...guards,...g],[...gpol,...gp],which+1);return;}
   const ix=c.indexOf(virtual);if(ix<0){lower(c,p,target,guards,gpol,which+1);return;}
   const rest=c.filter((_,i)=>i!==ix),rp=p.filter((_,i)=>i!==ix);
   if(!p[ix])lower(rest,rp,target,guards,gpol,which+1);
   lower([...rest,host],[...rp,true],target,[...guards,...g],[...gpol,...gp],which+1);
  }
  lower(cs,pol,z,[],[],0);
 }
 return rows;
};
// Before mask, U3 hosts count3 on high classes. Its ordinary mask is fused
// with the later carrier release, after a clean measurement port is available.
function mask3(){const hc=V.slice(n-5);put(raw([...hc,D,low3],[...hc.map(()=>false),false,true],U[3]));}
function restoreU3(back){
 for(let c=n-4;c<=n;c++){
  const hc=V.slice(c-1),cs=[...hc,...V.slice(0,4)],ps=[...hc.map((_,i)=>i===0),false,false,false,false];
  for(const w of [Q[3],Q[back?2:1],U[1]])put(raw([...cs,w],[...ps,true],host3));
  put(raw([...cs,D,S[1]],[...ps,false,true],host3));
 }
}
function gather3(port,back){
 for(let c=1;c<=n-5;c++)cl(c,fr(e,low3,port));
 if(back)restoreU3(true);
 for(let c=n-4;c<=n;c++){
  const hc=V.slice(c-1),cs=[...hc,...V.slice(0,4),host3],ps=[...hc.map((_,i)=>i===0),false,false,false,false,true];
  put(raw(cs,ps,port));
 }
 if(!back)restoreU3(false);
}
`+s.slice(b);
 one('function mask(){for(let j=0;j<bits;j++)put(logic([D,S[j]],[false,true],U[j]));}',
     'function mask(){for(let j=0;j<bits;j++)if(j===3)mask3();else put(logic([D,S[j]],[false,true],U[j]));}');
 one('return [...fr(e,src,V[c]),...(c===n-1?[[e,L[1]]]:[]),...p1(c)];',
     'return [...(c<=n-5?fr(e,Q[n-4],V[c+1]):[]),...fr(e,src,V[c]),...(c===n-1?[[e,L[1]]]:[]),...p1(c)];');
 one('const forwardAfter=c=>[...p2(c),...(c<n?fr(e,V[c],L[n-c]):[])];',
     'const forwardAfter=c=>[...p2(c),...(c<n?fr(e,V[c],L[n-c]):[]),...(c<=n-5?fr(e,V[c+1],low3):[])];');
 one('const reverseBefore=c=>[...(c<n?fr(e,L[n-c],V[c]):[]),...p2(c).reverse()];',
     'const reverseBefore=c=>[...(c<=n-5?fr(e,low3,V[c+1]):[]),...(c<n?fr(e,L[n-c],V[c]):[]),...p2(c).reverse()];');
 one('const rows=pw(c);if(c<n-2)return [...rows,...fr(e,V[c],Q[n-3])];',
     'const rows=[...pw(c),...(c<=n-5?fr(e,V[c+1],Q[n-4]):[])];if(c<n-2)return [...rows,...fr(e,V[c],Q[n-3])];');
 one("sink('hmr',[S[0],off+4]);\n for(let j=1;j<bits;j++)if(j!==4)sink('hmr',[S[j],off+j]);",
     "sink('hmr',[S[0],off+4]);gather3(S[0],false);sink('hmr',[S[0],off+3]);\n for(let j=1;j<bits;j++)if(j!==3&&j!==4)sink('hmr',[S[j],off+j]);");
 one("for(let j=1;j<bits;j++)if(j!==4){extractBit(j,S[j]);sink('phase',[S[j],off+j]);}",
     "extractBit(1,S[1]);sink('phase',[S[1],off+1]);extractBit(3,S[2]);sink('phase',[S[2],off+3]);gather3(S[2],true);\n for(let j=2;j<bits;j++)if(j!==3&&j!==4){extractBit(j,S[j]);sink('phase',[S[j],off+j]);}");
 return s+`
// High classes: Q3 XOR encoding -> count3 in U3, original Q restored.
// At height n-4, count3 still arrives in Q[n-4].
function D14AlphaHost(n,L,R,Q,loan,e,sink){
 const V=Array.from({length:n},(_,j)=>R[n+1-j]),U=Array.from({length:n},(_,j)=>L[n+1-j]),put=g=>sink('nct',g);
 for(let c=n-4;c<=n;c++){
  const hc=V.slice(c-1),cs=[...hc,...V.slice(0,4)],ps=[...hc.map((_,i)=>i===0),false,false,false,false];
  for(const w of [Q[3],Q[1],U[1]])put(mcN([...cs,w],[...ps,true],U[3],loan));
  if(c===n-4){
   const pred=mcN(cs,ps,e,loan);put(pred);put(fr(e,Q[n-4],U[3]));put([...pred].reverse());
  }else put(mcN([...cs,U[3]],[...ps,true],Q[3],loan));
 }
}
`;
};
