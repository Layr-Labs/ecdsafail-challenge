'use strict';
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D17 middle anchor '+a);s=s.replace(a,()=>b);};
 const a=s.indexOf('const c3=S[3],host3=U[3],low3=Q[n-5];'),b=s.indexOf('// Before mask, U3 hosts',a);
 if(a<0||b<0)throw Error('D17 logic span');
 s=s.slice(0,a)+`
const c3=S[3],host3=U[3],low3=Q[n-5],c2=S[2],low2=Q[n-6];
const logic=(cs,pol,z,markIndex=-1)=>{
 if(![c2,c3,c4].some(w=>cs.includes(w)||z===w))return raw(cs,pol,z);
 const rows=[];
 for(let cls=n-6;cls<=n;cls++)for(const parity of (cls===n-6?[-1]:[0,1])){
  if(markIndex>=0&&cls>n-6&&markIndex>=n-cls)continue;
  const hc=cls===n-6?V.slice(cls):V.slice(cls-1),hp=hc.map((_,i)=>cls!==n-6&&i===0);
  if(parity!==-1){hc.push(V[0]);hp.push(!!parity);}
  const h2=cls===n-6?low2:parity===0?U[0]:lowHost;
  const h3=cls<=n-5?low3:host3,h4=cls<=n-4?lowHost:cls===n?sg:L[n-cls];
  const roles=[c2,c3,c4],hosts=[h2,h3,h4];
  function lower(c,p,target,guards,gpol,which){
   if(which===3){rows.push(...raw([...hc,...guards,...c],[...hp,...gpol,...p],target));return;}
   const virtual=roles[which],host=hosts[which];
   const absent=(which===0&&cls>=n-3&&parity===1)||(which===2&&cls>n-6&&cls<=n-4&&parity===1);
   const gb=which===1?(cls>n-5?4:0):which===2?(cls===n?3:0):0,g=V.slice(0,gb),gp=g.map(()=>false);
   if(target===virtual){if(!absent)lower(c,p,host,[...guards,...g],[...gpol,...gp],which+1);return;}
   const ix=c.indexOf(virtual);if(ix<0){lower(c,p,target,guards,gpol,which+1);return;}
   const rest=c.filter((_,i)=>i!==ix),rp=p.filter((_,i)=>i!==ix);
   if(!p[ix])lower(rest,rp,target,guards,gpol,which+1);
   if(!absent)lower([...rest,host],[...rp,true],target,[...guards,...g],[...gpol,...gp],which+1);
  }
  lower(cs,pol,z,[],[],0);
 }
 return rows;
};
// Enumerate the third carrier's disjoint branches; high odd c2 is identically0.
function carrier2(fn){
 const low=V.slice(n-6);fn(low,low.map(()=>false),low2,false);
 for(let c=n-5;c<=n;c++){
  const hc=V.slice(c-1),hp=hc.map((_,i)=>i===0);
  fn([...hc,V[0]],[...hp,false],U[0],true);
  if(c<n)fn([...hc,V[0]],[...hp,true],c<=n-4?lowHost:L[n-c],false);
 }
}
function guardedSwap(cs,ps,a,b){for(const r of fr(e,a,b)){
 const rest=r.slice(0,-1).filter(w=>w!==e);put(raw([...cs,...rest],[...ps,...rest.map(()=>true)],r.at(-1)));}}
function swap02(){carrier2((cs,ps,h)=>guardedSwap(cs,ps,S[0],h));}
function marker0(cs,ps,z){for(let j=1;j<n-1;j+=2){const hi=V.slice(n-j-1);
 put(raw([...cs,D,...hi,...L.slice(0,j+1)],[...ps,true,...hi.map(()=>false),...L.slice(0,j).map(()=>false),true],z));}}
function read0(cs,ps,z){marker0(cs,ps,z);
 put(raw([...cs,D,V[0]],[...ps,false,false],z));
 put(raw([...cs,D,V[0],U[0]],[...ps,false,false,true],z));}
function mask0Carrier(){carrier2((cs,ps,h,even)=>{
 if(even){put(raw(cs,ps,U[0]));marker0(cs,ps,U[0]);}
 else put(raw([...cs,D,h],[...ps,false,true],U[0]));
});}
function gather0(back){carrier2((cs,ps,h,even)=>{
 if(even){if(!back)read0(cs,ps,S[0]);}
 else if(back)read0(cs,ps,h);else guardedSwap(cs,ps,h,S[0]);
});}
`+s.slice(b);
 one('function mask(){for(let j=0;j<bits;j++)if(j===3)mask3();else put(logic([D,S[j]],[false,true],U[j]));}',
     'function mask(){for(let j=1;j<bits;j++)if(j===3)mask3();else put(logic([D,S[j]],[false,true],U[j]));}');
 one('return [...(c<=n-5?fr(e,Q[n-4],V[c+1]):[])',
     'return [...(c<=n-6?fr(e,Q[n-5],V[c+2]):[]),...(c<=n-5?fr(e,Q[n-4],V[c+1]):[])');
 one('...(c<=n-5?fr(e,V[c+1],low3):[])];',
     '...(c<=n-5?fr(e,V[c+1],low3):[]),...(c<=n-6?fr(e,V[c+2],low2):[])];');
 one('const reverseBefore=c=>[...(c<=n-5?', 'const reverseBefore=c=>[...(c<=n-6?fr(e,low2,V[c+2]):[]),...(c<=n-5?');
 one('const rows=[...pw(c),...(c<=n-5?', 'const rows=[...pw(c),...(c<=n-6?fr(e,V[c+2],Q[n-5]):[]),...(c<=n-5?');
 one("delta();bias(false);mark();mask();\n sink('hmr',[S[0],off]);",
     "delta();bias(false);mark();mask();swap02();mask0Carrier();\n sink('hmr',[S[0],off+2]);gather0(false);sink('hmr',[S[0],off]);");
 one("for(let j=1;j<bits;j++)if(j!==3&&j!==4)sink('hmr',[S[j],off+j]);",
     "for(let j=1;j<bits;j++)if(j!==2&&j!==3&&j!==4)sink('hmr',[S[j],off+j]);");
 const start=s.indexOf(" extractBit(1,S[1]);sink('phase',[S[1],off+1]);extractBit(3,S[2]);"),end=s.indexOf(' for(let c=1;c<=n-4;c++)cl(c,fr(e,lowHost,L[n-c]));Gtop',start);
 if(start<0||end<0)throw Error('D17 reverse span');
 s=s.slice(0,start)+`
 extractBit(1,S[1]);sink('phase',[S[1],off+1]);
 extractBit(3,S[5]);sink('phase',[S[5],off+3]);gather3(S[5],true);
 for(let j=5;j<bits;j++){extractBit(j,S[j]);sink('phase',[S[j],off+j]);}
 for(let c=1;c<n;c++)cl(c,fr(e,S[0],c<=n-4?lowHost:L[n-c]));
 for(const w of [Q[1],U[1],S[1]])put(mcN([...leaseGuard,w],[...leasePol,true],sg,loan));
 const pr=mcN(leaseGuard,leasePol,e,loan);put(pr);put(fr(e,S[0],sg));put([...pr].reverse());
 extractBit(0,S[0]);sink('phase',[S[0],off]);extractBit(0,S[0]);
 extractBit(2,S[0]);sink('phase',[S[0],off+2]);
 gather0(true);mask0Carrier();swap02();
 mask();mark();bias(true);delta();
`+s.slice(end);
 one('function extractBit(bit,target){', `function extractBit(bit,target){
 const exraw=(cs,ps,z)=>{
  if(bit!==2||!rev)return raw(cs,ps,z);
  const ix=cs.indexOf(sg),rest=cs.filter((_,j)=>j!==ix),rp=ps.filter((_,j)=>j!==ix),hc=[V[n-1],...V.slice(0,3)],hp=[true,false,false,false];
  const rows=[...raw(cs,ps,z),...raw([...hc,...cs],[...hp,...ps],z)];
  if(!ps[ix])rows.push(...raw([...hc,...rest],[...hp,...rp],z));
  for(const w of [Q[1],U[1],S[1]])rows.push(...raw([...hc,...rest,w],[...hp,...rp,true],z));return rows;
 };
`);
 one('put(raw([e,sg,...Q.slice(0,j+1)],[true,!!si,...eq_bits(Q,q).slice(0,j+1)],target));',
     'put(exraw([e,sg,...Q.slice(0,j+1)],[true,!!si,...eq_bits(Q,q).slice(0,j+1)],target));');
 return s;
};
