'use strict';
// Route c4 through actual count consumers. Winding/reverse-outer parking OPEN.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('middle anchor '+a);s=s.replace(a,()=>b);};
 const a=s.indexOf('function delta(){',s.indexOf('function parkInner(')),b=s.indexOf('\nconst cl=',a);
 if(a<0||b<0)throw Error('middle span');
 s=s.slice(0,a)+`
const c4=S[4],lowHost=Q[n-4];
const raw=(cs,pol,z)=>{
 const map=new Map();for(let i=0;i<cs.length;i++){if(map.has(cs[i])&&map.get(cs[i])!==pol[i])return [];map.set(cs[i],pol[i]);}
 const keys=[...map.keys()];if(keys.includes(z))throw Error('middle alias '+keys+' ->'+z);
 return mcN(keys,keys.map(w=>map.get(w)),z,loan.filter(w=>w!==z&&!map.has(w)));
};
const logic=(cs,pol,z,markIndex=-1)=>{
 if(!cs.includes(c4)&&z!==c4)return raw(cs,pol,z);
 const rows=[];
 for(let cls=n-4;cls<=n;cls++){
  if(markIndex>=0&&cls>n-4&&markIndex>=n-cls)continue;
  const hc=cls===n-4?V.slice(cls):V.slice(cls-1),hp=hc.map((_,i)=>cls!==n-4&&i===0);
  const host=cls===n-4?lowHost:cls===n?sg:L[n-cls];
  if(cls!==n){rows.push(...raw([...hc,...cs.map(w=>w===c4?host:w)],[...hp,...pol],z===c4?host:z));continue;}
  const gc=[...hc,...V.slice(0,3)],gp=[...hp,false,false,false];
  if(z===c4){rows.push(...raw([...gc,...cs],[...gp,...pol],sg));continue;}
  const ix=cs.indexOf(c4),rest=cs.filter((_,i)=>i!==ix),rp=pol.filter((_,i)=>i!==ix);
  // Outside the lease guard the count is0, while physical sg retains orientation.
  if(!pol[ix])rows.push(...raw([...hc,...rest],[...hp,...rp],z));
  rows.push(...raw([...gc,sg,...rest],[...gp,true,...rp],z));
 }
 return rows;
};
function greater(value){const rows=[];for(let j=0;j<bits;j++)if(!(value>>j&1)){
 const cs=[S[j],...S.slice(j+1)],pol=[true,...S.slice(j+1).map((_,b)=>!!(value>>(b+j+1)&1))];rows.push(...logic(cs,pol,e));
}return rows;}
function delta(){for(let l=0;l<n-1;l++){const a=greater(l);put(a);put(raw([e,...V.slice(0,l+1)],[true,...V.slice(0,l).map(()=>false),true],D));put([...a].reverse());}}
function bias(back){for(let ii=0;ii<n;ii++){
 const l=back?n-1-ii:ii,g=raw([D,...V.slice(0,l+1)],[true,...V.slice(0,l).map(()=>false),true],e),v=(l+1)%n,rows=[];
 for(let j=0;j<bits;j++)if(v>>j&1)for(let k=bits-1;k>=j;k--)rows.push(...logic([e,...S.slice(j,k)],[true,...S.slice(j,k).map(()=>true)],S[k]));
 put(g);put(back?rows:rows.reverse());put([...g].reverse());
}}
function mark(){for(let i=0;i<n-1;i++)put(logic([D,...S],[true,...eq_bits(S,i)],L[i],i));}
function mask(){for(let j=0;j<bits;j++)put(logic([D,S[j]],[false,true],U[j]));}
function extractBit(bit,target){
 for(let j=0;j<n-1;j++)if(j>>bit&1){
  // The marker is strictly below n-height(V), including the rare high classes.
  const hi=V.slice(n-j-1),g=raw([D,...hi,...L.slice(0,j+1)],[true,...hi.map(()=>false),...L.slice(0,j).map(()=>false),true],e);
  put(g);put([[e,target]]);put([...g].reverse());
 }
 const j=bit,g=raw([D,...V.slice(0,j+1)],[false,...V.slice(0,j+1).map(()=>false)],e);put(g);put([[e,U[j],target]]);
 const m=1<<(j+1);for(let q=1;q<m;q+=2){const sol=shortinv(BigInt(q),BigInt(m));
  if(bit===0){put(raw([e,...Q.slice(0,1)],[true,true],target));continue;}
  for(let si=0;si<2;si++){
   const guess=(BigInt(si?1:-1)*kp*sol+BigInt(m*m)*kp)%BigInt(m);
   if(guess>>BigInt(j)&1n)put(raw([e,sg,...Q.slice(0,j+1)],[true,!!si,...eq_bits(Q,q).slice(0,j+1)],target));
  }
 }put([...g].reverse());
}
`+s.slice(b);
 one('Gtop(n,L,R,Q,[e,t],loan,put,forwardBefore,forwardAfter);transferMiddle(false);delta();bias(false);mark();mask();for(let j=0;j<bits;j++)sink(\'hmr\',[S[j],off+j]);routeZeros(n,L,R,e,loan,put,false,p3);',
 `Gtop(n,L,R,Q,[e,t],loan,put,forwardBefore,forwardAfter);
 for(let c=1;c<=n-4;c++)cl(c,fr(e,L[n-c],lowHost));
 delta();bias(false);mark();mask();
 sink('hmr',[S[0],off]);
 const gather=(c,host)=>cl(c,fr(e,host,S[0]));
 for(let c=1;c<n;c++)gather(c,c<=n-4?lowHost:L[n-c]);
 const pr=mcN(leaseGuard,leasePol,e,loan);put(pr);put(fr(e,sg,S[0]));put([...pr].reverse());
 for(const w of [Q[1],U[1],S[1]])put(mcN([...leaseGuard,w],[...leasePol,true],sg,loan));
 sink('hmr',[S[0],off+4]);
 for(let j=1;j<bits;j++)if(j!==4)sink('hmr',[S[j],off+j]);
 routeZeros(n,L,R,e,loan,put,false,p3);`);
 one("extract();for(let j=0;j<bits;j++)sink('phase',[S[j],off+j]);mask();mark();bias(true);delta();transferMiddle(true);",
 `extractBit(4,S[0]);sink('phase',[S[0],off+4]);
 for(let j=1;j<bits;j++)if(j!==4){extractBit(j,S[j]);sink('phase',[S[j],off+j]);}
 for(let c=1;c<n;c++)cl(c,fr(e,S[0],c<=n-4?lowHost:L[n-c]));
 for(const w of [Q[1],U[1],S[1]])put(mcN([...leaseGuard,w],[...leasePol,true],sg,loan));
 const pr=mcN(leaseGuard,leasePol,e,loan);put(pr);put(fr(e,S[0],sg));put([...pr].reverse());
 extractBit(0,S[0]);sink('phase',[S[0],off]);
 mask();mark();bias(true);delta();
 for(let c=1;c<=n-4;c++)cl(c,fr(e,lowHost,L[n-c]));`);
 return s;
};
