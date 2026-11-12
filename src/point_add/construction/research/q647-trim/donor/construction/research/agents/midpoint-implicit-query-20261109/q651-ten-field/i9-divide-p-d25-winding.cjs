'use strict';
const fs=require('fs');
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D25 winding anchor '+a);s=s.replace(a,()=>b);};
 one("D2Winding(n,L,R,Q,loan,sink);tap('winding');", "D25WindEncode(n,L,R,Q,loan,base+1,sink);tap('d25.winding.entry');D2Winding(n,L,R,Q,loan,sink);tap('winding');D25WindConnect(n,L,R,Q,loan,base+1,sink);tap('d25.winding.connected');");
 const a=s.indexOf('function D2Winding('),b=s.indexOf('// The actual gcd',a);let f=s.slice(a,b);
 const anchor="sink('nct',rot);";if(f.split(anchor).length!==2)throw Error('D25 rotation anchor');f=f.replace(anchor,anchor+`if(size>2){for(const r of [[Q[size-2],Q[0]],[Q[0],Q[size-2]]])sink('nct',D17Raw([sel,L[0],r[0]],[true,false,true],r[1],loan));}`);
 const body="sink('nct',body.reverse());";if(f.split(body).length!==2)throw Error('D25 body anchor');f=f.replace(body,`const encoded=body.reverse().map(r=>r.length===1&&r[0]===Q[0]?[L[0],Q[0]]:r);
  for(const r of encoded)if(r.includes(Q[0])&&!r.includes(L[0]))throw Error('D25 low-bit host has an unguarded operand');
  sink('nct',encoded);`);
 s=s.slice(0,a)+f+s.slice(b);return s+'\n'+require('./i9-divide-d25-winding-source.cjs');
};
