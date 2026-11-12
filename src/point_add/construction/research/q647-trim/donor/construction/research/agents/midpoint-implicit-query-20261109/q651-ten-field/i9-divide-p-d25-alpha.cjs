'use strict';
const fs=require('fs');
module.exports=s=>{
 s=require('./i9-divide-d25-alpha124.cjs')(s);
 const start=s.indexOf('if(t===n-3){\n  const gs='),end=s.indexOf('\n }',start);if(start<0||end<0)throw Error('D25 gather anchor');s=s.slice(0,start)+s.slice(end+3);
 const anchor='if(t>=n-5)D17AlphaEnter(n,L,R,J,sign,loan,e,t,sink);';if(s.split(anchor).length!==2)throw Error('D25 high anchor');s=s.replace(anchor,'if(t>=n-3){D25High(n,terms,L,R,J,sign,loan,t,sink);continue;}\n '+anchor);
 const a=s.indexOf('const h=v[n-1],implicit=[...v.slice(0,-1),1001];'),b=s.indexOf('// Interim integration boundary:',a);if(a<0||b<0)throw Error('D25 c4 anchor');const c4=s.slice(a,b);
 s+='\nconst D25ModAdd='+require('./i9-divide-d25-dirty-modadd.cjs').build.toString()+';\n'+require('./i9-divide-d25-high-source.cjs')+'\nfunction D25C4(n,L,R,J,sign,loan,e,sink,guard,pol){const v=Array.from({length:n},(_,j)=>R[n+1-j]),u=Array.from({length:n},(_,j)=>L[n+1-j]),put=g=>sink("nct",g);'+c4+'}\n';
 // Compatibility adapter belongs to the middle, after the alpha handoff.
 const call='parkInner(n,L,R,Q,T6,sig,p,0,temps,loan,sink,false);';if(s.split(call).length!==2)throw Error('D25 connect anchor');s=s.replace(call,'D25Connect(n,L,R,Q,loan,base+1,sink);'+call);
 return s;
};
