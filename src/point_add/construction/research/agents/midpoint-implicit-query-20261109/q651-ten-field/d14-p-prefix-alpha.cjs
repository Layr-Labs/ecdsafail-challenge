'use strict';
// Exact partial prefix. Full645 eviction remains OPEN at alpha128 and middle.
module.exports=s=>{const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D1 prefix anchor '+a);s=s.replace(a,()=>b);};
 one('S=[...vec(bits-2,base+1),Q[n-2],rp[0]],','S=[...vec(bits-2,base+1).map((w,i)=>i===4?Q[n-3]:w),Q[n-2],rp[0]],');
 // Only the alpha carrier uses the prefix count mapping. Restore normal S/T6
 // immediately afterwards so the untouched middle and R38 suffix stay bound.
 one("D2Alpha(n,terms,L,R,Q,sig,loan,[rm[1],e,t,L[0]],sink);tap('alpha');",
 `D2Alpha(n,terms,L,R,Q,sig,loan,[rm[1],e,t,L[0]],sink);
 for(let c=1;c<n;c++){
  const pred=flagHeight(vt,c,R[1],loan),host=c<n-2?Q[n-3]:c===n-2?L[4]:L[1];
  put(pred);put(fr(R[1],host,base+5));if(c===n-1)put([[R[1],L[1]]]);put(rev(pred));
 }
 S[4]=base+5;T6[4]=base+5;tap('alpha');`);
 one('if(t< n-1){ // Preserve all lower classes literally.','if(t< n-2){ // D1: top-three classes get explicit count routing.');
 one('put(cls);put(D2F.fr(e,J[n-2],utop));',
 `put(cls);
 if(t===n-1)put([[e,L[1]],...D2F.fr(e,J[n-3],L[1])]);
 if(t===n)put(D2F.fr(e,J[n-3],5*n+5));
 put(D2F.fr(e,J[t===n-2?n-3:n-2],utop));`);
 return s;
};
