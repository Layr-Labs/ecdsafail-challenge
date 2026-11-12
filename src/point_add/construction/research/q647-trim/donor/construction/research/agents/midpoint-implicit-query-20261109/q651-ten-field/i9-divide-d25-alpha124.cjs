'use strict';
// Experimental: count0 stays off641 through alpha124. Not selected package.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D24 alpha124 anchor '+a);s=s.replace(a,()=>b);};
 one('if(t===n-5)put([[J[n-6],5*n+1],[5*n+1,J[n-6]]]);',`if(t===n-3){
  const gs=[n-5,n-4].map(c=>D2F.flagHeight(v,c,e,loan));
  for(let j=0;j<2;j++){put(gs[j]);const h=J[n-5+j];put([[e,h,5*n+1],[e,5*n+1,h]]);put([...gs[j]].reverse());}
  put(gs[0]);put(gs[1]);put([[e],[e,J[n-6],5*n+1],[e,5*n+1,J[n-6]],[e]]);put([...gs[1]].reverse());put([...gs[0]].reverse());
 }`);
 one('if(t>=n-5)D17AlphaEnter(n,L,R,J,sign,loan,e,t,sink);',`if(t>=n-5)D17AlphaEnter(n,L,R,J,sign,loan,e,t,sink);
 if(t===n-5||t===n-4){put(cls);if(t===n-4)put(D2F.fr(e,J[n-4],J[3]));put([[e,J[n-6],J[t]],[e,J[t],J[n-6]]]);put([...cls].reverse());}`);
 const a=s.indexOf('function D12FoldSeed('),b=s.indexOf('function D12DecodeXor(',a);let f=s.slice(a,b);if(!f.includes('[n-3,n-2,n-1,n]'))throw Error('D24 fold span');s=s.slice(0,a)+f.replace('[n-3,n-2,n-1,n]','[n-4,n-3,n-2,n-1,n]')+s.slice(b);
 const c=s.indexOf('function D14AlphaHost('),d=s.indexOf('function D14Raw(',c);f=s.slice(c,d);if(!f.includes('if(c===n-4){'))throw Error('D24 host span');s=s.slice(0,c)+f.replace('if(c===n-4){','if(false){')+s.slice(d);
 return s;
};
