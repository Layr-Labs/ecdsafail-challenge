'use strict';
// Native645 eviction AFTER the reverse outer walk. Earlier count windows remain
// unresolved. Apply after p-walks.cjs. This is not a full nine-helper divider.
module.exports=s=>{const one=(a,b)=>{if(s.split(a).length!==2)throw Error('R38 tail anchor '+a);s=s.replace(a,()=>b);};
 one('S[bits-2]=sig;parkOuter(n,M,rm,Q,S,p,bits,L[n],loan,sink,true);',
     "if(n!==128)throw Error('R38 tail supports width128');S[bits-2]=sig;S[bits-3]=e;parkOuter(n,M,rm,Q,S,p,bits,L[n],loan,sink,true);");
 one('put(rev(split));put(rev(high));for(let j=0;',
     'put(rev(split));put(rev(high));put([[e,Htop],[Htop,e],[e,Htop]]);S[bits-3]=Htop;for(let j=0;');
 one("const ff=fieldprod(2*n,n,K),perm=w=>w===base+1?L[n]:w===base+2?e:w;put(rev(ff.g.map(a=>a.map(perm))));tap('F');",
     "const count4=[];for(let shift=16;shift<n;shift+=16){const w=M.slice(n-shift);count4.push(...mcN(w,w.map(()=>false),Htop,C));}put(count4);const ff=fieldprod(2*n,n,K),perm=w=>w===base+1?L[n]:w===base+2?e:w;put(rev(ff.g.map(a=>a.map(perm))));put(rev(count4));tap('F');");
 return s;};
