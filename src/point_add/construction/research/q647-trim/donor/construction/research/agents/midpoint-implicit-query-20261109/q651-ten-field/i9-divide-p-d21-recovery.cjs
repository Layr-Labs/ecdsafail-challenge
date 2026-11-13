'use strict';
// After qsplit patch: move count recovery past split/high reversal. Under its
// zero-low-M guard, remainder low bits are invariant modulo M.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D21 recovery anchor '+a);s=s.replace(a,b);};
 one("S[bits-2]=sig;S[bits-3]=e;parkOuter(n,M,rm,Q,S,p,bits,L[n],loan,sink,true);tap('restore');\nput(rev(split));put(rev(high));put([[e,Htop],[Htop,e],[e,Htop]]);S[bits-3]=Htop;", "put(rev(split));put(rev(high));S[0]=e;S[bits-2]=sig;S[bits-3]=Htop;parkOuter(n,M,rm,Q,S,p,bits,L[n],loan,sink,true);tap('restore');");
 one('const z=mcN(M.slice(0,3),[false,false,false],e,C);put(z);put([[e,Q[2],M[n-1]],[e,rm[2],M[n-1]]]);put(rev(z));', 'const z=mcN(M.slice(0,3),[false,false,false],t,C);put(z);put([[t,Q[2],M[n-1]],[t,rm[2],M[n-1]]]);put(rev(z));');
 one("const z=mcN(M.slice(0,4),[false,false,false,false],e,C);put(z);put([[e,Q[3],t],[e,rm[3],t]]);put(rev(z));sink('phase',[t,bits+3]);", "for(const w of [Q[3],rm[3]])put(D17Raw([...M.slice(0,4),w],[false,false,false,false,true],t,C));sink('phase',[t,bits+3]);");
 one("put([[S[0],e],[e,S[0]]]);S[0]=e;tap('qsplit.count0.host');", "tap('qsplit.count0.host');");
 return s;
};
