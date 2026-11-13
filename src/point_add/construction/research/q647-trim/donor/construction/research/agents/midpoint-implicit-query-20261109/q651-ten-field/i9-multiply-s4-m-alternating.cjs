'use strict';
// Exact arbitrary-dirty implementation. e and h are stable during output sweep.
function alternatingDigit(A,B,h,e,loan){
 const n=A.length,k=n-1,g=[];
 const x=q=>g.push([q]),cx=(a,b)=>g.push([a,b]),ccx=(a,b,c)=>g.push([a,b,c]);
 const toggle=(a,b,c,t)=>{ccx(a,b,loan);ccx(loan,c,t);ccx(a,b,loan);ccx(loan,c,t);};
 for(const b of B)x(b);
 if(n===1){toggle(e,A[0],B[0],h);x(B[0]);cx(e,h);toggle(e,h,A[0],B[0]);return g;}
 for(let i=1;i<n;i++)cx(A[i],B[i]);
 ccx(e,A[k],h);
 for(let i=n-2;i>=1;i--)cx(A[i],A[i+1]);
 for(let i=0;i<n-1;i++)ccx(B[i],A[i],A[i+1]);
 toggle(e,A[k],B[k],h);cx(e,h);
 const output=i=>{ccx(loan,A[i],B[i]);ccx(e,h,loan);ccx(loan,A[i],B[i]);};
 output(k);
 for(let i=n-2;i>=0;i--){ccx(B[i],A[i],A[i+1]);output(i);}
 if(n&1)ccx(e,h,loan);
 for(let i=1;i<n-1;i++)cx(A[i],A[i+1]);
 for(let i=1;i<n;i++)cx(A[i],B[i]);
 for(const b of B)x(b);
 return g;
}
module.exports={alternatingDigit};
