'use strict';
// The borrowed bit masks all output gates at once. A shared CNOT offset
// ensures that the prior mask cannot disturb an intervening ripple carry.
function sharedDigit(A,B,h,e,loan){
    const n=A.length,k=n-1,g=[];
    const x=q=>g.push([q]),cx=(a,b)=>g.push([a,b]),ccx=(a,b,c)=>g.push([a,b,c]);
    function togglePredicate(a,b,c,target){
        ccx(a,b,loan);ccx(loan,c,target);ccx(a,b,loan);ccx(loan,c,target);
    }
    for(const b of B)x(b);
    if(n===1){
        togglePredicate(e,A[0],B[0],h);x(B[0]);cx(e,h);
        togglePredicate(e,h,A[0],B[0]);return g;
    }
    for(let i=1;i<n;i++)cx(A[i],B[i]);
    ccx(e,A[k],h);
    for(let i=n-2;i>=1;i--)cx(A[i],A[i+1]);
    for(let i=0;i<n-1;i++)ccx(B[i],A[i],A[i+1]);
    togglePredicate(e,A[k],B[k],h);cx(e,h);
    for(let i=0;i<n;i++){ccx(loan,A[i],B[i]);if(i<k)cx(loan,B[i]);}
    ccx(e,h,loan);
    ccx(loan,A[k],B[k]);
    for(let i=n-2;i>=0;i--){
        ccx(B[i],A[i],A[i+1]);ccx(loan,A[i],B[i]);
    }
    ccx(e,h,loan);
    for(let i=0;i<k;i++)cx(loan,B[i]);
    for(let i=1;i<n-1;i++)cx(A[i],A[i+1]);
    for(let i=1;i<n;i++)cx(A[i],B[i]);
    for(const b of B)x(b);
    return g;
}
module.exports={sharedDigit};
