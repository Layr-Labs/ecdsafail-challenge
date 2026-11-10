'use strict';
// Controlled restoring division digit with an initially arbitrary borrowed bit.
// Once h is final, its conjunction with e supplies every output control.
// Two reads of the dirty loan, separated by one e*h flip, apply that product
// regardless of the loan's initial value. Intermediate rungs preserve e,h.
function alternatingDigit(A,B,h,e,loan){
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
    function digitBit(i){ccx(loan,A[i],B[i]);ccx(e,h,loan);ccx(loan,A[i],B[i]);}
    digitBit(k);
    for(let i=n-2;i>=0;i--){ccx(B[i],A[i],A[i+1]);digitBit(i);}
    if(n&1)ccx(e,h,loan);
    for(let i=1;i<n-1;i++)cx(A[i],A[i+1]);
    for(let i=1;i<n;i++)cx(A[i],B[i]);
    for(const b of B)x(b);
    return g;
}
module.exports={alternatingDigit};
