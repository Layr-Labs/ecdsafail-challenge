'use strict';
const assert=require('node:assert/strict');
const path=require('node:path');
const {threshold,toggle}=require('./mask.cjs');

// The high bit of A is the sector predicate. For every enabled digit it is one.
// C=[A_low<=B_low] gives the full comparison with the extra B-high control.
// Borrow d to hold C during the carry ripple, restore d before the second echo.
function highOne(w,A,B,h,e,remask) {
    const n=A.length-1,k=n-1,d=w.y.at(-1),top=B[n];
    assert(k>=1&&A.length===B.length&&w.y.length>=2);
    const x=q=>w.raw(-1,-1,q),cx=(a,t)=>w.raw(a,-1,t),ccx=(a,b,t)=>w.raw(a,b,t);
    w.op([e,top,d],h);
    for(let i=0;i<n;i++)x(B[i]);
    for(let i=1;i<=k;i++)cx(A[i],B[i]);
    cx(A[k],d);
    for(let i=k-1;i>=1;i--)cx(A[i],A[i+1]);
    for(let i=0;i<k;i++)ccx(B[i],A[i],A[i+1]);
    ccx(A[k],B[k],d);x(d);
    w.op([e,top,d],h);remask();
    ccx(e,d,top);x(d);ccx(A[k],B[k],d);
    ccx(e,A[k],B[k]);
    for(let i=k-1;i>=0;i--){ccx(B[i],A[i],A[i+1]);ccx(e,A[i],B[i]);}
    for(let i=1;i<k;i++)cx(A[i],A[i+1]);
    cx(A[k],d);ccx(e,d,top);remask();
    for(let i=1;i<=k;i++)cx(A[i],B[i]);
    for(let i=0;i<n;i++)x(B[i]);
}
function dividend(w,A,B,h,tag,base,hi,i,schedule={threshold,toggle}){
    const e=w.tst,spec=schedule.threshold(hi-base+1,i-base);
    if(A.length<3||w.y.length<2||2*spec.cost+3>=A.length){
        for(const r of w.d18digit(A,B,h,e,w.y[0]))w.raw(r.length===1?-1:r[0],r.length===3?r[1]:-1,r.at(-1));
        return;
    }
    const mask=()=>{w.raw(-1,-1,h);schedule.toggle(w,tag,spec,[w.fire,h],e);w.raw(-1,-1,h);};
    highOne(w,A,B,h,e,mask);
}
function install(){
    const id=require.resolve(path.resolve(__dirname,'../../q648-next/field/tail.cjs'));
    const old=require.cache[id]?.fieldMask;
    assert(old,'apply the field-mask preload first');
    const previous=old.transform;
    const needle='for(const z of this.d18digit(rh.slice(relay?Math.max(0,base-i-1):0,-1).concat(this.fire),ah.slice(relay?Math.max(0,base-i-1):0),carry,this.tst,this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1))';
    const code='tuning.coefficient.dividend(this,rh.slice(relay?Math.max(0,base-i-1):0,-1).concat(this.fire),ah.slice(relay?Math.max(0,base-i-1):0),carry,tg,base,hi,i)';
    old.transform=src=>{const s=previous(src);assert.equal(s.split(needle).length,2);return s.replace(needle,code);};
    old.coefficient.dividend=dividend;
}
module.exports={highOne,dividend,install};
