'use strict';
const assert=require('node:assert/strict');
const path=require('node:path');
const base=require('./mask.cjs');
const cache=new Map();
function threshold(width,limit) {
    const key=width+','+limit;
    if(cache.has(key))return cache.get(key);
    const standard=base.threshold(width,limit);
    if(limit<0||limit+1>=width)return standard;
    let lo=0;while(limit>>lo&1)++lo;
    const len=standard.bits-lo+2,cost=4*(len-2);
    const best=cost<standard.cost?{cost,bits:standard.bits,lo,limit,chain:true}:standard;
    cache.set(key,best);return best;
}
// If k_j=0, the higher comparison bit updates F to t_j OR F, or
// t_j XOR ((NOT t_j) AND F). For k_j=1 it updates F to t_j AND F.
// The two sweeps differ by all affine additions; the linear part is identical
// and cancels every incoming dirty value. Both sweeps restore the loan bank.
function toggle(w,tag,spec,fixed,z){
    if(!spec.chain)return base.toggle(w,tag,spec,fixed,z);
    assert(fixed.length===2);
    const cs=tag.slice(spec.lo,spec.bits).concat(fixed),n=cs.length;
    assert(w.y.length>=n-2);
    const t=(a,b,d)=>w.raw(a,b,d),cx=(a,d)=>w.raw(a,-1,d),x=a=>w.raw(-1,-1,a);
    const isOr=i=>i>0&&i<n-2&&!(spec.limit>>(spec.lo+i)&1);
    function layer(i,affine){
        const a=cs[i],b=i===1?cs[0]:w.y[i-2],d=i===n-1?z:w.y[i-1];
        const or=isOr(i);
        if(affine&&or)cx(a,d);
        if(or)x(a);t(a,b,d);if(or)x(a);
    }
    for(const affine of [true,false]){
        for(let i=affine?1:2;i<n;i++)layer(i,affine);
        for(let i=n-2;i>=(affine?1:2);i--)layer(i,affine);
    }
}
function install(){
    const id=require.resolve(path.resolve(__dirname,'../../q648-next/field/tail.cjs'));
    const carrier=require.cache[id]?.fieldMask;
    assert(carrier,'install the coefficient mask first');
    const old=carrier.coefficient;
    carrier.coefficient=function(w,A,B,h,tag,lo,hi,i){
        const s=threshold(hi-lo+1,i-lo);
        if(!s.chain)return old(w,A,B,h,tag,lo,hi,i);
        if(2*s.cost>=A.length+2){w.restore([w.tst],A,B,0,h);return;}
        base.digit(w,A,B,h,w.tst,()=>{w.raw(-1,-1,h);toggle(w,tag,s,[w.fire,h],w.tst);w.raw(-1,-1,h);});
    };
    if(old.dividend){
        carrier.coefficient.dividend=(...args)=>require('./dividend.cjs').dividend(...args,{threshold,toggle});
    }
}
module.exports={threshold,toggle,install};
