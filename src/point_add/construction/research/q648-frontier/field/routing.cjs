'use strict';
const assert=require('node:assert/strict');
const path=require('node:path');

// Cache the long common zero-prefix test once per block in a dirty bit.
// At most one local leading-bit predicate is true inside a block. Toggling
// one Fredkin in the arbitrary incoming e-controlled baseline changes that
// permutation by a conjugate of a single swap. The change is an involution.
function heightSwapPlan(n,start,last){
    const cost=k=>k<2?0:k===2?1:4*(k-2),best=Array(last+2).fill(0),plans=[];
    for(let lo=last;lo>=start;lo--){
        const m=n-lo+1,direct=1+cost(m+1),native=1+2*cost(m);
        best[lo]=Math.min(direct,native)+best[lo+1];
        plans[lo]={hi:lo,kind:direct<native?'direct':'native'};
        for(let hi=lo+1;hi<=last;hi++){
            const k=hi-lo+1,candidate=2*cost(n-hi)+5*k-4+4*k*(k+1)+best[hi+1];
            if(candidate<best[lo]){best[lo]=candidate;plans[lo]={hi,kind:'block'};}
        }
    }
    const result=[];for(let i=start;i<=last;){result.push({lo:i,...plans[i]});i=plans[i].hi+1;}
    return {ranges:result,ccx:best[start]};
}
function groupedHeightSwaps(V,start,last,pair,e,loan,put){
    const cache=loan.at(-1),pool=loan.slice(0,-1);
    for(const {lo,hi,kind} of heightSwapPlan(V.length,start,last).ranges){
        if(kind!=='block'){
            const [a,b]=pair(lo),word=V.slice(lo-1),ps=word.map((_,j)=>j===0);
            if(kind==='direct'){
                put(fr(e,a,b));put([[a,b]]);put(D14Raw([...word,b],[...ps,true],a,loan));put([[a,b]]);
            }else{
                const p=D14Raw(word,ps,e,loan);put(p);put(fr(e,a,b));put([...p].reverse());
            }
            continue;
        }
        const top=V.slice(hi),pred=D14Raw(top,top.map(()=>false),cache,pool);
        const original=[],on=[];
        for(let c=lo;c<=hi;c++){
            const [a,b]=pair(c),slice=V.slice(c-1,hi);
            original.push(fr(e,a,b));
            const cond=[cache,...slice,b],ps=[true,...slice.map((_,i)=>i===0),true];
            on.push([[a,b],...D14Raw(cond,ps,a,pool),[a,b]]);
        }
        const correction=()=>{
            for(let j=0;j<original.length;j++){if(j+1<original.length)put(original[j]);put(on[j]);}
            for(let j=original.length-2;j>=0;j--)put(original[j]);
        };
        correction();put(pred);correction();put([...pred].reverse());
        for(const g of original)put(g);
    }
}
function replace(s,from,to){assert.equal(s.split(from).length,2,from);return s.replace(from,()=>to);}
function transform(s){
    assert(s.includes('function fieldHeightRange('),'apply after buckets.cjs');
    s=replace(s,'for(let c=1;c<=n-4;c++)cl(c,fr(e,L[n-c],lowHost));',
        'groupedHeightSwaps(V,1,n-4,c=>[L[n-c],lowHost],e,loan,put);');
    s=replace(s,'for(let c=1;c<=n-4;c++)cl(c,fr(e,lowHost,L[n-c]));',
        'groupedHeightSwaps(V,1,n-4,c=>[lowHost,L[n-c]],e,loan,put);');
    s=replace(s,'for(let c=1;c<n-1;c++){const sel=flagHeight(vt,c,R[1],loan);put(sel);put(fr(R[1],Q[n-2],L[n+1-c]));put(rev(sel));}',
        'groupedHeightSwaps(vt,1,n-2,c=>[Q[n-2],L[n+1-c]],R[1],loan,put);');
    s=replace(s,'for(let c=1;c<=n;c++){const sel=flagHeight(vt,c,R[1],loan),host=c<n?L[n+1-c]:L[2];put(sel);put(fr(R[1],T6[0],host));put(rev(sel));}',
        'groupedHeightSwaps(vt,1,n,c=>[T6[0],c<n?L[n+1-c]:L[2]],R[1],loan,put);');
    s=replace(s,'for(let c=1;c<n;c++)cl(c,fr(R[1],T6[0],L[n+2-c]));',
        'groupedHeightSwaps(vt,1,n-1,c=>[T6[0],L[n+2-c]],R[1],loan,put);');
    return s+'\n'+heightSwapPlan.toString()+'\n'+groupedHeightSwaps.toString()+'\n';
}
function install(root,width){
    const owner=path.join(root,'construction/research/agents/midpoint-implicit-query-20261109/q651-ten-field'),six=width===647;
    assert(six||width===648);
    const file=require.resolve(path.join(owner,six?'i9-divide-complete-source.cjs':'d648-p-c2w.cjs')),old=require(file);
    if(six)require.cache[file].exports={...old,applySource:s=>transform(old.applySource(s))};
    else require.cache[file].exports=s=>transform(old(s));
}
module.exports={heightSwapPlan,transform,install};
