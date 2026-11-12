'use strict';
const path=require('node:path');
const assert=require('node:assert/strict');
function replace(s,a,b){assert.equal(s.split(a).length,2,a);return s.replace(a,()=>b);}
function compactHeightSwap(V,last,hA,hB,e,loan,put){
    if(last%2){
        const p=fieldHeightRange(V,1,last,[],[],e,loan);
        put(p);put(fr(e,hA,hB));put([...p].reverse());
    }else{
        put([[hA,hB]]);put(fieldHeightRange(V,1,last,[hB],[true],hA,loan));put([[hA,hB]]);
    }
}
function compactSignLease(n,L,V,Q,sg,e,loan,cl,put){
    const last=n-4;
    if(last%4)throw Error('four-cycle field width');
    const p=fieldHeightRange(V,1,last,[],[],e,loan),f=D5SignLease(n,L,V,Q,sg,e,loan,1,false,4);
    // A selected low-bit case acts as (x,y) -> (y,x XOR a), of order four.
    // With e incoming, m=0 mod 4 equal classes leave F^(P XOR e) F^(-e).
    put(p);put(f);put([...p].reverse());put([...f].reverse());
    cl(n-3,D5SignLease(n,L,V,Q,sg,e,loan,n-3,false,4));
}
function compactParity12(n,L,Q,k,size,cs,ps,dst,loan){
    // For odd residues mod 8, multiplication XORs the two nonconstant bits.
    const q=Q[k+1],xs=[Q[k+2],...L.slice(k+1,Math.min(k+3,size))],g=xs.map(b=>[b,q]);
    if(cs.includes(q))throw Error('conditional parity aliases its conjugation wire');
    return g.concat(D648C2Mc([...cs,q],[...ps,true],dst,loan),[...g].reverse());
}
function transform(s,six){
    assert(s.includes('function fieldHeightRange('),'apply after buckets.cjs');
    s=replace(s,'for(let c=1;c<=n-5;c++)cl(c,fr(e,low3,port));',
        'compactHeightSwap(V,n-5,low3,port,e,loan,put);');
    s=replace(s,'for(let c=1;c<n;c++)gather(c,c<=n-4?lowHost:L[n-c]);',
        'compactHeightSwap(V,n-4,lowHost,S[0],e,loan,put);for(let c=n-3;c<n;c++)gather(c,L[n-c]);');
    s=replace(s,'for(let c=1;c<n;c++)cl(c,fr(e,S[0],c<=n-4?lowHost:L[n-c]));',
        'compactHeightSwap(V,n-4,S[0],lowHost,e,loan,put);for(let c=n-3;c<n;c++)cl(c,fr(e,S[0],L[n-c]));');
    s=replace(s,'for(let c=1;c<n-2;c++)cl(c,D5SignLease(n,L,V,Q,sg,e,loan,c,false,4));',
        'compactSignLease(n,L,V,Q,sg,e,loan,cl,put);');
    if(!six){
        const a=s.indexOf('function D648C2J12('),b=s.indexOf('function D648C2WindOut(',a);assert(a>=0&&b>a);
        s=s.slice(0,a)+compactParity12.toString().replace('compactParity12','D648C2J12')+'\n'+s.slice(b);
    }
    return s+'\n'+compactHeightSwap.toString()+'\n'+compactSignLease.toString()+'\n';
}
function install(root,width){
    const owner=path.join(root,'construction/research/agents/midpoint-implicit-query-20261109/q651-ten-field'),six=width===647;
    assert(six||width===648);
    const file=require.resolve(path.join(owner,six?'i9-divide-complete-source.cjs':'d648-p-c2w.cjs')),old=require(file);
    if(six)require.cache[file].exports={...old,applySource:s=>transform(old.applySource(s),true)};
    else require.cache[file].exports=s=>transform(old(s),false);
}
module.exports={transform,install};
