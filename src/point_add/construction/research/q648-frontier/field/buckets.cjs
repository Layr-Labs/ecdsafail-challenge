'use strict';
const assert=require('node:assert/strict');
const path=require('node:path');
const {tables}=require('../../q648-next/field/winding.cjs');

// Toggle z when the positive bit length of V lies in the closed interval and
// the remaining controls match. Two nested zero predicates give the interval.
function fieldHeightRange(V, lo, hi, cs, ps, z, loan) {
    if (lo === hi) {
        const word=V.slice(lo-1);
        return D14Raw([...word,...cs],[...word.map((_,i)=>i===0),...ps],z,loan);
    }
    const zeros = word => D14Raw([...word,...cs],[...word.map(()=>false),...ps],z,loan);
    return zeros(V.slice(hi)).concat(zeros(V.slice(lo-1)));
}
function startRange(n,L,V,Q,U,e,loan,put) {
    // Every absent height used four identical dirty-controlled swaps. Their
    // product is the identity even when the incoming bit e is one.
    for(let k=0;k<4;k++) {
        const cs=[...V.slice(0,4),...L.slice(0,k+1)];
        const ps=[false,false,false,false,...Array(k).fill(false),true];
        const toggle=(extra,z)=>fieldHeightRange(V,5,n-5,[...cs,...extra],[...ps,...extra.map(()=>true)],z,loan);
        for(const bit of [Q[3],Q[2],U[1]]) put(toggle([bit],U[3]));
        const p=toggle([],e);put(p);put(fr(e,Q[n-4],U[3]));put([...p].reverse());
    }
}
function parkRange(n,L,R,Q,loan,port,record,sink) {
    const V=Array.from({length:n},(_,j)=>R[n+1-j]),U=Array.from({length:n},(_,j)=>L[n+1-j]);
    const put=g=>sink('nct',g),low=L.slice(0,4);
    // The same Fredkin occurs at every permitted height. An even number of
    // copies of the old selector cancels in the seven-helper implementation.
    if(n%2) throw Error('even field width expected');
    put([[Q[3],port]]);
    put(fieldHeightRange(V,1,n-4,[...low,port],[false,false,false,false,true],Q[3],loan));
    put([[Q[3],port]]);
    const qmap = TERMS;
    function group(k,lo,hi,gBits) {
        const known=lo===n?[]:L.slice(0,k+1);
        const cs=V.slice(0,4).concat(known),ps=cs.map((_,j)=>known.length>0&&j===cs.length-1);
        const P=(extra,z,pool=loan)=>fieldHeightRange(V,lo,hi,[...cs,...extra],[...ps,...extra.map(()=>true)],z,pool);
        put(P([U[3]],port));put(P([port],U[3]));
        const word=L.slice(k+1,k+1+gBits).concat(Q.slice(k+1,k+4));
        const avoid=new Set([...V,...cs,...word,U[1],U[3],port]);
        const d=loan.find(q=>!avoid.has(q));if(d===undefined)throw Error('height group dirty bit');
        const pool=loan.filter(q=>q!==d);
        const xor=()=>{
            put([[d,U[1],U[3]]]);
            for(const monomial of qmap[gBits]){
                const controls=[d,...word.filter((_,j)=>(monomial>>j)&1)];
                put(D14Raw(controls,controls.map(()=>true),U[3],pool));
            }
        };
        const pred=P([],d,pool);xor();put(pred);xor();put([...pred].reverse());
    }
    for(let k=0;k<4;k++) {
        const last=n-3-k;
        if(last>=5)group(k,5,last,3);
        for(let c=Math.max(last+1,5);c<=n-k;c++)group(k,c,c,Math.min(3,n-c-k));
    }
    put([[port,Q[3]]]);sink('hmr',[port,record]);
}
function replace(source,from,to) {
    assert.equal(source.split(from).length,2,from.slice(0,80));return source.replace(from,()=>to);
}
function region(s,from,until,code) {
    const a=s.indexOf(from),b=s.indexOf(until,a+from.length);
    assert(a>=0&&b>a,from);return s.slice(0,a)+code+s.slice(b);
}
function transform(s,six) {
    assert(s.includes('const pool=loan.filter(q=>q!==bit),terms='),'apply after winding.cjs');
    const start=s.indexOf('function D14BeforeWinding(');
    assert(start>=0);
    s=s.slice(0,start)+region(s.slice(start),' for(let c=5;c<=n-5;c++)for(let k=0;k<4;k++){',' // The only high class',
        ' startRange(n,L,V,Q,U,e,loan,put);\n');
    const p=s.indexOf('function D14ParkCount('),end=s.indexOf('\n}',p);assert(p>=0&&end>p);
    const park=replace(parkRange.toString(),'function parkRange(','function D14ParkCount(');
    s=s.slice(0,p)+replace(park,'TERMS',JSON.stringify(tables))+s.slice(end+2);
    if(!six){
        s=replace(s,'put(c3oracle);put(q);put(rev(c3oracle));','put(q);');
        s=replace(s,'put(c3oracle);put(rev(q));put(rev(c3oracle));','put(rev(q));');
    }else{
        const p=s.indexOf('function D17ParkCount(');assert(p>=0);
        s=s.slice(0,p)+region(s.slice(p),' for(let c=1;c<=n-4;c++){',' put([[port,Q[2]]]);',
            ` put([[Q[2],port]]);\n put(D17Raw([...V.slice(n-4),V[0],...L.slice(0,4),port],\n        [false,false,false,false,true,false,false,false,false,true],Q[2],loan));\n put([[Q[2],port]]);\n`);
        const from='  for(let c=1;c<=n;c++){const hc=V.slice(c-1),cs=[...hc,...eight],ps=[...hc.map((_,j)=>j===0),...ep],size=n+1-c;\n   for(const w of[Q[2],Q[1],U[1],...(size>1?[L[1]]:[]),...(size>2?[L[2]]:[])])put(raw([...cs,w],[...ps,true],U[2]));\n  }';
        const to=`  for(const [w,last] of [[Q[2],n],[Q[1],n],[U[1],n],[L[1],n-1],[L[2],n-2]])
      put(fieldHeightRange(V,1,last,[...eight,w],[...ep,true],U[2],loan));`;
        s=replace(s,from,to);
    }
    return s+'\n'+fieldHeightRange.toString()+'\n'+startRange.toString()+'\n';
}
function install(root,width) {
    const family='construction/research/agents/midpoint-implicit-query-20261109/q651-ten-field';
    const owner=path.join(root,family),six=width===647;
    assert(six||width===648);
    const file=require.resolve(path.join(owner,six?'i9-divide-complete-source.cjs':'d648-p-c2w.cjs'));
    const original=require(file);
    if (six) require.cache[file].exports={...original,applySource(s){return transform(original.applySource(s),true);}};
    else require.cache[file].exports=s=>transform(original(s),false);
}
module.exports={transform,install};
