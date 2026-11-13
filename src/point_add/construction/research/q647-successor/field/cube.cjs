'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const Module = require('node:module');
const path = require('node:path');

// P and Q are XORed into arbitrary borrowed bits. Walking the four corners
// of that square cancels their incoming values in the controlled R oracle.
function grayCube(A,r,u,v) {
    const m=A.length, t=u.length, top=r[m-1], saved=this.y;
    const a=saved.at(-1), b=saved.at(-2);
    this.y=saved.slice(0,-2);
    const mc=k=>k<2?0:k===2?1:4*(k-2);
    const comparison=(length,k)=>length===1?mc(k+2):2*(length-1)+mc(k+1)+mc(k+2);
    const F=(guards,z)=>this.lt(guards,A,r,z);
    const G=(guards,z)=>{
        this.op([...guards,top],z);
        this.raw(-1,-1,top);
        this.lt([...guards,top],r.slice(0,-1),A.slice(1),z);
        this.raw(-1,-1,top);
    };
    const H=(guards,z)=>{
        this.op(guards,z);
        for(const bit of u)this.raw(-1,-1,bit);
        this.lt(guards,v,u,z);
        for(const bit of u)this.raw(-1,-1,bit);
    };
    // Under strict A>r, the case A=1 requires r=0 and makes G false.
    // Therefore testing A>1 inside F is redundant in this three-way product.
    const ops=[F,G,H];
    const cost=[k=>comparison(m,k),k=>mc(k+1)+comparison(m-1,k+1),k=>mc(k)+comparison(t,k)];
    const directId=[0,1,2].reduce((best,i)=>4*cost[i](2)-2*cost[i](0)<4*cost[best](2)-2*cost[best](0)?i:best,0);
    const direct=ops[directId], [first,second]=ops.filter((_,i)=>i!==directId);
    try{
        direct([a,b],this.fire);
        first([],a);direct([a,b],this.fire);
        second([],b);direct([a,b],this.fire);
        first([],a);direct([a,b],this.fire);
        second([],b);
    }finally{this.y=saved;}
}
function replace(s,from,to){assert.equal(s.split(from).length,2,from);return s.replace(from,()=>to);}
function hosted(src){
    const a=src.indexOf(' const old=this.y,ds=old.slice(-3);'),b=src.indexOf('\n});',a);
    assert(a>=0&&b>a&&src.slice(a,b).includes('this.y=old;'),'six-helper cube block');
    return src.slice(0,a)+' module.grayCube.call(this,A,r,u,v);'+src.slice(b);
}
function install(research=path.resolve(__dirname,'../..')){
    const id=require.resolve(path.join(research,'q648-next/field/six.cjs'));
    assert(!require.cache[id],'install the successor before the six-helper field');
    const body=replace(fs.readFileSync(id,'utf8'),'built._compile(s,innerId);',
        'built.grayCube=module.grayCube;built._compile(module.hosted(s),innerId);');
    const fresh=new Module(id,module);fresh.filename=id;fresh.paths=Module._nodeModulePaths(path.dirname(id));
    fresh.hosted=hosted;fresh.grayCube=grayCube;
    fresh._compile(body,id);fresh.loaded=true;require.cache[id]=fresh;
}
module.exports={grayCube,hosted,install};
