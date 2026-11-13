'use strict';
const assert=require('node:assert/strict');
const path=require('node:path');
function correction(A,r,z){
    const neg=A.slice(1).concat(r);
    for(const w of neg)this.raw(-1,-1,w);
    this.op([A[0],...neg],z);
    for(const w of neg)this.raw(-1,-1,w);
}
function transform(s){
    const a=s.indexOf('  const select=(z,guard=[])=>{'),b=s.indexOf('\n};',a);
    assert(a>=0&&b>a&&s.slice(a,b).includes('large();this.lt'));
    s=s.slice(0,a)+'  const select=(z,guard=[])=>this.lt(guard,A,r,z);\n  const exceptional=z=>('+correction.toString()+').call(this,A,r,z);'+s.slice(b+3);
    const single='if(base===0&&hi===m-1)one(all,()=>select(this.fire));';
    assert.equal(s.split(single).length,2);s=s.replace(single,'if(base===0&&hi===m-1)one(all,()=>{if(m>1){select(this.fire);exceptional(this.fire);}});');
    const two='if(dirtySelector)select(this.fire,[tg[0]]);});';
    assert.equal(s.split(two).length,2);s=s.replace(two,'if(dirtySelector)select(this.fire,[tg[0]]);if(hi===m-1)exceptional(this.fire);});');
    return s;
}
function install(research=path.resolve(__dirname,'../..')){
    const six=require.cache[require.resolve(path.join(research,'q648-next/field/six.cjs'))];
    assert(six?.grayCube,'install the three-predicate successor first');
    const prev=six.hosted;six.hosted=s=>transform(prev(s));
}
module.exports={correction,transform,install};
