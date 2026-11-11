'use strict';

const assert=require('node:assert/strict');
const path=require('node:path');

// The predecessor on canonical C uses a conditional reflection. Factor its
// predicate [L<p] [C<T-1] with an arbitrary old hr. Both comparison visits
// change only h and restore every borrowed wire, including the high predicate.
function rewrite(s) {
    const old=`const gq=h=>{const out=[];ap(out,gtT(h,[]),eqT(h,[]));
   for(const [cs,bs] of cubes){const neg=cs.filter((_,i)=>!bs[i]).map(q=>[q]);ap(out,neg,gtT(h,cs),eqT(h,cs),neg);}
   return out;};`;
    const next=`const gq=h=>{
      const f=fX(hr),test=gtT(h,[hr]).concat(eqT(h,[hr]));
      return f.concat(test,[...f].reverse(),test);
    };`;
    assert.equal(s.split(old).length,2,'Q648 canonical decrement anchor');
    return s.replace(old,()=>next);
}

function install(owner) {
    const id=require.resolve(path.join(owner,'q648/p648-colour1.cjs')),old=require(id);
    require.cache[id].exports={...old,f:s=>rewrite(old.f(s))};
}

module.exports={install,rewrite};
