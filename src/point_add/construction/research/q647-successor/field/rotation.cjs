'use strict';
const assert=require('node:assert/strict');
const path=require('node:path');

// The six-helper divider installs the older full-word reflection after its
// walker is constructed. Reuse the donor's cyclewise reflection used by
// multiplication. A rotation with gcd(n,s) cycles needs n-gcd(n,s) swaps.
function install(research=path.resolve(__dirname,'../..'),point=process.env.Q647_POINT_ADD||path.join(research,'q647-trim/donor')){
    const owner=path.join(point,'construction/research/agents/midpoint-implicit-query-20261109/q651-ten-field');
    const id=require.resolve(path.join(owner,'i9-divide-walk-small.cjs')),old=require(id);
    const prototype={rot(controls,word,shift){return this.d9oldRot(controls,word,shift);}};
    require(path.join(owner,'i9-history-field-rotate.cjs')).adapt(Object.create(prototype));
    const rotate=prototype.rot;
    require.cache[id].exports={...old,install(w,...args){
        const result=old.install(w,...args);
        if(w.rot===old.rot2){assert.equal(typeof w.d9oldRot,'function');w.rot=rotate;}
        return result;
    }};
}
module.exports={install};
