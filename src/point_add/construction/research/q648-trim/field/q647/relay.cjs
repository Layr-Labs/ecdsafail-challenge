'use strict';

const assert=require('node:assert/strict');
const path=require('node:path');
const {adapt}=require('../graded-relay.cjs');

// After inverse compact normalization and the first shifted lift the six
// count sites are zero. The M8 planner assigns 640 to the second-highest
// normalization tag. This comparison instead assigns it to the low tag.
function install(owner) {
    const baseId=require.resolve(path.join(owner,'i9-multiply-m9-base.cjs'));
    assert(!require.cache[baseId],'Install the Q647 walk before the M9 base');
    const relayId=require.resolve(path.join(owner,'i9-multiply-multi-relay.cjs'));
    const relay=require(relayId);
    require.cache[relayId].exports={...relay,install(w,digit){return adapt(w,digit,1);}};
    const b=require(baseId),old='m[W.tag.at(-2)]=640;';
    assert.equal(b.f.split(old).length,2,'M8 physical tag');
    require.cache[baseId].exports={...b,f:b.f.replace(old,'m[W.tag[0]]=640;')};
}

module.exports={install};
