'use strict';
const assert=require('node:assert/strict');
const path=require('node:path');
function install(research=path.resolve(__dirname,'../..')){
    const six=require.cache[require.resolve(path.join(research,'q648-next/field/six.cjs'))];
    assert(six?.grayCube,'install the successor comparisons first');
    const prior=six.hosted, rotations=require(path.join(research,'q648-frontier/six/field.cjs')).hosted;
    six.hosted=source=>prior(rotations(source));
}
module.exports={install};
