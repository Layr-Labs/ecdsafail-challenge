'use strict';
const base=require('../q651-upper-reduction/upper.cjs'),{replace}=require('../q653-next/parts.cjs');
function upper(source){
    const marker='const field=(div)=>bracketMap(tape,m,BigInt(delta),d,y,div,';
    const prefix='../../../../agents/midpoint-implicit-query-20261109/';
    let s=replace(base.upper(source),marker,
        "const closeProducts=require('"+prefix+"q651-product-cache/cache.cjs').install(tape,2*m);"+
        "const closeFusion=require('"+prefix+"q651-parity-fusion/fusion.cjs').install(tape);"+marker);
    const tail='\n stepList(steps,back,fn=>fn(back));\n for(let i=0;i<states.length;i++)';
    return replace(s,tail,tail.replace(';\n',';closeFusion();closeProducts();\n'));
}
module.exports={upper};
