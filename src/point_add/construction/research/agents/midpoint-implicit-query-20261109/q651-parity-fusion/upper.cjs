'use strict';
const base=require('../q651-upper-reduction/upper.cjs'),{replace}=require('../q653-next/parts.cjs');
function upper(source){
    const marker='const field=(div)=>bracketMap(tape,m,BigInt(delta),d,y,div,';
    let s=replace(base.upper(source),marker,
        "const flushCompiler=require('../../../../agents/midpoint-implicit-query-20261109/q651-parity-fusion/fusion.cjs').install(tape);"+marker);
    const tail='\n stepList(steps,back,fn=>fn(back));\n for(let i=0;i<states.length;i++)';
    return replace(s,tail,tail.replace(';\n',';flushCompiler();\n'));
}
module.exports={upper};
