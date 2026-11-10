'use strict';
const path=require('node:path'),Module=require('node:module');
const {checkedSource}=require('../field128-height-experiment/pinned.cjs'),{replace}=require('../q653-next/parts.cjs');
const base=require.resolve('../q651-ten-field/point.cjs');
const src=replace(checkedSource(base,'7f2020652aa1204f826fcc0502d14b6c6e8d50822b0a01d70019cdaa3c146bba'),
    "m.field=require('./multiply.cjs');m.history=require('./regen.cjs');m.upper=require('./upper.cjs').upper;",
    'm.field=module.field;m.history=module.field;m.upper=module.upper;');
const m=new Module(base,module);m.filename=base;m.paths=Module._nodeModulePaths(path.dirname(base));
m.field=require('../q651-gate-reduction/kernels.cjs');m.upper=require('./upper.cjs').upper;
m._compile(src,base);module.exports=m.exports;
if(require.main===module){
    const [mode,file]=process.argv.slice(2);
    if(!['raw','spans'].includes(mode)||!file)throw Error('use raw FILE or spans FILE');
    console.log(JSON.stringify(new m.exports.GateWriter(mode==='raw'?file:null,mode==='spans'?file:undefined).produce(),null,2));
}
