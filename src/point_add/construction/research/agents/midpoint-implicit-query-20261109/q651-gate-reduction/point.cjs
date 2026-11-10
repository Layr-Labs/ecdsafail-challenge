'use strict';
const path=require('node:path'),Module=require('node:module');
const {checkedSource}=require('../field128-height-experiment/pinned.cjs');
const {replace}=require('../q653-next/parts.cjs');
const base=require.resolve('../q651-ten-field/point.cjs');
let s=checkedSource(base,'7f2020652aa1204f826fcc0502d14b6c6e8d50822b0a01d70019cdaa3c146bba');
s=replace(s,"m.field=require('./multiply.cjs');m.history=require('./regen.cjs');","m.field=module.kernels;m.history=module.kernels;");
const m=new Module(base,module);m.filename=base;m.paths=Module._nodeModulePaths(path.dirname(base));
m.kernels=require('./kernels.cjs');m._compile(s,base);module.exports=m.exports;
if(require.main===module){
    const [mode,file]=process.argv.slice(2);
    if(!['raw','spans'].includes(mode)||!file)throw Error('use raw FILE or spans FILE');
    console.log(JSON.stringify(new m.exports.GateWriter(mode==='raw'?file:null,mode==='spans'?file:undefined).produce(),null,2));
}
