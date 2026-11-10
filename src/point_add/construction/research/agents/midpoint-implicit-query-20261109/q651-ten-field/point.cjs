'use strict';
const path=require('node:path'),Module=require('node:module');
const {checkedSource}=require('../field128-height-experiment/pinned.cjs');
const {replace}=require('../q653-next/parts.cjs');
const base=path.join(__dirname,'../q653-next/point.cjs');
let s=checkedSource(base,'d850d912b5144bcd47227ff187d4118977dbe23665922a34eecefbe78ff74115');
s=replace(s,"'this.quantumWidth=653'","'this.quantumWidth=651'");
s=replace(s,"'if(width!==653)'","'if(width!==651)'");
s=replace(s,"'Input-independent Q653 gate export'","'Input-independent Q651 gate export'");
s=replace(s,"m.field=require('./backend.cjs');m.history=require('./regen.cjs');m.upper=require('./upper.cjs').upper;",
    'm.field=module.field;m.history=module.history;m.upper=module.upper;');
const m=new Module(base,module);m.filename=base;m.paths=Module._nodeModulePaths(path.dirname(base));
m.field=require('./multiply.cjs');m.history=require('./regen.cjs');m.upper=require('./upper.cjs').upper;
m._compile(s,base);module.exports=m.exports;
if(require.main===module){
    const [mode,file]=process.argv.slice(2);
    if(!['raw','spans'].includes(mode)||!file)throw Error('Use raw FILE or spans FILE');
    console.log(JSON.stringify(new m.exports.GateWriter(mode==='raw'?file:null,mode==='spans'?file:undefined).produce(),null,2));
}
