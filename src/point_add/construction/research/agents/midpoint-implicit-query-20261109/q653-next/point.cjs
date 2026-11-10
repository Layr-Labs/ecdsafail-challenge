'use strict';
const path=require('path'),Module=require('module');
const {checkedSource}=require('../field128-height-experiment/pinned.cjs');
const {replace}=require('./parts.cjs'),base=path.join(__dirname,'../q654-next/point.cjs');
let s=checkedSource(base,'122bfb04d1cce20c9e4a8f018921abdf0138d6ee8c4d941ccc915d76e7df1e44');
s=replace(s,'this.quantumWidth=654','this.quantumWidth=653');s=replace(s,'if(width!==654)','if(width!==653)');s=replace(s,'Input-independent Q654 gate export','Input-independent Q653 gate export');
s=replace(s,"m.newField=require('./backend.cjs');m.newHistory=require('./regen.cjs');m.newUpper=require('./upper.cjs').upper;",'m.newField=module.field;m.newHistory=module.history;m.newUpper=module.upper;');
const m=new Module(base,module);m.filename=base;m.paths=module.paths;m.field=require('./backend.cjs');m.history=require('./regen.cjs');m.upper=require('./upper.cjs').upper;
m._compile(s,base);module.exports=m.exports;
if(require.main===module){const [mode,f]=process.argv.slice(2);if(!['raw','spans'].includes(mode)||!f||require('os').endianness()!=='LE')throw Error('use raw FILE or spans FILE');console.log(JSON.stringify(new m.exports.GateWriter(mode==='raw'?f:null,mode==='spans'?f:undefined).produce(),null,2));}
