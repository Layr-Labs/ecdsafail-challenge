'use strict';
const path=require('path'),Module=require('module');
const {checkedSource}=require('../field128-height-experiment/pinned.cjs');
const base=path.join(__dirname,'../q655-next/point.cjs');
let src=checkedSource(base,'c442dadb61a292fbcfe06d3f98c7c7c56c4c78da752537188678f869084b0e1e');
function one(from,to){if(src.split(from).length!==2)throw Error('coordinate binding '+from);src=src.replace(from,to);}
one("require('./backend.cjs')",'module.newField');one("require('./regen.cjs')",'module.newHistory');
one('const api={upper:installUpper,','const api={upper:module.newUpper,');
one("'this.quantumWidth=655'","'this.quantumWidth=654'");
one('if(width!==655)throw Error','if(width!==654)throw Error');
one('Input-independent Q655 gate export','Input-independent Q654 gate export');
const m=new Module(base,module);m.filename=base;m.paths=module.paths;
m.newField=require('./backend.cjs');m.newHistory=require('./regen.cjs');m.newUpper=require('./upper.cjs').upper;
m._compile(src,base);module.exports=m.exports;
if(require.main===module){
  const [mode,file]=process.argv.slice(2);
  if(!['raw','spans'].includes(mode)||!file||require('os').endianness()!=='LE')throw Error('use raw FILE or spans FILE');
  console.log(JSON.stringify(new m.exports.GateWriter(mode==='raw'?file:null,mode==='spans'?file:undefined).produce(),null,2));
}
