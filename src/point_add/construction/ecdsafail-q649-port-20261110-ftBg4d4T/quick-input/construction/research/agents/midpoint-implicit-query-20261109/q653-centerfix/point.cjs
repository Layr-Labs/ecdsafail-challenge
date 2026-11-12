'use strict';
const path=require('path'),Module=require('module'),{replace}=require('../q653-next/parts.cjs'),{checkedSource}=require('../field128-height-experiment/pinned.cjs');
const file=path.join(__dirname,'../q653-next/point.cjs');let s=checkedSource(file,'d850d912b5144bcd47227ff187d4118977dbe23665922a34eecefbe78ff74115');s=replace(s,"m.upper=require('./upper.cjs').upper;",'m.upper=module.upper;');
const m=new Module(file,module);m.filename=file;m.paths=module.paths;m.upper=require('./upper.cjs').upper;m._compile(s,file);module.exports=m.exports;
if(require.main===module){const [mode,f]=process.argv.slice(2);if(!['raw','spans'].includes(mode)||!f||require('os').endianness()!=='LE')throw Error('use raw FILE or spans FILE');console.log(JSON.stringify(new m.exports.GateWriter(mode==='raw'?f:null,mode==='spans'?f:undefined).produce(),null,2));}
