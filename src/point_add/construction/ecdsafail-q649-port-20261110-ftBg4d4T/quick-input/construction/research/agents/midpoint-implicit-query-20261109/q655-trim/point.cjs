'use strict';
const path=require('path'),Module=require('module');
const {checkedSource}=require('../field128-height-experiment/pinned.cjs');
const file=path.join(__dirname,'../q655-next/point.cjs');
let src=checkedSource(file,'c442dadb61a292fbcfe06d3f98c7c7c56c4c78da752537188678f869084b0e1e');
const a="require('./backend.cjs')";if(src.split(a).length!==2)throw Error('wrong backend bind');src=src.replace(a,'module.trim');
const m=new Module(file,module);m.filename=file;m.paths=module.paths;m.trim=require('./backend.cjs');m._compile(src,file);
module.exports=m.exports;
if(require.main===module){const [mode,file]=process.argv.slice(2);if(!['raw','spans'].includes(mode)||!file||require('os').endianness()!=='LE')throw Error('use raw FILE or spans FILE');console.log(JSON.stringify(new m.exports.GateWriter(mode==='raw'?file:null,mode==='spans'?file:undefined).produce(),null,2));}
