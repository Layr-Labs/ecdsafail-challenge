'use strict';
const path=require('node:path'),Module=require('node:module');
const family=path.resolve(__dirname,'..');
const {checkedSource}=require(path.join(family,'field128-height-experiment/pinned.cjs'));
const source=path.join(family,'q653-next/point.cjs');
let s=checkedSource(source,'d850d912b5144bcd47227ff187d4118977dbe23665922a34eecefbe78ff74115');
function edit(a,b){if(s.split(a).length!==2)throw Error('Changed Q652 point binding '+a);s=s.replace(a,()=>b);}
edit("'this.quantumWidth=653'","'this.quantumWidth=652'");
edit("'if(width!==653)'","'if(width!==652)'");
edit("'Input-independent Q653 gate export'","'Input-independent Q652 gate export'");
edit("m.field=require('./backend.cjs');m.history=require('./regen.cjs');m.upper=require('./upper.cjs').upper;",
     'm.field=module.field;m.history=module.history;m.upper=module.upper;');
const mod=new Module(source,module);mod.filename=source;mod.paths=Module._nodeModulePaths(path.dirname(source));
mod.field=require(path.join(family,'q652-field-v1/backend-fast.cjs'));
mod.history=require(path.join(family,'q652-field-v1/regen-fast.cjs'));
mod.upper=require('./upper.cjs').upper;mod._compile(s,source);module.exports=mod.exports;
if(require.main===module){const [mode,file]=process.argv.slice(2);if(!['raw','spans'].includes(mode)||!file)throw Error('usage: raw|spans FILE');console.log(JSON.stringify(new mod.exports.GateWriter(mode==='raw'?file:null,mode==='spans'?file:undefined).produce(),null,2));}
