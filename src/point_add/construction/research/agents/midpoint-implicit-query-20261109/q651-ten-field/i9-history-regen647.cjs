'use strict';
// R48/R8. Copy the six files in FILES.txt next to original n651a regen.cjs.
const fs=require('fs'),path=require('path'),Module=require('module');
const root=process.env.R9_Q651_ROOT||(fs.existsSync(path.join(__dirname,'regen.cjs'))?__dirname:path.resolve(__dirname,'../../../r38/R/base/research/agents/midpoint-implicit-query-20261109/q651-ten-field'));
const file=path.join(root,'regen.cjs'),patches=require('./i9-history-p-r647.cjs');
const edit=(s,a,b)=>{if(s.split(a).length!==2)throw Error('R42 history anchor '+a.slice(0,100));return s.replace(a,()=>b);};
let s=fs.readFileSync(file,'utf8');s=edit(s,'m.adjust=adjust;','m.adjust=s=>module.applyR42(adjust(s));');
const m=new Module(file,module);m.filename=file;m.paths=Module._nodeModulePaths(root);
m.applyR42=s=>{for(const [a,b]of patches)s=edit(s,a,b);return s;};m._compile(s,file);
module.exports={emitRegenerateSparseRaw:m.exports.emitRegenerateSparse,emitRegenerateSparse(sink,erase=false){
 let batch=[];const flush=()=>{if(batch.length){sink(batch);batch=[];}};
 const p=require('./i9-history-r-selected-sink.cjs').create((a,b,t)=>{batch.push((a<<20)|(b<<10)|t);if(batch.length===65536)flush();},{mode:'commute',window:4096});
 m.exports.emitRegenerateSparse(gs=>{for(const x of gs)p.gate(x>>>20&1023,x>>>10&1023,x&1023);},erase);p.flush();flush();
}};
