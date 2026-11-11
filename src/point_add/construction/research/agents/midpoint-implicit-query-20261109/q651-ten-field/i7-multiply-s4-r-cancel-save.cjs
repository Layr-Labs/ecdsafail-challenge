
'use strict';
const fs=require('fs'),path=require('path'),Module=require('module'),root=process.env.S3_Q651_ROOT||__dirname;
const file=path.join(root,'regen.cjs');let s=fs.readFileSync(file,'utf8');
const anchor='m.adjust=adjust;';if(s.split(anchor).length!==2)throw Error('S3 regen anchor');s=s.replace(anchor,'m.adjust=s=>module.applyS3(adjust(s));');
const m=new Module(file,module);m.filename=file;m.paths=Module._nodeModulePaths(root);m.applyS3=require('./i7-multiply-s4-r-cancel-patch.cjs');m._compile(s,file);
module.exports={emitRegenerateSparseRaw:m.exports.emitRegenerateSparse,emitRegenerateSparse(sink,erase=false){
 let batch=[];const flush=()=>{if(batch.length){sink(batch);batch=[];}};
 const p=require('./i7-multiply-s4-sink.cjs').createPeep((a,b,t)=>{batch.push((a<<20)|(b<<10)|t);if(batch.length===65536)flush();},{window:4096,mode:'commute'});
 m.exports.emitRegenerateSparse(gs=>{for(const x of gs)p.gate(x>>>20&1023,x>>>10&1023,x&1023);},erase);p.flush();flush();
}};
