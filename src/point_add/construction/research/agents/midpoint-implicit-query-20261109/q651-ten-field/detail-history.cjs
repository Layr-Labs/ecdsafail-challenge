'use strict';
const fs=require('fs'),path=require('path'),Module=require('module');
const file=path.join(__dirname,'regen650.cjs');let s=fs.readFileSync(file,'utf8');
const a='return s;};',b="s=change(s,'sink(g.g);',\"sink(g.g,{stage:g===park?'park':g===scale?'scale':g===walk6?'walk1':'walk2',rev});\");return s;};";
if(s.split(a).length!==2)throw Error('detail R anchor');s=s.replace(a,()=>b);
const m=new Module(file,module);m.filename=file;m.paths=Module._nodeModulePaths(__dirname);m._compile(s,file);
exports.emitRegenerateSparse=(sink,...args)=>m.exports.emitRegenerateSparse((g,meta)=>{sink(g);globalThis.__iWindowEnd(meta?meta.stage+(meta.rev?'-':'+'):'exchange/sign');},...args);
