'use strict';
// Copy next to n651a q651-ten-field/regen.cjs together with p-r650.js.
// In point.cjs bind m.history=require('./regen650.cjs'). The original stays intact.
const fs=require('node:fs'),path=require('node:path'),Module=require('node:module');
const root=fs.existsSync(path.join(__dirname,'regen.cjs'))?__dirname:
 path.join(__dirname,'base/research/agents/midpoint-implicit-query-20261109/q651-ten-field');
const file=path.join(root,'regen.cjs');
const change=(s,a,b)=>{if(s.split(a).length!==2)throw Error('R38 history anchor '+a.slice(0,100));return s.replace(a,()=>b);};
let s=fs.readFileSync(file,'utf8');
const patches=require('./p-r650.js');
s=change(s,'m.adjust=adjust;','m.adjust=s=>module.applyR38(adjust(s));');
const m=new Module(file,module);m.filename=file;m.paths=Module._nodeModulePaths(root);
m.applyR38=s=>{for(const [a,b]of patches)s=change(s,a,b);return s;};
m._compile(s,file);
module.exports={emitRegenerateSparse:m.exports.emitRegenerateSparse};
