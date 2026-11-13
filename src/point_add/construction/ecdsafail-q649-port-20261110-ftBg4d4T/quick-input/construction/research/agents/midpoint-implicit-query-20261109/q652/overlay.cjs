'use strict';
// r35 overlay loader (ours). Compiles a source file from nasqret's 653 export in place (same filename, so its
// relative requires resolve) after applying [from,to] patches. Nothing upstream is written.
const path=require('path'),fs=require('fs'),Module=require('module');
const A=process.env.N653ROOT||path.join(__dirname,'..');
function patched(rel,patches,inject){
  const file=path.join(A,rel);let src=fs.readFileSync(file,'utf8').replace(/\r\n/g,'\n');
  for(const [a,b] of patches||[]){if(src.split(a).length!==2)throw Error('patch anchor not unique in '+rel+': '+a.slice(0,70));src=src.replace(a,()=>b);}
  const m=new Module(file,module);m.filename=file;m.paths=Module._nodeModulePaths(path.dirname(file));Object.assign(m,inject||{});m._compile(src,file);return m.exports;
}
const load=f=>f?require(path.resolve(f)):[];
module.exports={A,patched,load};
