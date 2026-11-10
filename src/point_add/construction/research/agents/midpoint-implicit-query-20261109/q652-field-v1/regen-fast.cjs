'use strict';
const path=require('node:path'),fs=require('node:fs'),Module=require('node:module');
const {replace,SectorSigned}=require('../q653-next/parts.cjs');
const file=path.join(__dirname,'regen.cjs');let text=fs.readFileSync(file,'utf8');
function faster(source){
    source=replace(source,'const stages=[[park,park.parking(),false]',
        'const wide=new module.Wide(n);wide.aux=walk.L[n+1];wide.tst=walk.R[n+1];wide.tag[4]=2*(n+2);const stages=[[park,park.parking(),false]');
    source=replace(source,'[walk,walk.plan().concat([shifts]),true]','[wide,wide.plan(),true],[walk,[shifts],true]');
    // Keep the literal adjoint of walk followed by shifts. Reversing the
    // stage reverses their execution order, just as the original plan did.
    source=replace(source,'[wide,wide.plan(),true],[walk,[shifts],true]','[walk,[shifts],true],[wide,wide.plan(),true]');
    return replace(source,'if(q===walk.tag.at(-1)&&g===walk)','if((g===walk||g===wide)&&q===g.tag.at(-1))');
}
text=replace(text,'m.Signed=Signed;m.thinTerminal=thinTerminal;m._compile(source,file);',
    'm.Signed=Signed;m.Wide=module.Wide;m.thinTerminal=thinTerminal;m._compile(module.faster(source),file);');
const m=new Module(file,module);m.filename=file;m.paths=module.paths;m.Wide=SectorSigned;m.faster=faster;
m._compile(text,file);module.exports=m.exports;
