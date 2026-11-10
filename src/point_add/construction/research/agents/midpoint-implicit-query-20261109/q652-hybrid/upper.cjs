'use strict';
const fs=require('node:fs'),path=require('node:path'),Module=require('node:module'),{createHash}=require('node:crypto');
const manifest=require('./UPPER-SOURCES.json'),root=path.resolve(__dirname,'../q652');
const source=new Map();
for(const [name,receipt] of Object.entries(manifest.files)){
    const f=path.join(root,name),s=fs.readFileSync(f);
    if(createHash('sha256').update(s).digest('hex')!==receipt.sha256)throw Error('Public upper source differs at '+name);
    source.set(f,s.toString('utf8'));
}
// Bind the public stage to its Q652 settings; field stages use our grouped kernels.
const settings=Object.freeze({R35_WIDTH:'652',G129_MODE:'same-width',G129_TOP:'pc'});
function stage(name,links,anchor){
    const f=path.join(root,name),mod=new Module(f,module);
    mod.filename=f;mod.paths=Module._nodeModulePaths(path.dirname(f));mod.settings=settings;
    Object.assign(mod,links);
    let s=source.get(f);
    if(anchor){
        if(s.split(anchor[0]).length!==2)throw Error('Changed public Q652 binding '+name);
        s=s.replace(anchor[0],()=>anchor[1]);
    }
    mod._compile("'use strict';const process={env:module.settings};\n"+s,f);
    return mod.exports;
}
const balance=stage('g129.cjs',{},null);
const ladder=stage('upper/upper.cjs',{balance:balance.upper},["const g129=require('../g129.cjs').upper;","const g129=module.balance;"]);
const opt="const base=process.env.R35_UBASE?require(path.resolve(process.env.R35_UBASE)).upper:require('./g129.cjs').upper;";
module.exports=stage('upper652.cjs',{ladder:ladder.upper},[opt,"const base=module.ladder;"]);
