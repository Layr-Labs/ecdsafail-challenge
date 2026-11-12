'use strict';
const fs=require('node:fs'),path=require('node:path'),Module=require('node:module'),{createHash}=require('node:crypto');
const publicRoot=path.join(__dirname,'upstream'),manifest=require('./public-source.json');
for(const [name,receipt] of Object.entries(manifest.files)){
    if(createHash('sha256').update(fs.readFileSync(path.join(publicRoot,name))).digest('hex')!==receipt.sha256)
        throw Error('Public Q651 file changed: '+name);
}
const base=path.join(__dirname,'../q653-next/backend.cjs');
let source=fs.readFileSync(base,'utf8');
if(createHash('sha256').update(source).digest('hex')!=='7672c89cb5628dc9aa613ad3844bca1d5bd78da23a8dec1c075b9e0f6f69c695')
    throw Error('Unexpected Q653 field dependency');
function edit(s,a,b){if(s.split(a).length!==2)throw Error('Unexpected Q651 anchor '+a.slice(0,80));return s.replace(a,()=>b);}
for(const [a,b] of require(path.join(publicRoot,'p-field651.js')))source=edit(source,a,b);
source=edit(source,"require('../q651/div10-rewrite.cjs')(d)","module.thin(d)");
function bind(digit){
    const m=new Module(base,module);m.filename=base;m.paths=Module._nodeModulePaths(path.dirname(base));
    m.thin=require(path.join(publicRoot,'div10-rewrite.cjs'));m.digit=digit;
    const src=digit?edit(edit(source,'replace,dirtyDigit,dirtyMdg','replace,dirtyDigit:oldDigit,dirtyMdg'),
        "let f=replace(oldF","const dirtyDigit=module.digit;let f=replace(oldF"):source;
    m._compile(src+'\nmodule.exports={f,d,dirtyDigit,dirtyMdg,dirtyBlock,lowValuationSweep,plusOneMod,R35UnitWalk,mapped,emitWalk,D2Reduced,D2Canonical,emitMultiplySparse,emitDivideSparse};',base);
    return m.exports;
}
module.exports={...bind(),withDigit:bind};
