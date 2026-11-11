'use strict';
const fs=require('node:fs'),path=require('node:path'),Module=require('node:module');
const pub=require('./public-backend.cjs'),{replace}=require('../q653-next/parts.cjs');
const {sharedDigit}=require('./shared-digit.cjs');
const root=path.join(__dirname,'upstream'),settings={R35_WIDTH:'651',G129_MODE:'same-width',G129_TOP:'pc'};
function load(name,bindings,edits){
    const f=path.join(root,name),m=new Module(f,module);
    let s=fs.readFileSync(f,'utf8');for(const [a,b] of edits)s=replace(s,a,b);
    m.filename=f;m.paths=Module._nodeModulePaths(path.dirname(f));m.settings=settings;Object.assign(m,bindings);
    m._compile("'use strict';const process={env:module.settings};\n"+s,f);return m.exports;
}
const balance=load('g129.cjs',{previous:require('../q653-centerfix/upper.cjs')},[
    ["const prev=require(path.join(Q,'upper.cjs'));","const prev=module.previous;"]]);
const ladder=load('upper/upper.cjs',{balance},[
    ["const g129=require('../g129.cjs').upper;","const g129=module.balance.upper;"]]);
const old=load('upper652.cjs',{ladder},[
    ["const base=process.env.R35_UBASE?require(path.resolve(process.env.R35_UBASE)).upper:require('./g129.cjs').upper;","const base=module.ladder.upper;"]]);
const current=load('upper651.cjs',{old},[
    ["const old=require('./upper652.cjs').upper;","const old=module.old.upper;"]]);
function upper(src){
    const s=current.upper(src),orig=pub.dirtyDigit.toString();
    return replace(s,orig,sharedDigit.toString().replace('function sharedDigit','function dirtyDigit'));
}
module.exports={upper};
