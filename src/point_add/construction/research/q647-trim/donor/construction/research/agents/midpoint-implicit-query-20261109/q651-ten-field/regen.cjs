'use strict';
const fs=require('node:fs'),path=require('node:path'),Module=require('node:module');
const {replace,SectorSigned}=require('../q653-next/parts.cjs');
const {withDigit}=require('./public-backend.cjs');
const {sharedDigit}=require('./shared-digit.cjs');
const noaux=withDigit(sharedDigit).D2Canonical;
const Base=Object.getPrototypeOf(Object.getPrototypeOf(noaux));
class NoAuxSigned extends Base {
    constructor(n,bits){super(n);this.tag=this.tag.slice(0,bits);}
    op(c,z){return noaux.prototype.op.call(this,c,z);}
}
const material=path.join(__dirname,'../q653-next/regen.cjs');
let text=fs.readFileSync(material,'utf8');
for(const [a,b] of require('./upstream/regen/p-regen651.js'))text=replace(text,a,b);
function extra(s){
    s=replace(s,'walk=new Signed(n,4),walk6=new Signed(n,5)','walk=new Signed(n,5),walk6=new Signed(n,6)');
    s=replace(s,'for(let i=this.S.length;i--;)this.op(c.concat(this.S.slice(0,i)),this.S[i]);',
        `const sub=()=>this.reverse(()=>this.add(c,this.D,this.S,0,null));
        sub();for(const q of this.D)this.raw(-1,-1,q);sub();for(const q of this.D)this.raw(-1,-1,q);`);
    return replace(s,'walk.tag[3]=651;walk.fire=650;',
        'walk.tag[3]=walk.L[n+1];walk6.tag[4]=walk6.L[n+1];walk.fire=650;');
}
text=replace(text,'m.replacement=SectorSigned;m._compile(s,file);',
    'm.replacement=module.Walk;m._compile(module.adjust(s),file);');
function construct(Walk,adjust){
    const m=new Module(material,module);m.filename=material;m.paths=Module._nodeModulePaths(path.dirname(material));
    m.Walk=Walk;m.adjust=adjust;m._compile(text,material);return m.exports;
}
module.exports={...construct(NoAuxSigned,extra),published:()=>construct(SectorSigned,s=>s)};
