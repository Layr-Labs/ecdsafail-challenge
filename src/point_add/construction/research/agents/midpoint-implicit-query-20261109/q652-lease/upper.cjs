'use strict';
const path=require('node:path'),fs=require('node:fs'),Module=require('node:module');
const published=require('../q652-hybrid/upper.cjs');
function replace(s,a,b){if(s.split(a).length!==2)throw Error('Unexpected public Q652 affine anchor '+a);return s.replace(a,()=>b);}
function upper(source){
    let s=published.upper(source);
    const a='const seq=[()=>this.toggle(tape,[],a.slice(-k),bit),rv=>this.permute(tape,a,orig,[bit],rv)];';
    s=replace(s,a,'const guard=(j===3&&this.rankHost===this.pick)?[this.take]:[];\n            const seq=[()=>this.toggle(tape,guard,a.slice(-k),bit),rv=>this.permute(tape,a,orig,[bit],rv)];');
    const head='class UnguardedGeneral extends OddEstimateGeneral {';
    return replace(s,head,head+'\n'+fs.readFileSync(path.join(__dirname,'lease-affine.js.inc'),'utf8'));
}
function upperComponent(){
    const f=path.resolve(__dirname,'../../../campaigns/2026-11-08-lowq-next/nov09-joined/checkpoint/centered-point.cjs');
    const m=new Module(f,module);m.filename=f;m.paths=Module._nodeModulePaths(path.dirname(f));m._compile(upper(fs.readFileSync(f,'utf8')),f);return m.exports;
}
module.exports={upper,upperComponent};
