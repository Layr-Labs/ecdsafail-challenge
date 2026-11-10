'use strict';
const path=require('node:path'),Module=require('node:module');
const {checkedSource}=require('../field128-height-experiment/pinned.cjs');
const {replace,SectorSigned}=require('../q653-next/parts.cjs');
const file=path.join(__dirname,'../q654-next/regen.cjs');
let source=checkedSource(file,'0cac8f32c234456119814212636c846c5a2c3125d96a69ef102d1c91028d69e1');
class Signed extends SectorSigned {constructor(n){super(n,5);}}
function thinTerminal(x){
    x.tag[4]=x.cin;
    x.add=Signed.prototype.add;
    x.lt=Signed.prototype.lt;
    x.orient=function(sign=this.sg) {
        const c=sign===null?[this.f]:[sign,this.f];
        this.zer([],this.S,this.f);this.raw(-1,-1,this.f);
        for(const q of this.S)this.op(c,q);
        this.add(c,this.M,this.S,null,null);
        const subtract=()=>this.reverse(()=>this.add(c,this.D,this.S,null,null));
        subtract();for(const q of this.D)this.raw(-1,-1,q);
        subtract();for(const q of this.D)this.raw(-1,-1,q);
        this.raw(-1,-1,this.f);this.zer([],this.S,this.f);
    };
}
source=replace(source,"const {Signed}=require('./walks.cjs');",'const Signed=module.Signed;');
source=replace(source,'x.tag[6]=walk.L[1];',
    'x.tag[6]=walk.L[1];x.tag[5]=walk.L[0];module.thinTerminal(x);');
source=replace(source,'[scale,scale.plan(),false]',
    '[scale,[{fn:()=>scale.raw(-1,-1,walk.L[0])}].concat(scale.plan(),[{fn:()=>scale.raw(-1,-1,walk.L[0])}]),false]');
source=replace(source,'q===walk.tag[6]&&g===walk','q===walk.tag.at(-1)&&g===walk');
source=replace(source,'if(q===653||q===655||q===656)','if(q===651||q===652||q===653||q===655||q===656)');
const m=new Module(file,module);m.filename=file;m.paths=Module._nodeModulePaths(path.dirname(file));
m.Signed=Signed;m.thinTerminal=thinTerminal;m._compile(source,file);module.exports=m.exports;
