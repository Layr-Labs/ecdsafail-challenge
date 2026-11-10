'use strict';
const path=require('node:path'),Module=require('node:module');
const {checkedSource}=require('../field128-height-experiment/pinned.cjs');
const {replace}=require('../q653-next/parts.cjs');
const {optimizeStream}=require('../q651-gate-reduction/commute.cjs');
const field=require('../q652-field-v1/backend-fast.cjs'),history=require('../q652-field-v1/regen-fast.cjs');
function bind(name,sha,edits,context){
    const file=require.resolve(name);let src=checkedSource(file,sha);
    for(const [old,next] of edits)src=replace(src,old,next);
    const m=new Module(file,module);m.filename=file;m.paths=Module._nodeModulePaths(path.dirname(file));
    Object.assign(m,context);m._compile(src,file);return m.exports;
}
const parent=require('../q652-alt-digit/upper.cjs');
const upperReduction=bind('../q651-upper-reduction/upper.cjs','9f0bcc3af22ed1d3a1c0854d1a815a62b84e670112950959968599c85b51d382',
    [["require('../q651-ten-field/upper.cjs')","module.stage"]],{stage:parent});
const upper=bind('../q651-fusion-cache/upper.cjs','ca0b93a66d15b94de42d4da2b40ff9a7fd8e2de87c024b4f5254cd9c5ac9a47e',
    [["require('../q651-upper-reduction/upper.cjs')","module.stage"]],{stage:upperReduction});
const kernels={
    emitMultiplySparse:sink=>optimizeStream(field.emitMultiplySparse,sink),
    emitDivideSparse:sink=>optimizeStream(field.emitDivideSparse,sink),
    emitRegenerateSparse(sink,erase=false){
        optimizeStream(visitor=>history.emitRegenerateSparse(words=>visitor('packed',words),erase),
            (kind,words)=>{if(kind!=='packed')throw Error('unexpected history barrier');sink(words);});
    }
};
const base=bind('../q652-alt-digit/point.cjs','70133f6249b7b2cdcdda07a448bbb4625f79bb13e94a44e19c803d2ece5d3e14',[
    ["mod.field=require(path.join(family,'q652-field-v1/backend-fast.cjs'));","mod.field=module.kernels;"],
    ["mod.history=require(path.join(family,'q652-field-v1/regen-fast.cjs'));","mod.history=module.kernels;"],
    ["mod.upper=require('./upper.cjs').upper;","mod.upper=module.upper;"]
],{kernels,upper:upper.upper});
class GateWriter extends base.GateWriter{
    hooks(){
        const opts=super.hooks(),start=opts.start;
        opts.start=(Tape,width,controls)=>{
            const tape=start(Tape,width,controls),bit=tape.nextBit++;
            tape.eraseProduct=(a,b,t)=>{this.emit(12,t,bit);this.emit(9,a,b,bit);this.emit(4,bit);};
            return tape;
        };
        return opts;
    }
}
module.exports={...base,GateWriter};
if(require.main===module){
    const [mode,file]=process.argv.slice(2);
    if(!['raw','spans'].includes(mode)||!file)throw Error('use raw FILE or spans FILE');
    console.log(JSON.stringify(new GateWriter(mode==='raw'?file:null,mode==='spans'?file:undefined).produce(),null,2));
}
