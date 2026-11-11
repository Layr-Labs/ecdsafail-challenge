'use strict';
const path=require('node:path');
const {patchPermutation}=require('./shared-controls.cjs'),{refineProbeCode}=require('./probe-code.cjs');
const {addWideTransforms}=require('./wide.cjs'),{patchIncrement}=require('./increment.cjs'),{patchImplicit}=require('./implicit-top.cjs');
function create650(donorRoot,variant){
    const dir=path.resolve(donorRoot,'research/agents/midpoint-implicit-query-20261109/q651-ten-field');
    const map=require(path.join(dir,'stage-map.cjs')),old=map.upper,parts=new Set(variant.split('-'));
    if(parts.has('rotate'))require('./field-rotate.cjs').install(dir);
    if(parts.has('multiply'))require('./hosted-multiply.cjs').install(dir);
    if(parts.has('host')){
        const target=require.resolve(path.join(dir,'divide-i.cjs'));require(target);
        require.cache[target].exports=require('./hosted-divide.cjs').build(dir,'both',parts.has('shared')?'shared':'alternating');
    }
    if(parts.has('history')){
        const target=require.resolve(path.join(dir,'regen650.cjs'));require(target);
        require.cache[target].exports=require('./hosted-history.cjs').build(dir);
    }
    if(parts.has('physical'))require('./physical.cjs').installStages(dir);
    map.upper=(raw,c)=>{
        let s=old(raw,c);
        if(parts.has('perm'))s=patchPermutation(s);
        if(parts.has('code'))s=refineProbeCode(s);
        if(parts.has('wide'))s=addWideTransforms(s);
        if(parts.has('inc'))s=patchIncrement(s);
        if(parts.has('top'))s=patchImplicit(s);
        if(parts.has('physical'))s=require('./physical.cjs').patchPhysical(s);
        return s;
    };
    const api=require(path.join(dir,'point-i.cjs'));
    class GateWriter extends api.GateWriter{
        hooks(){
            const opts=super.hooks(),start=opts.start,w=this;
            if(parts.has('physical'))opts.start=(Tape,width,controls)=>{
                const tape=start(Tape,width,controls),bit=tape.nextBit++;
                tape.eraseProduct=(a,b,t)=>{w.emit(12,t,bit);w.emit(9,a,b,bit);w.emit(4,bit);};return tape;
            };
            return opts;
        }
    }
    return {...api,GateWriter};
}
module.exports={create650};
