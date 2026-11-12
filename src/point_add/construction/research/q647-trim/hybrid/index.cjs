'use strict';
const path=require('node:path'),fs=require('node:fs'),{createHash}=require('node:crypto');
const {patch:sevenPatch}=require('../../q648-trim/upper/index.cjs');
const compiler=path.resolve(__dirname,'../../../ecdsafail-q649-port-20261110-ftBg4d4T/quick-input/compiler');
const pinned='c646e0ea8791fe21d702d7d28c27367f3cdeea2356e7d2bbe483fcbde933883e';
const donorFile=path.resolve(__dirname,'../../q648-trim/upper/donor.generated.cjs');
const pins=require('../../q648-trim/donor/construction/research/agents/midpoint-implicit-query-20261109/q651-ten-field/q648-pieces.json').env;
const kernels=new Map();
function phaseSign(host,k,target){
    const h=new UnguardedGeneral(256,(1n<<32n)+977n,k,657),t=new FoldTape(657,[],h.g);
    // This is the seven-helper algorithm's dirty pool. It can use all six
    // actual helpers. Its measured flag is excluded inside signProbe itself.
    t.ids=t.ids.filter(q=>q<=649&&q!==647);
    t.out=(a,b,z)=>host.out(a,b,z);
    t.z=q=>host.z(q);
    h.measureTarget=target;h.u5CleanPhase=target;h.probeBack=true;
    h.signProbe(t,target,true);
}
function kernelText(omitPhase=true){
    if(kernels.has(omitPhase))return kernels.get(omitPhase);
    const source=sevenPatch(fs.readFileSync(donorFile,'utf8'),compiler);
    if(createHash('sha256').update(source).digest('hex')!==pinned)throw Error('Q648 hybrid donor mismatch');
    const start=source.indexOf('function split(lo,hi) {'),end=source.indexOf('class MeasuredNct extends Tape {');
    if(start<0||end<start)throw Error('Q648 hybrid donor boundaries');
    // Keep the frozen source separate from transforms which scan the host's
    // method names. The generated program has ordinary JavaScript only and
    // needs no build-time source or filesystem reads during execution.
    const env=omitPhase?{...pins,Q648_P4F1:'0',Q648_P4R1:'0'}:pins;
    const text='"use strict";const process={env:'+JSON.stringify(env)+'};\n'+source.slice(start,end)+'\nreturn '+phaseSign.toString()+';';
    const encoded=Buffer.from(text).toString('base64');kernels.set(omitPhase,encoded);return encoded;
}
function patchThrough(source,last){
    if(!Number.isInteger(last)||last<0||last>112)throw Error('Q647 hybrid last probe '+last);
    const marker='function u37Select(w){';
    if(source.split(marker).length!==2||!source.includes("throw Error('U37 omitted role '")||source.includes('const q647SevenPhase='))throw Error('Q647 hybrid host mismatch');
    const body='const q647SevenPhase=Function(Buffer.from('+JSON.stringify(kernelText())+',"base64").toString("utf8"))();\n'+
        'const q647BeforePhase=UnguardedGeneral.prototype.signProbe;\n'+
        'UnguardedGeneral.prototype.signProbe=function(tape,target,back){\n'+
        '  if(this.m===256&&this.k>=0&&this.k<='+last+'&&back&&target===644&&this.measureTarget===target&&this.u5CleanPhase===target&&tape.u37Control?.frame===644){\n'+
        '    q647SevenPhase(tape,this.k,target);return;\n'+
        '  }\n  return q647BeforePhase.call(this,tape,target,back);\n};\n';
    return source.replace(marker,body+marker);
}
function patch(source){return patchThrough(source,110);}
module.exports={patch,patchThrough,kernelText,phaseSign,pinned};
