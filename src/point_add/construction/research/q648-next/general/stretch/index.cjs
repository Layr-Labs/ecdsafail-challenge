'use strict';
function mergeEnabled(o,a,d,tag){
    const lease=!o.u38ProbeLease&&o.useCoefficientDirection&&!o.wideBand;
    if(!lease)return true;
    const wire=o.v[o.k];return !a.includes(wire)&&!d.includes(wire)&&!tag.includes(wire);
}
function one(source,needle,repl,n=1){const chunks=source.split(needle);if(chunks.length!==n+1)throw Error('stretch source anchor '+needle);return chunks.join(repl);}
function mergePatch(source){
    let s=one(source,'class Tape {',mergeEnabled.toString()+'\nclass Tape {');
    function fuse(owner,tag,oldAdd,separator,n){
        const alignment=owner+'.alignedMix(tape,a,D,'+tag+',rv)',test='mergeEnabled('+owner+',a,D,'+tag+')';
        const a='rv=>'+oldAdd+','+separator+'rv=>'+alignment;
        const b='rv=>{if(!'+test+'){'+oldAdd+';}},rv=>{const G=Object.create('+owner+');G.q648MergedAdd='+test+';G.alignedMix(tape,a,D,'+tag+',rv);}';
        s=one(s,a,b,n);
    }
    fuse('H','tag','H.u648C?maskedProbeAdd(H,tape,a,D)(null,null,rv):H.u9H?markerAdd(H,tape,a,D,rv):leaseCoefficient(H,tape,a,1,tp=>tp.add(a,D,[],this.carry,rv))','',3);
    fuse('H','H.u40Tag','H.u40Tape(tape).add(a,D,[],this.carry,rv)','',1);
    fuse('this','tag','tape.add(a,D,[],this.carry,rv)','\n            ',1);
    fuse('this','tag','tape.add(a,D,[],this.carry,rv)','\n        ',1);
    const digit='        ops.push(rv=>this.nrAdder(tape,v,J.slice(0,n),null,J[n],rv),';
    return one(s,digit,`        ops.push(rv=>{
            if(!this.q648MergedAdd){this.nrAdder(tape,v,J.slice(0,n),null,J[n],rv);return;}
            tape.out(NONE,NONE,J[n]);
            this.nrAdder(tape,v,J.slice(0,n),null,J[n],!rv);
            tape.out(NONE,NONE,J[n]);
        },`);
}
function patch(source,mode='fused'){
    if(mode==='witness')return require('./witness.cjs').patch(source);
    if(mode==='merge')return mergePatch(source);
    if(mode==='fused')return require('./witness.cjs').patch(mergePatch(source));
    if(mode==='cone')return require('./cone.cjs').patch(source);
    throw Error('Q648 stretch mode');
}
module.exports={patch,mergeEnabled};
