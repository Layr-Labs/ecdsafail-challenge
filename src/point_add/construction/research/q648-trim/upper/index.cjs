'use strict';
const path = require('node:path');
const {portUpper} = require('../../../ecdsafail-q649-port-20261110-ftBg4d4T/quick-input/port/port.cjs');
const {leaseCoefficient} = require('../../../ecdsafail-q649-port-20261110-ftBg4d4T/quick-input/port/materialize.cjs');
const tails = require('../../q649-record/upper/upper.cjs');
const main = require('../../q649-record/upper/main.cjs');
const {rankMain} = require('./rank-main.cjs');
const masks = require('./masked-ripple.cjs');

function replaceCount(source, before, after, count = 1) {
    const parts = source.split(before);
    if (parts.length !== count + 1) throw Error('Q648 upper anchor (' + count + ' matches required): ' + before);
    return parts.join(after);
}

function guardedProbes(source) {
    const mixed = '    mixed(tape,q,v,rem,controls,back){\n      super.mixed(this.u40Tag';
    const adder = 'rv=>H.u6VirtualTape(tape).add(a,D,[],this.carry,rv),rv=>H.alignedMix(tape,a,D,tag,rv)';
    const bracket = 'stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);stepList(seq,true,fn=>fn(true));\n      for(const tp of H.u6Tapes)tp.u6Check();';
    const known = 'this.u5PhaseHost!==target&&target===this.dv[0]&&(this.measureTarget===target||!this.probeBack)&&!tag.includes(target)';
    source = replaceCount(source, 'class Tape {', leaseCoefficient.toString() + '\nclass Tape {');
    source = replaceCount(source, mixed, `    mixed(tape,q,v,rem,controls,back){
      if(this.u6Code&&v[0]===this.u40Low&&!controls.length){
        leaseCoefficient(this,tape,v,1,tp=>super.mixed(tp,q,v,rem,controls,back));return;
      }
      super.mixed(this.u40Tag`);
    source = replaceCount(source, adder, 'rv=>leaseCoefficient(H,tape,a,1,tp=>tp.add(a,D,[],this.carry,rv)),rv=>H.alignedMix(tape,a,D,tag,rv)', 3);
    return replaceCount(source, bracket, `const known=${known};H.q649Loan=known?target:null;
      stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);
      H.q649Loan=known&&this.measureTarget===target?target:null;stepList(seq,true,fn=>fn(true));
      for(const tp of H.u6Tapes)tp.u6Check();`, 3);
}

function patch(finalDonorUpper, compilerRoot, mode = 'mask') {
    if (!['port','both','middle-one','early-one','early-two','mask','mask-affine','mask-probe'].includes(mode)) throw Error('Unknown Q648 upper mode ' + mode);
    const compiler = path.resolve(compilerRoot, 'q650-joined-probes');
    let s = portUpper(finalDonorUpper, compiler, new Set(['arith','virtualtop','code','codetrans','prefix']));
    s = guardedProbes(s);
    s = tails.patch(s);
    // In Q648 A[2] hosts rank bit six for rows 0..63. Numerical A[2]
    // is still required in a cropped tail starting at bit two.
    s = replaceCount(s, 'if(this.u12&&cut>=2)', 'if(this.u12&&cut>=(this.u648?3:2))');
    if (mode === 'port') return s;
    s = main.patch(s, mode === 'both' ? 'both' : 'one');
    if (mode !== 'both') {
        s = replaceCount(s, "if(owner.u12&&variant==='one'", "if(owner.u12&&!owner.u648&&variant==='one'");
    }
    if (mode === 'early-one' || mode === 'early-two') {
        s = replaceCount(s, 'class Tape {', rankMain.toString() + '\nclass Tape {');
        const start = 'function mainDigits(owner,tape,layer,r,a,d,rv,variant) {';
        const limit = mode === 'early-one' ? 127 : 120;
        s = replaceCount(s, start, start + `
        if(owner.u648&&owner.maxShift<${limit}){rankMain(owner,tape,layer,r,a,d,rv,'${mode}');return;}`);
    }
    if (mode.startsWith('mask')) {
        s = replaceCount(s, 'class Tape {', Object.values(masks).map(f=>f.toString()).join('\n') + '\nclass Tape {');
        if (mode !== 'mask-probe') {
            const start = 'function mainDigits(owner,tape,layer,r,a,d,rv,variant) {';
            s = replaceCount(s, start, start + '\n      if(owner.u12){maskedAffine(owner,tape,layer,r,a,d,rv);return;}');
        }
        if (mode !== 'mask-affine') {
            const mix='if(this.u6Code&&v[0]===this.u40Low&&!controls.length){';
            s=replaceCount(s,mix,`if(this.u648C&&v[0]===this.u40Low&&!controls.length){maskedProbeProduct(this,tape,q,v,rem,back);return;}\n      ${mix}`);
            const add='rv=>leaseCoefficient(H,tape,a,1,tp=>tp.add(a,D,[],this.carry,rv))';
            s=replaceCount(s,add,'rv=>H.u648C?maskedProbeAdd(H,tape,a,D)(null,null,rv):leaseCoefficient(H,tape,a,1,tp=>tp.add(a,D,[],this.carry,rv))',3);
        }
    }
    return s;
}
module.exports = {patch, replaceCount};
