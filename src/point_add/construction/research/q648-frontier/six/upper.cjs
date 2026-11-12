'use strict';

const {mergeEnabled} = require('../../q648-next/general/stretch/index.cjs');

function replace(source, before, after, expected) {
    const pieces = source.split(before);
    if (pieces.length !== expected+1) throw Error('Q647 merge anchor '+before);
    return pieces.join(after);
}

function merge(source) {
    let result = replace(source, 'class Tape {', mergeEnabled.toString()+'\nclass Tape {', 1);
    function pair(owner, tag, add, separator, count) {
        const mix = `${owner}.alignedMix(tape,a,D,${tag},rv)`;
        const safe = `mergeEnabled(${owner},a,D,${tag})`;
        const joined = `rv=>{if(!${safe})${add};},rv=>{const mixRow=Object.create(${owner});`+
            `mixRow.q647MergedAdd=${safe};mixRow.alignedMix(tape,a,D,${tag},rv);}`;
        result = replace(result, 'rv=>'+add+','+separator+'rv=>'+mix, joined, count);
    }
    pair('H', 'tag', 'prefixAdd(H,tape,a,D,rv)', '', 2);
    pair('H', 'tag', 'denseAdd(H,tape,a,D,rv)', '', 1);
    pair('H', 'tag', 'leaseCoefficient(H,tape,a,1,tp=>tp.add(a,D,[],this.carry,rv))', '', 4);
    pair('H', 'H.u40Tag', 'H.u40Tape(tape).add(a,D,[],this.carry,rv)', '', 1);
    pair('this', 'tag', 'tape.add(a,D,[],this.carry,rv)', '\n            ', 1);
    pair('this', 'tag', 'tape.add(a,D,[],this.carry,rv)', '\n        ', 1);
    const op = 'ops.push(rv=>this.nrAdder(tape,v,J.slice(0,n),null,J[n],rv),';
    const replacement = `ops.push(rv=>{if(!this.q647MergedAdd){this.nrAdder(tape,v,J.slice(0,n),null,J[n],rv);return;}
        tape.out(NONE,NONE,J[n]);this.nrAdder(tape,v,J.slice(0,n),null,J[n],!rv);tape.out(NONE,NONE,J[n]);},`;
    const count = result.split(op).length-1;
    if (count !== 1 && count !== 2) throw Error('Q647 final adder count '+count);
    return replace(result, op, replacement, count);
}

function patch(source) {
    const reflect = require('../../q648-next/general/index.cjs').patch(source, 'split');
    const unit = require('../../q648-next/unit/unit.cjs').patch(reflect, 'split');
    return require('../../q648-next/unit/stair.cjs').patch(merge(unit));
}

module.exports = {patch, merge};
