'use strict';
const path = require('node:path');

const family = 'research/agents/midpoint-implicit-query-20261109';

function replaceOne(source, before, after) {
    if (source.split(before).length !== 2) throw Error('Q649 source anchor: ' + before);
    return source.replace(before, () => after);
}

function setExport(filename, replacement) {
    const id = require.resolve(filename);
    require(id);
    require.cache[id].exports = replacement;
}

function installDigits(owner, compiler) {
    const {sharedDigit} = require(path.join(owner, 'shared-digit.cjs'));
    const {implicitTopDigit} = require(path.join(compiler, 'implicit-top.cjs'));
    for (const name of ['m6-alternating.cjs', 'd14-alternating-digit.cjs']) {
        setExport(path.join(owner, name), {alternatingDigit: sharedDigit});
    }
    setExport(path.join(owner, 'm6-constant-fast.cjs'), function topDigit(a, b, h, e) {
        const walk = this;
        const tape = {
            loan(used, count) {
                const blocked = new Set(used);
                const choices = walk.y.filter(q => !blocked.has(q)).slice(0, count);
                if (choices.length !== count) throw Error('Q649 M6 dirty digit workspace');
                return choices;
            },
            out(x, y, target) {
                if (x === 1023) walk.raw(y === 1023 ? -1 : y, -1, target);
                else walk.raw(x, y === 1023 ? -1 : y, target);
            }
        };
        implicitTopDigit(tape, [...b, h], [...a, -1001], [e], false);
    });
}

function portUpper(source, compiler, options) {
    const use = name => require(path.join(compiler, name));
    if (options.has('arith')) {
        source = use('shared-controls.cjs').patchPermutation(source);
        source = use('wide.cjs').addWideTransforms(source);
        source = use('increment.cjs').patchIncrement(source);
        const {implicitTopDigit} = use('implicit-top.cjs');
        source = replaceOne(source, 'class Tape {', implicitTopDigit.toString() + '\nclass Tape {');
        const anchor = '    digitTopOne(tape,z,v,controls,back){\n        const B=z.slice(0,-1)';
        const condition = options.has('virtualtop') ? 'v.length>=8' : 'v.length>=8&&!this.u12';
        source = replaceOne(source, anchor, anchor.replace('        const B=',
            '        if(' + condition + '){implicitTopDigit(tape,z,v,controls,back);return;}\n        const B='));
    }
    if (options.has('code')) {
        const slot = 'H.u40Tag[this.u6ProbeSlot??1]=S[0];';
        const plain = 'H.u40Tag[1]=S[0];';
        source = replaceOne(source, slot, plain);
        source = use('probe-code.cjs').refineProbeCode(source);
        source = replaceOne(source, plain, slot);
    }
    if (options.has('codetrans') || options.has('prefix')) {
        source = require('./codebook.cjs').apply(source, replaceOne, options);
    }
    if (options.has('lease') || options.has('leasezero') || options.has('leasethree')) {
        source = require('./materialize.cjs').install(source, replaceOne, options);
    }
    if (options.has('physical')) {
        source = use('physical.cjs').patchPhysical(source);
        // The new filter emits into the donor's 4096-gate sorter. Drain both
        // in their actual dataflow order at every whole-stage boundary.
        source = replaceOne(source, 'this.endUpper=filter.flush;',
            'this.endUpper=()=>{filter.flush();this.s1Flush();};');
    }
    return source;
}

function build(donorRoot, compilerRoot, variant, inspect) {
    const owner = path.resolve(donorRoot, family, 'q651-ten-field');
    const root = path.resolve(compilerRoot);
    const compiler = path.join(root, 'q650-joined-probes');
    const options = new Set(variant.split('-'));
    if (options.has('fast')) require('./fast-window.cjs').install(owner);
    if (options.has('rotate')) require(path.join(compiler, 'field-rotate.cjs')).install(owner);
    if (options.has('digit')) installDigits(owner, compiler);
    if (options.has('crop')) require('./wide-walk.cjs').installMultiply(owner);
    if (options.has('host')) require('./wide-walk.cjs').installDivide(owner, compiler);
    if (options.has('physical')) {
        require(path.join(root, 'q650-field-fusion/stream.cjs')).install(root);
        require(path.join(compiler, 'physical.cjs')).installStages(owner);
    }
    const stages = require(path.join(owner, 'stage-map.cjs'));
    const original = stages.upper;
    stages.upper = (raw, config) => {
        const source = portUpper(original(raw, config), compiler, options);
        if (inspect) inspect(source);
        return source;
    };
    const api = require(path.join(owner, 'point-i.cjs'));
    class GateWriter extends api.GateWriter {
        hooks() {
            const config = super.hooks();
            if (options.has('physical')) {
                const start = config.start;
                config.start = (Tape, width, controls) => {
                    const tape = start(Tape, width, controls);
                    const bit = tape.nextBit++;
                    tape.eraseProduct = (a, b, target) => {
                        this.emit(12, target, bit);
                        this.emit(9, a, b, bit);
                        this.emit(4, bit);
                    };
                    return tape;
                };
            }
            return config;
        }
    }
    return {...api, GateWriter};
}
module.exports = {build, portUpper};
