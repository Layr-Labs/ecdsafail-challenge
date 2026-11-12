'use strict';

const assert = require('node:assert/strict');
const crypto = require('node:crypto');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const field = require('./field/index.cjs');
const upper = require('./upper/index.cjs');
const baseline = path.resolve(__dirname, '../../ecdsafail-q649-port-20261110-ftBg4d4T/quick-input');
const donor = path.join(__dirname, 'donor');
const compiler = path.join(baseline, 'compiler');

function circuit(mode = 'mask', fieldMode = 'power,lift,divide,history') {
    const owner = path.join(donor, field.family);
    // Start with the donor's seven-helper profile and its pinned switches.
    for (const key of Object.keys(process.env)) if (key.startsWith('Q648_')) delete process.env[key];
    field.install(donor, compiler, fieldMode);
    const stages = require(path.join(owner, 'stage-map.cjs'));
    const donorUpper = stages.upper;
    const {patchPhysical} = require(path.join(compiler, 'q650-joined-probes/physical.cjs'));
    stages.upper = (source, config) => {
        const shortened = upper.patch(donorUpper(source, config), compiler, mode);
        const arithmetic = require('./alternate/square.cjs').patch(shortened);
        const physical = patchPhysical(arithmetic);
        return upper.replaceCount(physical, 'this.endUpper=filter.flush;',
            'this.endUpper=()=>{filter.flush();this.s1Flush();};');
    };
    const api = require(path.join(owner, 'point-i.cjs'));
    assert.equal(api.config.width, 648);
    assert.equal(api.config.signPhysical, 647);
    class GateWriter extends api.GateWriter {
        hooks() {
            const hooks = super.hooks();
            const start = hooks.start;
            hooks.start = (Tape, width, controls) => {
                const tape = start(Tape, width, controls);
                const bit = tape.nextBit++;
                tape.eraseProduct = (a, b, target) => {
                    this.emit(12, target, bit);
                    this.emit(9, a, b, bit);
                    this.emit(4, bit);
                };
                return tape;
            };
            return hooks;
        }
    }
    return {...api, GateWriter};
}

function check(api, direction, count) {
    assert(['forward', 'reverse'].includes(direction));
    const fixture = fs.readFileSync(path.join(baseline, 'fixtures/openssl-384.json'));
    const rows = JSON.parse(fixture);
    assert(Number.isInteger(count) && count >= 1 && count <= rows.length);
    const points = rows.slice(0, count).map(row => Object.fromEntries(
        Object.entries(row).map(([name, point]) => [name, point && point.map(BigInt)])));
    const result = api.arithmetic(null).shellWithFieldOracles(
        256, (1n << 32n) + 977n, points, direction === 'reverse',
        {forward: api.forward, regenerate: api.regenerate}, api.divide, 'random', false);
    assert.equal(result.width, 648);
    for (const key of ['shortForwardOracles', 'shortInverseOracles', 'historyOracles']) assert.equal(result[key], 0);
    return {direction, fixtureSha256: crypto.createHash('sha256').update(fixture).digest('hex'), ...result};
}

if (require.main === module) {
    const [task, first, second] = process.argv.slice(2);
    const api = circuit(process.env.UPPER_VARIANT, process.env.FIELD_VARIANT);
    let result;
    if (task === 'check') result = check(api, first, Number(second || 32));
    else if (task === 'count') result = new api.GateWriter(null).produce();
    else if (task === 'scheduled' && first && second) {
        assert.equal(os.endianness(), 'LE');
        result = new api.GateWriter(first, second).produce();
    } else if (task === 'stream' && first) {
        assert.equal(os.endianness(), 'LE');
        const writer = new api.GateWriter(null, second);
        writer.file = 1;
        result = writer.produce();
        fs.writeFileSync(first, JSON.stringify(result, null, 2) + '\n', {flag:'wx'});
    } else throw Error('Use check forward|reverse N, count, stream RECEIPT [RANGES], or scheduled TRACE RANGES');
    if (task !== 'stream') console.log(JSON.stringify(result, null, 2));
}

module.exports = {circuit, check};
