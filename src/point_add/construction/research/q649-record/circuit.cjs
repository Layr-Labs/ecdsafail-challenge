'use strict';

const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const {build, root} = require('./upper/build.cjs');

function circuit() {
    require('./field/index.cjs').install(root);
    const api = build(true);
    const stages = require(path.join(root, 'construction/research/agents/midpoint-implicit-query-20261109/q651-ten-field/stage-map.cjs'));
    const upper = stages.upper;
    const {patch} = require('./upper/main.cjs');
    stages.upper = (source, config) => patch(upper(source, config), 'both');
    if (api.config.width !== 649) throw Error('Unexpected physical width');
    return api;
}

function checkPoints(api, direction, count) {
    const fixture = path.join(root, 'fixtures', 'openssl-384.json');
    const bytes = fs.readFileSync(fixture);
    const points = JSON.parse(bytes);
    if (!['forward', 'reverse'].includes(direction) || !Number.isInteger(count) ||
        count < 1 || count > points.length) throw Error('Invalid direction or case count');
    const rows = points.slice(0, count).map(row => Object.fromEntries(
        Object.entries(row).map(([key, point]) => [key, point && point.map(BigInt)])));
    const result = api.arithmetic(null).shellWithFieldOracles(
        256, (1n << 32n) + 977n, rows, direction === 'reverse',
        {forward: api.forward, regenerate: api.regenerate}, api.divide, 'random', false);
    if (result.width !== 649 || result.shortForwardOracles !== 0 ||
        result.shortInverseOracles !== 0 || result.historyOracles !== 0)
        throw Error('Partially implemented point circuit');
    return {direction, fixtureSha256: crypto.createHash('sha256').update(bytes).digest('hex'), ...result};
}

if (require.main === module) {
    const [mode, argument, count] = process.argv.slice(2);
    const api = circuit();
    let result;
    if (mode === 'check') result = checkPoints(api, argument, Number(count || 32));
    else if (mode === 'count') result = new api.GateWriter(null).produce();
    else if (mode === 'raw') {
        if (!argument || require('node:os').endianness() !== 'LE') throw Error('Expected an output path on a little endian host');
        result = new api.GateWriter(argument).produce();
    } else if (mode === 'scheduled') {
        if (!argument || !count || require('node:os').endianness() !== 'LE') throw Error('Expected new trace and ranges paths');
        result = new api.GateWriter(argument, count).produce();
    } else if (mode === 'stream') {
        if (!argument || require('node:os').endianness() !== 'LE') throw Error('Expected a receipt path on a little endian host');
        const writer = new api.GateWriter(null);
        writer.file = 1;
        result = writer.produce();
        fs.writeFileSync(argument, JSON.stringify(result, null, 2) + '\n', {flag:'wx'});
    } else throw Error('Use check forward|reverse [N], count, raw FILE, scheduled TRACE RANGES, or stream RECEIPT');
    if (mode !== 'stream') console.log(JSON.stringify(result, null, 2));
}

module.exports = {circuit, checkPoints};
