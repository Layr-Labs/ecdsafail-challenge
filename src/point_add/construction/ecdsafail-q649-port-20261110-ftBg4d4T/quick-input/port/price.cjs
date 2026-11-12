'use strict';
const fs = require('node:fs');
const crypto = require('node:crypto');
const {build} = require('./port.cjs');
const [donor, compiler, variant, mode, file, count] = process.argv.slice(2);
const sourceHash = data => crypto.createHash('sha256').update(data).digest('hex');
let ownerSHA;
const api = build(donor, compiler, variant, source => {
    ownerSHA = sourceHash(source);
    if (mode === 'source' && file) fs.writeFileSync(file, source);
});
if (mode === 'source') {
    api.arithmetic(null);
    console.log(JSON.stringify({variant, ownerSHA, width:api.config.width}));
} else if (['forward','reverse','upperforward','upperreverse'].includes(mode)) {
    const raw = fs.readFileSync(file);
    const rows = JSON.parse(raw).slice(0, Number(count || 32)).map(
        row => Object.fromEntries(Object.entries(row).map(([k, p]) => [k, p === null ? null : p.map(BigInt)]))
    );
    const source = api.arithmetic(null);
    const isolatedUpper=mode.startsWith('upper'), oracles=isolatedUpper?2:0;
    const result = source.shellWithFieldOracles(256, (1n << 32n) + 977n, rows, mode.endsWith('reverse'),
        isolatedUpper?null:{forward:api.forward, regenerate:api.regenerate}, isolatedUpper?null:api.divide, 'random', false);
    if (result.width !== 649 || result.shortForwardOracles!==oracles || result.shortInverseOracles!==oracles || result.historyOracles!==oracles) {
        throw Error('wrong point ABI ' + JSON.stringify(result));
    }
    console.log(JSON.stringify({variant, ownerSHA, mode, fixtureSHA:sourceHash(raw), cases:rows.length, observedLoanChecks:globalThis.q649LoanChecks||0, ...result}));
} else if (mode === 'raw' || mode === 'spans' || mode === 'count') {
    const writer = new api.GateWriter(mode === 'raw' ? file : null, mode === 'spans' ? file : undefined);
    const result = writer.produce();
    console.log(JSON.stringify({variant, ownerSHA, mode, ...result}));
} else throw Error('unknown mode ' + mode);
