'use strict';

const assert = require('node:assert/strict');
const fs = require('node:fs');
const Module = require('node:module');
const path = require('node:path');

// Both physical optimizers span the point's field calls. Retire a product in
// tape order, then tell the symbolic cache that the measured wire is zero.
// Its existing erase primitive owns the reusable bit and the phase correction.
function install(research) {
    const compiler = path.resolve(research, '../ecdsafail-q649-port-20261110-ftBg4d4T/quick-input/compiler');
    const file = require.resolve(path.join(compiler, 'q651-product-cache/cache.cjs'));
    const cache = require(file);
    const source = fs.readFileSync(file, 'utf8');
    const anchor = 'flush.stats=capStats;return flush;';
    assert.equal(source.split(anchor).length, 2);
    const addition = `tape.retireFieldProduct=(a,b,t)=>{
        flush();erase(a,b,t);v.put(t,0);
    };`;
    const replacement = new Module(file, module);
    replacement.filename = file;
    replacement.paths = Module._nodeModulePaths(path.dirname(file));
    replacement._compile(source.replace(anchor, addition + anchor), file);
    cache.install = replacement.exports.install;

    const fusion = require(path.join(compiler, 'q651-parity-fusion/fusion.cjs'));
    const installFusion = fusion.install;
    fusion.install = function(tape) {
        const retire = tape.retireFieldProduct;
        const flush = installFusion(tape);
        if (retire) tape.retireFieldProduct = (a, b, t) => {
            flush();
            retire(a, b, t);
        };
        return flush;
    };
}

module.exports = {install};
