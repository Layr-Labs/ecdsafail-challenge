'use strict';
const assert = require('node:assert/strict');
const path = require('node:path');
const trim = path.resolve(__dirname, '../q648-trim');
require(path.join(trim,'refinements.cjs'));
require('./field/tail.cjs').install(path.join(trim,'field'));
const field = require(path.join(trim,'field/index.cjs'));
const originalInstall = field.install;
field.install = (root, compiler, selection) => {
    assert.equal(selection, 'power,lift,divide,history');
    return originalInstall(root, compiler, selection + ',multiply');
};
const upper = require(path.join(trim,'upper/index.cjs'));
const refined = upper.patch;
upper.patch = (...args) => {
    const general = require('./general/index.cjs').patch(refined(...args));
    return require('./unit/unit.cjs').patch(general, 'split');
};
