'use strict';
const path = require('node:path');
require('./preload.cjs');
const base = path.resolve(__dirname, '../q648-trim');
const field = require(path.join(base, 'field/index.cjs'));
require('./field/outer.cjs').install(path.join(base, 'donor', field.family));
const upper = require(path.join(base, 'upper/index.cjs'));
const previous = upper.patch;
upper.patch = (...args) => require('./unit/stair.cjs').patch(previous(...args));
