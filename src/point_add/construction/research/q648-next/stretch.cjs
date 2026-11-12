'use strict';
const path = require('node:path');
require('./staircase.cjs');
const upper = require(path.resolve(__dirname,'../q648-trim/upper/index.cjs'));
const previous = upper.patch;
upper.patch = (...args) => require('./general/stretch/index.cjs').patch(previous(...args), 'fused');
