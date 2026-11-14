'use strict';
const path = require('node:path');
require('./stretch.cjs');
const base = path.resolve(__dirname, '../q648-trim');
const field = require(path.join(base, 'field/index.cjs'));
require('./field/winding.cjs').install648(path.join(base, 'donor', field.family));
