'use strict';

const path = require('node:path');
require('./field/final.cjs');
require('./upper/routing.cjs').install(path.resolve(__dirname, '..'));
