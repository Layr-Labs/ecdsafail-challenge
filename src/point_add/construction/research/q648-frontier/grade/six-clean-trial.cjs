'use strict';

// In the six-helper host, affineProduct uses its clean carry as the digit
// selector. The separately embedded sign replay retains its own allocation.
const six = require('../upper/six.cjs');
const before = six.patch;
const clean = require('../upper/clean.cjs');
const short = require('../upper/short.cjs');
six.patch = source => short.patch(clean.patch(before(source)));
require('./six-reference-trial.cjs');
