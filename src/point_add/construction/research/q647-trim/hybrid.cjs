'use strict';
// The transplants run only in reverse phase-probe windows with the named
// evicted helper. The caller still owns the complete six-helper row.
const upper = require('./upper/integrated.cjs');
const hybrid = require('./hybrid/index.cjs');
const original = upper.patch;
upper.patch = (...args) => hybrid.patch(original(...args));
