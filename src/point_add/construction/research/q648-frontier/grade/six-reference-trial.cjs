'use strict';

// Retain the earlier Q647 reverse trial at heights 96 through 106. The hybrid
// preload installs that trial before the optional borrowed-wire rewrite.
const witness = require('../../q648-next/unit/six/index.cjs');
witness.patch = source => source;
require('./six-extended.cjs');
