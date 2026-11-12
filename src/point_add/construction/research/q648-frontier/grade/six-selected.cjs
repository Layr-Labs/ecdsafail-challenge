'use strict';

// The coefficient rewrite hooks the field source before its six-helper installation.
require('../field/preload.cjs');
require('../six/ripple.cjs');
require('../field/after647.cjs');
const unit = require('../../q648-trim/alternate/unit/unit.cjs');
const prior = unit.patch;
unit.patch = (...args) => require('../upper/six.cjs').patch(prior(...args));
