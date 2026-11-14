'use strict';
// Preload with node -r ./refinements.cjs before the ordinary circuit entry.
// The two field substitutions act on different stage modules.
const path = require('node:path');
const field = require('./field/index.cjs');
const owner = path.join(__dirname,'donor',field.family);
require('./field/decrement.cjs').install(owner);
require('./field/history-low.cjs').install(owner);
const upper = require('./upper/index.cjs');
const patch = upper.patch;
upper.patch = (...args) => {
    const withMarkers = require('./upper/marker.cjs').extend(patch(...args));
    return require('./alternate/unit/unit.cjs').patch(withMarkers);
};
