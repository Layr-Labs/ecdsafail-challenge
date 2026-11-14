"use strict";
// Apply once after n651a q651-ten-field upper(raw). All changes precede one sink.
exports.wholeStageFreed=true;
exports.sourceUpper=s=>require('./u-upper-helper-map.cjs').upper(require('./u-upper-u14.cjs').sourceUpper(s,{overlays:[require('./u-u11-witness.cjs').upper,require('./u-u12-carrier.cjs').upper]}));
exports.upper=s=>require('./u-p-upper-peep.cjs').upper(exports.sourceUpper(s));
