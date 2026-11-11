"use strict";
// Apply once after n651a q651-ten-field upper(raw). All changes precede one sink.
exports.wholeStageFreed=true;
exports.sourceUpper=s=>require('./i7-upper-u15-upper-helper-map.cjs').upper(require('./i7-upper-u15-upper-u14.cjs').sourceUpper(s,{overlays:[require('./i7-upper-u15-u11-witness.cjs').upper,require('./i7-upper-u15-u12-carrier.cjs').upper]}));
exports.upper=s=>require('./i7-upper-u15-p-upper-peep.cjs').upper(exports.sourceUpper(s));
