"use strict";
// Apply once after n651a q651-ten-field upper(raw). All changes precede one sink.
exports.wholeStageFreed=false;
exports.sourceUpper=s=>require('./i7-multiply-s3-u-upper-helper-map.cjs').upper(require('./i7-multiply-s3-u-upper-u14.cjs').sourceUpper(s,{overlays:[require('./i7-multiply-s3-u-u11-witness.cjs').upper,require('./i7-multiply-s3-u-u12-carrier.cjs').upper]}));
const old=exports.sourceUpper;
exports.sourceUpper=s=>require('./i7-multiply-s3-u-s3-arithmetic.cjs').upper(require('./i7-multiply-s4-u-probe-compact.cjs').upper(old(s)),['perm','wide','top']);
exports.upper=s=>require('./i7-multiply-s3-u-p-upper-peep.cjs').upper(exports.sourceUpper(s));
