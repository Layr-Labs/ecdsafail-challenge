'use strict';
// Apply to n651a upper(raw), once. Preserve donor source hash checks.
exports.upper=s=>{
 s=require('./i7-multiply-s3-u-upper-partial.cjs').upper(s);
 s=require('./i7-multiply-s3-u-trial-carriers.cjs').upper(s);
 return require('./i7-multiply-s3-u-probe-carriers.cjs').upper(s);
};
