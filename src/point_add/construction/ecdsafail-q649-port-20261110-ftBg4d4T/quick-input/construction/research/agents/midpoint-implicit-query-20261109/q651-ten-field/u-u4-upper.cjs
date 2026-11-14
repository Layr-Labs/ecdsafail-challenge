'use strict';
// Apply to n651a upper(raw), once. Preserve donor source hash checks.
exports.upper=s=>{
 s=require('./u-upper-partial.cjs').upper(s);
 s=require('./u-trial-carriers.cjs').upper(s);
 return require('./u-probe-carriers.cjs').upper(s);
};
