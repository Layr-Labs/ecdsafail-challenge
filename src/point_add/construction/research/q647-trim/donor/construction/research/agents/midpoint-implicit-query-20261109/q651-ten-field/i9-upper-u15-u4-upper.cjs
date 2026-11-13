'use strict';
// Apply to n651a upper(raw), once. Preserve donor source hash checks.
exports.upper=s=>{
 s=require('./i9-upper-u15-upper-partial.cjs').upper(s);
 s=require('./i9-upper-u15-trial-carriers.cjs').upper(s);
 return require('./i9-upper-u15-probe-carriers.cjs').upper(s);
};
