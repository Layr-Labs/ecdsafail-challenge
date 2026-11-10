'use strict';
// Apply to n651a upper(raw), once. Preserve donor source hash checks.
exports.upper=s=>{
 s=require('./upper-partial.cjs').upper(s);
 s=require('./trial-carriers.cjs').upper(s);
 return require('./probe-carriers.cjs').upper(s);
};
