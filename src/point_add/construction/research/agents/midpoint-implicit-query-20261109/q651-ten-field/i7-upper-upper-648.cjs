"use strict";
exports.wholeStageFreed=true; // final-source raw/sink bans and finite checks passed
const extensions={U21:require('./i7-upper-trials-u21.cjs').upper,U22:require('./i7-upper-u22-affine.cjs').upper,U23:s=>require('./i7-upper-late-u23.cjs').upper(require('./i7-upper-upper-u23.cjs').upper(s)),U24:require('./i7-upper-u25-glue-select.cjs').upper};
exports.sourceUpper=s=>require('./i7-upper-upper-u20.cjs').sourceUpper(s,{extensions,strict648:true});
exports.upper=s=>require('./i7-upper-upper-u20.cjs').upper(s,{extensions,strict648:true});
