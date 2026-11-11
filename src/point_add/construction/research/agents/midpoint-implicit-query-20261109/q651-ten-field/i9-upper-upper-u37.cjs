'use strict';
exports.wholeStageFreed=false;
const base=require('./i9-upper-upper-u20.cjs');
const extensions={U21:require('./i9-upper-trials-u21.cjs').upper,U22:require('./i9-upper-u22-affine.cjs').upper,U23:s=>require('./i9-upper-late-u23.cjs').upper(require('./i9-upper-upper-u23.cjs').upper(s)),U24:require('./i9-upper-u25-glue-select.cjs').upper};
function options(opts={}){return {extensions,strict648:true,overlays:[require('./i9-upper-u28-unit.cjs').upper,require('./i9-upper-u32-family.cjs').upper,require('./i9-upper-u30-trials.cjs').upper,require('./i9-upper-u29-dense.cjs').upper,require('./i9-upper-crop-affine.cjs').upper,require('./i9-upper-u31-affine.cjs').upper,...(opts.overlays||[])]};}
exports.sourceUpper=(s,opts)=>base.sourceUpper(s,options(opts));
exports.upper=(s,opts)=>base.upper(s,options(opts));
exports.sourceUpperAllocated=(s,opts={})=>require('./i9-upper-u37-allocator.cjs').upper(exports.sourceUpper(s,opts),opts);
exports.upperAllocated=(s,opts={})=>require('./i9-upper-u37-allocator.cjs').upper(exports.upper(s,opts),opts);
exports.sourceUpper647=(s,opts={})=>exports.sourceUpperAllocated(s,{...opts,strict:true});
exports.upper647=(s,opts={})=>exports.upperAllocated(s,{...opts,strict:true});
