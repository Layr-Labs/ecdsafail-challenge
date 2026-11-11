'use strict';
const base=require('./i9-upper-upper-u37.cjs');
const probe=require('./i9-upper-u41-selected.cjs'),early=require('./i9-upper-u38-witness.cjs'),late=require('./i9-upper-u39-late.cjs');
exports.wholeStageFreed=false;
// Self-contained: serialized by U37, hence no captured module variables.
exports.select=w=>{
 if(w.kind==='signProbe'&&w.phaseHost!==w.args[0]&&((w.k===112&&!w.back&&w.args[0]===644)||(w.k===113&&(w.args[0]===644||w.args[0]===370))||(w.k===114&&w.args[0]===371)))return {evict:643};
 if(w.kind==='affine')return {evict:642};
 if(w.kind==='trial'&&w.args[0]===true&&w.k<=112)return {evict:642};
 if(w.kind==='signProbe'&&((w.k<=111&&!w.back&&w.args[0]===644)||(w.k===114&&w.args[0]===644)||(w.k>=115&&w.k<=124)))return {evict:643};
 return null;
};
function options(opts={}){return {...opts,overlays:[require('./i9-upper-u36-affine.cjs').upper,probe.upper,require('./i9-upper-u40-probe-api.cjs').upper,require('./i9-upper-u44-last-seven.cjs').upper,require('./i9-upper-u35-direction.cjs').upper,early.upper,late.upper,require('./i9-upper-u42-witness.cjs').upper,require('./i9-upper-u43-late.cjs').upper,require('./i9-upper-u40-rank.cjs').upper,...(opts.overlays||[])],selectors:[...(opts.selectors||[]),exports.select]};}
for(const name of ['upper','sourceUpper','upperAllocated','sourceUpperAllocated','upper647','sourceUpper647'])exports[name]=(s,opts)=>base[name](s,options(opts));
