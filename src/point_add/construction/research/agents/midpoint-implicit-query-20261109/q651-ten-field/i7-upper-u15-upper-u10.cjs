'use strict';
// Apply to n651a q651-ten-field upper(raw), exactly once. Nine-helper ABI retained.
exports.wholeStageFreed=false;
exports.sourceUpper=(s,options={})=>{
 s=require('./i7-upper-u15-u4-upper.cjs').upper(s);
 for(const f of ['i7-upper-u15-p650-coef.js','i7-upper-u15-p650-tail.js'])for(const [a,b]of require('./'+f)){if(s.split(a).length!==2)throw Error('U10 S1 anchor');s=s.replace(a,b);}
 s=require('./i7-upper-u15-second-carriers.cjs').upper(s);
 s=require('./i7-upper-u15-u6-carriers.cjs').upper(s,options);
 s=require('./i7-upper-u15-u6-probes.cjs').upper(s);
 s=require('./i7-upper-u15-u6-double.cjs').upper(s);
 s=require('./i7-upper-u15-late-second-carriers.cjs').upper(s);
 s=require('./i7-upper-u15-u10-opt.cjs').upper(s);
 for(const overlay of options.overlays||[])s=overlay(s);
 return s;
};
exports.upper=(s,options={})=>require('./i7-upper-u15-p-upper-peep.cjs').upper(exports.sourceUpper(s,options));
