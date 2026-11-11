'use strict';
// Apply to n651a q651-ten-field upper(raw), exactly once. Nine-helper ABI retained.
exports.wholeStageFreed=false;
exports.sourceUpper=(s,options={})=>{
 s=require('./i7-multiply-s3-u-u4-upper.cjs').upper(s);
 for(const f of ['i7-multiply-s3-u-p650-coef.js','i7-multiply-s3-u-p650-tail.js'])for(const [a,b]of require('./'+f)){if(s.split(a).length!==2)throw Error('U10 S1 anchor');s=s.replace(a,b);}
 s=require('./i7-multiply-s3-u-second-carriers.cjs').upper(s);
 s=require('./i7-multiply-s3-u-u6-carriers.cjs').upper(s,options);
 s=require('./i7-multiply-s3-u-u6-probes.cjs').upper(s);
 s=require('./i7-multiply-s3-u-u6-double.cjs').upper(s);
 s=require('./i7-multiply-s3-u-late-second-carriers.cjs').upper(s);
 s=require('./i7-multiply-s3-u-u10-opt.cjs').upper(s);
 for(const overlay of options.overlays||[])s=overlay(s);
 return s;
};
exports.upper=(s,options={})=>require('./i7-multiply-s3-u-p-upper-peep.cjs').upper(exports.sourceUpper(s,options));
