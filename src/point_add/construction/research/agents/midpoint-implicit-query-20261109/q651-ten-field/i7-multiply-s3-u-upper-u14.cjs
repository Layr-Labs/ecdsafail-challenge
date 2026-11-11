'use strict';
// Apply exactly once after n651a q651-ten-field upper(raw).
exports.wholeStageFreed=false;
exports.sourceUpper=(s,options={})=>{
 s=require('./i7-multiply-s3-u-upper-u10.cjs').sourceUpper(s);
 s=require('./i7-multiply-s3-u-u8-trials.cjs').upper(s);
 s=require('./i7-multiply-s3-u-u9-carriers.cjs').upper(s);
 s=require('./i7-multiply-s3-u-u9-three.cjs').upper(s);
 s=require('./i7-multiply-s3-u-u14-opt.cjs').upper(s);
 // U11/U12/U13 must transform this pre-sink source, never install a sink.
 for(const overlay of options.overlays||[])s=overlay(s);
 return s;
};
exports.upper=(s,options={})=>require('./i7-multiply-s3-u-p-upper-peep.cjs').upper(exports.sourceUpper(s,options));
