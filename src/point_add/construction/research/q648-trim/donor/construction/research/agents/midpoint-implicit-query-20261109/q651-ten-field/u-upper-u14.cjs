'use strict';
// Apply exactly once after n651a q651-ten-field upper(raw).
exports.wholeStageFreed=false;
exports.sourceUpper=(s,options={})=>{
 s=require('./u-upper-u10.cjs').sourceUpper(s);
 s=require('./u-u8-trials.cjs').upper(s);
 s=require('./u-u9-carriers.cjs').upper(s);
 s=require('./u-u9-three.cjs').upper(s);
 s=require('./u-u14-opt.cjs').upper(s);
 // U11/U12/U13 must transform this pre-sink source, never install a sink.
 for(const overlay of options.overlays||[])s=overlay(s);
 return s;
};
exports.upper=(s,options={})=>require('./u-p-upper-peep.cjs').upper(exports.sourceUpper(s,options));
