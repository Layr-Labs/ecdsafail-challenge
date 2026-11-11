'use strict';
const path=require('path'),candidate=require('./i7-multiply-s4-m-candidate.cjs');
module.exports={f:candidate.f,source:(s,e)=>e(s,'class Walk extends pub.D2Canonical{constructor(n){super(n,6);}}',`const alt=published.withDigit(require(${JSON.stringify(path.join(__dirname,'alternating.cjs'))}).alternatingDigit);const Walk=require(${JSON.stringify(path.join(__dirname,'host-walk.cjs'))})(alt,5);`)};
