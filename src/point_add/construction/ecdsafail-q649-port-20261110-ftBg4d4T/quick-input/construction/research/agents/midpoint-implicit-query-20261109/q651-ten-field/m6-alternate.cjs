'use strict';
const path=require('path'),candidate=require('./m6-candidate.cjs');
module.exports={f:candidate.f,source:(s,e)=>e(s,'class Walk extends pub.D2Canonical{constructor(n){super(n,6);}}',`const alt=published.withDigit(require(${JSON.stringify(path.join(__dirname,'m6-alternating.cjs'))}).alternatingDigit);const Walk=require(${JSON.stringify(path.join(__dirname,'m6-host-walk.cjs'))})(alt,5);`)};
