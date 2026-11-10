'use strict';
const path=require('path');
const config=require(process.env.TRACK_I_CONFIG?path.resolve(process.env.TRACK_I_CONFIG):'./stage-config.json');
const pub=require('./public-backend.cjs').withDigit(require('./shared-digit.cjs').sharedDigit);
const d=require(config.divideEntry).build(pub);
exports.emitDivideSparse=sink=>d.emitDivideSparse(sink);
