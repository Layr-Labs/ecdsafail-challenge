'use strict';
// M9 complete six-helper multiply source overlay. Exactly one inherited final sink.
const base=require('./i9-multiply-m9-base.cjs');
const pub=require('./public-backend.cjs').withDigit(require('./shared-digit.cjs').sharedDigit);
const stage=require('./i9-multiply-m9-build.cjs')(base,pub,require('./i9-multiply-s4-sink.cjs').wrapSparse);
module.exports={...stage,emitDivideSparse:base.emitDivideSparse,status:'six-helper candidate; see M9 RESULT.md for qualification'};
