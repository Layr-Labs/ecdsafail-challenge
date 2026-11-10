'use strict';
const pub=require('./public-backend.cjs').withDigit(require('./shared-digit.cjs').sharedDigit);
const d=require('./divide-650.cjs').build(pub);
exports.emitDivideSparse=sink=>d.emitDivideSparse(sink);
