'use strict';
exports.wholeStageFreed=false;
exports.upper=s=>require('./i9-upper-u32-estimate.cjs').upper(require('./i9-upper-u32-debt.cjs').upper(require('./i9-upper-u32-glue.cjs').upper(s)));
