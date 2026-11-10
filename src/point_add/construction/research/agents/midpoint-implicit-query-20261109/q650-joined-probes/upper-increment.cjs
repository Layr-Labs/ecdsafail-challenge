'use strict';
const base=require('./upper-wide.cjs'),{patchIncrement}=require('./increment.cjs');
module.exports={upper:raw=>patchIncrement(base.upper(raw))};
