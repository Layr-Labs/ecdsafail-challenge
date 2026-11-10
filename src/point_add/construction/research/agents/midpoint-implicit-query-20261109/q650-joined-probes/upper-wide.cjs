'use strict';
const old=require('./upper.cjs'),{addWideTransforms}=require('./wide.cjs');
module.exports={upper:raw=>addWideTransforms(old.upper(raw))};
