'use strict';
const partial=require('./m6-partial.cjs');
module.exports={source:partial.source,f:s=>require('./m6-lift-eight.cjs')(partial.f(s))};
