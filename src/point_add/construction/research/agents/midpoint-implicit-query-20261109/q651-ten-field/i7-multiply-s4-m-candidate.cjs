'use strict';
const partial=require('./i7-multiply-s4-m-partial.cjs');
module.exports={source:partial.source,f:s=>require('./i7-multiply-s4-m-lift-eight.cjs')(partial.f(s))};
