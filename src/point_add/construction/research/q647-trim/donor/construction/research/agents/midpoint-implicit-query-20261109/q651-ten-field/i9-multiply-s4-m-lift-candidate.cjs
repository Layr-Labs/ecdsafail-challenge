'use strict';
const base=require('./i9-multiply-s4-m-prep-copy.cjs');
module.exports={source:base.source,f:s=>{
 // Avoid M5 virtual-enable override by selecting the partial source then applying prep transforms.
 let v=base.f(s),start=v.indexOf('\n less(c,arr,value,z){',v.indexOf('class LiftKit extends UnitWalk{')),end=v.indexOf('\n rows(g){',start);
 if(start<0||end<0)throw Error('virtual lift override anchor');
 v=v.slice(0,start)+v.slice(end);return require('./i9-multiply-s4-m-lift-count.cjs')(v);
}};
