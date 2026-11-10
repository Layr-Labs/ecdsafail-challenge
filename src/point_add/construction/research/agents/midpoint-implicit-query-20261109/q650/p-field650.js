'use strict';
// q650 field list (hole): multiply (q650/mul, papers) + divide rewrites (q650/div, evict).
// div/p-field-div.js = [...q651/p-field651.js, hook]; we take its hook and append it after the multiply list.
const base=require('../q651/p-field651.js'),div=require('./div/p-field-div.js'),mul=require('./mul/p-field-mul650.js');
const hook=div.slice(base.length);
if(hook.length<1||div.length!==base.length+hook.length||base.some((e,i)=>div[i][0]!==e[0]||div[i][1]!==e[1]))throw Error('q650 field: divide list is not q651 + hooks');
if(mul.length<base.length||base.some((e,i)=>mul[i][0]!==e[0]||mul[i][1]!==e[1]))throw Error('q650 field: multiply list is not q651 + patches');
module.exports=[...mul,...hook];
