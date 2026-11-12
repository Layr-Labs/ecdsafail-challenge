'use strict';
// r35 merged field patch (ours): multiply at 11 helper sites (mul/p-mul652.js) + divide at 11 helper sites
// (p-div10.js / div10-rewrite.cjs). Neither field stage touches physical 652.
//  multiply: logical 640..647,649,650,651 mapped identically (logical 655 is no longer used).
//  divide:   logical 653 -> physical 647 (logical 647 is no longer used by the divide).
const FREE="const free=back?[648,652,654,655,656]:[648,652,653,654,656],move=back?653:655;";
const mul=require('./mul/p-mul652.js').filter(e=>e[0]!==FREE);
if(mul.length!==require('./mul/p-mul652.js').length-1)throw Error('mul free anchor');
module.exports=mul.concat([
 [FREE,"const free=back?[647,648,652,654,655,656]:[648,652,653,654,655,656],move=back?653:-1;"],
 ["ids[i]=i===move?652:i;","ids[i]=i===move?647:i;"],
 ["const divide=Function('module',","d=require('../q652/div10-rewrite.cjs')(d);const divide=Function('module',"],
]);
