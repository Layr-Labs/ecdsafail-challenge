"use strict";
// U24 is cheaper and directly 648-compatible only at selected rows124..126.
exports.upper=s=>{
 s=require('./i9-upper-u24-glue.cjs').upper(s);
 const a='if(this.k>=113&&this.k<=126){this.u24Core(tape,back);return;}';
 if(s.split(a).length!==2)throw Error('U25 selected glue anchor');
 return s.replace(a,'if(this.k>=124&&this.k<=126){this.u24Core(tape,back);return;}');
};
