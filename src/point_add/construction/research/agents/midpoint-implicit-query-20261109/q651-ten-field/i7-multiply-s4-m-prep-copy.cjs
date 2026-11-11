'use strict';
// H is clean at prep entry. First modular add is exactly a residue copy.
const base=require('./i7-multiply-s4-m-prep-relay.cjs');
module.exports={source:base.source,f:s=>{s=base.f(s);const a='[[hole]],[[hole]],ops,md,inv,[[hole]],add,ops',b='[[hole]],[[hole]],ops,R.slice(0,128).map((q,i)=>[q,H[i]]),inv,[[hole]],add,ops';if(s.split(a).length!==2)throw Error('prep copy anchor');return s.replace(a,()=>b);}};
