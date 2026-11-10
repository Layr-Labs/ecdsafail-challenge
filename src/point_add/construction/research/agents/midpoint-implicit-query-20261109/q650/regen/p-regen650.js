'use strict';
// Complete standalone replacement list for history.regenerate at 650: the 651 list, then one injection that routes
// emitRegenerateSparse to q650/regen/regen650.cjs (the 651 body is kept as emitRegenerate651, unused).
module.exports=require('../../q651/regen/p-regen651.js').concat([
  [
    "const m=new Module(file,module);",
    "s=replace(s,\"function emitRegenerateSparse(sink,erase=false){\",\"const Q650=require('../q650/regen/regen650.cjs')({UnitPark,Terminal,terms,Signed,TopHost,UnitWalk:Object.getPrototypeOf(Signed.prototype).constructor});\\nfunction emitRegenerateSparse(sink,erase=false){return Q650.emit(sink,erase);}\\nfunction emitRegenerate651(sink,erase=false){\");const m=new Module(file,module);"
  ]
]);
