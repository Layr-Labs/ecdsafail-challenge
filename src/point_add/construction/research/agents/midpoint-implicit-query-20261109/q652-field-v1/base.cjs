'use strict';
const path=require('node:path'),Module=require('node:module');
const {checkedSource}=require('../field128-height-experiment/pinned.cjs');
const file=path.resolve(__dirname,'../q653-next/backend.cjs');
const source=checkedSource(file,'7672c89cb5628dc9aa613ad3844bca1d5bd78da23a8dec1c075b9e0f6f69c695');
const m=new Module(file,module);m.filename=file;m.paths=Module._nodeModulePaths(path.dirname(file));
m._compile(source+'\nmodule.exports={f,d,VirtualCanonical,SectorReduced,SectorCanonical,emitWalk,dirtyDigit,dirtyMdg,dirtyBlock,lowValuationSweep,plusOneMod,replace};',file);
module.exports=m.exports;
