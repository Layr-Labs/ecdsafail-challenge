'use strict';
// Load the history.regenerate generator with a given patch list, plus a stage hook for census/simulation.
// HOOK: globalThis.__rgStage(index,label) is called before each of the seven stage windows.
const path=require('path');
const {patched}=require('../../q651/overlay.cjs');
const hook=['const m=new Module(file,module);',
 's=replace(s,"for(const [g,blocks,back] of stages){","let __si=0;for(const [g,blocks,back] of stages){if(globalThis.__rgStage)globalThis.__rgStage(__si++,g===walk?\'walk\':g===park?\'park\':g===scale?\'scale\':\'walk6\',blocks.length);");const m=new Module(file,module);'];
function loadRegen(patchFile,{instrument=true}={}){
  const list=patchFile?require(path.resolve(patchFile)).slice():[];
  if(instrument)list.push(hook);
  return patched('q653-next/regen.cjs',list);
}
module.exports={loadRegen};
