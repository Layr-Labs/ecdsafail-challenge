'use strict';
const path=require('path'),Module=require('module');
const {joined,checkedSource}=require('../field128-height-experiment/pinned.cjs');
const {emitMultiplySparse,emitDivideSparse}=require('./index.cjs');
const {emitRegenerateSparse}=require('./regen.cjs');
const original=path.join(joined,'checkpoint/export-native.cjs');
let source=checkedSource(original,'6a97985e03c4eac477d53db57ad8818d1f31775f4488af2879d817c165c7d74d');
function once(text,old,next){
  if(text.split(old).length!==2)throw Error('ambiguous frozen construction: '+old);
  return text.replace(old,next);
}
function resize(text){
  // Only the outer point carrier shrinks. Its Euclidean emitter already
  // folds a fixed-one logical wire, which reduces 657 logical sites to 656.
  text=once(text,'2*m+m/2+10+Math.ceil(Math.log2(m/2))+(extraEnable?1:0)',
    '2*m+m/2+9+Math.ceil(Math.log2(m/2))+(extraEnable?1:0)');
  text=once(text,'ids[i]=i===648?-2:clean[z++];return ids;',
    'ids[i]=(i===648||i===656)?-2:clean[z++];if(clean.length!==15||z!==15)throw Error("Q656 factor geometry");return ids;');
  text=once(text,'ids[645]=-2;let j=0;','ids[645]=-2;ids[656]=-2;let j=0;');
  text=once(text,'const sink=nativeSink(tape,ids);emitter.regenerate(',
    'if(j!==15)throw Error("Q656 regeneration geometry");const sink=nativeSink(tape,ids);emitter.regenerate(');
  return text;
}
source=once(source,"const {emitRegenerate}=require('../field/forward.cjs');",'const emitRegenerate=module.q656.regenerate;');
source=once(source,"const {emitMultiplyWithSign657,emitDivideWithSign657}=require('../../../../agents/midpoint-implicit-query-20261109/field656-clean-lease/index.cjs');",
  'const {forward:emitMultiplyWithSign657,divide:emitDivideWithSign657}=module.q656;');
source=once(source,"if(digest!==SOURCE_SHA)throw Error('wrong centered construction '+digest);",
  "if(digest!==SOURCE_SHA)throw Error('wrong centered construction '+digest);src=module.q656.resize(src);");
source=once(source,'this.quantumWidth=657','this.quantumWidth=656');
source=once(source,"if(width!==657)throw Error('wrong native width');","if(width!==656)throw Error('wrong native width');");
source=once(source,'Input-independent Q657 gate export','Input-independent Q656 gate export');
const q656={resize,forward:emitMultiplySparse,divide:emitDivideSparse,regenerate:emitRegenerateSparse};
const binding=new Module(original,module);binding.filename=original;binding.paths=module.paths;binding.q656=q656;
binding._compile(source,original);
if(typeof Array.prototype.flat!=='function')Object.defineProperty(Array.prototype,'flat',{
  configurable:true,writable:true,value:function flat(depth=1){return depth>0?[].concat(...this.map(x=>Array.isArray(x)?x.flat(depth-1):x)):this.slice();}
});
if(typeof Object.fromEntries!=='function')Object.fromEntries=rows=>Object.assign({},...rows.map(([k,v])=>({[k]:v})));
const {arithmetic,GateWriter}=binding.exports;
module.exports={arithmetic,GateWriter,forward:emitMultiplySparse,divide:emitDivideSparse,regenerate:emitRegenerateSparse};
if(require.main===module){
  const [mode,dest]=process.argv.slice(2);
  if(!['raw','spans'].includes(mode)||!dest||require('os').endianness()!=='LE')throw Error('use raw FILE or spans FILE on little-endian hardware');
  const writer=new GateWriter(mode==='raw'?dest:null,mode==='spans'?dest:undefined);
  console.log(JSON.stringify(writer.produce(),null,2));
}
