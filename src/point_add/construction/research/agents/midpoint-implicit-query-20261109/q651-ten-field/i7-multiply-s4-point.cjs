'use strict';
const path=require('node:path'),Module=require('node:module');
const {checkedSource}=require('../field128-height-experiment/pinned.cjs');
const {replace}=require('../q653-next/parts.cjs');
const config=require(process.env.TRACK_I_CONFIG?path.resolve(process.env.TRACK_I_CONFIG):'./i7-multiply-s4-stage-config.json');
require('./i7-multiply-s4-stage-map.cjs').validate(config);
const divEntry=require(config.divideEntry);
if(divEntry.wholeStageFreed===false&&!(config.width>=650&&config.stages.divide.logical.length===9&&divEntry.status==='nine-helper operation saving; Q649 OPEN'))throw Error('divider helper requirement is not admitted by this configuration');
const base=path.join(__dirname,'../q653-next/point.cjs');
let s=checkedSource(base,'d850d912b5144bcd47227ff187d4118977dbe23665922a34eecefbe78ff74115');
s=replace(s,"'this.quantumWidth=653'",JSON.stringify('this.quantumWidth='+config.width));
s=replace(s,"'if(width!==653)'",JSON.stringify('if(width!=='+config.width+')'));
s=replace(s,"'Input-independent Q653 gate export'",JSON.stringify('Input-independent Q'+config.width+' gate export'));
s=replace(s,"m.field=require('./backend.cjs');m.history=require('./regen.cjs');m.upper=require('./upper.cjs').upper;",
 'm.field=module.field;m.history=module.history;m.upper=module.upper;');
const m=new Module(base,module);m.filename=base;m.paths=Module._nodeModulePaths(path.dirname(base));
m.field={emitMultiplySparse:require(config.multiplyModule).emitMultiplySparse,emitDivideSparse:require(config.divideModule).emitDivideSparse};
m.history=require(config.historyModule);m.upper=raw=>require('./i7-multiply-s4-stage-map.cjs').upper(raw,config);
m._compile(s,base);
class GateWriter extends m.exports.GateWriter{
 emit(k,a=65535,b=65535,c=65535){
  const ports=k===13?[a,b,c]:k===8||k===9?[a,b]:[6,7,12].includes(k)?[a]:k===2?[b]:[];
  for(const w of ports)if(!Number.isInteger(w)||w<0||w>=config.width)throw Error('PHYSICAL WIDTH BAN '+w+' at op '+this.total);
  super.emit(k,a,b,c);
 }
 produce(back=false){
  if(!back)return super.produce();
  this.registers();const wrap=(label,operator)=>!this.log?operator:(...args)=>this.log.span(label,false,()=>operator(...args));
  m.exports.arithmetic(this.log).shellWithFieldOracles(256,(1n<<32n)+977n,[],true,
   {forward:wrap('short.multiply',m.exports.forward),regenerate:wrap('history.regenerate',m.exports.regenerate)},
   wrap('short.divide',m.exports.divide),'random',false,this.hooks());
  this.flush();if(this.file!==null)require('fs').closeSync(this.file);if(this.log)this.log.close();
  return {kind:'Input-independent inverse Q'+config.width+' gate export',wordsPerOp:4,opWordBits:16,width:this.quantumWidth,classicalBits:this.classicalPeak,counts:this.kinds,ops:this.total};
 }
}
module.exports={...m.exports,GateWriter,config};
if(require.main===module){const [mode,file]=process.argv.slice(2);if(!['raw','spans'].includes(mode)||!file||require('os').endianness()!=='LE')throw Error('Use raw FILE or spans FILE');console.log(JSON.stringify(new GateWriter(mode==='raw'?file:null,mode==='spans'?file:undefined).produce(),null,2));}
