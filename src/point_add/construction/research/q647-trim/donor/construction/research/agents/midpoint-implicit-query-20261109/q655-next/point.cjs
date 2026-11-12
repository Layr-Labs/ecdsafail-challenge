'use strict';
const fs=require('fs'),path=require('path'),Module=require('module');
const {joined,checkedSource}=require('../field128-height-experiment/pinned.cjs');
const {emitMultiplySparse,emitDivideSparse}=require('./backend.cjs');
const {emitRegenerateSparse}=require('./regen.cjs');
const original=path.join(joined,'checkpoint/export-native.cjs');
let exportSource=checkedSource(original,'6a97985e03c4eac477d53db57ad8818d1f31775f4488af2879d817c165c7d74d');
function once(src,from,to){
  if(src.split(from).length!==2)throw Error('ambiguous frozen coordinate expression: '+from);
  return src.replace(from,to);
}
function installUpper(src){
  src=once(src,'class UnguardedGeneral extends OddEstimateGeneral {',
  `class UnguardedGeneral extends OddEstimateGeneral {
    constructor(m,delta,k,width){
      super(m,delta,k,width);
      if(m!==256)throw Error("this release targets the full field");
      this.useCoefficientDirection=this.tag.length===this.tags.length;
      if(this.useCoefficientDirection){
        if(!this.layouts())throw Error("missing rounded-quotient layout");
        const top=this.tags.length-1,free=this.dv[1];
        this.tag[top]=free;this.tags[top]=free;
        this.dv=[this.dv[0],this.v[this.k]];
      }
    }
    trial(tape,witness,back){
      if(!this.useCoefficientDirection){super.trial(tape,witness,back);return;}
      const temp=Object.create(this);temp.dv=[this.dv[0],this.carry];
      const coeff=this.v[this.k],c=this.ctrl;
      const moved=rv=>{
        const steps=[r=>this.permute(tape,[this.carry,coeff],[coeff,this.carry],c,r),
          ()=>this.toggle(tape,c,[],this.carry)];
        stepList(steps,rv,fn=>fn(rv));
      };
      const dirs=()=>temp.direction(tape);
      const steps=[dirs,rv=>this.packNumber(tape,rv),moved,rv=>this.normalize(tape,rv)];
      for(const band of this.layouts())steps.push(rv=>witness?this.oddWitness(tape,band,rv):this.oddQuotient(tape,band,rv));
      steps.push(rv=>this.normalize(tape,!rv),rv=>moved(!rv),rv=>this.packNumber(tape,!rv),dirs);
      stepList(steps,back,fn=>fn(back));
    }`);
  src=once(src,'layer.pick=this.layouts()?this.dv[1]:this.tags.at(-1);layer.carry=this.take;',
    'layer.pick=this.layouts()?this.dv[1]:this.tags.at(-2);layer.carry=this.take;');
  src=once(src,'const ops=[rv=>this.mixed(tape,this.r.slice(0,base),S,D,[],rv),flip,extra,flip];',
    'const lease=()=>{if(this.useCoefficientDirection)tape.out(NONE,this.take,this.v[this.k]);};'+
    'const ops=[lease,rv=>this.mixed(tape,this.r.slice(0,base),S,D,[],rv),flip,extra,flip,lease];');
  src=once(src,'super(logical,[],l.g);const b=l.bank.length,m=l.m;',
    'super(logical,[],l.g);this.ids=this.ids.slice(0,-1);const b=l.bank.length,m=l.m;');
  src=once(src,'...split(2*m+b+1,logical-1)];','...split(2*m+b+1,logical-2)];');
  src=once(src,'if(new Set(map).size!==logical-1||map.length!==logical-1)','if(new Set(map).size!==logical-2||map.length!==logical-2)');
  src=once(src,'this.map=map;const wire=x=>x===NONE?NONE:map[x];',
    'this.map=map;const wire=x=>{if(x===NONE)return NONE;if(map[x]===undefined)throw Error("upper used removed physical site "+x);return map[x];};');
  src=once(src,'2*m+m/2+10+Math.ceil(Math.log2(m/2))+(extraEnable?1:0)',
    '2*m+m/2+8+Math.ceil(Math.log2(m/2))+(extraEnable?1:0)');
  src=once(src,'ids[i]=i===648?-2:clean[z++];return ids;',
    'ids[i]=(i===648||i>=655)?-2:clean[z++];if(clean.length!==14||z!==14)throw Error("Q655 field geometry");return ids;');
  src=once(src,'ids[645]=-2;let j=0;','ids[645]=-2;ids[655]=-2;ids[656]=-2;let j=0;');
  src=once(src,'const sink=nativeSink(tape,ids);emitter.regenerate(',
    'if(j!==14)throw Error("Q655 history geometry");const sink=nativeSink(tape,ids);emitter.regenerate(');
  return src;
}
exportSource=once(exportSource,"const {emitRegenerate}=require('../field/forward.cjs');",'const emitRegenerate=module.q655.regenerate;');
exportSource=once(exportSource,"const {emitMultiplyWithSign657,emitDivideWithSign657}=require('../../../../agents/midpoint-implicit-query-20261109/field656-clean-lease/index.cjs');",
  'const {forward:emitMultiplyWithSign657,divide:emitDivideWithSign657}=module.q655;');
exportSource=once(exportSource,"if(digest!==SOURCE_SHA)throw Error('wrong centered construction '+digest);",
  "if(digest!==SOURCE_SHA)throw Error('wrong centered construction '+digest);src=module.q655.upper(src);");
exportSource=once(exportSource,'this.quantumWidth=657','this.quantumWidth=655');
exportSource=once(exportSource,"if(width!==657)throw Error('wrong native width');","if(width!==655)throw Error('wrong native width');");
exportSource=once(exportSource,'Input-independent Q657 gate export','Input-independent Q655 gate export');
const api={upper:installUpper,forward:emitMultiplySparse,divide:emitDivideSparse,regenerate:emitRegenerateSparse};
const binding=new Module(original,module);binding.filename=original;binding.paths=module.paths;binding.q655=api;
binding._compile(exportSource,original);
if(!Array.prototype.flat)Object.defineProperty(Array.prototype,'flat',{configurable:true,writable:true,
  value:function flat(d=1){return d>0?[].concat(...this.map(x=>Array.isArray(x)?x.flat(d-1):x)):this.slice();}
});
if(!Object.fromEntries)Object.fromEntries=r=>Object.assign({},...r.map(([k,v])=>({[k]:v})));
const {GateWriter,arithmetic}=binding.exports;
module.exports={GateWriter,arithmetic,installUpper,forward:emitMultiplySparse,divide:emitDivideSparse,regenerate:emitRegenerateSparse};
if(require.main===module){
  const [mode,file]=process.argv.slice(2);
  if(!['raw','spans'].includes(mode)||!file||require('os').endianness()!=='LE')throw Error('use raw FILE or spans FILE');
  console.log(JSON.stringify(new GateWriter(mode==='raw'?file:null,mode==='spans'?file:undefined).produce(),null,2));
}
