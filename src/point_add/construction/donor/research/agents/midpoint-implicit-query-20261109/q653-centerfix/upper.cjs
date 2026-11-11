'use strict';
const path=require('path'),Module=require('module');
const {joined,checkedSource}=require('../field128-height-experiment/pinned.cjs');
const {replace}=require('../q653-next/parts.cjs');
function upper(s){
  s=require('../q653-next/upper.cjs').upper(s);
  s=replace(s,'layer.tags[4]=this.r.at(-1);layer.r=this.r.slice(0,-1);','layer.tags[4]=this.r.at(-1);layer.r=this.r.slice(0,-1);layer.centeredFree=true;');
  s=replace(s,'const a=D[i+this.h-1-base],b=this.r[i],mark=','const a=D[i+this.h-1-base+(this.centeredFree?1:0)],b=this.r[i],mark=');
  s=replace(s,'this.constBelow(tape,word,this.p,this.ctrl,[target]);','this.constBelow(tape,word,this.centeredFree?this.p-(1n<<BigInt(this.k)):this.p,this.ctrl,[target]);');
  return s;
}
function upperComponent(){const f=path.join(joined,'checkpoint/centered-point.cjs');const m=new Module(f,module);m.filename=f;m.paths=module.paths;m._compile(upper(checkedSource(f,'10790de4c79338419f92a5a2fd72017c829fc94900fe053627884cddc568283a')),f);return m.exports;}
module.exports={upper,upperComponent};
