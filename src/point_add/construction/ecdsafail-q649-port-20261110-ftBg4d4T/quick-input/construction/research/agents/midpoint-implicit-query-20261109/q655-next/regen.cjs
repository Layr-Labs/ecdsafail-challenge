'use strict';
const path=require('path'),Module=require('module');
const {checkedSource}=require('../field128-height-experiment/pinned.cjs');
const file=path.join(__dirname,'../field655-boundary/regen.cjs');
let src=checkedSource(file,'aa1d9c9b651ba8820c03ec6d63582d6eced50aca1df46d72a2007f4fd1084313');
function one(old,fix){if(src.split(old).length!==2)throw Error('regen source');src=src.replace(old,fix);}
one('this.aux=this.L[n+1];','this.aux=this.L[n+1];this.tst=this.R[n+1];');
one('park.yq=walk.R[0];scale.yq=walk.R[0];','park.yq=walk.R[0];scale.yq=walk.R[0];park.f=walk.R[1];scale.f=walk.R[1];');
one('if((op>>>20&1023)===656','if((op>>>20&1023)===655||(op>>>10&1023)===655||(op&1023)===655||(op>>>20&1023)===656');
const m=new Module(file,module);m.filename=file;m.paths=module.paths;m._compile(src,file);
module.exports=m.exports;
