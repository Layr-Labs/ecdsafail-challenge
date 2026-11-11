'use strict';
module.exports=s=>{
 s=require('./i7-multiply-s4-m-power-final.cjs').f(s);
 const edit=(a,b)=>{if(s.split(a).length!==2)throw Error('M7 map anchor '+a);s=s.replace(a,()=>b);};
 edit('m[W.L[n]]=647;m[W.R[n]]=645;m[W.tst]=643;m[W.fire]=646;','m[W.L[n]]=646;m[W.R[n]]=644;m[W.tst]=642;m[W.fire]=645;');
 edit('m[W.sign]=640+tg.length;m[W.aux]=641+tg.length;','m[W.sign]=643;m[W.aux]=644;');
 edit('if(q===G.tag.at(-2))q=block.tagPort;','if(q===G.tag.at(-3)&&block.extraPort!==null&&block.extraPort!==undefined)q=block.extraPort;else if(q===G.tag.at(-2))q=block.tagPort;');
 return require('./i7-multiply-s4-m-color-seven.cjs')(require('./i7-multiply-s4-m-power-seven.cjs')(require('./i7-multiply-s4-m-lift-seven.cjs')(s)));
};
