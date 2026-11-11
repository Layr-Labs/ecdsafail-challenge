'use strict';
const path=require('path'),Module=require('module');
const {checkedSource}=require('../field128-height-experiment/pinned.cjs');
const file=path.join(__dirname,'../q655-next/backend.cjs');
let src=checkedSource(file,'988f67ac4f950a0320a1cdfb6854a5c829b98ba1b44097c62750fd332fa63e88');
function change(x,y){if(src.split(x).length!==2)throw Error('ambiguous field source '+x);src=src.replace(x,y);}
// Transition between adjacent intervals using their symmetric difference.
// Each expensive zero-prefix comparator now occurs twice across the sweep.
change('const interval=1<<J.length;','const interval=1<<J.length;let previous=[];');
change('const mark=prefix(a).concat(prefix(b));\n    gates=gates.concat(mark);',
 'const current=[a,b].filter(k=>k<n);for(const k of previous)if(!current.includes(k))gates=gates.concat(prefix(k));'+
 'for(const k of current)if(!previous.includes(k))gates=gates.concat(prefix(k));previous=current;');
change('gates=gates.concat(mark.reverse());','');
change('gates.push([groupBit]);','for(const k of previous)gates=gates.concat(prefix(k));\n  gates.push([groupBit]);');
// Height t already has its own clean pad below the first t coefficient
// cells. Every unselected modular deposit is guarded and its NR pair cancels.
change(" 'moveGcdPad(n,L,vt,rm[1],loan,sink,false,{flagHeight,fr});outerloadJ(n,terms,L,R,Q,sig,loan,[rm[1],e,t,L[0]],sink);moveGcdPad(n,L,vt,rm[1],loan,sink,true,{flagHeight,fr});');",
 " 'outerloadJ(n,terms,L,R,Q,sig,loan,[rm[1],e,t,L[0]],sink);');\n"+
 "d=replace(d,'t,data,pad,tmp,sp,e,sink);if(t>1)','t,data,L[n+1-t],tmp,sp,e,sink);if(t>1)');");
const m=new Module(file,module);m.filename=file;m.paths=module.paths;m._compile(src,file);module.exports=m.exports;
