'use strict';
const path=require('path');
const {checkedSource,joined}=require('../field128-height-experiment/pinned.cjs');
const {CanonicalUnit,ReducedGcdWalk}=require('../field128-height-experiment/walks.cjs');
function replace(s,x,y) {
  if(s.split(x).length!==2)throw Error('ambiguous source needle '+x);
  return s.replace(x,y);
}

const f0=checkedSource(path.join(joined,'field/forward.cjs'),
  '7e7ac506467480fd3e2e064af32f98f11cd1cf177319178406a553d4ddf90239');
let f=replace(f0,'w=new FlatUnit(n)','w=new Replacement(n)');
// Every factor is positive. The whole intrinsic is called unconditionally.
f=replace(f,'color=647,outer=648,idx=','color=647,outer=null,idx=');
const nativeForward=Function('module','Replacement',f+'\nreturn emitForward128;')({exports:{}},CanonicalUnit);

let d=checkedSource(path.join(joined,'inverse/inverse.cjs'),
  'a566a7102a0ac0a50078cd4415312b4ae3f67ad62e6ceab0d31be92e19596f63');
// The initial fixed-one was inverted to obtain a local zero. Use an already
// clean bank pad at each individual consumer, so that wire can carry a sign.
d=replace(d,'put([[act]]);put(norm);','put(norm);');
d=replace(d,"put(rev(norm));put([[act]]);tap('complete')","put(rev(norm));tap('complete')");
d=replace(d,'temps=[act,e,t,x]','temps=[rm[1],e,t,x]');
d=replace(d,'const wi={sign:act,tag:S','const wi={sign:R[1],tag:S');
d=replace(d,'mulG(n,L,R,Q,act,[e,t],loan,sink);','mulG(n,L,R,Q,R[1],[e,t],loan,sink);');
d=replace(d,'parkOuter(n,M,rm,Q,S,p,bits,act,loan,sink);',
  'parkOuter(n,M,rm,Q,S,p,bits,R[1],loan,sink);');
d=replace(d,'parkOuter(n,M,rm,Q,S,p,bits,act,loan,sink,true);',
  'parkOuter(n,M,rm,Q,S,p,bits,L[n],loan,sink,true);');
d=replace(d,'perm=w=>w===base+1?act:w===base+2?e:w',
  'perm=w=>w===base+1?L[n]:w===base+2?e:w');
const nativeInverse=Function('module',d+'\nreturn inverseField;')({exports:{}});

function portSink(sink,dense) {
  const ports=new Int16Array(1024);ports.fill(-1);ports[1023]=1023;
  for(let q=0;q<=656;q++)if(q!==648)ports[q]=dense && q>648 ? q-1 : q;
  function map(q){const v=ports[q];if(v===undefined||v<0)throw Error('sign or invalid port '+q);return v;}
  return (kind,data)=>{
    if(kind==='packed'){
      const g=new Uint32Array(data.length);
      for(let i=0;i<data.length;i++){
        const v=data[i];g[i]=(map((v>>>20)&1023)<<20)|(map((v>>>10)&1023)<<10)|map(v&1023);
      }
      sink(kind,g);
    }else if(kind==='nct')sink(kind,data.map(row=>row.map(map)));
    else{
      const last=data.length-1;
      sink(kind,data.map((x,i)=>i===last?x:map(x)));
    }
  };
}
function emitMultiply656(sink){nativeForward(portSink(sink,true));}
function emitDivide656(sink){nativeInverse(128,ReducedGcdWalk,CanonicalUnit,portSink(sink,true));}
function emitMultiplyWithSign657(sink){nativeForward(portSink(sink,false));}
function emitDivideWithSign657(sink){nativeInverse(128,ReducedGcdWalk,CanonicalUnit,portSink(sink,false));}
module.exports={emitMultiply656,emitDivide656,emitMultiplyWithSign657,emitDivideWithSign657};
