'use strict';
// r35 regenerate stage at 11 helper sites (ours). R35_REGEN patch list for scratch/r35/point.cjs: [from,to] pairs
// applied to the text of nasqret's q653-next/regen.cjs. `inner` adds one more replace() on the q654 regenerate
// text; the last entry edits the 653 unused-site check directly. Logical site 651 is never touched.
//  1. walk = SectorSigned(n,5) (nasqret's own knob): the walk's top tag 651 is the row's topPort.
//  2. park and scale tag[4] move to the walk sign site 646 (clean in park; emptied before scale).
//  3. scale: the sign waits on R[0] (130); yq is hosted on M's top wire (132), which is 1 after norm for v>=1
//     and is cleared by one X; every adder with M as addend takes the constant 1 as M's top bit.
const ANCH="const m=new Module(file,module);";
const inner=(a,b)=>[ANCH,'s=replace(s,'+JSON.stringify(a)+','+JSON.stringify(b)+');'+ANCH];
const maj='const x=a[i],y=b[i],v=i?a[i-1]:cin;this.raw(x,-1,y);this.raw(x,-1,v);this.raw(v,y,x);';
const cls=`class TopHost extends Terminal{
 add(ctrl,a,b,cin,cout){
  if(a!==this.M){super.add(ctrl,a,b,cin,cout);return;}
  const t=a.length-1,w=a[t-1],z=b[t],cc=ctrl.filter(q=>q!==this.E);
  for(let i=0;i<t;i++){${maj}}
  if(!ctrl.length){
   if(cout!==null){this.raw(-1,-1,z);this.raw(-1,-1,w);this.raw(-1,-1,cout);this.raw(w,z,cout);this.raw(-1,-1,w);this.raw(w,-1,z);}
   else{this.raw(-1,-1,z);this.raw(w,-1,z);}
   for(let i=t;i--;){const x=a[i],y=b[i],v=i?a[i-1]:cin;this.raw(v,y,x);this.raw(x,-1,v);this.raw(v,-1,y);}
   return;}
  if(cout!==null){this.raw(-1,-1,z);this.raw(-1,-1,w);this.op(cc,cout);this.op(cc.concat([w,z]),cout);this.raw(-1,-1,w);this.raw(-1,-1,z);}
  this.op(ctrl,z);this.op(ctrl.concat(w),z);
  for(let i=t;i--;){const x=a[i],y=b[i],v=i?a[i-1]:cin;this.raw(v,y,x);this.raw(x,-1,v);this.raw(x,-1,y);this.op(ctrl.concat(x),y);this.op(ctrl.concat(v),y);}
 }
 plan(){const b=super.plan(),k=this.tag.length,x=()=>this.raw(-1,-1,this.M[this.m-1]);b.splice(k,0,{fn:x,rev:false});b.splice(b.length-k,0,{fn:x,rev:false});return b;}
}
`;
module.exports=[
 inner('walk=new Signed(n)','walk=new Signed(n,5)'),
 inner('function emitRegenerateSparse(sink,erase=false){',cls+'function emitRegenerateSparse(sink,erase=false){'),
 inner('scale=new Terminal(n,true,terms(p));','scale=new TopHost(n,true,terms(p));'),
 inner('x.tag[5]=walk.L[0];}','x.tag[5]=walk.L[0];x.tag[4]=walk.sign;}scale.sg=walk.R[0];scale.yq=scale.M[n-1];const mv=()=>{scale.raw(walk.sign,-1,walk.R[0]);scale.raw(walk.R[0],-1,walk.sign);scale.raw(-1,-1,walk.L[0]);};'),
 inner('[scale,[{fn:()=>scale.raw(-1,-1,walk.L[0])}].concat(scale.plan(),[{fn:()=>scale.raw(-1,-1,walk.L[0])}]),false]','[scale,[{fn:mv}].concat(scale.plan(),[{fn:mv,rev:true}]),false]'),
 ["'if(q===652||q===653||q===655||q===656)'","'if(q===651||q===652||q===653||q===655||q===656)'"],
];
