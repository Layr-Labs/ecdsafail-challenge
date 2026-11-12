'use strict';
// r35 regenerate stage at 11 helper sites, cheaper form (ours). Same as p-regen.js, except that only the walk that
// runs while U is present (after scale) uses SectorSigned(n,5). The walk that runs while U is still empty keeps
// nasqret's 6 tag bits and hosts tag[4] on T[0] (logical 260): park never touches T[0], the walk never touches T,
// and U is zero at stage entry, so that wire is zero for the whole of that walk. Logical site 651 is never touched.
const base=require('./p-regen.js');
const ANCH="const m=new Module(file,module);";
const inner=(a,b)=>[ANCH,'s=replace(s,'+JSON.stringify(a)+','+JSON.stringify(b)+');'+ANCH];
const direct=base.at(-1);
module.exports=base.slice(0,-1).concat([
 inner('walk=new Signed(n,5)','walk=new Signed(n,5),walk6=new Signed(n)'),
 inner('walk.aux=walk.L[n+1];walk.tst=walk.R[n+1];','walk.aux=walk.L[n+1];walk.tst=walk.R[n+1];walk6.aux=walk6.L[n+1];walk6.tst=walk6.R[n+1];walk6.tag[4]=scale.T[0];const shifts6={fn:()=>{for(const bank of [walk6.L,walk6.R])for(let j=n;j>=1;j--)walk6.swap([],bank[j],bank[j+1]);}};'),
 inner('[walk,walk.plan().concat([shifts]),true]','[walk6,walk6.plan().concat([shifts6]),true]'),
 inner('q===walk.tag.at(-1)&&g===walk','(g===walk||g===walk6)&&q===g.tag.at(-1)'),
 direct,
]);
