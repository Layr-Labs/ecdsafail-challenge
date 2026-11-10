'use strict';
// r35 short.multiply patch (ours): the multiply never touches logical 655 (physical 652); its helpers are 640..647,649,650,651.
// [from,to] pairs on nasqret's q653-next/backend.cjs text (R35_FIELD format).  Four exact changes, all on the multiply text f:
//  1 shprod: the X+M carry xh is uncomputed around each A / A^-1 block, so the modular-add scratch shares its wire (4 -> 3 sites)
//  2 prep  : one clean hole (bit 256) + dirty-borrow constant adds of 2^32+977 replace three holes and the 47 +1 steps (4 -> 2 sites)
//  3 can   : the C digit (colour 647) is undone across unit+power, where C is not read; power's enable/scratch sit on 647
//  4 walk  : nasqret's own sector walk with 6 tag bits (the 654 divide's inner walk) instead of the 7-tag flat walk (12 -> 11 sites)
const R=[
 ["const [xh,th,t2,tmp]=P;const mm=plus(M,X,xh),D0=[...X,xh];let all=[...mm];",
  "const [xh,th,t2]=P,tmp=xh;const mm=plus(M,X,xh),um=[...mm].reverse(),D0=[...X,xh];let all=[];"],
 ["A=where(NR(n+1,n),[...D0,...raw]).reverse(),B=","A=[...mm,...where(NR(n+1,n),[...D0,...raw]).reverse(),...um],B="],
 ["depo(br,true));}return all.concat([...mm].reverse());}","depo(br,true));}return all;}"],
 ["idx=vec(3,649),en=655,tmp=655;","idx=vec(3,649),en=647,tmp=647;"],
 ["mad=madd(T,C,H,tmp),","mad=madd(T,C,H,649),"],
 ["shprod(128,T,H,C,L,[649,650,651,655])","shprod(128,T,H,C,L,[649,650,651])"],
 ["function prep(back){const inc=plusOneMod(T,H,en,L,{MCX,negate,plus,incReg});if(back)for(let i=0;i<47;i++)run(inc,true);const loc=[10,32,256],R=[];let k=0;for(let j=0;j<257;j++){const a=loc.indexOf(j);R.push(a<0?L[k++]:idx[a]);}run(remprep(128,257,T,R,C,H,en,idx,[2],[1,0]),back);if(!back)for(let i=0;i<47;i++)run(inc);}",
  "function prep(back){const hole=649,sc=650,R=[...L,hole],lut=[...T,...R,...C],ops=NR(128,257).map(r=>r.map(i=>lut[i])),inv=[...ops].reverse(),md=madd(T,R.slice(0,128),H,sc),G=[...T,...C,...H];let add=[];for(const i of [0,4,6,7,8,9,32])add=add.concat(incReg(R.slice(i),G));run([].concat([[hole]],ops,md,inv,[[hole]],add,ops,[...md].reverse(),inv,[...add].reverse()),back);}"],
 ["function unit(back){run(can,true);emitPUnit(back,buf=>sink('packed',buf));run(can);}","function unit(back){emitPUnit(back,buf=>sink('packed',buf));}"],
 ["sink('phase',[C[i],i]);}prep(false);unit(false);power(false);prod(true);for(let i=0;i<n;i++)sink('phase',[C[i],i]);prod(false);power(true);unit(true);prep(true);run(can,true);run(unn,true);}",
  "sink('phase',[C[i],i]);}prep(false);run(can,true);unit(false);power(false);run(can);prod(true);for(let i=0;i<n;i++)sink('phase',[C[i],i]);prod(false);run(can,true);power(true);unit(true);run(can);prep(true);run(can,true);run(unn,true);}"],
 ["function unitMap(n,W,K){",
  "function unitMap(n,W,K){const m=new Array(W.nq).fill(-1),tg=W.tag.slice(0,-1);for(let j=0;j<n;j++){m[W.L[j]]=j;m[W.R[j]]=3*n+j;}for(let j=0;j<2*n;j++)m[W.y[j]]=n+j;m[W.L[n]]=647;m[W.R[n]]=650;m[W.tst]=649;m[W.fire]=651;for(let j=0;j<tg.length;j++)m[tg[j]]=640+j;m[W.sign]=640+tg.length;m[W.aux]=641+tg.length;if(641+tg.length>646)throw Error('walk sites');return m;}function unitMapFlat(n,W,K){"],
 ["const tr=q=>q===1023?1023:map[q===G.tag[6]?block.topPort:q];",
  "const top=G.tag.at(-1),tr=q=>{if(q===1023)return q;if(q===top){if(block.topPort==null)throw Error('height outside row');q=block.topPort;}const z=map[q];if(!(z>=0))throw Error('unbound unit port '+q);return z;};"],
];
const inject=R.map(([a,b])=>'f=replace(f,'+JSON.stringify(a)+','+JSON.stringify(b)+');\n').join('')
 +'class R35UnitWalk extends SectorCanonical{constructor(n){super(n,6);}}\n';
module.exports=[
 ['const multiply=Function(',inject+'const multiply=Function('],
 ['({exports:{}},VirtualCanonical,dirtyDigit,lowValuationSweep,plusOneMod);','({exports:{}},R35UnitWalk,dirtyDigit,lowValuationSweep,plusOneMod);'],
 ["const free=back?[648,652,654,655,656]:[648,652,653,654,656],move=back?653:655;","const free=back?[648,652,654,655,656]:[648,652,653,654,655,656],move=back?653:-1;"],
];
