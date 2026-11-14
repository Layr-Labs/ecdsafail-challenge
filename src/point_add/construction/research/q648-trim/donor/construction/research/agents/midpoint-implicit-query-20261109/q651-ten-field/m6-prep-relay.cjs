'use strict';
// Optional micro-window reduction. Still needs site649 around each modular add.
const base=require('./m6-candidate.cjs');
const edit=(s,a,b)=>{if(s.split(a).length!==2)throw Error('prep relay anchor '+a);return s.replace(a,()=>b);};
module.exports={source:base.source,f:s=>{
 s=base.f(s);
 s=edit(s,'const hole=649,sc=T.at(-1),R=[...L,hole],lut=[...T,...R,...C],ops=NR(128,257).map(r=>r.map(i=>lut[i])),inv=[...ops].reverse(),md=[[sc],...r36madd([...T.slice(0,-1),1001],R.slice(0,128),H,sc),[sc]],G=[...T,...C,...H];',
 'const hole=T.at(-1),sc=hole,R=[...L,hole],lut=[...T.slice(0,-1),1001,...R,...C],ops=r36nr(128,257,lut),inv=[...ops].reverse(),relay=[[hole,649],[649,hole],[hole,649]],md=[...relay,...r36madd([...T.slice(0,-1),1001],R.slice(0,128),H,sc),...relay],G=[...T.slice(0,-1),...C,...H];');
 s=edit(s,'run([].concat([[hole]],ops,md,inv,[[hole]],add,ops,[...md].reverse(),inv,[...add].reverse()),back);',
 'run([].concat([[hole]],[[hole]],ops,md,inv,[[hole]],add,ops,[...md].reverse(),inv,[...add].reverse(),[[hole]]),back);');
 return s;
}};
