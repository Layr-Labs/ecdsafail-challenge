'use strict';
exports.upper=s=>{
 const anchor='const norm=ts=>{const m=new Map();for(const c of ts){if(c.yes.some(q=>c.no.includes(q)))continue;const k=key(c);if(m.has(k))m.delete(k);else m.set(k,c);}return [...m.values()];};';
 const start=s.indexOf('    u6VirtualTape(tape){'),at=s.indexOf(anchor,start);if(at<start)throw Error('U41 ESOP anchor');
 return s.slice(0,at)+s.slice(at).replace(anchor,`const norm=ts=>{
  const m=new Map();const add=c=>{if(c.yes.some(q=>c.no.includes(q)))return;const k=key(c);if(m.has(k))m.delete(k);else m.set(k,c);};
  for(const c of ts)add(c);
  let changed=true;while(changed){changed=false;const cs=[...m.values()];outer:for(let i=0;i<cs.length;i++)for(let j=i+1;j<cs.length;j++){
    const a=cs[i],b=cs[j],qs=new Set([...a.yes,...a.no,...b.yes,...b.no]);let count=0,wire,va,vb;
    for(const q of qs){const x=a.yes.includes(q)?1:a.no.includes(q)?-1:0,y=b.yes.includes(q)?1:b.no.includes(q)?-1:0;if(x!==y){count++;wire=q;va=x;vb=y;if(count>1)break;}}
    if(count!==1)continue;
    m.delete(key(a));m.delete(key(b));const yes=a.yes.filter(q=>q!==wire),no=a.no.filter(q=>q!==wire);
    if(!va||!vb)((va||vb)===1?no:yes).push(wire);
    add(cube(yes,no));changed=true;break outer;
  }}return [...m.values()];
 };`);
};
