'use strict';
const {hostedNormal}=require('./i9-multiply-m9-normal-host.cjs');
function code(s,low){const c=s===0?0:s<=2?1:s<=6?2:3;let out=low;if(c===1)out=(low&~1)|(s-1);if(c===2)out=(low&~3)|(s-3);if(c===3)out=s;return out|(c<<7)|((s>>3)<<9)|(1<<13);}
function permutation(){const m=new Map;for(let s=0;s<128;s++)for(let low=0;low<128;low++)if(!(low&((1<<Math.min(s,7))-1))){const a=low|((s>>1)<<7)|((s&1)<<13),b=code(s,low);if(m.has(a))throw Error('duplicate input');m.set(a,b);}if(new Set(m.values()).size!==m.size)throw Error('encoding collision');
 const full=new Map(m),outputs=new Set(m.values());for(const start of m.keys())if(!outputs.has(start)){let end=start;while(m.has(end))end=m.get(end);full.set(end,start);}
 const done=new Set,swaps=[];for(const a of full.keys())if(!done.has(a)){let b=a,cy=[];do{done.add(b);cy.push(b);b=full.get(b);if(b===undefined)throw Error('open chain');}while(b!==a);for(let j=1;j<cy.length;j++)swaps.push([a,cy[j]]);}
 return{m,swaps};
}
function encode(T,S,D,p){const ports=[...T.slice(0,7),...S,T.at(-1)],g=[],{swaps,m}=permutation();
 const step=(x,j)=>{const ctl=ports.filter((_,k)=>k!==j),pol=ports.map((_,k)=>k).filter(k=>k!==j).map(k=>!!(x>>k&1));g.push(...p.negate(ctl,p.MCX(ctl,ports[j],D),pol));};
 for(const [a,b]of swaps){let x=a;const path=[];for(let j=0;j<14;j++)if((a^b)>>j&1){path.push([x,j]);step(x,j);x^=1<<j;}for(let k=path.length-2;k>=0;k--)step(...path[k]);}
 return{g,cases:m.size,swaps:swaps.length};
}
function compactNormal(T,Q,S,D,p,qmove=true){if(T.length!==128||S.length!==6)throw Error('v2 width128');return [...hostedNormal(T,Q,S,D,p,qmove),...encode(T,S,D,p).g];}
module.exports={compactNormal,encode,permutation,code};
