'use strict';
// Final allocator, applied to the U16 eight-helper allocator after all source overlays.
// It rejects unresolved 647 uses. Never aliases a missing helper onto the sign.
const helpers=[256,642,643,644,645,646,648],physical=[512,641,642,643,644,645,646];
exports.map={helpers,physical,sign:{logical:649,physical:647},absent:[647,650,651],ready:false};
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U19 seven-map anchor '+a);s=s.replace(a,()=>b);};
 const prior='for(const q of [256,642,643,644,645,646,647,648,650,651]){const j=[256,642,643,644,645,646,647,648].indexOf(q);map[q>l.g?q-1:q]=j<0?undefined:[512,641,642,643,644,645,646,647][j];}';
 one(prior,'for(const q of [256,642,643,644,645,646,647,648,649,650,651]){const j='+JSON.stringify(helpers)+'.indexOf(q);map[q>l.g?q-1:q]=q===649?647:j<0?undefined:'+JSON.stringify(physical)+'[j];}');
 one('new Set(map.filter(q=>q!==undefined)).size!==649||map.filter(q=>q!==undefined).length!==649','new Set(map.filter(q=>q!==undefined)).size!==648||map.filter(q=>q!==undefined).length!==648');
 one('this.toGlobal=x=>map[x>l.g?x-1:x];','this.toGlobal=x=>wire(x>l.g?x-1:x);');
 one('throw Error("upper used removed physical site "+x);','throw Error("upper unresolved logical site "+(x>=l.g?x+1:x));');
 return s;
};
