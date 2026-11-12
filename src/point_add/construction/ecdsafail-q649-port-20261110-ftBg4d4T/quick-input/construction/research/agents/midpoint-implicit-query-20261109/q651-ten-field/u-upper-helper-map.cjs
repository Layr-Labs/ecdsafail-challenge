'use strict';
const logical=[256,642,643,644,645,646,647,648],physical=[512,641,642,643,644,645,646,647];
exports.map={logical,physical,externalSign:{logical:649,physical:648},evicted:[650,651],ready:true};
// Same mapping replacement as I4 stage-map.cjs; source-only and deliberately
// rejects any unresolved reference rather than mapping it onto another value.
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('eight-map anchor '+a);s=s.replace(a,()=>b);};
 one('const map=[...d,2*m,...split(2*m+1,2*m+1+b),...y,...split(2*m+b+1,logical-6)];',
 'const map=[...d,2*m,...split(2*m+1,2*m+1+b),...y,...split(2*m+b+1,logical-6)];'+
 'for(const q of [256,642,643,644,645,646,647,648,650,651]){const j='+JSON.stringify(logical)+'.indexOf(q);map[q>l.g?q-1:q]=j<0?undefined:'+JSON.stringify(physical)+'[j];}'+
 'this.ids=this.ids.filter(q=>q!==650&&q!==651);');
 one('new Set(map).size!==logical-6||map.length!==logical-6',
 'new Set(map.filter(q=>q!==undefined)).size!==649||map.filter(q=>q!==undefined).length!==649');
 return s;
};
