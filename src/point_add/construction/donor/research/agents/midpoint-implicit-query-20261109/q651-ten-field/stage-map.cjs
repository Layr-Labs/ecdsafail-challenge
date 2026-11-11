'use strict';
const {replace}=require('../q653-next/parts.cjs');
const roles={upper:[256,642,643,644,645,646,647,648,650,651],multiply:[640,641,642,643,644,645,646,647,649,650],divide:[640,641,642,643,644,645,646,647,649,650],history:[0,1,130,131,388,646,647,648,649,650]};
function validate(c){
 if(![650,651].includes(c.width))throw Error('supported tape widths: 650,651');
 for(const [stage,allowed] of Object.entries(roles)){
  const s=c.stages[stage];if(!s||s.logical.length!==s.physical.length||new Set(s.logical).size!==s.logical.length||new Set(s.physical).size!==s.physical.length)throw Error('duplicate/unequal helper map '+stage);
  if(s.logical.some(q=>!allowed.includes(q))||s.physical.some(q=>!Number.isInteger(q)||q>=c.width||!(q===512||(q>=641&&q<=650&&q!==648))))throw Error('invalid helper map '+stage);
 }
}
function upper(raw,c){
 validate(c);let s=require('./upper.cjs').upper(raw);
 for(const p of c.upperPatches){const patch=require(p);if(typeof patch==='function')s=patch(s);else if(typeof patch.upper==='function')s=patch.upper(s);else for(const [a,b]of patch)s=replace(s,a,b);}
 if(c.historyNine)for(const [a,b]of require('./p-history9.js'))s=replace(s,a,b);
 s='const stageConfig='+JSON.stringify(c)+';\n'+s;
 // Logical upper enable641 is omitted from PointFoldTape.map; sign649 stays physical648.
 s=replace(s,'const map=[...d,2*m,...split(2*m+1,2*m+1+b),...y,...split(2*m+b+1,logical-6)];',
  'const map=[...d,2*m,...split(2*m+1,2*m+1+b),...y,...split(2*m+b+1,logical-6)];'+
  'for(const q of '+JSON.stringify(roles.upper)+'){const j=stageConfig.stages.upper.logical.indexOf(q);map[q>l.g?q-1:q]=j<0?undefined:stageConfig.stages.upper.physical[j];}'+
  'this.ids=this.ids.filter(q=>!'+JSON.stringify(roles.upper)+'.includes(q)||stageConfig.stages.upper.logical.includes(q));');
 s=replace(s,'new Set(map).size!==logical-6||map.length!==logical-6',
  'new Set(map.filter(q=>q!==undefined)).size!==641+stageConfig.stages.upper.logical.length||map.filter(q=>q!==undefined).length!==641+stageConfig.stages.upper.logical.length');
 // Only the physical tape width changes; donor logical dimensions remain fixed.
 s=replace(s,'2*m+m/2+4+Math.ceil(Math.log2(m/2))','stageConfig.width');
 const old='const fieldMap=(a,b)=>{const ids=[...a,...U,...Y,...b];let z=0;for(let i=640;i<657;i++)ids[i]=i===651?undefined:(i===648||i>=652)?-2:clean[z++];if(clean.length!==10||z!==10)throw Error("Q655 field geometry");return ids;};';
 s=replace(s,old,'const stageClean=name=>{const x=stageConfig.stages[name];if(x.physical.some(q=>!clean.includes(q)))throw Error("occupied helper "+name);return x;};'+
  'const fieldMap=(a,b,name)=>{const ids=[...a,...U,...Y,...b],cfg=stageClean(name);for(let i=640;i<657;i++)ids[i]=(i===648||i>=652)?-2:undefined;cfg.logical.forEach((q,j)=>ids[q]=cfg.physical[j]);return ids;};');
 s=replace(s,'fieldMap(small,other)','fieldMap(small,other,"multiply")');
 s=replace(s,'fieldMap(other,small)','fieldMap(other,small,"divide")');
 const hist=c.historyNine?'if(ids[i]===undefined&&i!==654&&i!==650)ids[i]=clean[j++];':'if(ids[i]===undefined&&i!==654)ids[i]=clean[j++];';
 s=replace(s,hist,'if(ids[i]===undefined){const hcfg=stageClean("history"),ix=hcfg.logical.indexOf(i);if(ix>=0){ids[i]=hcfg.physical[ix];j++;}}');
 s=replace(s,c.historyNine?'if(j!==9||clean.length!==9)throw Error("Q650 history geometry");':'if(j!==10||clean.length!==10)throw Error("Q651 history geometry");',
  'if(j!==stageConfig.stages.history.logical.length)throw Error("configured history geometry");');
 return s;
}
module.exports={upper,validate};
