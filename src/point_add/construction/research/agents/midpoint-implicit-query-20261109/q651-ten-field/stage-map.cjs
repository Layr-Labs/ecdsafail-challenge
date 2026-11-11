'use strict';
const replace=(s,a,b)=>{if(s.split(a).length!==2)throw Error('I7 source anchor '+a.slice(0,100));return s.replace(a,()=>b);};
const roles={upper:[256,642,643,644,645,646,647,648,650,651],multiply:[640,641,642,643,644,645,646,647,649,650],divide:[640,641,642,643,644,645,646,647,649,650],history:[0,1,130,131,388,646,647,648,649,650]};
function validate(c){
 if(![648,649].includes(c.width))throw Error('supported tape widths: 648,649');
 const pool=[512,641,642,643,644,645,646,...(c.width===649?[648]:[])];
 if(JSON.stringify(c.helperSites)!==JSON.stringify(pool)||c.stageSign!==647)throw Error('stage pool/sign geometry');
 if(c.width===648&&c.upperSign!==647)throw Error('final upper sign must be647');
 if(!Number.isInteger(c.upperSign)||c.upperSign<0||c.upperSign>=c.width)throw Error('upper sign out of range');
 for(const [stage,allowed] of Object.entries(roles)){
  const s=c.stages[stage],poolHere=stage==='upper'?Array.from({length:c.width},(_,i)=>i).filter(i=>i!==c.upperSign):pool.filter(q=>q!==648);
  if(!s||!Array.isArray(s.logical)||!Array.isArray(s.physical)||s.logical.length!==s.physical.length||new Set(s.logical).size!==s.logical.length||new Set(s.physical).size!==s.physical.length)throw Error('duplicate/unequal helper map '+stage);
  if(s.logical.length!==7&&(stage!=='upper'||c.width!==649||s.logical.length!==8))throw Error('wrong helper count '+stage);
  if(s.logical.some(q=>!allowed.includes(q))||s.physical.some(q=>!Number.isInteger(q)||!poolHere.includes(q)))throw Error('invalid helper map '+stage);
  if(stage==='upper'&&c.width===648&&JSON.stringify(s.physical.slice().sort((a,b)=>a-b))!==JSON.stringify(pool))throw Error('final upper helpers must be512,641..646');
 }
 if(!['owner','adapter'].includes(c.upperMapMode))throw Error('upper map mode must be owner or adapter');
}
function transport(tape,G,sign){
 const from=G.sign,perm=q=>q===from?sign:q===sign?from:q;
 const swap=()=>{if(from!==sign){tape.out(1023,from,sign);tape.out(1023,sign,from);tape.out(1023,from,sign);}};
 const H={R:G.R.map(perm),U:G.U.map(perm),V:G.V.map(perm),Y:G.Y.map(perm),sign,clean:G.clean.map(perm)};
 const live=[...H.R,...H.U,...H.V,...H.Y,sign,...H.clean];
 if(new Set(live).size!==live.length)throw Error('non-injective sign transport');
 return {enter:swap,leave:swap,G:H};
}
function upper(raw,c){
 validate(c);let s=require('./upper.cjs').upper(raw);
 for(const p of c.upperPatches){const patch=require(p);if(typeof patch==='function')s=patch(s);else if(typeof patch.upper==='function')s=patch.upper(s);else for(const [a,b]of patch)s=replace(s,a,b);}

 s='const stageConfig='+JSON.stringify(c)+';\n'+s;
 // Owner-bound allocators are accepted only after runtime ABI/range/injectivity checks.
 if(c.upperMapMode==='adapter'){
  s=replace(s,'const map=[...d,2*m,...split(2*m+1,2*m+1+b),...y,...split(2*m+b+1,logical-6)];',
   'const map=[...d,2*m,...split(2*m+1,2*m+1+b),...y,...split(2*m+b+1,logical-6)];'+
   'for(const q of '+JSON.stringify(roles.upper)+'){const j=stageConfig.stages.upper.logical.indexOf(q);map[q>l.g?q-1:q]=j<0?undefined:stageConfig.stages.upper.physical[j];}map[l.sig>l.g?l.sig-1:l.sig]=stageConfig.upperSign;'+
   'this.ids=this.ids.filter(q=>!'+JSON.stringify(roles.upper)+'.includes(q)||stageConfig.stages.upper.logical.includes(q));');
  s=replace(s,'new Set(map).size!==logical-6||map.length!==logical-6',
   'new Set(map.filter(q=>q!==undefined)).size!==stageConfig.width||map.filter(q=>q!==undefined).length!==stageConfig.width');
 }
 s=replace(s,'this.map=map;const wire=',
  'const live=map.filter(q=>q!==undefined);if(live.length!==stageConfig.width||new Set(live).size!==live.length||live.some(q=>!Number.isInteger(q)||q<0||q>=stageConfig.width))throw Error("upper physical map ban/injectivity");'+
  'if(map[l.sig>l.g?l.sig-1:l.sig]!==stageConfig.upperSign)throw Error("upper sign ABI");stageConfig.stages.upper.logical.forEach((q,j)=>{if(map[q>l.g?q-1:q]!==stageConfig.stages.upper.physical[j])throw Error("upper helper ABI");});'+
  'this.map=map;const wire=');
 // Conjugate the backend by a value-independent SWAP, including its data maps.
 const call='backend(tape,{R,U,V,Y,sign,clean},div,(1n<<BigInt(m))-BigInt(delta));';
 s=replace(s,call,'const tr=stageTransport(tape,{R,U,V,Y,sign,clean},stageConfig.stageSign);tr.enter();backend(tape,tr.G,div,(1n<<BigInt(m))-BigInt(delta));tr.leave();');
 s='const stageTransport='+transport.toString()+';\n'+s;
 // Only the physical tape width changes; donor logical dimensions remain fixed.
 s=replace(s,'2*m+m/2+4+Math.ceil(Math.log2(m/2))','stageConfig.width');
 const old='const fieldMap=(a,b)=>{const ids=[...a,...U,...Y,...b];let z=0;for(let i=640;i<657;i++)ids[i]=i===651?undefined:(i===648||i>=652)?-2:clean[z++];if(clean.length!==10||z!==10)throw Error("Q655 field geometry");return ids;};';
 s=replace(s,old,'const stageClean=name=>{const x=stageConfig.stages[name];if(x.physical.some(q=>!clean.includes(q)))throw Error("occupied helper "+name);return x;};'+
  'const fieldMap=(a,b,name)=>{const ids=[...a,...U,...Y,...b],cfg=stageClean(name);for(let i=640;i<657;i++)ids[i]=(i===648||i>=652)?-2:undefined;cfg.logical.forEach((q,j)=>ids[q]=cfg.physical[j]);return ids;};');
 s=replace(s,'fieldMap(small,other)','fieldMap(small,other,"multiply")');
 s=replace(s,'fieldMap(other,small)','fieldMap(other,small,"divide")');
 const hist='if(ids[i]===undefined&&i!==654)ids[i]=clean[j++];';
 s=replace(s,hist,'if(ids[i]===undefined){const hcfg=stageClean("history"),ix=hcfg.logical.indexOf(i);if(ix>=0){ids[i]=hcfg.physical[ix];j++;}}');
 s=replace(s,'if(j!==10||clean.length!==10)throw Error("Q651 history geometry");',
  'if(j!==stageConfig.stages.history.logical.length)throw Error("configured history geometry");');
 return s;
}
module.exports={upper,validate,transport};
