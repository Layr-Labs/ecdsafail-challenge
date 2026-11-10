'use strict';
// q650 integration entry (hole). From src/point_add/construction:
//   node research/agents/midpoint-implicit-query-20261109/q650/point.cjs raw|spans FILE
// Q650_GEOM=650 (default): width 650 (physical 650 removed everywhere).
// Q650_GEOM=651: 651 tape; Q650_TIGHT=field,history,upper (comma list, default none) hands those stages only 9 clean sites.
// Stage lists and freed logicals: ./stages.cjs. Geometry edits: ./geom650.js (applied after q651/upper651.cjs).
const path=require('path'),q651=f=>path.join(__dirname,'../q651',f);
const cfg=require('./stages.cjs'),geom=require('./geom650.js');
const G=process.env.Q650_GEOM||'650';if(G!=='650'&&G!=='651')throw Error('Q650_GEOM must be 650 or 651');
const tight=new Set((process.env.Q650_TIGHT||'').split(',').filter(Boolean));
for(const t of tight)if(!['field','history','upper'].includes(t))throw Error('Q650_TIGHT entry '+t);
for(const k of ['Q650_HTOP_STAGE','Q650_WIND_TEMP','HTX','Q650_ABUCKET','Q650_ABTOP'])delete process.env[k];
Object.assign(process.env,cfg.divideEnv||{});
for(const k of ['R35_UPPER','R35_FIELD11','R35_UPATCH','R35_UPPER_GROUPS','R35_UPPER_NARROW','R35_LISTS','G129_MODE','G129_TOP','N653','N653ROOT'])delete process.env[k];
Object.assign(process.env,{Q651_ENV:'keep',R35_WIDTH:G,R35_FIELD:cfg.field,R35_REGEN:cfg.regen,R35_UBASE:cfg.ubase});
const edits=geom({width:+G,tight,cfg});
const u=require(q651('upper651.cjs')),base=u.upper;
// Q650_UPPER_APPLY=<module exporting apply(src)> overrides stages.cjs upperApply (development / WIP testing only).
const UA=process.env.Q650_UPPER_APPLY||cfg.upperApply;const ua=UA?require(require('path').resolve(UA)).apply:(x=>x);
u.upper=src=>{let s=ua(base(src));for(const [a,b] of edits){if(s.split(a).length!==2)throw Error('q650 geometry anchor '+a.slice(0,80));s=s.replace(a,()=>b);}return s;};
const {GateWriter}=require(q651('point.cjs'));
module.exports={GateWriter,edits};
if(require.main===module){
  const [mode,f]=process.argv.slice(2);
  if(!['raw','spans'].includes(mode)||!f||require('os').endianness()!=='LE')throw Error('use raw FILE or spans FILE');
  console.error('q650: geometry '+G+(tight.size?' tight='+[...tight]:'')+', '+edits.length+' geometry edits');
  console.log(JSON.stringify(new GateWriter(mode==='raw'?f:null,mode==='spans'?f:undefined).produce(),null,2));
}
