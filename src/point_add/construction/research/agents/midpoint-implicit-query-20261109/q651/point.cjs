'use strict';
// q651 build entry. Usage: node point.cjs raw trace.u16le ; node point.cjs spans ranges.tsv
// The 651 configuration is fixed here; Q651_ENV=keep leaves the R35_* switches to the caller (development only).
if(process.env.Q651_ENV!=='keep'){
  const here=f=>require('path').join(__dirname,f);
  for(const k of ['R35_UPPER','R35_FIELD11','R35_UPATCH','R35_UPPER_GROUPS','R35_UPPER_NARROW','R35_LISTS','G129_MODE','G129_TOP','N653','N653ROOT'])delete process.env[k];
  Object.assign(process.env,{R35_WIDTH:'651',R35_FIELD:here('p-field651.js'),R35_REGEN:here('regen/p-regen651.js'),R35_UBASE:here('upper/upper.cjs')});
}
// r35 build entry (ours): nasqret's 653 point binding + g129 upper overlay (../r34-g129/upper.cjs)
// + optional textual patches to the field backend (R35_FIELD) and the history regen (R35_REGEN).
const path=require('path'),Module=require('module');
const {A,patched,load}=require('./overlay.cjs');
const {replace}=require(path.join(A,'q653-next/parts.cjs')),{checkedSource}=require(path.join(A,'field128-height-experiment/pinned.cjs'));
const file=path.join(A,'q653-next/point.cjs');
let s=checkedSource(file,'d850d912b5144bcd47227ff187d4118977dbe23665922a34eecefbe78ff74115');
s=replace(s,"m.field=require('./backend.cjs');m.history=require('./regen.cjs');m.upper=require('./upper.cjs').upper;",'m.field=module.field;m.history=module.history;m.upper=module.upper;');
const W=process.env.R35_WIDTH;
if(W&&W!=='653'){s=replace(s,"'Input-independent Q653 gate export');","'Input-independent Q"+W+" gate export');");s=replace(s,"s=replace(s,'this.quantumWidth=654','this.quantumWidth=653');s=replace(s,'if(width!==654)','if(width!==653)');","s=replace(s,'this.quantumWidth=654','this.quantumWidth="+W+"');s=replace(s,'if(width!==654)','if(width!=="+W+")');");}
const m=new Module(file,module);m.filename=file;m.paths=module.paths;
m.field=patched('q653-next/backend.cjs',load(process.env.R35_FIELD));
m.history=patched('q653-next/regen.cjs',load(process.env.R35_REGEN));
m.upper=process.env.R35_UPPER==='base'?require(path.join(A,'q653-centerfix/upper.cjs')).upper:require('./upper651.cjs').upper;
m._compile(s,file);module.exports=m.exports;
if(require.main===module){
  const [mode,f]=process.argv.slice(2);
  if(!['raw','spans'].includes(mode)||!f||require('os').endianness()!=='LE')throw Error('use raw FILE or spans FILE');
  console.log(JSON.stringify(new m.exports.GateWriter(mode==='raw'?f:null,mode==='spans'?f:undefined).produce(),null,2));
}
