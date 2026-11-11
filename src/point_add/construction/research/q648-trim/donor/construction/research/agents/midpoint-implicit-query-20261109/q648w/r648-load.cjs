// Loader for jackylee0424's regen R6 (q649j q651-ten-field/r6-regen649.cjs) with optional extra source edits and a stage hook.
// Mirrors r6-regen649.cjs exactly (same patches, same W4096 commute peep when PEEP=1).
const Q=require('path').join(__dirname,'../q651-ten-field')+'/';
const fs=require('fs'),path=require('path'),Module=require('module');
function load(extra=[]){
  const file=path.join(Q,'regen.cjs'),patches=require(Q+'r6-p-r649-final.js');
  const edit=(s,a,b)=>{if(s.split(a).length!==2)throw Error('anchor '+a.slice(0,90));return s.replace(a,()=>b);};
  let s=fs.readFileSync(file,'utf8');s=edit(s,'m.adjust=adjust;','m.adjust=s=>module.applyR42(adjust(s));');
  const m=new Module(file,module);m.filename=file;m.paths=Module._nodeModulePaths(Q);
  const HOOK='for(const [g,blocks,back] of stages){';
  m.applyR42=s=>{for(const [a,b]of patches)s=edit(s,a,b);if(process.env.DUMPSRC)fs.writeFileSync(process.env.DUMPSRC,s);for(const [a,b] of extra)s=edit(s,a,b);
    if(process.env.BLOCKHOOK)s=edit(s,'g.g[i]=(a<<20)|(b<<10)|t;\n      }\n      sink(g.g);','g.g[i]=(a<<20)|(b<<10)|t;\n      }\n      if(globalThis.__rgBlock)globalThis.__rgBlock(g===walk?"walk":g===walk6?"walk6":g===park?"park":"scale",block,g.g);sink(g.g);');
    return edit(s,HOOK,'let __si=0;'+HOOK+'if(globalThis.__rgStage)globalThis.__rgStage(__si++,g===walk?"walk":g===walk6?"walk6":g===park?"park":"scale",blocks.length);');};
  m._compile(s,file);
  const raw=m.exports.emitRegenerateSparse;
  return {raw,emitRegenerateSparse(sink,erase=false){
    if(process.env.PEEP!=='1')return raw(sink,erase);
    let batch=[];const flush=()=>{if(batch.length){sink(batch);batch=[];}};
    const p=require(Q+'r6-peep.cjs').createPeep((a,b,t)=>{batch.push((a<<20)|(b<<10)|t);if(batch.length===65536)flush();},{mode:'commute',window:4096});
    raw(gs=>{for(const x of gs)p.gate(x>>>20&1023,x>>>10&1023,x&1023);},erase);p.flush();flush();}};
}
// ledger q648 edit: stage-4 walk -> TstRelay(4) on 647, L[129] + fire 648 (no tst); b (Jtop 388) rides the freed R[129]
const TR=[["[walk,r43RelayPlan(walk).concat([shifts]),false]",
  "[walk,((globalThis.__TRPLAN&&globalThis.__TRPLAN(walk,n))||r43RelayPlan(walk)).concat([shifts]),false]"]];
globalThis.__TRPLAN=(walk,n)=>{
  if(process.env.TR==='5'){ // 649-width saving: TstRelay(5) on 647,L[129],R[129] + fire 648 (b stays on 388)
    const {TstRelay}=require(require('path').join(__dirname,'walktf.cjs'));const tw=new TstRelay(n,[647,walk.L[n+1],walk.R[n+1]],648);
    return tw.plan().map(b=>({...b,fn:()=>{tw.g=walk.g;b.fn();}}));}
  if(process.env.TR!=='4')return null;
  const {TstRelay}=require(require('path').join(__dirname,'walktf.cjs'));
  const tw=new TstRelay(n,[647,walk.L[n+1]],648);
  if(tw.sign!==walk.sign||tw.y[0]!==walk.y[0]||tw.R[n+1]!==walk.R[n+1])throw Error('layout');
  const wrap=b=>({...b,fn:()=>{tw.g=walk.g;b.fn();}});
  const bmove={fn:()=>{walk.swap([],388,walk.R[n+1]);},rev:false};
  return [bmove,...tw.plan().map(wrap),bmove];
};
// ledger q648 edit 2: walk6 -> TstRelay(6) on real tags 647,648,L[129],R[129] + row top, fire T[0]; their small-v
// pre/post remap is dropped (T[1],T[2] are no longer tags, so parked q_low there is never read by the walk).
const W6=[["[walk6,r42HostPlan(walk6,scale).concat([shifts6]),true]",
  "[walk6,((globalThis.__W6PLAN&&globalThis.__W6PLAN(walk6,scale,n))||r42HostPlan(walk6,scale)).concat([shifts6]),true]"]];
globalThis.__W6PLAN=(w6,scale,n)=>{
  if(process.env.W6!=='R6')return null;
  const {TstRelay}=require(require('path').join(__dirname,'walktf.cjs'));
  const tw=new TstRelay(n,[647,648,w6.L[n+1],w6.R[n+1]],scale.T[0]);
  if(tw.sign!==w6.sign||tw.y[0]!==w6.y[0])throw Error('layout6');
  return tw.plan().map(b=>({...b,fn:()=>{tw.g=w6.g;b.fn();}}));
};
module.exports={load,TR,W6,EDITS:process.env.Q648_REGEN==='1'?require('./r648-regen.cjs').EDITS:process.env.Q648_REGEN==='1k'?require('./r648-regen.cjs').EDITS_1K:process.env.Q648_REGEN==='1kr'?require('./r648-regen.cjs').EDITS_1KR:[...TR,...W6]};
