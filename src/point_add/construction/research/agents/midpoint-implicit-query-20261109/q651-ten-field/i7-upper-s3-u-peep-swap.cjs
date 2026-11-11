'use strict';
const base=require('./i7-upper-s3-u-peep-s1.cjs').createPeep;
function frameFactory(out,options={}){
 const stats={swaps:0,restoreSwaps:0,input:0,output:0,removed:0,removedCCX:0};
 const core=BASE((a,b,z)=>{out(a,b,z);stats.output++;},options);
 const map=Int32Array.from({length:1024},(_,i)=>i),inv=Int32Array.from(map),pending=[];
 function send(g){core.gate(map[g[0]],map[g[1]],map[g[2]]);}
 function gate(a,b,z){
  stats.input++;
  if(a!==1023&&b===1023){b=a;a=1023;}
  pending.push([a,b,z]);
  if(pending.length===3){const [u,v,w]=pending;
   if(u[0]===1023&&v[0]===1023&&w[0]===1023&&u[1]!==1023&&v[1]===u[2]&&v[2]===u[1]&&u[1]===w[1]&&u[2]===w[2]){
    const x=u[1],y=u[2],p=map[x],q=map[y];map[x]=q;map[y]=p;inv[p]=y;inv[q]=x;pending.length=0;stats.swaps++;return;
   }
   send(pending.shift());
  }
 }
 function flush(){
  while(pending.length)send(pending.shift());
  for(let i=0;i<1023;i++)if(map[i]!==i){const j=map[i],other=inv[i];core.gate(1023,i,j);core.gate(1023,j,i);core.gate(1023,i,j);map[i]=i;map[other]=j;inv[i]=i;inv[j]=other;stats.restoreSwaps++;}
  core.flush();stats.removed=stats.input-stats.output;stats.removedCCX=core.stats.removedCCX;
 }
 return {gate,flush,stats};
}
const createPeep=Function('return '+frameFactory.toString().replace('BASE(', '('+base.toString()+')('))();
function wrapSparse(sink,options){const p=createPeep((a,b,z)=>sink('nct',[a===1023?(b===1023?[z]:[b,z]):b===1023?[a,z]:[a,b,z]]),options);function wrapped(kind,data){if(kind==='nct')for(const r of data)p.gate(r.length===3?r[0]:1023,r.length>=2?r.at(-2):1023,r.at(-1));else if(kind==='packed')for(const x of data)p.gate(x>>>20&1023,x>>>10&1023,x&1023);else{p.flush();sink(kind,data);}}return {sink:wrapped,flush:p.flush,stats:p.stats};}
module.exports={createPeep,wrapSparse};
