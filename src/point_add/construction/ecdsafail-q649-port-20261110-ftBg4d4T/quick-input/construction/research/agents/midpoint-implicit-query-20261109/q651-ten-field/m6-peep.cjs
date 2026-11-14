'use strict';
// Bounded, online, deterministic NCT pair cancellation. Metadata is a barrier.
// strict: all intervening live gates have disjoint operand sets.
// commute: X-type commutation iff neither target is a control of the other.
function createPeep(out,{window=4096,mode='strict'}={}){
 if(!Number.isInteger(window)||window<1||!['strict','commute'].includes(mode))throw Error('peep config');
 const N=window+1,A=new Int32Array(N),B=new Int32Array(N),Z=new Int32Array(N),live=new Uint8Array(N);
 const stats={input:0,output:0,removed:0,removedCCX:0,window,mode};let first=0,end=0;
 function emit(i){const j=i%N;if(live[j]){out(A[j],B[j],Z[j]);live[j]=0;stats.output++;}}
 function flush(){while(first<end)emit(first++);first=end=0;}
 function gate(a,b,z){
  if(z===1023||a===z||b===z||(a===b&&a!==1023))throw Error('peep alias');
  stats.input++;if(end-first===window)emit(first++);
  let hit=-1;
  for(let i=end-1;i>=first;i--){const j=i%N;if(!live[j])continue;
   const x=A[j],y=B[j],t=Z[j];
   if(a===x&&b===y&&z===t){hit=j;break;}
   if(mode==='commute') {if(t===a||t===b||z===x||z===y)break;}
   else if(z===t||z===x||z===y||a!==1023&&(a===x||a===y||a===t)||b!==1023&&(b===x||b===y||b===t))break;
  }
  if(hit>=0){live[hit]=0;stats.removed+=2;if(a!==1023&&b!==1023)stats.removedCCX+=2;return;}
  const j=end++%N;A[j]=a;B[j]=b;Z[j]=z;live[j]=1;
 }
 return {gate,flush,stats};
}
function wrapSparse(sink,options){
 const p=createPeep((a,b,z)=>sink('nct',[a===1023?(b===1023?[z]:[b,z]):b===1023?[a,z]:[a,b,z]]),options);
 function wrapped(kind,data){
  if(kind==='nct')for(const r of data)p.gate(r.length===3?r[0]:1023,r.length>=2?r.at(-2):1023,r.at(-1));
  else if(kind==='packed')for(const x of data)p.gate(x>>>20&1023,x>>>10&1023,x&1023);
  else {p.flush();sink(kind,data);}
 }
 return {sink:wrapped,flush:p.flush,stats:p.stats};
}
module.exports={createPeep,wrapSparse};
