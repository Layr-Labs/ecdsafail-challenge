'use strict';
// Exact commuting cancellation. Per-wire read/write lists permit O(1) blocker queries.
// Ring ids are positive monotonically increasing insertion positions; 0 means none.
function createPeep(out,{window=65536,mode='commute'}={}){
 if(!Number.isInteger(window)||window<1)throw Error('window');
 const N=window+1,A=new Int32Array(N),B=new Int32Array(N),Z=new Int32Array(N),live=new Uint8Array(N);
 const wp=new Float64Array(N),wn=new Float64Array(N),ap=new Float64Array(N),an=new Float64Array(N),bp=new Float64Array(N),bn=new Float64Array(N);
 const R=new Float64Array(1024),W=new Float64Array(1024),keys=new Map();let first=1,end=1;
 const stats={input:0,output:0,removed:0,removedCCX:0,window,mode:'indexed'};
 const key=(a,b,z)=>a*1048576+b*1024+z;
 function rnext(id,q,value){const j=id%N;if(A[j]===q)an[j]=value;else if(B[j]===q)bn[j]=value;else throw Error('read link');}
 function rprev(id,q,value){const j=id%N;if(A[j]===q)ap[j]=value;else if(B[j]===q)bp[j]=value;else throw Error('read link');}
 function unlink(id){const j=id%N,a=A[j],b=B[j],z=Z[j];
  if(wp[j])wn[wp[j]%N]=wn[j];if(wn[j])wp[wn[j]%N]=wp[j];else W[z]=wp[j];
  if(a!==1023){if(ap[j])rnext(ap[j],a,an[j]);if(an[j])rprev(an[j],a,ap[j]);else R[a]=ap[j];}
  if(b!==1023){if(bp[j])rnext(bp[j],b,bn[j]);if(bn[j])rprev(bn[j],b,bp[j]);else R[b]=bp[j];}
  const k=key(a,b,z);if(keys.get(k)===id)keys.delete(k);live[j]=0;
 }
 function emit(id){const j=id%N;if(live[j]){out(A[j],B[j],Z[j]);stats.output++;unlink(id);}}
 function flush(){while(first<end)emit(first++);first=end=1;keys.clear();}
 function gate(a,b,z){
  if(z===1023||a===z||b===z||(a===b&&a!==1023))throw Error('peep alias');
  if(a>b){const q=a;a=b;b=q;}stats.input++;
  if(end-first===window)emit(first++);
  const k=key(a,b,z),id=keys.get(k);
  if(id!==undefined&&W[a]<id&&W[b]<id&&R[z]<id){unlink(id);stats.removed+=2;if(b!==1023)stats.removedCCX+=2;return;}
  const j=end%N;A[j]=a;B[j]=b;Z[j]=z;live[j]=1;
  wp[j]=W[z];wn[j]=0;if(W[z])wn[W[z]%N]=end;W[z]=end;
  ap[j]=a===1023?0:R[a];an[j]=0;if(a!==1023){if(R[a])rnext(R[a],a,end);R[a]=end;}
  bp[j]=b===1023?0:R[b];bn[j]=0;if(b!==1023){if(R[b])rnext(R[b],b,end);R[b]=end;}
  keys.set(k,end);end++;
 }
 return {gate,flush,stats};
}
function wrapSparse(sink,options){
 const p=createPeep((a,b,z)=>sink('nct',[a===1023?(b===1023?[z]:[b,z]):b===1023?[a,z]:[a,b,z]]),options);
 function wrapped(kind,data){if(kind==='nct')for(const r of data)p.gate(r.length===3?r[0]:1023,r.length>=2?r.at(-2):1023,r.at(-1));else if(kind==='packed')for(const x of data)p.gate(x>>>20&1023,x>>>10&1023,x&1023);else{p.flush();sink(kind,data);}}
 return {sink:wrapped,flush:p.flush,stats:p.stats};
}
module.exports={createPeep,wrapSparse};
