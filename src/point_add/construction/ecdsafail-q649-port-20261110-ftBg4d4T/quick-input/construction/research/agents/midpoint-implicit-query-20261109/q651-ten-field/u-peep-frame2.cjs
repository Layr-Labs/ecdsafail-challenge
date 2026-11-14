'use strict';
// All state is classical emitter state. No circuit input controls emission.
function createPeep(out,{window=4096,mode='commute',merge=true}={}){
 if(!Number.isInteger(window)||window<1)throw Error('window');
 const N=window+1,A=new Int32Array(N),B=new Int32Array(N),Z=new Int32Array(N),P=new Uint8Array(N),live=new Uint8Array(N);
 const F=new Uint8Array(1024),O=new Uint8Array(1024),writes=new Float64Array(1024);
 const stats={input:0,output:0,inputCCX:0,outputCCX:0,removed:0,removedCCX:0,cancel:0,merge:0,window,mode:'frame'};
 let first=0,end=0;
 function raw(a,b,z){out(a,b,z);stats.output++;if(a!==1023&&b!==1023)stats.outputCCX++;}
 function polarity(q,p){if(q!==1023&&O[q]!==p){raw(1023,1023,q);O[q]=p;}}
 function emit(i){const j=i%N;if(!live[j])return;const a=A[j],b=B[j],z=Z[j],p=P[j];polarity(a,p&1);polarity(b,p>>1&1);raw(a,b,z);live[j]=0;}
 function flush(){while(first<end)emit(first++);first=end=0;for(let q=0;q<1023;q++){if(O[q]!==F[q])raw(1023,1023,q);O[q]=F[q]=0;}stats.removed=stats.input-stats.output;stats.removedCCX=stats.inputCCX-stats.outputCCX;}
 function gate(a,b,z){
  if(z===1023||a===z||b===z||(a===b&&a!==1023))throw Error('peep alias');
  stats.input++;if(a!==1023&&b!==1023)stats.inputCCX++;
  if(a===1023&&b===1023){F[z]^=1;return;}
  if(a>b){const t=a;a=b;b=t;}
  let p=F[a]|F[b]<<1;
  if(end-first===window)emit(first++);
  for(let i=end-1;i>=first;i--){const j=i%N;if(!live[j])continue;const x=A[j],y=B[j],t=Z[j],r=P[j];
   if(z===t){
    if(a===x&&b===y){
     if(p===r){live[j]=0;stats.cancel++;return;}
     const d=p^r;
     if(merge&&(d===1||d===2)){
      live[j]=0;stats.merge++;
      if(d===1){a=b;b=1023;p=p>>1&1;}else{b=1023;p&=1;}
      if(a===1023){F[z]^=1;return;}
      continue;
     }
    }
    // Product XOR subset product: c*d XOR c = c*!d.
    if(false){
     let aa=-1,bb=-1,pp=0;
     if(b===1023&&y!==1023){if(a===x&&(p&1)===(r&1)){aa=x;bb=y;pp=r^2;}else if(a===y&&(p&1)===(r>>1&1)){aa=x;bb=y;pp=r^1;}}
     else if(y===1023&&b!==1023){if(x===a&&(r&1)===(p&1)){aa=a;bb=b;pp=p^2;}else if(x===b&&(r&1)===(p>>1&1)){aa=a;bb=b;pp=p^1;}}
     if(aa>=0&&writes[aa]!==stats.input&&writes[bb]!==stats.input){live[j]=0;stats.merge++;a=aa;b=bb;p=pp;continue;}
    }
   }
   if(t===a||t===b||z===x||z===y)break;
   writes[t]=stats.input;
  }
  const j=end++%N;A[j]=a;B[j]=b;Z[j]=z;P[j]=p;live[j]=1;
 }
 return {gate,flush,stats};
}
function wrapSparse(sink,options){
 const p=createPeep((a,b,z)=>sink('nct',[a===1023?(b===1023?[z]:[b,z]):b===1023?[a,z]:[a,b,z]]),options);
 function wrapped(kind,data){if(kind==='nct')for(const r of data)p.gate(r.length===3?r[0]:1023,r.length>=2?r.at(-2):1023,r.at(-1));else if(kind==='packed')for(const x of data)p.gate(x>>>20&1023,x>>>10&1023,x&1023);else{p.flush();sink(kind,data);}}
 return {sink:wrapped,flush:p.flush,stats:p.stats};
}
module.exports={createPeep,wrapSparse};

