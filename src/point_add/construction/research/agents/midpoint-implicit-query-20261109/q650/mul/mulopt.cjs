'use strict';
// q650 short.multiply op-count reductions (exact; loaded by p-mul650.js into the field backend).

// Controlled rotation for >=2 controls, called with `this` = a walk gate object (raw, op, y).
// rot = r_t o r_0 (two reflections, each a product of disjoint swaps). Each reflection V is controlled through one
// dirty wire d:  V^d . (d ^= AND c) . V^d . (d ^= AND c) = V^(AND c)  because V is an involution; the CX layers of
// the controlled swaps cancel between the two halves. Same permutation as Gate.rot; ~4 ops per swap instead of 6.
function rot2(c,A,s){const n=A.length;s=(s%n+n)%n;if(!s)return;
 const lab=Array.from({length:n},(_,i)=>i),seen=new Uint8Array(n);
 for(let k=0;k<n;k++){if(seen[k])continue;seen[k]=1;for(let j=(k+s)%n;j!==k;j=(j+s)%n){const x=lab[k];lab[k]=lab[j];lab[j]=x;seen[j]=1;}}
 const sig=new Array(n);for(let p=0;p<n;p++)sig[lab[p]]=p;const t=sig[0];for(let i=0;i<n;i++)if(sig[i]!==(i+t)%n)throw Error('rot2 not a rotation');
 const refl=a=>{const pr=[];for(let i=0;i<n;i++){const j=((a-i)%n+n)%n;if(i<j)pr.push([A[i],A[j]]);}return pr;};
 const V1=refl(0),V2=refl(t),d=this.y.find(q=>!c.includes(q)&&!A.includes(q));if(d===undefined)throw Error('rot2 loan');
 const G=()=>{if(c.length===2)this.raw(c[0],c[1],d);else this.op(c,d);};
 const CXL=V=>{for(const [a,b] of V)this.raw(a,-1,b);},TL=V=>{for(const [a,b] of V)this.raw(d,b,a);};
 CXL(V1);TL(V1);G();TL(V1);CXL(V1);CXL(V2);TL(V2);G();TL(V2);CXL(V2);}

// Exact peephole: drop a pair of identical X/CX/CCX gates when every live gate between them commutes with both
// (two multi-controlled X gates commute iff neither target is a control of the other). Gates are packed
// a<<20|b<<10|t (1023 = none). hmr/phase records are barriers; chunks of 2^22 gates are optimized
// independently, two passes with a 4096-gate look-back window.
function peep(buf,n,W){const keep=new Uint8Array(n).fill(1),live=[];
 for(let i=0;i<n;i++){const x=buf[i],t=x&1023,a=x>>>20&1023,b=x>>>10&1023;let j=live.length-1,steps=0,hit=-1;
  while(j>=0&&steps<W){const y=buf[live[j]];if(y===x){hit=j;break;}const ty=y&1023;
   if(ty===a||ty===b||t===(y>>>20&1023)||t===(y>>>10&1023))break;j--;steps++;}
  if(hit>=0){keep[live[hit]]=0;keep[i]=0;live.splice(hit,1);}else{live.push(i);if(live.length>4*W)live.splice(0,live.length-2*W);}}
 return keep;}
function peepSink(out,W=4096,CH=1<<22,passes=2){const buf=new Uint32Array(CH);let n=0;
 const flush=()=>{if(!n)return;let cur=buf,len=n;for(let p=0;p<passes;p++){const keep=peep(cur,len,W),o=new Uint32Array(len);let m=0;for(let i=0;i<len;i++)if(keep[i])o[m++]=cur[i];cur=o;len=m;}if(len)out('packed',cur.slice(0,len));n=0;};
 const push=x=>{if(n===CH)flush();buf[n++]=x>>>0;};
 const f=(kind,d)=>{if(kind==='packed'){for(let i=0;i<d.length;i++)push(d[i]);}
  else if(kind==='nct'){for(const r of d)push(((r.length>1?r[0]:1023)<<20)|((r.length===3?r[1]:1023)<<10)|r[r.length-1]);}
  else{flush();out(kind,d);}};
 f.flush=flush;return f;}
module.exports={rot2,peep,peepSink};
