'use strict';
// Exact top-one digit without retaining a symbolic virtual ripple bit.
module.exports=function constantFast(A,B,h,e){
 const a=A,b=B.slice(0,-1),z=B.at(-1),n=a.length;
 const gate=(cs,t)=>this.op(cs,t),x=t=>gate([],t),cx=(s,t)=>gate([s],t),ccx=(r,s,t)=>gate([r,s],t);
 function cmp(ctrl,t){
  for(const q of b)x(q);
  if(n===1){gate([...ctrl,a[0],b[0]],t);x(b[0]);return;}
  for(let i=1;i<n;i++)cx(a[i],b[i]);gate([...ctrl,a[n-1]],t);
  for(let i=n-2;i>=1;i--)cx(a[i],a[i+1]);for(let i=0;i<n-1;i++)ccx(b[i],a[i],a[i+1]);
  gate([...ctrl,b[n-1],a[n-1]],t);
  for(let i=n-2;i>=0;i--)ccx(b[i],a[i],a[i+1]);for(let i=1;i<n-1;i++)cx(a[i],a[i+1]);for(let i=1;i<n;i++)cx(a[i],b[i]);for(const q of b)x(q);
 }
 function lowadd(){
  if(n===1){gate([e,h,a[0]],b[0]);return;}
  for(let i=1;i<n;i++)cx(a[i],b[i]);for(let i=n-2;i>=1;i--)cx(a[i],a[i+1]);for(let i=0;i<n-1;i++)ccx(b[i],a[i],a[i+1]);
  gate([e,h,a[n-1]],b[n-1]);
  for(let i=n-2;i>=0;i--){ccx(b[i],a[i],a[i+1]);gate([e,h,a[i]],b[i]);}
  for(let i=1;i<n-1;i++)cx(a[i],a[i+1]);for(let i=1;i<n;i++)cx(a[i],b[i]);
 }
 if(!n){gate([e,z],h);gate([e,h],z);return;}
 gate([e,z],h);cmp([e,z],h);
 // Reverse controlled addition of (1,a).
 gate([e,h],z);cmp([e,h],z);this.reverse(lowadd);
};
