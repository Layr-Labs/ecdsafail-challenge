'use strict';
// Retain count0 on Q120 until the first alpha body that can touch it.
// This is an exact seven-helper partial; it is not a high-alpha carrier.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D22 alpha delay anchor '+a);s=s.replace(a,()=>b);};
 one('put([[Q[n-8],base+1],[base+1,Q[n-8]]]);S[0]=base+1;T6[0]=base+1;', 'S[0]=base+1;T6[0]=base+1;');
 one('for(let t=2;t<=n;t++){const m=v.slice(0,t),a=J.slice(0,t),gap=L[n+1-t],cls=D2F.flagHeight(v,t,e,loan),utop=u[t-1];',
     'for(let t=2;t<=n;t++){const m=v.slice(0,t),a=J.slice(0,t),gap=L[n+1-t],cls=D2F.flagHeight(v,t,e,loan),utop=u[t-1];if(t===n-7){put([[J[n-8],5*n+1],[5*n+1,J[n-8]]]);}');
 return s;
};
