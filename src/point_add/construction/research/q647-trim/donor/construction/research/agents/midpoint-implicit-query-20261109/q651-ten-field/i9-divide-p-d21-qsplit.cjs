'use strict';
// Apply after D20 shared tail. Keep count0 on e through qsplit and M unrotation.
module.exports=s=>{
 const a='for(let j=0;j<n-1;j++){const q=D17GTEncoded(S,j,e,C);put(q);const rows=[];eliminate(D2F.dirtyDigit(M.slice(j+1),Q.slice(0,n-1-j),Q[n-1-j],e,C[0]),M[n-1],1,(cs,z)=>rows.push(...MCX(cs,z,C.filter(w=>w!==z&&!cs.includes(w)))));put(rows);put(rev(q));}';
 if(s.split(a).length!==2)throw Error('D21 qsplit anchor');
 s=s.replace(a,`put([[S[0],e],[e,S[0]]]);S[0]=e;tap('qsplit.count0.host');
 for(let j=0;j<n-1;j++){
  const rows=[],virtual=1000;
  eliminate(D2F.dirtyDigit(M.slice(j+1),Q.slice(0,n-1-j),Q[n-1-j],virtual,C[0]),M[n-1],1,(cs,z)=>{
   if(z===virtual)throw Error('D21 enable target');
   if(!cs.includes(virtual)){rows.push(...MCX(cs,z,C.filter(w=>w!==z&&!cs.includes(w))));return;}
   const rest=cs.filter(w=>w!==virtual);
   for(let bit=0;bit<bits;bit++)if(!(j>>bit&1)){
    const c=[S[bit],...S.slice(bit+1)],p=[true,...S.slice(bit+1).map((_,k)=>!!(j>>(k+bit+1)&1))];
    const ix=c.indexOf(S[2]);if(ix>=0)p[ix]=!p[ix];
    rows.push(...D17Raw([...rest,...c],[...rest.map(()=>true),...p],z,C));
   }
  });put(rows);
 }`);
 return s;
};
