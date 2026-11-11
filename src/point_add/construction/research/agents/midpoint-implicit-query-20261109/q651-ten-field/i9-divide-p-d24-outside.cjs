'use strict';
// Source overlay on D22. Partial: advance first641 use to alpha123;
// release641 after count4 outer HMR by reusing the measured count1 port642.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D24 anchor '+a);s=s.replace(a,()=>b);};
 one('if(t===n-7){put([[J[n-8],5*n+1],[5*n+1,J[n-8]]]);}',
     'if(t===n-7)put([[J[n-8],J[n-6]],[J[n-6],J[n-8]]]);if(t===n-5)put([[J[n-6],5*n+1],[5*n+1,J[n-6]]]);');
 const early="for(let j=1;j<2;j++){put([[T6[j],Q[j]]]);sink('hmr',[T6[j],bits+j]);}";
 one(early,'');
 one("put([[T6[0],Q[4]]]);sink('hmr',[T6[0],bits+4]);D17ParkCount(n,L,R,Q,loan,T6[0],bits+2,sink);",
     "put([[T6[0],Q[4]]]);sink('hmr',[T6[0],bits+4]);"+early+"T6[0]=T6[1];tap('d24.port642');D17ParkCount(n,L,R,Q,loan,T6[0],bits+2,sink);");
 return s;
};
