'use strict';
// D16 candidate: all three walks avoid native643; count2 reconnects before alpha.
// Whole-stage count2 eviction remains OPEN.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D16 anchor '+a);s=s.replace(a,()=>b);};
 one('i===3?Q[n-4]:w','i===3?Q[n-4]:i===2?Q[n-5]:w');
 one('tag:[...T6.slice(0,3),Q[n-6],Q[n-5],Q[n-4],-1]','tag:[...T6.slice(0,2),Q[n-7],Q[n-6],Q[n-5],Q[n-4],-1]');
 one("T6[3]=base+4;tap('outer');", "T6[3]=base+4;S[2]=base+3;T6[2]=base+3;tap('outer');");
 // Q123 is untouched in the alpha bands ending at120. Reconnect before
 // the first124 band uses it; the123 index is a fixed source-loop boundary.
 one('for(let t=2;t<=n;t++){const m=v.slice(0,t),a=J.slice(0,t),gap=L[n+1-t],cls=D2F.flagHeight(v,t,e,loan),utop=u[t-1];',
     'for(let t=2;t<=n;t++){const m=v.slice(0,t),a=J.slice(0,t),gap=L[n+1-t],cls=D2F.flagHeight(v,t,e,loan),utop=u[t-1];if(t===n-7)put([[J[n-5],5*n+3],[5*n+3,J[n-5]],[J[n-5],5*n+3]]);');
 one('fire:S[1],tst:S[2],aux:-1};emitWalk(new SectorCanonical(n,3),','fire:S[0],tst:S[1],aux:-1};emitWalk(new SectorCanonical(n,2),');
 one('w.tag=w.tag.slice(0,4);return w;})(),L,R,{...ws,fire:S[2]','w.tag=w.tag.slice(0,3);return w;})(),L,R,{...ws,fire:S[1]');
 return s;
};
