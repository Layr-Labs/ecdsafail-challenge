'use strict';
// AFTER D5. Prefix is D7's exact relocation/reconnect. No non-walk changes.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D10 stage anchor '+a);s=s.replace(a,()=>b);};
 one('i===4?Q[n-3]:w','i===4?Q[n-3]:i===3?Q[n-4]:w');
 one('tag:[...T6.slice(0,4),Q[n-5],Q[n-4],-1]','tag:[...T6.slice(0,3),Q[n-6],Q[n-5],Q[n-4],-1]');
 one("put(rev(ss));tap('outer');","put(rev(ss));put([[Q[n-4],base+4],[base+4,Q[n-4]],[Q[n-4],base+4]]);S[3]=base+4;T6[3]=base+4;tap('outer');");
 // Missing inner tag1 is virtual, so its stale mapping can overlap fire.
 one('fire:S[2],tst:S[3],aux:-1};emitWalk(new SectorCanonical(n,3),','fire:S[1],tst:S[2],aux:-1};emitWalk(new SectorCanonical(n,3),');
 one('w.tag=w.tag.slice(0,4);return w;})(),L,R,{...ws,fire:S[3]','w.tag=w.tag.slice(0,4);return w;})(),L,R,{...ws,fire:S[2]');
 return s;
};
