'use strict';
// D7 partial only: remove native644 from normalization/split and all three
// walks. Reconnect count3 before alpha. Remaining count windows still use644.
// Apply AFTER the full D5 overlay; this is not an eight-helper stage.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D7 anchor '+a);s=s.replace(a,()=>b);};
 one('i===4?Q[n-3]:w','i===4?Q[n-3]:i===3?Q[n-4]:w');
 one('tag:[...T6.slice(0,4),Q[n-5],Q[n-4],-1]','tag:[...T6.slice(0,3),Q[n-6],Q[n-5],Q[n-4],-1]');
 one("put(rev(ss));tap('outer');", "put(rev(ss));put([[Q[n-4],base+4],[base+4,Q[n-4]],[Q[n-4],base+4]]);S[3]=base+4;T6[3]=base+4;tap('outer');");
 one('fire:S[2],tst:S[3],aux:-1};emitWalk(new SectorCanonical(n,3),','fire:S[1],tst:S[2],aux:-1};emitWalk(new SectorCanonical(n,2),');
 one('w.tag=w.tag.slice(0,4);return w;})(),L,R,{...ws,fire:S[3]','w.tag=w.tag.slice(0,3);return w;})(),L,R,{...ws,fire:S[2]');
 return s;
};
