'use strict';
// Partial ninth-helper construction: removes native645 from the three walks only.
// Retained c4 and non-walk windows remain unchanged. Not a complete 650 stage.
module.exports=function(s){function one(a,b){if(s.split(a).length!==2)throw Error('R37 D walk anchor '+a);s=s.replace(a,()=>b);}
one('tag:[...T6.slice(0,5),Q[n-4],-1],fire:Q[n-2],tst:Q[n-3]','tag:[...T6.slice(0,4),Q[n-5],Q[n-4],-1],fire:Q[n-2],tst:Q[n-3]');
one('const wi={sign:L[1],tag:[...T6,-1],fire:S[3],tst:S[4],aux:-1};emitWalk(new SectorCanonical(n,4),','const wi={sign:L[1],tag:[...T6,-1],fire:S[2],tst:S[3],aux:-1};emitWalk(new SectorCanonical(n,3),');
one('emitWalk(new Reduced(n,4),L,R,{...ws,fire:S[4],tst:L[n+1],aux:-1},loan,true,sink);','emitWalk((()=>{const w=new Reduced(n,4);w.tag=w.tag.slice(0,4);return w;})(),L,R,{...ws,fire:S[3],tst:L[n+1],aux:-1},loan,true,sink);');return s;};
