'use strict';
// Optional exact extension AFTER p-partial: retain count3 on Q124 through
// alpha bands2..124, then reconnect immediately before the emitted125 band.
// This moves only the reconnect gates; it does not solve heights125..128.
module.exports=s=>{
 const move='put([[Q[n-4],base+4],[base+4,Q[n-4]],[Q[n-4],base+4]]);';
 if(s.split(move).length!==2)throw Error('extended reconnect');s=s.replace(move,'');
 const needle='for(let t=2;t<=n;t++){const m=v.slice(0,t),a=J.slice(0,t),gap=L[n+1-t],cls=D2F.flagHeight(v,t,e,loan),utop=u[t-1];';
 if(s.split(needle).length!==2)throw Error('extended alpha');
 return s.replace(needle,needle+'\n if(t===n-3)put([[J[n-4],5*n+4],[5*n+4,J[n-4]],[J[n-4],5*n+4]]);');
};
