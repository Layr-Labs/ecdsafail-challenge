'use strict';
// Count0 occupies unused Q[n-8] through the split and forward outer walk.
// Transfer to the still-clean native base+1 at the unchanged alpha interface.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D20 prefix anchor '+a);s=s.replace(a,()=>b);};
 one('i===2?Q[n-5]:w','i===2?Q[n-5]:i===0?Q[n-8]:w');
 one("T6[2]=base+3;tap('outer');", "T6[2]=base+3;put([[Q[n-8],base+1],[base+1,Q[n-8]]]);S[0]=base+1;T6[0]=base+1;tap('outer');");
 return s;
};
