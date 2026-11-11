'use strict';
// Exploratory source: release count0 for the entire denormalized-M tail.
module.exports=s=>{
 s=require('./i9-divide-p-tail-threshold.cjs')(s);
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D20 tail room anchor '+a);s=s.replace(a,()=>b);};
 one('S[2]=base+3;\n const count3=', 'S[2]=base+3;put(D20Count(M,S[0],C,0));\n const count3=');
 one('S[2]=e;put(D17Count2(M,e,C));put(rot(M,1));put(rev(normal(M,[],S,C,false)));',
 'for(const bit of [1,3,4,5,6])put(D20Count(M,S[bit],C,bit));');
 one('for(const r of fr(S[j],word[a],word[b]))rows.push(...D17Oracle(r.slice(0,-1),r.slice(0,-1).map(()=>true),r.at(-1),S[2],M,loan));',
 'for(const r of fr(S[j],word[a],word[b]))rows.push(...(j===0?D20Bit0Oracle(r.slice(0,-1),r.at(-1),S[0],M,loan):D17Oracle(r.slice(0,-1),r.slice(0,-1).map(()=>true),r.at(-1),S[2],M,loan)));');
 return s+`
function D20Count(M,z,loan,bit){const out=[];for(let k=1<<bit;k<M.length;k+=1<<bit){const w=M.slice(M.length-k);out.push(...D17Raw(w,w.map(()=>false),z,loan));}return out;}
function D20Bit0Oracle(cs,z,virtual,M,loan){
 if(!cs.includes(virtual))return D17Raw(cs,cs.map(()=>true),z,loan);
 const rest=cs.filter(q=>q!==virtual),out=[];
 for(let k=1;k<M.length;k++){const w=M.slice(M.length-k);out.push(...D17Raw([...rest,...w],[...rest.map(()=>true),...w.map(()=>false)],z,loan));}return out;
}
`;
};
