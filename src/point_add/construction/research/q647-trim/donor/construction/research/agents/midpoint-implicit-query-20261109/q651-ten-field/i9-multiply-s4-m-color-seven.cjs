'use strict';
module.exports=s=>{
 const edit=(a,b)=>{if(s.split(a).length!==2)throw Error('color7 '+a);s=s.replace(a,()=>b);};
 // Increment/decrement canonical residue with an arbitrary, restored dirty bit.
 const def=`
function m7dec(M,B,h,dirty){
 const top=B.at(-1),loM=M.slice(0,-1),loB=B.slice(0,-1);
 const lessA=negate(B,MCX(B,h,dirty.filter(q=>q!==h)),B.map(()=>false));
 const lessM=[[h],[top,h],...r36lt(loM,loB,h,top)];
 const refl=withM=>[...B.map(z=>[h,z]),...incReg(B,dirty.filter(q=>q!==h),h),...(withM?r36plus(M,B,null,h):[])];
 const a=refl(false),b=refl(true),p=[...lessA,...lessM];
 return [...a,...lessA,...a,...lessA,...b,...p,...b,...p,...B.map(z=>[z]),...r36plus(M,B,null)];
}
function m7controlled(g,e,dirty){const out=[];for(const row of g){const cs=[e,...row.slice(0,-1)],z=row.at(-1);if(z===e||row.slice(0,-1).includes(e))throw Error('color control alias');out.push(...MCX(cs,z,dirty.filter(q=>q!==z&&!cs.includes(q))));}return out;}
`;
 edit('can=digit(n,T,C,color),mad=[[T[127]],[color,T[127]],[T[127],color],[color,T[127]],...r36madd([...T.slice(0,-1),1001],C,H,color),[color,T[127]],[T[127],color],[color,T[127]],[T[127]]]',
 'can=r36digit([...T.slice(0,-1),1001],C,T[127]),mad=m6sub([...T.slice(0,-1),1001],C,H,L[0]).reverse()');
 edit('ops,R.slice(0,128).map((q,i)=>[q,H[i]]),inv','ops,md,inv');
 const start='run(ff.g);run(norm);run(can);run(mad);for(let i=0;i<n;i++){run([[C[i],H[i]]]);sink(\'hmr\',[H[i],i]);sink(\'phase\',[C[i],i]);}prep(false);run(can,true);unit(false);power(false);run(can);prod(true);for(let i=0;i<n;i++)sink(\'phase\',[C[i],i]);prod(false);run(can,true);power(true);unit(true);run(can);prep(true);run(can,true);run(unn,true);';
 const body=`
 const q=T[127],odd=T[0],dec=m7controlled(m7dec([...T.slice(0,-1),1001],H,L[0],L.slice(1)),q,L.slice(1));
 const oddCopy=[[odd,q,S[6]]],evenRead=[[odd],[odd,q],[odd,H[0],q],[odd]],oddRead=[[odd,S[6],q]];
 function colorIn(){run([[q]]);run(can);}
 function colorOut(){run(can,true);run([[q]]);}
 function remember(){run([[q,H[0]],...oddCopy,[H[0],q],[q]]);}
 function readAfter(){run([[q],...evenRead,...oddRead,...oddCopy]);}
 const er4=[];for(let j=16;j<128;j+=16){const lo=[...T.slice(0,j),...H.slice(0,j)];er4.push(...negate(lo,MCX(lo,S[4],L),lo.map(()=>false)));}
 const prodcan=digit(n,T,C,S[4]);
 run(ff.g);run(norm);colorIn();run(mad);
 for(let i=0;i<n;i++){run([[C[i],H[i]]]);sink('hmr',[H[i],i]);sink('phase',[C[i],i]);}
 remember();prep(false);readAfter();run(dec);colorOut();
 unit(false);power(false);run(er4);run(prodcan);prod(true);
 for(let i=0;i<n;i++)sink('phase',[C[i],i]);
 prod(false);run(prodcan,true);run(er4,true);power(true);unit(true);
 colorIn();run(dec,true);run(oddCopy);run([...evenRead,...oddRead,[q]]);
 prep(true);run([[q],[H[0],q],[q,H[0]],...oddCopy]);colorOut();run(unn,true);`;
 edit(start,body);
 return def+s;
};
