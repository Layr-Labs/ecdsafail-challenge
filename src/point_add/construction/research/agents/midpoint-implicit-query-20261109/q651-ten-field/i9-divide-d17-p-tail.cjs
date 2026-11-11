'use strict';
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D17 tail anchor '+a);s=s.replace(a,()=>b);};
 one('S.length===7&&j===3)continue;', 'S.length===7&&(j===2||j===3))continue;');
 one(' S[3]=t;\n {const z=', ` S[3]=t;
 {const z=mcN(M.slice(0,3),[false,false,false],e,C);put(z);put([[e,Q[2],M[n-1]],[e,rm[2],M[n-1]]]);put(rev(z));
 put([[M[n-1]]]);sink('phase',[M[n-1],bits+2]);put([[M[n-1],Q[2]],[M[n-1]]]);}
 S[2]=M[n-1];
 {const z=`);
 one('const q=gt(S,j,e,null,C);put(q);put(D2F.dirtyDigit(M.slice(j+1),Q.slice(0,n-1-j),Q[n-1-j],e,C[0]));put(rev(q));',
     'const q=D17GTEncoded(S,j,e,C);put(q);const rows=[];eliminate(D2F.dirtyDigit(M.slice(j+1),Q.slice(0,n-1-j),Q[n-1-j],e,C[0]),M[n-1],1,(cs,z)=>rows.push(...MCX(cs,z,C.filter(w=>w!==z&&!cs.includes(w)))));put(rows);put(rev(q));');
 one('put(rot(M,-1));', `// Remove count2's four-bit rotation while its negative host stays fixed.
 put([[M[n-1]]]);for(const [a,b]of rotleft(n-1,n-5))put(fr(M[n-1],M[a],M[b]));put([[M[n-1],M[n-5]],[M[n-1]]]);
 for(let j=0;j<bits;j++)if(j!==2)for(const [a,b]of rotleft(n,n-(1<<j)))put(fr(S[j],M[a],M[b]));
 S[2]=base+3;`);
 const needle='const q=gt(S,n-i-1,e,null,C);';if(s.split(needle).length!==3)throw Error('D17 tail threshold count');
 s=s.split(needle).join('const q=D17GTOracle(S,n-i-1,e,C,M);');
 one('const rt=rot(rm,-1);', 'const rt=D17RotOracle(rm,-1,S,M,C);');
 one('put(rot(M,1));put(rev(normal(M,[],S,C,false)));',
     'S[2]=e;put(D17Count2(M,e,C));put(rot(M,1));put(rev(normal(M,[],S,C,false)));');
 return s+`
function D17GTEncoded(S,value,e,loan){const rows=[];
 for(let j=0;j<S.length;j++)if(!(value>>j&1)){
  const cs=[S[j],...S.slice(j+1)],ps=[true,...S.slice(j+1).map((_,b)=>!!(value>>(b+j+1)&1))];
  const ix=cs.indexOf(S[2]);if(ix>=0)ps[ix]=!ps[ix];rows.push(...D17Raw(cs,ps,e,loan));
 }return rows;
}
function D17Count2(M,z,loan){const rows=[];for(let shift=4;shift<M.length;shift+=4){const w=M.slice(M.length-shift);rows.push(...D17Raw(w,w.map(()=>false),z,loan));}return rows;}
function D17Oracle(cs,ps,z,virtual,M,loan){
 const i=cs.indexOf(virtual);if(i<0)return D17Raw(cs,ps,z,loan);
 const c=cs.filter((_,j)=>j!==i),p=ps.filter((_,j)=>j!==i),rows=[];
 if(!ps[i])rows.push(...D17Raw(c,p,z,loan));
 for(let shift=4;shift<M.length;shift+=4){const w=M.slice(M.length-shift);rows.push(...D17Raw([...c,...w],[...p,...w.map(()=>false)],z,loan));}
 return rows;
}
function D17GTOracle(S,value,e,loan,M){const rows=[];
 for(let j=0;j<S.length;j++)if(!(value>>j&1)){
  const cs=[S[j],...S.slice(j+1)],ps=[true,...S.slice(j+1).map((_,b)=>!!(value>>(b+j+1)&1))];rows.push(...D17Oracle(cs,ps,e,S[2],M,loan));
 }return rows;
}
function D17RotOracle(word,dir,S,M,loan){const rows=[];
 for(let j=0;j<S.length;j++)for(const [a,b]of rotleft(word.length,(word.length+dir*(1<<j))%word.length)){
  for(const r of fr(S[j],word[a],word[b]))rows.push(...D17Oracle(r.slice(0,-1),r.slice(0,-1).map(()=>true),r.at(-1),S[2],M,loan));
 }return rows;
}
`;
};
