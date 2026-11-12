'use strict';
// B <- B+A mod M on 0<=A,B<M. The external guard is disjoint from B.
// Three interval reflections implement rotation by A. Each reflection is an
// involution preserving its membership predicate. Two dirty-control echoes
// implement it exactly, without requiring any zero-valued scratch wire.
function build({M,A,B,guard=[],pol=guard.map(()=>true),loan,plus,ltg,mcN,incReg,back=false}){
 const used=new Set([...M,...(A===1?[]:A),...B,...guard]);const free=loan.filter(q=>!used.has(q));if(free.length<3)throw Error('D25 modular-add loans');const[d,f,g]=free;
 const triples=rows=>{const out=[];for(let j=0;j<rows.length;j++){const r=rows[j];if(!r.includes(1000)){out.push(r);continue;}const b=rows[j+1],c=rows[j+2];if(r.length!==3||r[2]!==1000||b?.[0]!==1000||JSON.stringify(r)!==JSON.stringify(c))throw Error('D25 product anchor');const x=[r[0],r[1],g],y=[g,b[1],b[2]];out.push(x,y,x,y);j+=2;}return out;};
 const flag=mcN(guard,pol,f,loan.filter(q=>q!==d&&q!==f));
 // XOR guard AND (B<K) into arbitrary d; f,g are arbitrary and restored.
 const cmp=K=>{const c=triples(ltg(K,B,d,f,1000));return [...flag,...c,...flag.slice().reverse(),...c];};
 const cm=cmp(M),ca=A===1?mcN([...guard,...B],[...pol,...B.map(()=>false)],d,loan.filter(q=>q!==d)):cmp(A),out=[];
 for(const kind of [0,1,2]){const p=kind===0?cm:kind===1?ca:[...cm,...ca];const reflect=B.map(q=>[d,q]);if(kind!==1)reflect.push(...plus(M,B,null,d));if(kind!==0)reflect.push(...(A===1?incReg(B,loan.filter(q=>q!==d&&!B.includes(q)),d):plus(A,B,null,d)));out.push(...p,...reflect,...p,...reflect);}
 return back?out.reverse():out;
}
module.exports={build};
