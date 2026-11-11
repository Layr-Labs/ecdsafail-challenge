// c2w diagnostics: lane states at in0 (entry), in1 (after entry moves), out0 (po.hmr, before gather).
const path=require('path');const Q=process.env.JQ;const DJ=process.env.DJ;
const D=require(path.join(Q,'divide-i.cjs'));const {Sim}=require(path.join(DJ,'../sim.cjs'));const {gen}=require(path.join(DJ,'../lanes.cjs'));
const n=128,K=+(process.env.K||2),LN=32*K;const vec=(m,o)=>Array.from({length:m},(_,i)=>o+i);
const M=vec(n,0),rm=vec(n,n),H=vec(n,2*n),C=vec(n,4*n);
const sim=new Sim(1024,K);const cs=gen(LN,BigInt(process.env.SEED||1),process.env.MODE||'mixed');cs.forEach(({m,x,c},l)=>{sim.put(M,l,m);sim.put([...rm,...H],l,x);sim.put(C,l,c);});
const lane=[];for(let l=0;l<LN;l++)lane.push({});
globalThis.__c2dbg=(lab,{L,R,Q:QQ})=>{const V=i=>R[n+1-i],U=i=>L[n+1-i],b=(w,l)=>sim.getBit(w,l);
 for(let l=0;l<LN;l++){const z=lane[l];let h=0;for(let i=n-1;i>=0;i--)if(b(V(i),l)){h=i+1;break;}
  let tz=0;while(tz<8&&!b(L[tz],l))tz++;let tv=0;while(tv<8&&!b(V(tv),l))tv++;
  const st={q:[0,1,2,3,4,5].map(i=>b(QQ[i],l)).join(''),g:[0,1,2,3].map(i=>b(L[i],l)).join(''),U1:b(U(1),l),p641:b(641,l),c2:b(643,l),Q127:b(QQ[n-1],l),U2:b(U(2),l),Q1:b(QQ[1],l),Q2:b(QQ[2],l),h,tz,tv};
  z[lab]=st;}
 if(lab==='out1'){let bad=0;for(let l=0;l<LN;l++){const z=lane[l],c2=z.in0.c2,o=z.out0,e=z.out1;
   const okU2=e.U2===z.in0.U2,ok641=e.p641===c2,cls=z.in0.h===128?'C':z.in0.tz>=3?'A':z.in0.tz===2?'B':'C';
   const q2po=cls==='A'?0:cls==='B'?1:o.Q2;const k1=cls==='C'&&z.in0.tz===1&&z.in0.h!==128&&z.in0.tv>=3;const okQ2=e.Q2===(q2po^c2),okQ1=cls==='B'?e.Q1===0:k1?e.Q1===1:e.Q1===o.Q1;
   if(!(okU2&&ok641&&okQ2&&okQ1)){bad++;if(bad<=10)console.log('OUT1 in0',JSON.stringify(z.in0),'out0',JSON.stringify(o),'lane',l,cls,'c2',c2,'h',z.in0.h,'tz',z.in0.tz,'tv',z.in0.tv,'U2 ok',okU2,'641 ok',ok641,'Q2 ok',okQ2,'Q1 ok',okQ1);}}
  console.log('out1 bad',bad);}
 if(lab==='out0'){let bad=0;const rep={};
  for(let l=0;l<LN;l++){const z=lane[l],c2=z.in0.c2,o=z.out0,cls=z.in0.h===128?'C':z.in0.tz>=3?'A':z.in0.tz===2?'B':'C';
   let ok=true,why='';
   if(cls==='A'&&o.Q2!==c2){ok=false;why='A Q2 '+o.Q2;}
   if(cls==='B'&&!(o.Q1===c2&&o.Q2===1)){ok=false;why='B Q1 '+o.Q1+' Q2 '+o.Q2;}
   if(cls==='C'&&z.in0.tv>=3&&z.in0.tz!==1&&o.U2!==c2){ok=false;why='C U2 '+o.U2;}if(cls==='C'&&z.in0.tv>=3&&z.in0.tz===1&&z.in0.h!==128&&!(o.Q1===(1^c2)&&o.U2===z.in0.U2)){ok=false;why='Ck1 Q1 '+o.Q1+' U2 '+o.U2;}
   if(cls==='C'&&z.in0.tv>=3&&z.in1.U2!==c2){ok=false;why+=' C in1 U2 '+z.in1.U2+' (identity?)';}
   if(z.in1.c2!==0){ok=false;why+=' 643 not cleared';}
   if(c2&&z.in0.tz+z.in0.tv<4){ok=false;why+=' FACT violated tz+tv='+(z.in0.tz+z.in0.tv);}
   if(!ok){bad++;if(bad<=12)console.log('lane',l,'cls',cls,'c2',c2,'h',z.in0.h,'tz',z.in0.tz,'tv',z.in0.tv,'|',why,'| out0',JSON.stringify(o));}}
  console.log('out0 check bad',bad,'/',LN,'c2=1 lanes',lane.filter(z=>z.in0.c2).length);}};
D.emitDivideSparse(sim.sink());
