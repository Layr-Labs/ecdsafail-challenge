'use strict';
const {source,compiler}=require('./build.cjs'),{patch}=require('./index.cjs');
const {createHash}=require('node:crypto');
const original=source(),candidate=patch(original,compiler,'mask');
const mark='return {pointReference,exceptionTable,';
const exposed=candidate.replace(mark,'return {Tape,MixedArithmetic,maskedRipple,cleanTop,implicitTopDigit,pointReference,exceptionTable,');
const E=Function('module','require',exposed+'\nreturn module.exports;')({exports:{}},require);
const none=1023,stats=[];
const range=(n,start=0)=>Array.from({length:n},(_,i)=>start+i);
const put=(st,ids,v,l)=>{const mask=1<<(l&31);for(const id of ids){st[id]=(st[id]&~mask)|((v&1)?mask:0);v>>=1;}};
const get=(st,ids,l)=>ids.reduce((v,id,i)=>v|((st[id]>>>(l&31)&1)<<i),0);
for(const h of [1,2,3,4])for(const kind of ['adc','predicated','digit'])for(const back of [false,true]){
    const n=h+2,bound=2**n,low=2**h-1;
    const a=range(n),b=range(n,n),payload=range(h,2*n),flag=2*n+h,hi=flag+1,en=hi+1,clean=en+1,width=clean+9;
    const tuples=[];
    for(const f of [0,1])for(const side of [0,1])for(const predicate of [0,1])
      for(let raw=kind==='digit'?bound/2:0;raw<bound;raw++)for(let y=0;y<bound;y++){
        const x=(raw&~low)|(f?(raw&low):0);
        tuples.push([f,side,predicate,raw,y,x]);
      }
    const initial=range(Math.ceil(tuples.length/32)).map((_,i)=>Uint32Array.from({length:width},(_,q)=>Math.imul(i*0x673+q,0x22a9d053)));
    for(let i=0;i<tuples.length;i++){
      const [f,side,predicate,raw,y,x]=tuples[i],st=initial[i>>5];
      put(st,a,x,i);put(st,b,y,i);put(st,payload,raw&low,i);put(st,[flag,hi,en,clean],f+2*side+4*predicate,i);
    }
    const before=initial.map(st=>st.slice()),target=initial.map(st=>st.slice());
    const t=new E.Tape(width,initial,null,none),u=new E.Tape(width,target,null,none);
    const high=kind==='adc'?hi:null,condition=kind==='predicated'?en:null;
    const run=(tp,m)=>kind==='digit'?E.cleanTop(tp,[...b,hi],m,[en],clean,back):E.MixedArithmetic.prototype.nrAdder.call(null,tp,m,b,high,condition,back);
    if(kind==='digit')E.implicitTopDigit(t,[...b,hi],a,[en],back);else run(t,a);
    const bb=kind==='digit'?[...b,hi]:b;
    E.maskedRipple(u,a,bb,payload,flag,[flag,...payload,hi,en,clean],kind==='adc',run);
    const hash=createHash('sha256');
    for(let g=0;g<initial.length;g++)for(let q=0;q<width;q++){
      if(initial[g][q]!==target[g][q])throw Error('Q648 exhaustive physical mismatch '+[h,kind,back,g,q]);
      if(!b.includes(q)&&q!==hi&&before[g][q]!==target[g][q])throw Error('Q648 exhaustive scratch '+[h,kind,back,g,q]);
    }
    for(let i=0;i<tuples.length;i++){
      const [,side,predicate,,y,x]=tuples[i],st=target[i>>5];let expected=y,bit=side;
      if(kind==='digit'){
        if(back){expected=(y+(predicate&&side?x:0))&(bound-1);bit^=Number(predicate&&expected>=x);}
        else{bit^=Number(predicate&&y>=x);expected=(y-(predicate&&bit?x:0))&(bound-1);}
      }else{
        if(kind==='adc'||predicate)expected=(y+(back?-x:x))&(bound-1);
        if(kind==='adc')bit^=Number(back?y<x:y+x>=bound);
      }
      if(expected!==get(st,b,i)||bit!==get(st,[hi],i))throw Error('Q648 exhaustive arithmetic '+[h,kind,back,i,expected,bit,get(st,b,i),get(st,[hi],i)]);
    }
    for(const st of target)hash.update(new Uint8Array(st.buffer));
    stats.push({prefixWidth:h,kind,back,cases:tuples.length,checksum:hash.digest('hex'),counts:u.count});
}
console.log(JSON.stringify({candidateSha256:createHash('sha256').update(candidate).digest('hex'),cases:stats.reduce((a,x)=>a+x.cases,0),stats},null,2));
