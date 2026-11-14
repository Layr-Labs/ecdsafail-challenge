'use strict';
const {source,compiler}=require('./build.cjs'),{patch}=require('./index.cjs'),{extend}=require('./marker.cjs'),{createHash}=require('node:crypto');
const raw=extend(patch(source(),compiler)),s=raw.replace('return {pointReference,exceptionTable,','return {Tape,UnguardedGeneral,markerCode,markerAdder,pointReference,exceptionTable,');
const E=Function('module','require',s+'\nreturn module.exports;')({exports:{}},require);
const range=(n,start=0)=>Array.from({length:n},(_,i)=>i+start);
const put=(st,ids,v,l)=>{const mask=1<<(l&31);for(const id of ids){st[id]=(st[id]&~mask)|((v&1)?mask:0);v>>=1;}};
const get=(st,ids,l)=>ids.reduce((v,w,q)=>v|((st[w]>>>(l&31)&1)<<q),0);
const stages=[];
for(const h of [3,4])for(const plain of [false,true])for(const back of [false,true]){
    const n=h+2,m=1<<n,a=range(n),b=range(n,n),tag=range(h+2,2*n),f=tag.at(-1),hi=f+1,c=f+2,width=f+8;
    const H=Object.create(E.UnguardedGeneral.prototype);H.u9H=h;H.u40Tag=tag;
    const cases=[];
    for(let code=0;code<(1<<(h+1));code++)for(const flag of [0,1])for(const high of [0,1])for(const pred of [0,1])for(let aHigh=0;aHigh<4;aHigh++)for(let y=0;y<m;y++){
        let r=0,off=0;while(r<h-1&&code>=off+(1<<(h-r))){off+=1<<(h-r);r++;}
        const low=(code&((1<<(h-r))-1))<<r,x=(aHigh<<h)+(flag?low:0);
        cases.push({code,flag,high,pred,y,x});
    }
    const words=range(cases.length/32).map((_,i)=>Uint32Array.from({length:width},(_,j)=>Math.imul(j+i,0xbc7d5649)));
    for(let i=0;i<cases.length;i++){
        const z=cases[i],st=words[i>>5];put(st,tag,z.code+(z.flag<<(h+1)),i);
        put(st,[hi,c],z.high+2*z.pred,i);put(st,a,z.x,i);put(st,b,z.y,i);
    }
    const before=words.map(w=>w.slice()),t=new E.Tape(width,words,null,1023);
    E.markerCode(H,t,false);E.markerAdder(H,t,a,b,plain?hi:null,plain?null:c,back);E.markerCode(H,t,true);
    for(let i=0;i<cases.length;i++){
        const {high,pred,y,x}=cases[i],st=words[i>>5];
        const dest=(y+((plain||pred)?(back?-x:x):0))&(m-1),bit=high^Number(plain&&(back?y<x:y+x>=m));
        if(dest!==get(st,b,i)||bit!==get(st,[hi],i))throw Error('marker arithmetic '+[h,plain,back,i]);
    }
    const hash=createHash('sha256');for(let j=0;j<words.length;j++){
        const st=words[j];for(let k=0;k<width;k++)if(k!==hi&&!b.includes(k)&&st[k]!==before[j][k])throw Error('marker scratch '+[h,plain,back,j,k]);
        hash.update(new Uint8Array(st.buffer));
    }
    stages.push({h,plain,back,cases:cases.length,counts:t.count,digest:hash.digest('hex')});
}
console.log(JSON.stringify({sourceDigest:createHash('sha256').update(raw).digest('hex'),cases:stages.reduce((sum,r)=>sum+r.cases,0),stages},null,2));
