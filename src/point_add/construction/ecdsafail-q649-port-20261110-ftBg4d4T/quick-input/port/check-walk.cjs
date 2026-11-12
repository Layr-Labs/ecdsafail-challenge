'use strict';
const path = require('node:path');
const [ownerArg, compilerArg, widthArg, name] = process.argv.slice(2);
const owner=path.resolve(ownerArg), compiler=path.resolve(compilerArg), n=Number(widthArg), limit=1n<<BigInt(n);
const pub=require(path.join(owner,'public-backend.cjs')).withDigit(require(path.join(owner,'shared-digit.cjs')).sharedDigit);
const {installMultiply,hostedTypes}=require('./wide-walk.cjs');
const H=hostedTypes(owner,compiler,pub), range=(start,len)=>Array.from({length:len},(_,i)=>i+start);
const L=range(0,n+2),R=range(n+2,n+2),dirty=range(2*n+4,2*n),first=4*n+4;
const ports={sign:first,tag:range(first+1,Math.ceil(Math.log2(n))),fire:first+10,tst:first+11,aux:first+12};
const width=first+13;
let reference, candidate;
if(name==='m6'){
    reference=new pub.D2Canonical(n,5);
    installMultiply(owner);
    const donor=require(path.join(owner,'m6-host-walk.cjs'))(pub,5),{implicitTopDigit}=require(path.join(compiler,'implicit-top.cjs'));
    class Multiplication extends donor {
        constantDigit(a,b,h,e){
            const tape={loan:(used,num)=>this.y.filter(q=>!used.includes(q)).slice(0,num),out:(x,y,t)=>x===1023?this.raw(y===1023?-1:y,-1,t):this.raw(x,y===1023?-1:y,t)};
            implicitTopDigit(tape,[...b,h],[...a,-1001],[e],false);
        }
    }
    candidate=new Multiplication(n);candidate.joinedHost=true;
}else if(name==='canonical'){
    reference=new pub.D2Canonical(n,3);candidate=new H.canonical(n);
}else if(name==='reduced'){
    reference=new pub.D2Reduced(n,4);candidate=new H.reduced(n);
}else throw Error('unknown walk family');

function gates(w,hosted){
    const groups=[], ws={...ports,tag:ports.tag.slice()};
    if(hosted){ws.tag[w.tag.length-2]=-1;ws.tag[w.tag.length-1]=-1;}
    (hosted?H.map:pub.emitWalk)(w,L,R,ws,dirty,false,(kind,data)=>{
        if(kind!=='packed')throw Error('logic event in walk');groups.push(Uint32Array.from(data));
    });
    return groups;
}
function run(groups,state,back){
    for(let i=0;i<groups.length;i++){
        const g=groups[back?groups.length-1-i:i];
        for(let j=0;j<g.length;j++){
            const z=g[back?g.length-1-j:j],a=z>>>20,b=z>>>10&1023,t=z&1023;
            state[t]^=a===1023?0xffffffff:b===1023?state[a]:state[a]&state[b];
        }
    }
}
let seed=157698155;function rand(){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed;}
function randomBig(){let result=0n;for(let i=0;i<n;i+=32)result=(result<<32n)|BigInt(rand());return result&(limit-1n);}
function gcd(a,b){while(b)[a,b]=[b,a%b];return a;}
const inputs=[],seen=new Set();
function put(v,r){if(v<=0n||v>=limit||r<0n||r>=v||name!=='reduced'&&gcd(v,r)!==1n)return;const k=v+':'+r;if(!seen.has(k)){seen.add(k);inputs.push([v,r]);}}
if(n<=8){for(let v=1n;v<limit;v++)for(let r=0n;r<v;r++)put(v,r);}
else {
    for(const v of [limit-1n,limit-3n,(limit>>1n)+1n,(limit>>1n)-1n])
        for(let shift=0;shift<n;shift++)for(const delta of [-1n,0n,1n])put(v,(v>>BigInt(shift))+delta);
    for(let i=0;i<1500;i++){const v=randomBig()|1n;if(v>1n)put(v,randomBig()%v);}
}
const before=gates(reference,false),after=gates(candidate,true);
for(let k=0;k<inputs.length;k+=32){
    const x=new Uint32Array(width);
    for(const q of dirty)x[q]=rand();
    for(let j=0;j<32;j++){
        const [v,r]=inputs[(k+j)%inputs.length];for(let i=0;i<n;i++){
            const shift=BigInt(i);x[L[i]]|=Number(v>>shift&1n)<<j;x[R[i]]|=Number(r>>shift&1n)<<j;
        }
    }
    const want=x.slice(),actual=x.slice();
    run(before,want,false);run(after,actual,false);
    for(let i=0;i<width;i++)if(want[i]!==actual[i]){
        const d=(want[i]^actual[i])>>>0, j=31-Math.clz32(d&-d);
        throw Error(JSON.stringify({name,n,wire:i,input:inputs[(k+j)%inputs.length].map(String),expected:(want[i]>>>j)&1,actual:(actual[i]>>>j)&1}));
    }
    run(after,actual,true);
    if(actual.some((v,i)=>v!==x[i]))throw Error('full inverse did not restore workspace');
}
const size=gs=>gs.reduce((sum,group)=>sum+group.length,0);
console.log(JSON.stringify({name,n,inputCount:inputs.length,referenceOps:size(before),candidateOps:size(after),allRegistersAndReverse:true,absentPhysicalTags:2}));
