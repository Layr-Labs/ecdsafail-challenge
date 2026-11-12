'use strict';
const {replaceCount}=require('./index.cjs');

// For the compact four-/five-bit register encode the normalized coefficient
// A and its rank r by c=2*A+2^r. Bit A[j] is c[j+1] when c[0..j] contains
// the marker. The ripple suppresses the first gate propagating out of that
// marker, so none of its operations can move the lowest one down or up.
function markerCode(owner,tape,back){
    const h=owner.u9H,word=owner.u40Tag.slice(0,h+1),map=new Map();
    if((h!==3&&h!==4)||word.length!==h+1||word.includes(owner.u40Tag.at(-1)))throw Error('Q648 noncompact marker capacity');
    let offset=0;
    for(let r=0;r<h;r++){
        const count=1<<(h-r);
        for(let low=0;low<count;low++)map.set(offset+low,((low<<1)+1)<<r);
        offset+=count;
    }
    // The two spare old codewords decode through the final rank category
    // with low magnitudes zero and 2^(h-1). Cover them as well so the probe
    // bracket has the same permutation even on arbitrary disabled lanes.
    map.set(offset,0);map.set(offset+1,1<<h);
    if(new Set(map.values()).size!==1<<(h+1))throw Error('Q648 marker permutation collision');
    const swapped=[],visited=new Set();
    for(const start of map.keys())if(!visited.has(start)){
        let at=start;
        while(!visited.has(at)){visited.add(at);at=map.get(at);if(at!==start)swapped.push([start,at]);}
    }
    for(const [u,v] of back?swapped.reverse():swapped)owner.u6Transpose(tape,word,u,v,[],[],false);
}

function markerAdder(owner,tape,a,b,high,condition,back){
    const h=owner.u9H,tag=owner.u40Tag,flag=tag.at(-1),q=tag.slice(0,h+1),none=1023,base=-1240;
    const symbols=Array.from({length:h},(_,j)=>base-j),which=x=>base-x;
    const low=x=>x<=base&&x>base-h,rewrite=x=>low(x)?q[which(x)+1]:x;
    const occurrences=Array(h).fill(0),plain=condition===null,proxy=Object.create(tape);
    proxy.ids=tape.ids.filter(w=>!tag.includes(w));
    proxy.out=(x,y,t)=>{
        const xo=low(x),yo=low(y),to=low(t);
        if(!xo&&!yo&&!to){tape.out(x,y,t);return;}
        if(Number(xo)+Number(yo)!==1)throw Error('noncompact sign unexpected prefix gate');
        const j=which(xo?x:y),actual=rewrite(t),other=xo?y:x;
        const controls=[q[j+1]];if(other!==none)controls.push(other);
        let permanent=t===a[h];
        if(!permanent&&!to){
            if(b[j]!==t)throw Error('noncompact sign prefix output');
            if(x===none){occurrences[j]++;permanent=plain&&(j===0||occurrences[j]===2);}
            else permanent=true;
        }
        if(permanent)controls.push(flag);
        owner.toggle(tape,controls,[],actual);
        if(j<h-1)owner.toggle(tape,controls,q.slice(0,j+1),actual);
    };
    MixedArithmetic.prototype.nrAdder.call(owner,proxy,symbols.concat(a.slice(h)),b,high,condition,back);
    for(let j=0;j<h;j++)if(occurrences[j]!==2*(j>0)+Number(plain))throw Error('noncompact sign write count');
}

function markerMixed(owner,tape,q,a,d,back){
    const layer=Object.create(owner);
    layer.nrAdder=(tp,src,b,high,c,rv)=>markerAdder(owner,tp,src,b,high,c,rv);
    markerCode(owner,tape,false);layer.unguardedMixed(tape,q,a,d,back);markerCode(owner,tape,true);
}
function markerAdd(owner,tape,a,d,back){
    markerCode(owner,tape,false);markerAdder(owner,tape,a,d,null,null,back);markerCode(owner,tape,true);
}
function extend(s){
    s=replaceCount(s,'class Tape {',[markerCode,markerAdder,markerMixed,markerAdd].map(f=>f.toString()).join('\n')+'\nclass Tape {');
    const mix='if(this.u648C&&v[0]===this.u40Low&&!controls.length)';
    s=replaceCount(s,mix,"if(this.u9H&&!this.u648C&&v[0]===this.u40Low&&!controls.length){markerMixed(this,tape,q,v,rem,back);return;}\n      "+mix);
    const add='rv=>H.u648C?maskedProbeAdd(H,tape,a,D)(null,null,rv):';
    return replaceCount(s,add,add+"H.u9H?markerAdd(H,tape,a,D,rv):",3);
}
module.exports={extend};
