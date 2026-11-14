'use strict';
const N=1023;
function toggle(set,k){if(set.has(k))set.delete(k);else set.add(k);}
function synthesize(left,right,ca,cb,old,t){
    const u=old>>>20,v=(old>>>10)&1023;
    const variables=[u,v];
    for(const q of left)if(!variables.includes(q))variables.push(q);
    for(const q of right)if(!variables.includes(q))variables.push(q);
    if(variables.length>8)return null;
    const n=variables.length, x=variables.map(q=>Number(left.has(q))), y=variables.map(q=>Number(right.has(q)));
    const linear=x.map((xi,i)=>(xi&y[i])^(ca&y[i])^(cb&xi));
    const Q=new Uint8Array(n*n);
    let a=-1,b=-1;
    for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){
        const value=(x[i]&y[j])^(x[j]&y[i])^Number(i===0&&j===1);
        Q[n*i+j]=Q[n*j+i]=value;
        if(value&&a===-1){a=i;b=j;}
    }
    const cx=(q,z)=>(q<<20)|(N<<10)|z, out=[];
    if(a>=0){
        const U=variables.map((_,i)=>Q[n*i+b]), V=variables.map((_,i)=>Q[n*a+i]);
        for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)
            if(((U[i]&V[j])^(U[j]&V[i]))!==Q[n*i+j])return null;
        for(let i=0;i<n;i++){
            if(U[i]&&i!==a)out.push(cx(variables[i],variables[a]));
            if(V[i]&&i!==b)out.push(cx(variables[i],variables[b]));
            linear[i]^=U[i]&V[i];
        }
        const basis=out.slice(),aWire=variables[a],bWire=variables[b];
        out.push((Math.min(aWire,bWire)<<20)|(Math.max(aWire,bWire)<<10)|t);
        for(let i=basis.length-1;i>=0;i--)out.push(basis[i]);
    }
    for(let i=0;i<n;i++)if(linear[i])out.push(cx(variables[i],t));
    if(ca&cb)out.push((N<<20)|(N<<10)|t);
    return out;
}
function reduceAffine(words,window=16){
    const buf=[];
    for(const g of words){
        const a=g>>>20,b=(g>>>10)&1023,t=g&1023;
        if(b===N){buf.push(g);continue;}
        const first=Math.max(0,buf.length-window);
        let pair=-1;
        for(let i=buf.length-1;i>=first;i--){
            const k=buf[i],u=k>>>20,v=(k>>>10)&1023;
            if(u===t||v===t)break;
            if((k&1023)===t&&v!==N){pair=i;break;}
        }
        if(pair<0){buf.push(g);continue;}
        const left=new Set([a]),right=new Set([b]);let ca=0,cb=0,ok=true;
        for(let i=buf.length-1;i>pair;i--){
            const k=buf[i],z=k&1023,u=k>>>20,v=(k>>>10)&1023;
            const l=left.has(z),r=right.has(z);
            if(!l&&!r)continue;
            if(v!==N){ok=false;break;}
            if(u===N){ca^=Number(l);cb^=Number(r);}
            else{if(l)toggle(left,u);if(r)toggle(right,u);}
        }
        const seq=ok?synthesize(left,right,ca,cb,buf[pair],t):null;
        if(seq&&seq.length<=12)buf.splice(pair,1,...seq);
        else buf.push(g);
    }
    return buf;
}
module.exports={reduceAffine};
