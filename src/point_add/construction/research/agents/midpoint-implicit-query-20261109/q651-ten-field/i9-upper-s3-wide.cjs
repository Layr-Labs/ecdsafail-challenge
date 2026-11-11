'use strict';
// In the ripple descent a_i is a control of the next carry restoration.
// Pre-mask b_i by d*(1 xor a_i) so that its use beside a_i is unchanged.
function sharedRippleTail(a,b,controls,loans,one){
    const n=a.length,enabled=controls.filter(q=>q!==one),m=enabled.length;
    if(n<2||m<2||enabled.some(q=>q<0)||new Set(enabled).size!==m)return null;
    const choose=new Set([...a,...b,...controls]);
    const available=loans.filter(q=>!choose.has(q));
    if(available.length<1+Math.max(0,m-2))return null;
    const toggles=m===2?1:4*m-8;
    if(2*n+2*toggles>=(4*m-4)*n)return null;
    const d=available[0],rest=available.slice(1),list=[];
    for(let i=0;i<n;i++){list.push([[d,a[i]],b[i]]);if(i+1<n)list.push([[d],b[i]]);}
    list.push([enabled,d,rest],[[d,a[n-1]],b[n-1]]);
    for(let i=n-2;i>=0;i--)list.push([[a[i],b[i]],a[i+1]],[[d,a[i]],b[i]]);
    list.push([enabled,d,rest]);for(let i=0;i+1<n;i++)list.push([[d],b[i]]);
    return list;
}
function addWideTransforms(source){
    const one=(a,b)=>{if(source.split(a).length!==2)throw Error('wide arithmetic anchor '+a);source=source.replace(a,()=>b);};
    one('class Tape {',sharedRippleTail.toString()+'\nclass Tape {');
    const e='for(let i=n-1;i>=1;i--){lasting(a[i],b[i]);cc(a[i-1],b[i-1],a[i]);}';
    one(e,'const sharedTail=sharedRippleTail(a,b,controls,loans,this.one);if(sharedTail)calls.push(...sharedTail);else '+e);
    one('        lasting(a[0],b[0]);','        if(!sharedTail)lasting(a[0],b[0]);');
    one('stepList(calls,inverse,g=>this.mc(g[0],g[1],loans));','stepList(calls,inverse,g=>this.mc(g[0],g[1],g[2]||loans));');
    const a='for(let i=k-1;i>=1;i--){after.push([[...base,a[i]],b[i]]);cc(after,a[i-1],b[i-1],a[i]);}';
    one(a,'const sharedTail=sharedRippleTail(a,b,base,loans,this.one);if(sharedTail)after.push(...sharedTail);else '+a);
    one('        after.push([[...base,a[0]],b[0]]);','        if(!sharedTail)after.push([[...base,a[0]],b[0]]);');
    one('const execute=(list,rev)=>stepList(list,rev,g=>this.mc(g[0],g[1],loans));','const execute=(list,rev)=>stepList(list,rev,g=>this.mc(g[0],g[1],g[2]||loans));');
    const list='        for(const q of word)tape.mc(controls,q,loans);';
    one(list,`        const nonfixed=controls.filter(q=>q!==tape.one);
        if(nonfixed.length>=2&&word.length>=2&&new Set(word).size===word.length&&!word.some(q=>controls.includes(q))){
            const pivot=word[0];
            for(let i=1;i<word.length;i++)tape.out(NONE,pivot,word[i]);
            tape.mc(controls,pivot,loans);
            for(let i=1;i<word.length;i++)tape.out(NONE,pivot,word[i]);
        }else for(const q of word)tape.mc(controls,q,loans);`);
    return source;
}
module.exports={sharedRippleTail,addWideTransforms};
