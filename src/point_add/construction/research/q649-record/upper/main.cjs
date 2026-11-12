'use strict';
function cleanTop(tape,z,v,enabled,d,back) {
    if(enabled.length!==1||z.length!==v.length+1)throw Error('clean implicit digit ports');
    const n=v.length,k=n-1,e=enabled[0],h=z[n],top=z[k],a=v.slice(0,-1),b=z.slice(0,k);
    if(!k)return implicitTopDigit(tape,z,v,enabled,back);
    if([...z,...v,e].includes(d))throw Error('overlapping clean digit carry');
    const u=tape.loan([...z,...v,e,d],1)[0],g=[];
    const x=q=>g.push([1023,1023,q]),cx=(c,t)=>g.push([1023,c,t]),cc=(p,q,t)=>g.push([p,q,t]);
    function conditional(other,target){cc(e,u,d);cc(d,other,target);cc(e,u,d);}
    conditional(top,h);
    b.forEach(x);
    for(let i=1;i<k;i++)cx(a[i],b[i]);
    x(u);if(k>1)cx(a[k-1],u);
    for(let i=k-2;i>=1;i--)cx(a[i],a[i+1]);
    for(let i=0;i<k-1;i++)cc(b[i],a[i],a[i+1]);
    cc(b[k-1],a[k-1],u);
    cc(e,u,d);cc(d,top,h);cc(d,h,top);cc(e,u,d);
    cc(b[k-1],a[k-1],u);
    cc(e,h,d);cc(d,a[k-1],b[k-1]);
    for(let i=k-2;i>=0;i--){cc(b[i],a[i],a[i+1]);cc(d,a[i],b[i]);}
    cc(e,h,d);
    for(let i=1;i<k-1;i++)cx(a[i],a[i+1]);
    if(k>1)cx(a[k-1],u);x(u);
    conditional(h,top);
    for(let i=1;i<k;i++)cx(a[i],b[i]);
    b.forEach(x);
    if(back)g.reverse();for(const row of g)tape.out(...row);
}

function decodedAffine(owner,tape,layer,r,a,d,rv) {
    const word=[owner.carry,a[0],a.at(-1),owner.tag[2],a[1]],high=owner.tag.slice(3);
    if(new Set(word.concat(high)).size!==5+high.length)throw Error('overlapping affine recode');
    // After exchanging carry and low, the ordinary ranks already have
    // their two numerical low zeros. Decode rank 0 and 1 at high rank zero.
    const links=new Map();
    for(let x=0;x<2;x++)for(let y=0;y<2;y++)links.set(16+x+4*y,2*x+16*y);
    for(let y=0;y<2;y++)links.set(24+y,1+16*y);
    for(let c=2;c<8;c++){const x=(c&1)+2*(c&6);links.set(x,x);}
    const incoming=new Set(links.values());
    for(const src of [...links.keys()])if(!incoming.has(src)){
        let at=src;while(links.has(at))at=links.get(at);links.set(at,src);
    }
    const seen=new Set(),pairs=[];
    for(const start of links.keys())if(!seen.has(start)){
        let at=start;const cycle=[];
        while(!seen.has(at)){seen.add(at);cycle.push(at);at=links.get(at);}
        for(let i=1;i<cycle.length;i++)pairs.push([start,cycle[i]]);
    }
    const swap=()=>{tape.out(1023,word[0],word[1]);tape.out(1023,word[1],word[0]);tape.out(1023,word[0],word[1]);};
    const recode=back=>{
        if(!back)swap();
        for(const [x,y] of back?pairs.slice().reverse():pairs)owner.u6Transpose(tape,word,x,y,[owner.take],high,false);
        if(back)swap();
    };
    recode(false);
    const local=Object.create(layer),protectedTape=Object.create(tape);
    protectedTape.ids=tape.ids.filter(q=>!word.includes(q)&&!high.includes(q));
    local.digit=(tp,z,v,on,back)=>implicitTopDigit(tp,z,v,on,back);
    local.mixed(protectedTape,r,a,d,[owner.take],rv);
    recode(true);
}
function oneVirtualBit(owner,tape,layer,r,a,d,rv) {
    const tag=owner.tag,word=[...tag,a[1]],b=tag.length,scale=1<<b,exception=scale-1;
    if(owner.maxShift>=exception||new Set(word).size!==b+1)throw Error('affine exceptional rank');
    // Existing U12 encodes both numerical low bits on rare rank 0/1.
    // Encode just A[0] as one unused rank and leave A[1] literal.
    const perm=new Map();
    for(let x=0;x<2;x++)for(let y=0;y<2;y++)perm.set(scale+x+2*y,(x?exception:0)+scale*y);
    for(let y=0;y<2;y++)perm.set(scale+4+y,1+scale*y);
    for(let j=2;j<=owner.maxShift;j++)perm.set(j,j);
    const incoming=new Set(perm.values());
    if(incoming.size!==perm.size)throw Error('affine rank collision');
    for(const start of [...perm.keys()])if(!incoming.has(start)){
        let at=start;while(perm.has(at))at=perm.get(at);perm.set(at,start);
    }
    const used=new Set(),pairs=[];
    for(const start of perm.keys())if(!used.has(start)){
        let at=start;while(!used.has(at)){used.add(at);at=perm.get(at);if(at!==start)pairs.push([start,at]);}
    }
    const recode=back=>{for(const [x,y] of back?pairs.slice().reverse():pairs)owner.u6Transpose(tape,word,x,y,[owner.take],[],false);};
    let lowest=b-1;while(exception-((1<<lowest)-1)<=owner.maxShift)lowest--;
    const ones=tag.slice(lowest),V=-1000,mod=[V,...a.slice(1)],proxy=Object.create(tape);
    proxy.ids=tape.ids.filter(q=>!tag.includes(q));
    proxy.out=(x,y,z)=>{
        if(z===V)throw Error('affine low coefficient was written');
        if(x!==V&&y!==V){tape.out(x,y,z);return;}
        owner.toggle(tape,ones.concat([x,y].filter(q=>q!==V&&q!==1023)),[],z);
    };
    const local=Object.create(layer);
    local.digit=(tp,z,v,on,back)=>cleanTop(tp,z,v,on,owner.carry,back);
    recode(false);local.mixed(proxy,r,mod,d,[owner.take],rv);recode(true);
}
function mainDigits(owner,tape,layer,r,a,d,rv,variant) {
    const local=Object.create(layer);
    if(owner.u12&&variant==='one'&&owner.maxShift<(1<<owner.tag.length)-1){
        oneVirtualBit(owner,tape,layer,r,a,d,rv);return;
    }
    if(variant==='one')variant='clean';
    if(owner.u12&&variant==='decode'){decodedAffine(owner,tape,layer,r,a,d,rv);return;}
    if(!owner.u12||variant==='clean') {
        local.digit=(tp,z,v,on,back)=>{
            const target=owner.u12?owner.u12VirtualTape(tp):tp;
            cleanTop(target,z,v,on,owner.carry,back);
            if(owner.u12)target.u12Check();
        };
        local.mixed(tape,r,a,d,[owner.take],rv);return;
    }
    const source=a[1],carry=owner.carry,protectedTape=Object.create(tape);
    if(owner.tag.includes(carry)||a.includes(carry))throw Error('affine materialization overlap');
    protectedTape.ids=tape.ids.filter(q=>q!==carry);
    const virtual=owner.u12VirtualTape(protectedTape),material=Object.create(virtual);
    const wire=q=>q===source?carry:q;
    material.out=(x,y,z)=>virtual.out(wire(x),wire(y),wire(z));
    virtual.out(1023,source,carry);
    local.digit=(tp,z,v,on,back)=>implicitTopDigit(tp,z,v,on,back);
    local.mixed(material,r,a,d,[owner.take],rv);
    virtual.out(1023,source,carry);virtual.u12Check();
}
// withV swaps the rank into a clean carry and complements the new zero
// high coefficient wire. Its known-one top can serve as a clean scratch
// throughout this mixed product, including when the arithmetic is disabled.
function mixedKnownTop(owner,tape,r,v,d,back) {
    const high=v.at(-1),virtual=v.slice(0,-1).concat(-1001),local=Object.create(owner);
    const protectedTape=Object.create(tape);
    protectedTape.ids=tape.ids.filter(q=>q!==high);
    tape.out(1023,1023,high);
    local.digit=(tp,z,mod,on,rev)=>cleanTop(tp,z,mod,on,high,rev);
    local.mixed(protectedTape,r,virtual,d,[owner.take],back);
    tape.out(1023,1023,high);
}
function patch(s,variant) {
    if(!['clean','materialize','both','decode','one'].includes(variant))throw Error('unknown upper variant');
    function one(a,b){if(s.split(a).length!==2)throw Error('upper main anchor '+a);s=s.replace(a,()=>b);}
    one('class Tape {',cleanTop.toString()+'\n'+mainDigits.toString()+'\n'+decodedAffine.toString()+'\n'+oneVirtualBit.toString()+'\n'+mixedKnownTop.toString()+'\nclass Tape {');
    one("rv=>layer.mixed(tape,this.r.slice(0,base),a,d,[this.take],rv),tail",
        "rv=>mainDigits(this,tape,layer,this.r.slice(0,base),a,d,rv,'"+(variant==='both'?'clean':variant)+"'),tail");
    if(['both','decode','one'].includes(variant))one('layer.mixed(tape,r,v,d,[this.take],!rr);','mixedKnownTop(this,tape,r,v,d,!rr);');
    return s;
}
module.exports={patch,cleanTop,mainDigits,mixedKnownTop};
