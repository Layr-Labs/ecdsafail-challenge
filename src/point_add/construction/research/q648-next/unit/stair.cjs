'use strict';

function stairPlan(owner){
    const k=owner.k,n=k+2,p=owner.prime,top=1n<<BigInt(owner.m),gap=1n<<BigInt(k+1);
    const minimum=k>=32?top-p:1n;
    let best={gain:0,S:0,chunks:[],margin:gap};
    for(let S=1;S<=k;S++)for(const size of [1,2,3,4,6,8]){
        if(size>S)continue;
        const B=1n<<BigInt(S);let err=B-1n,gain=0,o=0;
        const chunks=[];
        for(let j=0;j<size;j++){
            const b=Math.floor(S/size)+(j<S%size?1:0),d=S-o;
            err+=((1n<<BigInt(b))-1n)*(B-(1n<<BigInt(o)));
            gain+=2*b*d-3*(n-d)+2;chunks.push(b);o+=b;
        }
        if(gap-err>=minimum&&gain>best.gain)best={gain,S,chunks,margin:gap-err};
    }
    if(top-p<=best.margin){best.low=owner.m;best.w=1n;return best;}
    let low=best.margin.toString(2).length-1,w=(p>>BigInt(low))+1n;
    while((w&1n)===0n){low++;w>>=1n;}
    best.low=low;best.w=w;return best;
}

function stairStages(r,a,c,plan){
    let d=c.slice(plan.S),o=0;const stages=[];
    for(const b of plan.chunks){
        const q=r.slice(o,o+b);stages.push([q,a.slice(plan.S-o),d]);
        d=q.concat(d);o+=b;
    }
    const q=r.slice(o);stages.push([q,a,d]);
    return {stages,watch:q.concat(d).slice(plan.low-plan.S)};
}

function stairProduct(owner,tape,parts,back){
    if(!back){
        if(owner.unitCone)throw Error('Unclosed staircase unit product');
        const rows=[],trace=Object.create(tape),live=new Uint8Array(tape.n),N=1023;
        trace.out=(a,b,z)=>rows.push((a<<20)|(b<<10)|z);
        for(const [q,v,d] of parts.stages)owner.mixed(trace,q,v,d,[],false);
        for(const i of parts.watch)live[i]=1;
        const keep=[];
        for(let i=rows.length-1;i>=0;i--){
            const row=rows[i],z=row&N;if(!live[z])continue;
            keep.push(row);const a=row>>>20,b=row>>>10&N;
            if(a!==N)live[a]=1;if(b!==N)live[b]=1;
        }
        owner.unitCone=keep;
    }
    const keep=owner.unitCone;
    for(let i=0;i<keep.length;i++){const g=keep[back?i:keep.length-1-i];tape.out(g>>>20,g>>>10&1023,g&1023);}
    if(back)owner.unitCone=null;
}

function patch(split){
    const begin=split.indexOf('function unitThreshold(owner,s=0){'),end=split.indexOf('class EarlyUnit extends UnitPreparation {',begin);
    if(begin<0||end<begin||!split.slice(begin,end).includes('function coinProduct('))throw Error('Expected frozen split helper source');
    let s=split.slice(0,begin)+[stairPlan,stairStages,stairProduct].map(f=>f.toString()).join('\n')+'\n'+split.slice(end);
    function one(a,b){if(s.split(a).length!==2)throw Error('Stair attach '+a);s=s.replace(a,()=>b);}
    one('const s=this.k>>1,threshold=unitThreshold(this,s),watch=r.slice(s).concat(r.slice(0,s),c.slice(s)).slice(threshold.low-s);',
        'const threshold=stairPlan(this),parts=stairStages(r,a,c,threshold),watch=parts.watch;');
    for(const rev of ['rv','!rv'])one(`coinProduct(this,tape,r,a,c,${rev},threshold.low,s)`,`stairProduct(this,tape,parts,${rev})`);
    return s;
}
module.exports={patch,stairPlan};
