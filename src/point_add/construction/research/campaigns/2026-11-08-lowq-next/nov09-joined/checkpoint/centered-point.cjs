// Reversible secp256k1 midpoint and passenger arithmetic. Node.js 18 or later.
// Run "node midpoint656.cjs field" for an input-independent field-width forward and inverse gate replay.
// Other modes are toy, stress, payload-toy, payload-field, and math.
//
// At each Euclidean step p=H*V+r*U and A=U+floor(H/r)*V. The successor satisfies
// p=r*A+z*V and 0<z<r. A public coefficient-height schedule admits arbitrary quotients.
// A quotient-one preparation halves the number of unrestricted steps. The shorter
// public-divisor calculation uses the top digits of normalized rV+U. Six guard bits
// give q or q+1 when the odd divisor is chosen below the top word for 2U<=V and
// above it otherwise. Its oddness permits in-place quotient recovery modulo a power
// of two. Small remaining coefficient-height ranges use the two-correction variant.
//
// The field replay includes raw sign normalization and the first r<2^128 crossing.
// All 256 passenger bits are preserved. The 657-wire callable encoder's outer enable
// is fixed at one in the 656-wire circuit. Input fixtures provide no width itinerary.
// The gate alphabet is X, CX and CCX. PayloadDigit is separately tested on its prepared
// ports. The point-addition construction in math mode is an integer reference. The
// routed end-to-end point addition still needs a gate-stream implementation.
// Fused and nonrestoring division follow https://arxiv.org/abs/2603.18110 .
// Passenger recurrence follows the public ECDSA Fail payload.rs algorithm.
//
const midpoint656 = (function arithLab() {
"use strict";

function split(lo,hi) {
    const out=[];
    for(let i=lo;i<hi;i++)out.push(i);
    return out;
}
function stepList(seq,back,perform) {
    if(back){for(let i=seq.length-1;i>=0;i--)perform(seq[i]);}
    else for(const item of seq)perform(item);
}
function codeGate(a,b,t) {
    // gate ids 0..1022; 1023 is the omitted-control sentinel
    return (a*1024+b)*1024+t;
}
const NONE=1023;
class Tape {
    constructor(size,batches,extraDirty,guard) {
        this.n=size;this.batches=batches;this.ids=split(0,size);
        this.guard=guard;this.extraDirty=extraDirty;this.count=[0,0,0];this.wireUse=new Set();
        this.clock=0;this.sig=0x811c9dc5;
    }
    out(a,b,t) {
        if(t===a||t===b||(a!==NONE&&a===b))throw Error("gate aliases");
        const k=a!==NONE?2:b!==NONE?1:0;this.count[k]++;
        this.wireUse.add(t);if(a!==NONE)this.wireUse.add(a);if(b!==NONE)this.wireUse.add(b);
        this.sig=Math.imul(this.sig^codeGate(a,b,t),0x01000193)>>>0;
        if(k===2){for(const r of this.batches)r[t]=(r[t]^(r[a]&r[b]))>>>0;}
        else if(k===1){for(const r of this.batches)r[t]=(r[t]^r[b])>>>0;}
        else{for(const r of this.batches)r[t]=~r[t]>>>0;}
    }
    // A gate (possibly with extra controls) is decomposed to X/CX/CCX.
    // For three or more controls, conjugate about one restored dirty bit.
    mc(cs,t,dirty) {
        const n=cs.length;
        if(n===0){this.out(NONE,NONE,t);return;}
        if(n===1){this.out(NONE,cs[0],t);return;}
        if(n===2){this.out(cs[0],cs[1],t);return;}
        if(dirty.length>=n-2){
            const d=dirty;
            for(let i=0;i<n-2;i++)this.out(i===0?cs[0]:d[i-1],cs[i+1],d[i]);
            this.out(d[n-3],cs[n-1],t);
            for(let i=n-3;i>=0;i--)this.out(i===0?cs[0]:d[i-1],cs[i+1],d[i]);
            for(let i=1;i<n-2;i++)this.out(d[i-1],cs[i+1],d[i]);
            this.out(d[n-3],cs[n-1],t);
            for(let i=n-3;i>=1;i--)this.out(d[i-1],cs[i+1],d[i]);
            return;
        }
        const cut=Math.ceil(n/2),a=cs.slice(0,cut),b=cs.slice(cut);
        const x=dirty[0],pool=dirty.slice(1);
        if(x===undefined||cs.includes(x)||x===t)throw Error("missing dirty control");
        this.mc(a,x,pool);this.mc([x,...b],t,pool);
        this.mc(a,x,pool);this.mc([x,...b],t,pool);
    }
    loan(used,limit) { if(limit===0)return [];
        const bad=new Set([...used,this.guard]);
        const out=[];
        for(const q of this.ids){if(!bad.has(q))out.push(q);if(out.length===limit)break;}
        if(out.length<limit)throw Error("loan capacity");
        return out;
    }
    // The conditional Takahashi ripple has no input carry wire.
    equal(a,b,controls,discard,inverse,loans) {
        const n=b.length;
        if(a.length!==n||n===0)throw Error("unequal ripple");
        let calls=[];
        const cx=(x,y)=>calls.push([[x],y]);
        const cc=(x,y,z)=>calls.push([[x,y],z]);
        const lasting=(x,y)=>calls.push([[...controls,x],y]);
        for(let i=1;i<n;i++)cx(a[i],b[i]);
        for(let i=n-2;i>=1;i--)cx(a[i],a[i+1]);
        for(let i=0;i<n-1;i++)cc(a[i],b[i],a[i+1]);
        for(let i=n-1;i>=1;i--){lasting(a[i],b[i]);cc(a[i-1],b[i-1],a[i]);}
        for(let i=1;i<n-1;i++)cx(a[i],a[i+1]);
        lasting(a[0],b[0]);
        for(let i=1;i<n;i++)cx(a[i],b[i]);
        stepList(calls,inverse,g=>this.mc(g[0],g[1],loans));
    }
    increment(b,controls,dirtyWord,loans,inverse=false) {
        // D+~D=-1 modulo 2^n. Each of the two conditional equal-size
        // additions restores its source, even for arbitrary dirty D.
        const blocks=[
            rev=>this.equal(dirtyWord,b,controls,null,rev,loans),
            rev=>{for(const q of dirtyWord)this.out(NONE,NONE,q);},
            rev=>this.equal(dirtyWord,b,controls,null,rev,loans),
            rev=>{for(const q of dirtyWord)this.out(NONE,NONE,q);}
        ];
        stepList(blocks,!inverse,k=>k(!inverse));
    }
    add(src,dest,c,carry,inverse=false) {
        if(!src.length||!dest.length)return;
        const k=Math.min(src.length,dest.length),a=src.slice(0,k),b=dest.slice(0,k),hi=dest.slice(k);
        const base=c===null?[]:Array.isArray(c)?c:[c];
        const used=[...a,...dest,...base,carry];
        const pool=this.loan(used,hi.length+4),dword=pool.slice(0,hi.length),loans=pool.slice(hi.length);
        if(!hi.length){this.equal(a,b,base,null,inverse,loans);return;}
        // a_high xor (a'_high AND b'_high) is the unsigned overflow
        // during the ripple for k>=2. For k=1 the two input bits give it.
        const before=[],after=[];
        const cx=(list,x,y)=>list.push([[x],y]);
        const cc=(list,x,y,z)=>list.push([[x,y],z]);
        if(k>1)cx(before,a[k-1],carry);
        for(let i=1;i<k;i++)cx(before,a[i],b[i]);
        for(let i=k-2;i>=1;i--)cx(before,a[i],a[i+1]);
        for(let i=0;i<k-1;i++)cc(before,a[i],b[i],a[i+1]);
        cc(before,a[k-1],b[k-1],carry);
        cc(after,a[k-1],b[k-1],carry);
        for(let i=k-1;i>=1;i--){after.push([[...base,a[i]],b[i]]);cc(after,a[i-1],b[i-1],a[i]);}
        for(let i=1;i<k-1;i++)cx(after,a[i],a[i+1]);
        after.push([[...base,a[0]],b[0]]);
        for(let i=1;i<k;i++)cx(after,a[i],b[i]);
        if(k>1)cx(after,a[k-1],carry);
        const execute=(list,rev)=>stepList(list,rev,g=>this.mc(g[0],g[1],loans));
        const blocks=[rev=>execute(before,rev),rev=>this.increment(hi,[...base,carry],dword,loans,rev),rev=>execute(after,rev)];
        stepList(blocks,inverse,k=>k(inverse));
    }
}

function put(state,word,x,lane) {
    const bit=(1<<lane)>>>0;
    for(let i=0;i<word.length;i++){let w=word[i];state[w]=((state[w]&~bit)|((x>>BigInt(i))&1n?bit:0))>>>0;}
}
function get(state,word,lane){
    let x=0n;for(let i=word.length-1;i>=0;i--)x=2n*x+BigInt((state[word[i]]>>>lane)&1);
    return x;
}
function rand(seed){let v=seed>>>0;return ()=>{v=(Math.imul(1664525,v)+1013904223)>>>0;return v;};}

class WordArithmetic {
    constructor(fieldBits,delta){ this.fieldBits=fieldBits;this.delta=BigInt(delta); }
    toggle(tape,positive,negative,target) {
        const controls=[...positive,...negative];
        if(controls.includes(target)||new Set(controls).size!==controls.length)throw Error("toggle aliases");
        for(const i of negative)tape.out(NONE,NONE,i);
        const loans=tape.loan([...controls,target],Math.max(0,controls.length-2));
        tape.mc(controls,target,loans);
        for(let i=negative.length-1;i>=0;i--)tape.out(NONE,NONE,negative[i]);
    }
    cnotList(tape,controls,word) {
        const loans=tape.loan([...controls,...word],Math.max(0,controls.length-1));
        for(const q of word)tape.mc(controls,q,loans);
    }
    inc(tape,word,controls,back) {
        if(!word.length)return;
        const loans=tape.loan([...word,...controls],word.length+6);
        tape.increment(word,controls,loans.slice(0,word.length),loans.slice(word.length),back);
    }
    reflect(tape,word,controls,back) {
        // p-x = ~x + 2^fieldBits - (delta-1), including widths above p.
        const seq=[()=>this.cnotList(tape,controls,word)];
        if(this.fieldBits<word.length)seq.push(r=>this.inc(tape,word.slice(this.fieldBits),controls,r));
        for(let i=0;(this.delta-1n)>>BigInt(i);i++)if(((this.delta-1n)>>BigInt(i))&1n)
            seq.push(r=>this.inc(tape,word.slice(i),controls,!r));
        stepList(seq,back,fn=>fn(back));
    }
}
class MixedArithmetic extends WordArithmetic {
    gatedSwap(tape,x,y,controls,loans) {
        tape.out(NONE,x,y);
        tape.mc([...controls,y],x,loans);
        tape.out(NONE,x,y);
    }
    permute(tape,word,origins,controls,back) {
        const at=word.slice(),where=new Map(at.map((wire,i)=>[wire,i])),swaps=[];
        for(let to=0;to<at.length;to++){
            const from=where.get(origins[to]);
            if(from===undefined)throw Error("permutation origin");
            if(from===to)continue;
            const take=at[from],move=at[to];at[to]=take;at[from]=move;
            where.set(take,to);where.set(move,from);swaps.push([word[to],word[from]]);
        }
        const pool=tape.loan([...word,...controls],Math.max(0,controls.length-1));
        stepList(swaps,back,([x,y])=>this.gatedSwap(tape,x,y,controls,pool));
    }
    greaterEqual(tape,z,v,controls,target) {
        // z has one extra high bit. v + ~z_low overflows exactly for v > z_low.
        const n=v.length,top=z[n],x=z.slice(0,n),last=n-1;
        const pool=tape.loan([...z,...v,...controls,target],controls.length+1);
        tape.mc(controls,target,pool);
        for(const wire of z)tape.out(NONE,NONE,wire);
        if(n>1)tape.mc([...controls,top,v[last]],target,pool);
        const changes=[];
        for(let i=1;i<n;i++)changes.push([NONE,v[i],x[i]]);
        for(let i=n-2;i>=1;i--)changes.push([NONE,v[i],v[i+1]]);
        for(let i=0;i<n-1;i++)changes.push([x[i],v[i],v[i+1]]);
        stepList(changes,false,g=>tape.out(...g));
        tape.mc([...controls,top,v[last],x[last]],target,pool);
        stepList(changes,true,g=>tape.out(...g));
        for(const wire of z)tape.out(NONE,NONE,wire);
    }
    digit(tape,z,v,controls,back) {
        // Fused comparison and subtraction. The two primitive ancillas start and finish zero.
        const n=v.length,B=z.slice(0,n),h=z[n],t=this.pick;
        const e=controls.length===1?controls[0]:this.carry,ops=[];
        const X=x=>ops.push([NONE,NONE,x]),cx=(x,y)=>ops.push([NONE,x,y]),cc=(x,y,z)=>ops.push([x,y,z]);
        const multi=controls.length>1,enabled=controls.length>0;
        if(multi)this.toggle(tape,controls,[],e);
        if(n===1){
            if(enabled){X(B[0]);cc(e,v[0],t);cc(t,B[0],h);X(B[0]);cx(e,h);cc(t,h,B[0]);cc(e,v[0],t);}
            else{X(B[0]);cc(B[0],v[0],h);X(B[0]);X(h);cc(h,v[0],B[0]);}
        }else{
            for(const b of B)X(b);
            for(let i=1;i<n;i++)cx(v[i],B[i]);
            if(enabled)cc(e,v[n-1],h);else cx(v[n-1],h);
            for(let i=n-2;i>=1;i--)cx(v[i],v[i+1]);
            for(let i=0;i<n-1;i++)cc(B[i],v[i],v[i+1]);
            if(enabled){cc(e,v[n-1],t);cc(t,B[n-1],h);cc(e,v[n-1],t);cx(e,h);cc(e,h,t);}
            else{cc(B[n-1],v[n-1],h);X(h);}
            const pred=enabled?t:h;cc(pred,v[n-1],B[n-1]);
            for(let i=n-2;i>=0;i--){cc(B[i],v[i],v[i+1]);cc(pred,v[i],B[i]);}
            if(enabled)cc(e,h,t);
            for(let i=1;i<n-1;i++)cx(v[i],v[i+1]);
            for(let i=1;i<n;i++)cx(v[i],B[i]);
            for(const b of B)X(b);
        }
        stepList(ops,back,op=>tape.out(...op));
        if(multi)this.toggle(tape,controls,[],e);
    }
    nrAdder(tape,A,B,H,P,back) {
        const n=A.length,ops=[],cx=(x,y)=>ops.push([NONE,x,y]),cc=(x,y,z)=>ops.push([x,y,z]);
        const put=(x,y)=>P===null?cx(x,y):cc(P,x,y);
        if(n===1){if(H!==null)cc(B[0],A[0],H);put(A[0],B[0]);}
        else {
            for(let i=1;i<n;i++)cx(A[i],B[i]);if(H!==null)cx(A[n-1],H);
            for(let i=n-2;i>=1;i--)cx(A[i],A[i+1]);
            for(let i=0;i<n-1;i++)cc(B[i],A[i],A[i+1]);
            if(H!==null)cc(B[n-1],A[n-1],H);put(A[n-1],B[n-1]);
            for(let i=n-2;i>=0;i--){cc(B[i],A[i],A[i+1]);put(A[i],B[i]);}
            for(let i=1;i<n-1;i++)cx(A[i],A[i+1]);for(let i=1;i<n;i++)cx(A[i],B[i]);
        }
        stepList(ops,back,op=>tape.out(...op));
    }
    unguardedMixed(tape,q,v,rem,back) {
        const J=[...q,...rem],n=v.length,k=q.length,ops=[];
        for(let j=k-1;j>=0;j--){
            const B=J.slice(j,j+n),h=J[j+n],old=j===k-1?null:J[j+n+1];
            const flip=()=>{if(old!==null)tape.out(NONE,NONE,old);
                for(const x of[...B,h])tape.out(NONE,old===null?NONE:old,x);
                if(old!==null)tape.out(NONE,NONE,old);};
            ops.push(flip,rv=>this.nrAdder(tape,v,B,h,null,rv),flip);
        }
        ops.push(rv=>this.nrAdder(tape,v,J.slice(0,n),null,J[n],rv),
            ()=>{for(const b of J.slice(n))tape.out(NONE,NONE,b);},
            rv=>this.permute(tape,J,[...J.slice(n),...J.slice(0,n)],[],rv));
        stepList(ops,!back,fn=>fn(!back));
    }

    mixed(tape,q,v,rem,controls,back) {
        if(!controls.length){this.unguardedMixed(tape,q,v,rem,back);return;}
        if(v.length!==rem.length)throw Error("mixed coefficient width");
        let moving=rem.slice();const done=[],seq=[];
        for(const bit of q){
            const z=[...moving,bit];
            seq.push(rev=>this.digit(tape,z,v,controls,!rev));
            done.push(moving[0]);
            moving=[...moving.slice(1),bit];
        }
        const physical=[...q,...rem],origins=[...done,...moving];
        seq.push(rev=>this.permute(tape,physical,origins,controls,rev));
        stepList(seq,back,fn=>fn(back));
    }
    constBelow(tape,word,limit,controls,targets) {
        if(!targets.length||limit<=0n)return;
        const n=word.length;
        if(limit>=(1n<<BigInt(n))){this.cnotList(tape,controls,targets);return;}
        const bits=Array.from({length:n},(_,i)=>Number((limit>>BigInt(i))&1n));
        // D[n] carries the enable around two identical dirty majority-free ladders.
        const d=tape.loan([...word,...controls,...targets],n+1);
        const more=tape.loan([...word,...controls,...targets,...d],Math.max(0,controls.length-2));
        const coeff=new Uint8Array(n+1);
        for(let i=0;i<n;i++)if(bits[i]){coeff[i]^=1;coeff[i+1]^=1;}
        const deposits=split(0,n+1).filter(i=>coeff[i]);
        for(let i=0;i<n;i++)if(!bits[i])tape.out(NONE,NONE,word[i]);
        for(let echo=0;echo<2;echo++){
            tape.mc(controls,d[n],more);
            for(let i=n-1;i>=0;i--)tape.out(word[i],d[i+1],d[i]);
            for(const i of deposits)for(const t of targets)tape.out(NONE,d[i],t);
            for(let i=0;i<n;i++)tape.out(word[i],d[i+1],d[i]);
        }
        for(let i=0;i<n;i++)if(!bits[i])tape.out(NONE,NONE,word[i]);
    }
}
function eg(a,b){if(b===0n)return [a,1n,0n];const [g,x,y]=eg(b,a%b);return[g,y,x-(a/b)*y];}
function mod(a,m){return (a%m+m)%m;}




function bits(x){return x.toString(2).length;}
function toyPacked(m,p){
    const C=1n<<BigInt(m/2),rows=[];
    for(let v=1n;v<C;v++)for(let u=0n;u<v;u++)for(let r=C;r<=p;r++){
        const d=p-r*u;if(d<=0n||d%v||d/v<r)continue;
        if(r===p)continue;
        rows.push([r,u,v]);
    }
    return rows;
}

function ordinaryPath(m,delta,x) {
    const p=(1n<<BigInt(m))-BigInt(delta),cut=1n<<BigInt(m/2);
    if(x<0n||x>=p)throw Error("noncanonical field coordinate");
    let sign=x>p/2n?1:0,r=sign?p-x:x,h=p,u=0n,v=1n;const bands=[],qs=[];
    while(r>=cut){
        const q=h/r,n=r*v+u;
        bands.push([bits(n),bits(v)]);qs.push(q);
        [h,r,u,v]=[r,h%r,v,u+q*v];sign^=1;
    }
    if(v>=cut||r>=cut||u>=v||mod(x*v-(sign?-r:r),p)!==0n)throw Error("terminal scalar contract");
    return {bands,qs,r,u,v,sign};
}



function fieldRoutes(){
    const p=(1n<<256n)-(1n<<32n)-977n;
    let a=0n,b=1n;for(let i=0;i<384;i++)[a,b]=[b,a+b];
    return {zero:0n,short:37n,largeQuotient:1n<<128n,interior:p/((1n<<72n)+133n),
        ordinary:0x4adfa74c67838bae7c53d432178369f2033a391c138a4734e1c321de33321cf7n,slow:p*a/(a+b)};
}


function selectedFieldData() {
    const p=(1n<<256n)-(1n<<32n)-977n,cut=1n<<128n,rng=rand(0x6938f278);
    const groups=new Map(),natural=new Map();
    function noise(){let x=0n;for(let j=0;j<8;j++)x=(x<<32n)|BigInt(rng());return x;}
    for(let ell=129;ell<=256;ell++){
        const lo=1n<<BigInt(ell-1),hi=ell===256?p:2n*lo;
        const rs=[lo,lo+1n,hi-1n,hi-2n];for(let j=0;j<12;j++)rs.push(lo+noise()%(hi-lo));
        groups.set(ell+"/1",rs.map(r=>[r,0n,1n]));
    }
    for(let j=0;j<512;j++){
        let h=p,r=1n+noise()%(p-1n),u=0n,v=1n;
        while(r>=cut){
            const key=[bits(r*v+u),bits(v)].join("/");
            if(!natural.has(key))natural.set(key,[]);const bucket=natural.get(key);
            if(bucket.length<112)bucket.push([r,u,v]);
            const q=h/r;
            [h,r,u,v]=[r,h%r,v,u+q*v];
        }
    }
    return {groups,natural};
}




class UnitPreparation extends MixedArithmetic {
    constructor(m,delta,k,width) {
        super(m,delta);
        this.k=k;this.m=m;this.prime=(1n<<BigInt(m))-BigInt(delta);
        let at=0;const port=n=>{const p=split(at,at+n);at+=n;return p;};
        this.r=port(m-k);this.u=port(k+1);this.bank=port(m/2);this.dirty=port(m);
        this.g=port(1)[0];this.pick=port(1)[0];this.carry=port(1)[0];this.norm=port(1)[0];
        this.spare=port(1)[0];this.shape=port(1)[0];this.qual=port(1)[0];this.fired=port(1)[0];this.sign=port(1)[0];
        this.clean=[this.pick,this.carry,this.norm,this.spare,this.shape,this.qual,this.fired];this.width=width;
        if(k<=0||k>=m/2-1||at>width)throw Error("bad unit-preparation control width");
        this.v=this.bank.slice(0,k+1);this.a=[...this.u,this.spare];this.fullV=this.bank.slice(0,k+2);
    }
    unit(tape,ctrl,back) {
        const v=this.v,a=this.a,d=this.dirty.slice(0,v.length),wideCarry=[...d,this.bank[v.length]],word=[...this.r,...wideCarry];
        const canon=rv=>this.digit(tape,[...d,this.norm],v,ctrl,rv);
        const tmp=[...a,...this.fullV],swap=[...this.fullV,...a];
        const seq=[
            rv=>tape.add(v,a,ctrl,this.carry,rv),canon,
            rv=>this.mixed(tape,this.r,a,wideCarry,ctrl,rv),rv=>this.reflect(tape,word,ctrl,rv),
            rv=>this.inc(tape,word,ctrl,!rv),rv=>this.mixed(tape,this.r,v,d,ctrl,!rv),
            ()=>this.cnotList(tape,ctrl,d),rv=>tape.add(v,d,ctrl,this.carry,rv),
            rv=>canon(!rv),rv=>this.inc(tape,this.r,ctrl,rv),rv=>this.permute(tape,tmp,swap,ctrl,rv)
        ];
        stepList(seq,back,fn=>fn(back));
    }
}


class UniversalGeneral extends MixedArithmetic {
    constructor(m,delta,k,width) {
        super(m,delta);this.m=m;this.k=k;this.h=k+1;this.half=m/2;this.width=width;this.p=(1n<<BigInt(m))-BigInt(delta);
        let at=0;const port=n=>{const a=split(at,at+n);at+=n;return a;};
        this.r=port(m-k);this.u=port(this.h);this.bank=port(m/2);this.zword=port(m);
        this.g=port(1)[0];this.pick=port(1)[0];this.carry=port(1)[0];const f1=port(1)[0];
        const q0=port(1)[0],q1=port(1)[0],f2=port(1)[0];this.take=port(1)[0];this.sig=port(1)[0];
        this.tags=port(Math.ceil(Math.log2(m/2)));this.dv=[f1,f2];this.qtop=q1;
        this.ctrl=[this.g,this.take];this.v=this.bank.slice(0,this.h);
        this.q=[...this.bank.slice(this.h),q0,q1];this.A=[...this.q,...this.u];
        this.big=[...this.r,...this.u];this.n=this.big.slice(0,m);this.borrow=this.big[m];
        this.maxShift=this.half-this.h;
        this.tag=this.tags.slice(0,this.maxShift?Math.floor(Math.log2(this.maxShift))+1:0);
        this.aux=[this.pick,this.carry,...this.dv,q0,q1,this.take,...this.tags];
        if(at>width||this.h>m/2)throw Error("universal width");
    }
    normalize(tape,back){
        const n=this.n,js=split(0,this.tag.length).reverse();
        stepList(js,back,j=>{
            const s=1<<j,t=this.tag[j],origins=n.slice(-s).concat(n.slice(0,-s));
            const seq=[()=>this.toggle(tape,[],n.slice(-s),t),rv=>this.permute(tape,n,origins,[t],rv)];
            stepList(seq,back,fn=>fn(back));
        });
    }
    packNumber(tape,back){this.mixed(tape,this.r,this.v,this.u,[],back);}


    makeBand(lo,hi,affine){
        const cap=Math.min(this.r.length,this.m+(affine?1:3)-lo),a=this.A.slice(0,hi),r=this.r.slice(0,cap);
        const pool=[...this.r.slice(cap),...this.A.slice(hi),...this.tags.slice(1)];
        const pad=pool.slice(0,hi-this.h);
        if(pad.length!==hi-this.h||2*(cap+hi)+9>this.width)return null;
        return {lo,hi,a,r,pad};
    }
    bands(affine) {
        const max=this.half+(affine?0:1),out=[];
        for(let lo=this.h;lo<=max;){
            let best=this.makeBand(lo,lo,affine);if(!best)throw Error("unfunded width "+[this.m,this.k,lo,affine]);
            for(let hi=lo+1;hi<=max;hi++){const candidate=this.makeBand(lo,hi,affine);if(!candidate)break;best=candidate;}
            out.push(best);lo=best.hi+1;
        }
        return out;
    }
    widthFlag(tape,b,flag) {
        const high=this.A.slice(b.hi);
        this.toggle(tape,this.ctrl,high,flag);
        this.toggle(tape,this.ctrl,[...high,...this.A.slice(b.lo-1,b.hi)],flag);
    }
    signProbe(tape,target,back) {
        const flag=this.tags[0],on=[this.g,flag];
        stepList(this.bands(false),back,b=>{
            this.widthFlag(tape,b,flag);
            const c=[...this.v,...b.pad],word=[...b.r,...c];
            this.inc(tape,c,[],true);this.mixed(tape,b.r,b.a,c,[],false);
            phaseDeposit(this,tape,target,()=>{this.toggle(tape,on,[],target);this.constBelow(tape,word,this.p+1n,on,[target]);});
            this.mixed(tape,b.r,b.a,c,[],true);this.inc(tape,c,[],false);
            this.widthFlag(tape,b,flag);
        });
    }
    affine(tape,back){
        const flag=this.tags[0],on=[this.g,flag],d=this.zword.slice(0,this.h),v=this.v;
        stepList(this.bands(true),back,b=>{
            this.widthFlag(tape,b,flag);
            const c=[...d,...b.pad],word=[...b.r,...c];
            const canon=rv=>this.digit(tape,[...d,this.dv[0]],v,on,rv);
            const seq=[canon,rv=>this.mixed(tape,b.r,b.a,c,on,rv),rv=>this.reflect(tape,word,on,rv),
                rv=>this.inc(tape,word,on,!rv),rv=>this.mixed(tape,b.r,v,d,on,!rv),
                ()=>this.cnotList(tape,on,d),rv=>tape.add(v,d,on,this.carry,rv),
                rv=>canon(!rv),rv=>this.inc(tape,b.r,on,rv)];
            stepList(seq,back,fn=>fn(back));this.widthFlag(tape,b,flag);
        });
    }
    select(tape){
        const high=this.bank.slice(this.h),g=[this.g,this.bank[this.k]];
        this.toggle(tape,g,high,this.take);
        this.toggle(tape,g,[...high,...this.r.slice(this.half)],this.take);
    }
    core(tape,back){
        const q=this.q,v=this.v,u=this.u,ctrl=this.ctrl,coef=rv=>this.mixed(tape,q,v,u,ctrl,rv);
        const seq=[rv=>this.estimate(tape,rv),coef];
        for(const flag of this.dv)seq.push(rv=>this.signProbe(tape,flag,rv),rv=>tape.add(v,this.A,[...ctrl,flag],this.carry,!rv));
        const twoPad=q.slice(-2);
        seq.push(rv=>coef(!rv),rv=>this.removeDebt(tape,rv),coef,rv=>this.affine(tape,rv),
            rv=>this.permute(tape,[...this.bank,...u,...twoPad],[...this.A.slice(0,this.half),...v,...this.A.slice(this.half)],ctrl,rv));
        stepList(seq,back,fn=>fn(back));
    }
    emit(tape,back){
        const seq=[()=>this.select(tape),rv=>this.core(tape,rv),()=>this.toggle(tape,this.ctrl,[],this.sig),
            ()=>this.toggle(tape,[this.g,this.u[this.k]],[],this.take)];
        stepList(seq,back,fn=>fn(back));
    }
}


class TruncatedGeneral extends UniversalGeneral {
    // K bounds clz(N). The top K+2 bits of normalized N determine an upper
    // quotient within two of floor(H/r), with no dependence on the passenger.
    topDivisor(){return this.n.slice(this.m-this.q.length);}
    indicator(tape,j,kind,controls,target) {
        if(kind==="eq"){
            const yes=controls.slice(),no=[];
            for(let i=0;i<this.tag.length;i++)((j>>i)&1?yes:no).push(this.tag[i]);
            this.toggle(tape,yes,no,target);
        }else{
            if(kind==="gt")this.toggle(tape,controls,[],target);
            this.constBelow(tape,this.tag,BigInt(j+1),controls,[target]);
        }
    }
    middleDigit(tape,j,D,back){
        const b=this.n[j],Q=this.q,selected=this.carry,g=this.ctrl;
        const z=[b,...Q],owners=[...Q,b];
        const seq=[()=>this.indicator(tape,j,"gt",g,selected),
            ()=>tape.out(NONE,selected,b),rv=>this.digit(tape,z,D,[selected],rv),
            rv=>this.permute(tape,owners,z,[selected],rv),()=>this.indicator(tape,j,"gt",g,selected)];
        stepList(seq,back,fn=>fn(back));
    }
    reducedTerm(tape,D,j,back){
        const s=this.carry,g=this.ctrl;
        const mark=()=>{this.indicator(tape,j,"eq",g,s);
            if(j<this.maxShift)this.indicator(tape,j,"gt",[...g,this.n[j]],s);};
        mark();tape.add(D.slice(0,this.q.length-j),this.q.slice(j),[s],this.pick,back);mark();
    }
    moveQuotient(tape,j,back){
        const g=this.ctrl,s=this.carry,Q=this.q,seq=[];
        if(j<this.maxShift)seq.push(()=>this.indicator(tape,j,"gt",g,s),
            rv=>this.permute(tape,[this.n[j],Q[j]],[Q[j],this.n[j]],[s],rv),
            ()=>this.indicator(tape,j,"gt",g,s));
        seq.push(()=>this.indicator(tape,j,"eq",g,Q[j]));
        stepList(seq,back,fn=>fn(back));
    }
    estimate(tape,back){
        const D=this.topDivisor(),Q=this.q,g=this.ctrl,js=split(0,this.maxShift+1),seq=[
            rv=>this.packNumber(tape,rv),rv=>this.normalize(tape,rv),
            ()=>this.cnotList(tape,g,Q),
            ()=>{for(let i=0;i<Q.length;i++)this.toggle(tape,[...g,D[i]],[],Q[i]);}
        ];
        for(let j=this.maxShift-1;j>=0;j--)seq.push(rv=>this.middleDigit(tape,j,D,rv));
        seq.push(rv=>this.inc(tape,Q,g,rv));
        for(const j of js)seq.push(rv=>this.reducedTerm(tape,D,j,rv));
        for(const j of js)seq.push(rv=>this.moveQuotient(tape,j,rv));
        seq.push(rv=>this.normalize(tape,!rv),rv=>this.packNumber(tape,!rv));
        stepList(seq,back,fn=>fn(back));
    }
    installZeros(tape,back){
        const Q=this.q,sel=this.carry;
        stepList(split(0,this.maxShift),back,j=>{
            this.indicator(tape,j,"le",[],sel);
            this.permute(tape,[this.n[j],Q[j+2]],[Q[j+2],this.n[j]],[sel],back);
            this.indicator(tape,j,"le",[],sel);
        });
        tape.out(NONE,NONE,this.n.at(-1));
    }
    mixedHead(tape,D,C,back) {
        const Q=this.q,sel=this.carry;
        const stages=[rv=>this.mixed(tape,Q.slice(0,2),D,C,[],rv)];
        for(let i=2;i<Q.length;i++){
            const z=[...C,Q[i]],origins=[...z.slice(1),z[0]];
            stages.push(rv=>{
                this.indicator(tape,i-2,"gt",[],sel);
                const seq=[rr=>this.digit(tape,z,D,[sel],!rr),rr=>this.permute(tape,z,origins,[sel],rr)];
                stepList(seq,rv,fn=>fn(rv));
                this.indicator(tape,i-2,"gt",[],sel);
            });
        }
        stepList(stages,back,fn=>fn(back));
    }
    threshold(tape,target){
        // Active inputs have normalized N's top bit = G = 1. The two freed
        // N wires complete the clean carry without another full register.
        const D=[...this.topDivisor().slice(0,-1),this.g],C=[...this.n.slice(0,this.maxShift),this.borrow,this.n.at(-1)];
        this.installZeros(tape,false);this.mixedHead(tape,D,C,false);
        this.toggle(tape,this.ctrl,C.slice(-2),target);
        this.mixedHead(tape,D,C,true);this.installZeros(tape,true);
    }
    removeDebt(tape,back){
        const g=this.ctrl,Q=this.q;
        const seq=[rv=>this.packNumber(tape,rv),rv=>this.normalize(tape,rv),
            rv=>this.inc(tape,Q,g,rv),()=>this.threshold(tape,this.dv[0]),
            rv=>this.inc(tape,Q,g,rv),()=>this.threshold(tape,this.dv[1]),
            rv=>this.inc(tape,Q,g,!rv),rv=>this.inc(tape,Q,g,!rv),
            rv=>this.normalize(tape,!rv),rv=>this.packNumber(tape,!rv)];
        stepList(seq,back,fn=>fn(back));
    }
}


class AlignedGeneral extends TruncatedGeneral {
    rank(tape,tag) {
        const high=this.r.slice(this.half+2);if(!high.length)return;
        const n=high.length,d=tape.loan([...high,...tag],n+1),coeff=Array.from({length:n+1},()=>0);
        for(let i=0;i<n;i++){coeff[i]^=i+1;coeff[i+1]^=i+1;}
        for(const x of high)tape.out(NONE,NONE,x);
        for(let rep=0;rep<2;rep++){
            tape.out(NONE,NONE,d[n]);
            for(let i=n-1;i>=0;i--)tape.out(high[i],d[i+1],d[i]);
            for(let i=0;i<=n;i++)for(let k=0;k<tag.length;k++)if((coeff[i]>>k)&1)tape.out(NONE,d[i],tag[k]);
            for(let i=0;i<n;i++)tape.out(high[i],d[i+1],d[i]);
        }
        for(const x of high)tape.out(NONE,NONE,x);
    }
    barrel(tape,word,tag,left,back){
        stepList(split(0,tag.length),back,j=>{
            const k=(1<<j)%word.length;if(!k)return;
            const src=left?word.slice(-k).concat(word.slice(0,-k)):word.slice(k).concat(word.slice(0,k));
            this.permute(tape,word,src,[tag[j]],back);
        });
    }
    parkTail(tape,D,tag,back) {
        const base=this.half+2,top=[this.A.at(-1),this.pick,this.carry];
        const moving=rv=>stepList(split(base,this.r.length),rv,i=>{
            const a=D[i+this.h-1-base],b=this.r[i],mark=()=>this.constBelow(tape,tag,BigInt(i-base+1),[],[this.pick]);
            mark();this.permute(tape,[a,b],[b,a],[this.pick],rv);mark();
        });
        const extra=rv=>{const upper=D.slice(-3);this.permute(tape,[...upper,...top],[...top,...upper],[],rv);};
        const seq=[moving,extra];stepList(seq,back,fn=>fn(back));
    }
    alignedMix(tape,S,D,tag,back){
        const base=this.half+2,layer=Object.create(this);layer.pick=this.g;layer.carry=this.take;
        const flip=()=>{tape.out(NONE,NONE,this.g);tape.out(NONE,NONE,this.take);};
        const extra=rv=>stepList(split(base,this.r.length),rv,i=>{
            const z=[...D,this.r[i]],dest=z.slice(1).concat(z[0]);
            const select=()=>{tape.out(NONE,NONE,this.take);this.constBelow(tape,tag,BigInt(i-base+1),[],[this.take]);};
            const q=[select,rr=>layer.digit(tape,z,S,[this.take],!rr),rr=>this.permute(tape,z,dest,[this.take],rr),select];
            stepList(q,rv,fn=>fn(rv));
        });
        const seq=[rv=>this.mixed(tape,this.r.slice(0,base),S,D,[],rv),flip,extra,flip];
        stepList(seq,back,fn=>fn(back));
    }
    alignedSign(tape,target){
        const base=this.half+2,w=this.half+1;
        if(this.r.length<base){super.signProbe(tape,target,false);return;}
        const free=this.r.length-base,tag=this.tags.slice(0,free?Math.floor(Math.log2(free))+1:0),S=this.A.slice(0,w),D=this.zword.slice(0,w);
        const word=[...this.r.slice(0,base),...D];
        const seq=[
            ()=>this.rank(tape,tag),rv=>this.barrel(tape,S,tag,true,rv),rv=>this.inc(tape,this.r,[],!rv),
            rv=>this.parkTail(tape,D,tag,rv),()=>this.cnotList(tape,[],D),rv=>tape.add(S,D,[],this.carry,rv),
            rv=>this.alignedMix(tape,S,D,tag,rv),rv=>this.barrel(tape,this.r,tag,false,rv)
        ];
        stepList(seq,false,fn=>fn(false));
        phaseDeposit(this,tape,target,()=>{this.toggle(tape,this.ctrl,[],target);this.constBelow(tape,word,this.p,this.ctrl,[target]);});
        stepList(seq,true,fn=>fn(true));
    }
    signProbe(tape,target,back){this.alignedSign(tape,target);}
}


class SingleAffineGeneral extends AlignedGeneral {
    guardedPermutation(tape,word,origins,extra,back) {
        const cs=[...this.ctrl,...extra];
        this.toggle(tape,cs,[],this.carry);
        this.permute(tape,word,origins,[this.carry],back);
        this.toggle(tape,cs,[],this.carry);
    }
    guardedBarrel(tape,word,left,back) {
        stepList(split(0,this.tag.length),back,j=>{
            const k=(1<<j)%word.length;if(!k)return;
            const origin=left?word.slice(-k).concat(word.slice(0,-k)):word.slice(k).concat(word.slice(0,k));
            this.guardedPermutation(tape,word,origin,[this.tag[j]],back);
        });
    }
    normalizeA(tape,a,back) {
        stepList(split(0,this.tag.length).reverse(),back,j=>{
            const k=1<<j,orig=a.slice(-k).concat(a.slice(0,-k)),bit=this.tag[j];
            const seq=[()=>this.toggle(tape,[],a.slice(-k),bit),rv=>this.permute(tape,a,orig,[bit],rv)];
            stepList(seq,back,fn=>fn(back));
        });
    }
    parkAffine(tape,D,back) {
        const base=this.half+1,off=base-this.h,t=this.carry;
        stepList(split(this.h,this.half),back,i=>{
            const mark=()=>this.indicator(tape,i-this.h,"le",this.ctrl,t);
            mark();this.permute(tape,[D[i],this.r[off+i]],[this.r[off+i],D[i]],[t],back);mark();
        });
    }
    affineProduct(tape,a,d,back) {
        const base=this.half+1,ctrl=this.ctrl,t=this.carry;
        const tail=rv=>stepList(split(base,this.r.length),rv,i=>{
            const mark=()=>this.indicator(tape,i-base,"gt",ctrl,t),z=[...d,this.r[i]],orig=z.slice(1).concat(z[0]);
            const seq=[mark,rr=>this.digit(tape,z,a,[t],!rr),rr=>this.permute(tape,z,orig,[t],rr),mark];
            stepList(seq,rv,fn=>fn(rv));
        });
        const seq=[rv=>this.mixed(tape,this.r.slice(0,base),a,d,ctrl,rv),tail];
        stepList(seq,back,fn=>fn(back));
    }
    affine(tape,back){
        const a=this.A.slice(0,this.half),r=this.r,v=this.v,D=this.zword.slice(0,this.half),d=D.slice(0,this.h);
        const base=this.half+1,word=[...r.slice(0,base),...D],tail=r.slice(base),g=this.ctrl;
        const canon=rv=>this.digit(tape,[...d,this.dv[0]],v,[],rv);
        const seq=[
            rv=>this.normalizeA(tape,a,rv),canon,
            rv=>this.guardedBarrel(tape,D,true,rv),rv=>this.parkAffine(tape,D,rv),
            rv=>this.affineProduct(tape,a,D,rv),rv=>this.guardedBarrel(tape,r,false,rv),
            rv=>this.reflect(tape,word,g,rv),rv=>this.inc(tape,word,g,!rv),
            rv=>this.guardedPermutation(tape,[...tail,...D],[...D,...tail],[],rv),
            rv=>this.mixed(tape,r,v,d,g,!rv),()=>this.cnotList(tape,g,d),
            rv=>tape.add(v,d,g,this.carry,rv),rv=>this.inc(tape,r,g,rv),
            rv=>canon(!rv),rv=>this.normalizeA(tape,a,!rv)
        ];
        stepList(seq,back,fn=>fn(back));
    }
}


function phaseDeposit(o,tape,wire,write){write();if(o.measureTarget===wire){tape.z(wire);write();}}
function retirePredicate(o,tape,wire,emit){const mask=tape.hmr(wire);tape.cond(mask,()=>{o.measureTarget=wire;emit();o.measureTarget=null;});}
class EarlyUnit extends UnitPreparation {
    emit(tape,back){
        const r=this.r,v=this.v,a=this.a,c=this.fullV,g=[this.g],sel=[this.g,this.shape],active=[this.g,this.qual];
        const shape=()=>{const hi=this.bank.slice(this.k+1),pos=[this.g,this.bank[this.k]];
            this.toggle(tape,pos,hi,this.shape);this.toggle(tape,pos,[...hi,...r.slice(this.m/2)],this.shape);};
        const qual=()=>this.toggle(tape,sel,[a.at(-1)],this.qual);
        const mark=()=>phaseDeposit(this,tape,this.fired,()=>{this.toggle(tape,active,[],this.fired);this.constBelow(tape,[...r,...c],this.prime+1n,active,[this.fired]);});
        const pre=[shape,rv=>tape.add(v,a,[],this.carry,rv),qual,rv=>tape.add(v,a,[],this.carry,rv),
            rv=>this.inc(tape,c,[],!rv),rv=>this.mixed(tape,r,a,c,[],rv),mark,rv=>this.mixed(tape,r,a,c,[],!rv),
            rv=>this.inc(tape,c,[],rv),rv=>tape.add(v,a,[],this.carry,!rv),qual,rv=>tape.add(v,a,[],this.carry,!rv),shape];
        const seq=[rv=>{const emit=()=>stepList(pre,rv,fn=>fn(rv));if(rv)retirePredicate(this,tape,this.fired,emit);else emit();},
            rv=>this.unit(tape,[this.g,this.fired],rv),()=>this.toggle(tape,[this.g,this.fired],[],this.sign),
            ()=>this.toggle(tape,[this.g,this.u[this.k]],[],this.fired)];
        stepList(seq,back,fn=>fn(back));
    }
}
class EarlyGeneral extends SingleAffineGeneral {
    emit(tape,back){
        const finish=()=>{
            const mark=[this.g,this.u[this.k]];
            this.toggle(tape,mark,[],this.take);
            if(this.k>0&&this.k<this.half-1)this.toggle(tape,mark,this.bank.slice(this.h),this.take);
        };
        const seq=[()=>this.select(tape),rv=>this.core(tape,rv),()=>this.toggle(tape,this.ctrl,[],this.sig),finish];
        stepList(seq,back,fn=>fn(back));
    }
}


class OddEstimateGeneral extends EarlyGeneral {
    constructor(m,delta,k,width) {
        super(m,delta,k,width);const end=this.tags.at(-1)+1;this.spareWork=split(end,width);
        this.aux.push(...this.spareWork);
    }
    layouts(){
        const K=this.maxShift,out=[];
        for(const [lo,hi]of [[0,Math.min(7,K)],[8,K]]){
            if(lo>hi)continue;
            const w=hi+6,W=w+1;if(w-1>this.m)return null;
            const spare=[...this.n.slice(0,lo),...this.spareWork];
            const T=[...this.q,...spare.splice(0,Math.max(0,W+1-this.q.length))].slice(0,W+1);
            const free=[...this.q.slice(W+1),...spare];if(T.length!==W+1||free.length<2)return null;
            const H=[...this.n.slice(this.m-w+1),free[1]],D=[free[0],...H];
            if(new Set([...T,...D]).size!==T.length+D.length)return null;
            out.push({lo,hi,w,W,T,D,H,d0:free[0]});
        }
        return out;
    }
    direction(tape){
        // upper approximation for V/2 < U: toggle floor(V/2) < U.
        const x=[...this.v.slice(1),this.pick],y=this.u,n=x.length,last=n-1,bit=this.dv[1],ctrl=this.ctrl;
        this.cnotList(tape,[],x);
        if(n>1)this.toggle(tape,[...ctrl,y[last]],[],bit);
        const ops=[];
        for(let i=1;i<n;i++)ops.push([NONE,y[i],x[i]]);
        for(let i=n-2;i>=1;i--)ops.push([NONE,y[i],y[i+1]]);
        for(let i=0;i<n-1;i++)ops.push([x[i],y[i],y[i+1]]);
        stepList(ops,false,op=>tape.out(...op));this.toggle(tape,[...ctrl,y[last],x[last]],[],bit);
        stepList(ops,true,op=>tape.out(...op));this.cnotList(tape,[],x);
    }
    bandMark(tape,B){
        if(this.maxShift<8)this.toggle(tape,this.ctrl,[],this.borrow);
        else this.indicator(tape,7,B.lo?"gt":"le",this.ctrl,this.borrow);
    }
    roundedDivisor(tape,B,back){
        const seq=[()=>tape.out(NONE,NONE,B.d0),rv=>this.inc(tape,B.H,[],!rv),rv=>this.inc(tape,B.H.slice(1),[this.dv[1]],rv)];
        stepList(seq,back,fn=>fn(back));
    }
    withDivisor(tape,B,fn,back){
        this.bandMark(tape,B);this.roundedDivisor(tape,B,false);
        fn([this.g,this.take,this.borrow],back);
        this.roundedDivisor(tape,B,true);this.bandMark(tape,B);
    }
    onesBlock(tape,R,D,n,extra,ctrl,back){
        const t=this.carry,origin=[...R,this.dv[0]],active=[...ctrl,...extra];
        this.toggle(tape,active,[],t);
        let remain=R.slice(),spare=this.dv[0];const seq=[];
        for(let j=0;j<n;j++){
            const input=spare,z=[input,...remain],high=z.at(-1);
            seq.push(()=>tape.out(NONE,t,input),rv=>this.digit(tape,z,D,[t],rv),()=>this.toggle(tape,[t],[input],high));
            remain=z.slice(0,-1);spare=high;
        }
        seq.push(rv=>this.permute(tape,origin,[...remain,spare],[t],rv));
        stepList(seq,back,fn=>fn(back));this.toggle(tape,active,[],t);
    }
    lowReflect(tape,T,w,ctrl,back){
        const seq=[()=>this.cnotList(tape,ctrl,T)];
        for(let j=0;j<T.length-w;j++)if(j<=this.maxShift)seq.push(rv=>{
            this.indicator(tape,j,"eq",ctrl,this.carry);
            this.inc(tape,T.slice(w+j),[this.carry],rv);
            this.indicator(tape,j,"eq",ctrl,this.carry);
        });
        stepList(seq,back,fn=>fn(back));
    }
    oddProduct(tape,T,D,ctrl,back){
        stepList(split(0,T.length-1).reverse(),back,i=>{
            const on=[...ctrl,T[i]];
            this.toggle(tape,on,[],this.carry);
            tape.add(D.slice(1,T.length-i),T.slice(i+1),[this.carry],this.pick,back);
            this.toggle(tape,on,[],this.carry);
        });
    }
    oddQuotient(tape,B,back){
        this.withDivisor(tape,B,(ctrl,rv)=>{
            const T=B.T.slice(0,B.W),D=B.D,w=B.w,seq=[()=>this.cnotList(tape,ctrl,T.slice(0,w-2)),
                rr=>this.onesBlock(tape,T,D,2,[],ctrl,rr)];
            for(let j=0;j<this.tag.length&&(1<<j)<=B.hi;j++)seq.push(rr=>this.onesBlock(tape,T,D,1<<j,[this.tag[j]],ctrl,rr));
            seq.push(rr=>this.lowReflect(tape,T,w,ctrl,rr),rr=>this.oddProduct(tape,T,D,ctrl,!rr));
            stepList(seq,rv,fn=>fn(rv));
        },back);
    }
    oddWitness(tape,B,back){
        this.withDivisor(tape,B,(ctrl,rv)=>{
            const T=B.T,D=B.D;const pre=[s=>this.inc(tape,T,[],s),s=>this.oddProduct(tape,T,D,[],s),
                s=>this.lowReflect(tape,T,B.w,[],s)];
            stepList(pre,false,fn=>fn(false));
            phaseDeposit(this,tape,this.dv[0],()=>this.toggle(tape,ctrl,[T.at(-1)],this.dv[0]));
            stepList(pre,true,fn=>fn(true));
        },back);
    }
    trial(tape,witness,back){
        const Bs=this.layouts();
        const seq=[()=>this.direction(tape),rv=>this.packNumber(tape,rv),rv=>this.normalize(tape,rv)];
        for(const B of Bs)seq.push(rv=>witness?this.oddWitness(tape,B,rv):this.oddQuotient(tape,B,rv));
        seq.push(rv=>this.normalize(tape,!rv),rv=>this.packNumber(tape,!rv),()=>this.direction(tape));
        stepList(seq,back,fn=>fn(back));
    }
    core(tape,back){
        if(!this.layouts()){super.core(tape,back);return;}
        const v=this.v,q=this.q,g=this.ctrl,flag=this.dv[0],coef=rv=>this.mixed(tape,q,v,this.u,g,rv);
        const seq=[rv=>this.trial(tape,false,rv),coef,rv=>{const probe=()=>this.signProbe(tape,flag,rv);if(rv)retirePredicate(this,tape,flag,probe);else probe();},
            rv=>tape.add(v,this.A,[...g,flag],this.carry,!rv),rv=>coef(!rv),
            rv=>{const probe=()=>this.trial(tape,true,rv);
                if(!tape.hist){if(!rv)retirePredicate(this,tape,flag,probe);else probe();}
                else if(!rv){if(tape.hist.has(this.k))throw Error("history collision");tape.hist.set(this.k,tape.hmr(flag));}
                else{probe();if(!tape.hist.has(this.k))throw Error("missing history");const ms=tape.hist.get(this.k);tape.cond(ms,()=>tape.z(flag));tape.hist.delete(this.k);}
            },coef,rv=>this.affine(tape,rv),
            rv=>this.permute(tape,[...this.bank,...this.u,...q.slice(-2)],[...this.A.slice(0,this.half),...v,...this.A.slice(this.half)],g,rv)];
        stepList(seq,back,fn=>fn(back));
    }
}


class UnguardedGeneral extends OddEstimateGeneral {
    alignedMix(tape,S,D,tag,back){
        const base=this.half+2,layer=Object.create(this);
        layer.pick=this.layouts()?this.dv[1]:this.tags.at(-1);layer.carry=this.take;
        const flip=()=>tape.out(NONE,NONE,this.take);
        const extra=rv=>stepList(split(base,this.r.length),rv,i=>{
            const z=[...D,this.r[i]],dest=z.slice(1).concat(z[0]);
            const mark=()=>{tape.out(NONE,NONE,this.take);this.constBelow(tape,tag,BigInt(i-base+1),[],[this.take]);};
            const ops=[mark,rr=>layer.digit(tape,z,S,[this.take],!rr),rr=>this.permute(tape,z,dest,[this.take],rr),mark];
            stepList(ops,rv,fn=>fn(rv));
        });
        const ops=[rv=>this.mixed(tape,this.r.slice(0,base),S,D,[],rv),flip,extra,flip];
        stepList(ops,back,fn=>fn(back));
    }
    threshold(tape,target){
        const D=[...this.topDivisor().slice(0,-1),this.take],C=[...this.n.slice(0,this.maxShift),this.borrow,this.n.at(-1)];
        this.installZeros(tape,false);this.mixedHead(tape,D,C,false);
        this.toggle(tape,this.ctrl,C.slice(-2),target);
        this.mixedHead(tape,D,C,true);this.installZeros(tape,true);
    }
}
class FoldTape extends Tape {
    constructor(logical,rows,g) {
        super(logical,[],null,g);this.one=g;this.physical=new Tape(logical-1,rows,null,NONE);this.count=this.physical.count;
    }
    out(a,b,t){
        const g=this.one,cv=x=>x>g?x-1:x;if(t===g)throw Error("write to fixed enable");
        if(a===g)a=NONE;if(b===g)b=NONE;if(b===NONE&&a!==NONE){b=a;a=NONE;}
        this.physical.out(a===NONE?NONE:cv(a),b===NONE?NONE:cv(b),cv(t));
    }
    mc(cs,t,dirty){super.mc(cs.filter(q=>q!==this.one),t,dirty);}
}



// X-basis reset on a known Boolean function plus outcome-controlled phase replay.
class MeasuredNct extends Tape {
    constructor(sz,rows,seed,policy) {
        super(sz,rows,null,NONE);this.phase=rows.map(()=>0);this.draw=rand(seed);
        this.policy=policy;this.current=null;this.measured=0;this.zCount=0;this.cCh=0;
        this.controlled=[0,0,0];this.branchHits=[];this.branchCost=[];
    }
    out(a,b,t) {
        if(this.current===null){super.out(a,b,t);return;}
        if(t===a||t===b||(a!==NONE&&a===b))throw Error("NCT overlap");
        const k=a!==NONE?2:b!==NONE?1:0;this.count[k]++;this.controlled[k]++;
        this.wireUse.add(t);if(a!==NONE)this.wireUse.add(a);if(b!==NONE)this.wireUse.add(b);
        this.sig=Math.imul(this.sig^codeGate(a,b,t),0x01000193)>>>0;
        const ms=this.current;
        for(let i=0;i<this.batches.length;i++){const r=this.batches[i],x=k===0?-1:k===1?r[b]:r[a]&r[b];r[t]=(r[t]^(ms[i]&x))>>>0;}
    }
    hmr(q) {
        if(this.current!==null)throw Error("nested HMR");
        const id=this.measured++,ms=[];
        for(let i=0;i<this.batches.length;i++){
            const r=this.batches[i],p=this.policy,m=p==="zero"?0:p==="one"?0xffffffff:typeof p==="number"?(id===p?0xffffffff:0):this.draw();
            this.phase[i]=(this.phase[i]^(r[q]&m))>>>0;r[q]=0;ms.push(m>>>0);
        }this.wireUse.add(q);this.sig=Math.imul(this.sig^(0xffe00000+q),0x01000193)>>>0;return ms;
    }
    z(q) {this.zCount++;for(let i=0;i<this.batches.length;i++)this.phase[i]=(this.phase[i]^(this.batches[i][q]&(this.current===null?-1:this.current[i])))>>>0;}
    cond(ms,fn) {if(this.current!==null)throw Error("nested classical replay");this.current=ms;
        const base=this.count[2];fn();this.branchCost.push(this.count[2]-base);this.branchHits.push(ms);this.current=null;}
}
class MeasuredFold extends FoldTape {
    constructor(logical,rows,g,seed,policy){super(logical,rows,g);this.physical=new MeasuredNct(logical-1,rows,seed,policy);this.count=this.physical.count;}
    cq(q){if(q===this.one)throw Error("fixed measurement");return q>this.one?q-1:q;}
    hmr(q){return this.physical.hmr(this.cq(q));}
    z(q){this.physical.z(this.cq(q));}
    cond(ms,fn){this.physical.cond(ms,fn);}
}

function runFold(m,delta,logical,inputs,seed,back,policy='random'){
    const p=(1n<<BigInt(m))-BigInt(delta),l=new UnguardedGeneral(m,delta,0,logical),rng=rand(seed),g=[l.g];
    const source=[],want=[],physicalWidth=logical-1,physical=word=>word.map(q=>q>l.g?q-1:q);
    const qR=physical(l.r),qV=physical(l.bank),qSig=physical([l.sig]),data=physical(l.big),work=physical(l.aux);
    for(let off=0;off<inputs.length;off+=32){
        const a=Uint32Array.from({length:physicalWidth},rng),b=a.slice();
        for(let lane=0;lane<32;lane++){
            const input=inputs[(off+lane)%inputs.length],res=ordinaryPath(m,delta,input);
            for(const ar of[a,b]){put(ar,work,0n,lane);put(ar,data,0n,lane);}
            put(a,qR,input,lane);put(a,qV,0n,lane);put(a,qSig,0n,lane);
            put(b,data.slice(0,m/2),res.r,lane);put(b,data.slice(m/2,m),res.u,lane);put(b,qV,res.v,lane);put(b,qSig,BigInt(res.sign),lane);
        }
        source.push(back?b:a);want.push(back?a:b);
    }
    const tape=new MeasuredFold(logical,source,l.g,seed^0x872eadb1,policy),ops=[];
    const classify=()=>{l.toggle(tape,g,[],l.sig);l.constBelow(tape,l.r,(p+1n)/2n,g,[l.sig]);};
    ops.push(classify,rv=>l.reflect(tape,l.r,[l.g,l.sig],rv),()=>l.toggle(tape,g,[],l.bank[0]));
    for(let k=0;k<m/2;k++){
        const row=new UnguardedGeneral(m,delta,k,logical);
        if(k>0&&k<m/2-1){const unit=new EarlyUnit(m,delta,k,logical);ops.push(rv=>unit.emit(tape,rv));}
        ops.push(rv=>row.emit(tape,rv),rv=>row.permute(tape,[row.r.at(-1),...row.u],[...row.u,row.r.at(-1)],g,rv));
    }
    stepList(ops,back,fn=>fn(back));
    for(let i=0;i<source.length;i++)for(let j=0;j<physicalWidth;j++)if(source[i][j]!==want[i][j])throw Error("folded midpoint "+[m,back,i,j]);
    const t=tape.physical;if(t.phase.some(x=>x!==0))throw Error("midpoint phase "+[m,back,policy,t.phase]);
    const spent=t.branchCost.reduce((sum,v)=>sum+v,0),laneCounts=[];
    for(let i=0;i<source.length;i++)for(let j=0;j<32;j++){let cost=t.count[2]-spent;for(let d=0;d<t.branchCost.length;d++)if((t.branchHits[d][i]>>>j)&1)cost+=t.branchCost[d];laneCounts.push(cost);}
    return {m,hmr:t.measured,fixed:t.count[2]-spent,conditional:spent,expected:t.count[2]-spent/2,min:Math.min(...laneCounts),max:Math.max(...laneCounts),avg:laneCounts.reduce((a,b)=>a+b,0)/laneCounts.length,peak:physicalWidth,touched:t.wireUse.size,unique:inputs.length,lanes:32*source.length,ccx:t.count[2],cx:t.count[1],x:t.count[0],sig:t.sig.toString(16)};
}


class PayloadDigit extends MixedArithmetic {
    constructor(m,delta,h,a,width){
        super(m,delta);this.m=m;this.h=h;this.a=a;this.width=width;let at=0;
        const port=n=>{const v=split(at,at+n);at+=n;return v;};
        this.oldR=port(m-h+1);this.r=this.oldR.slice(0,a);this.u=port(h);this.bank=port(m/2);this.v=this.bank.slice(0,h);
        const P=port(m),pads=port(3);this.word=[...P,...pads];
        this.g=port(1)[0];this.pick=port(1)[0];this.carry=port(1)[0];this.flag=port(1)[0];this.qual=port(1)[0];
        this.clean=[this.pick,this.carry,this.flag,this.qual];
        const dw=m-h+2;this.d=this.word.slice(0,dw);this.c=this.word.slice(dw);
        this.e=this.d.slice(0,dw-a);this.rem=this.d.slice(dw-a);this.low=this.c.slice(0,h);this.amount=[...this.e,...this.c];
        if(at>width||a>this.oldR.length||this.c.length!==h+1)throw Error("payload port capacity");
    }
    lt(tape,x,y,ctrl,target){
        const n=y.length,z=x.slice(0,n),last=n-1,ops=[];
        this.cnotList(tape,[],z);
        if(n>1)this.toggle(tape,[...ctrl,y[last]],[],target);
        for(let i=1;i<n;i++)ops.push([NONE,y[i],z[i]]);
        for(let i=n-2;i>=1;i--)ops.push([NONE,y[i],y[i+1]]);
        for(let i=0;i<n-1;i++)ops.push([z[i],y[i],y[i+1]]);
        stepList(ops,false,op=>tape.out(...op));this.toggle(tape,[...ctrl,y[last],z[last]],[],target);
        stepList(ops,true,op=>tape.out(...op));this.cnotList(tape,[],z);
    }
    emit(tape,back){
        const g=[this.g],v=this.v,w=this.flag;
        const head=()=>this.greaterEqual(tape,this.c,v,g,w);
        const mark=()=>this.toggle(tape,g,this.amount.slice(this.u.length),this.qual);
        const tail=()=>{mark();this.lt(tape,this.amount.slice(0,this.u.length),this.u,[this.g,this.qual],w);mark();};
        const seq=[head,rv=>tape.add(v,this.c,[this.g,w],this.carry,!rv),
            ()=>this.cnotList(tape,g,this.low),rv=>tape.add(v,this.low,g,this.carry,rv),
            rv=>this.mixed(tape,this.e,this.r,this.rem,g,!rv),rv=>this.mixed(tape,this.e,v,this.low,g,rv),
            rv=>tape.add(this.u,this.amount,g,this.carry,rv),rv=>tape.add(v,this.amount,[this.g,w],this.carry,!rv),tail];
        stepList(seq,back,fn=>fn(back));
    }
}
function payloadReplay(m,delta,h,a,width,cases,seed,back){
    const L=new PayloadDigit(m,delta,h,a,width),p=(1n<<BigInt(m))-BigInt(delta),rng=rand(seed);
    const obs=[],expect=[];let oldStrip=0,newStrip=0,disabled=0;
    for(let off=0;off<cases.length;off+=24){const st=Uint32Array.from({length:width},rng),ed=st.slice();
        for(let lane=0;lane<32;lane++){
            for(const u of[st,ed])put(u,[L.pick,L.carry],0n,lane);
            const ix=off+lane-Math.floor(lane/4)-1;if(lane%4===0||ix>=cases.length){disabled++;for(const s of[st,ed])put(s,[L.g],0n,lane);continue;}
            const [r,u,v,d,c]=cases[ix],H=(p-r*u)/v,q=H/r,z=H%r,A=u+q*v,e=d/r,mr=d%r,nc=(e+1n)*v+u-1n-c;
            if(!(p===H*v+r*u&&q>=1n&&z>0n&&r>=1n<<BigInt(m/2)&&u>=0n&&u<v&&d>=0n&&d<H&&c>=0n&&c<v+(d<r?u:0n)&&nc>=0n&&nc<A+(mr<z?v:0n)&&bits(r)===a&&bits(v)===h))throw Error("invalid payload domain");
            if(c>=v)oldStrip++;if(nc>=A)newStrip++;
            for(const s of[st,ed]){put(s,[L.g],1n,lane);put(s,L.clean,0n,lane);put(s,L.oldR,r,lane);put(s,L.u,u,lane);put(s,L.bank,v,lane);}
            put(st,L.d,d,lane);put(st,L.c,c,lane);put(ed,L.rem,mr,lane);put(ed,L.amount,nc,lane);
        }
        obs.push(back?ed:st);expect.push(back?st:ed);
    }
    const tape=new Tape(width,obs,null,L.g);L.emit(tape,back);
    for(let b=0;b<obs.length;b++)for(let j=0;j<width;j++)if(obs[b][j]!==expect[b][j])throw Error("payload replay "+[m,h,a,back,b,j]);
    return {m,h,a,width,prepared:cases.length,disabled,oldStrip,newStrip,ccx:tape.count[2],x:tape.count[0],cx:tape.count[1],sig:tape.sig.toString(16)};
}


function invMod(a,p){if(p===1n)return 0n;const [g,x]=eg(mod(a,p),p);if(g!==1n)throw Error("nonunit");return mod(x,p);}
function payloadRoute(p,cut,x) {
    if(!(x>0n&&x<p))throw Error("nonzero field factor required");
    let sign=x>p/2n?-1n:1n,r=sign<0n?p-x:x,H=p,u=0n,v=1n;
    const path=[];while(r>=cut){const q=H/r,z=H%r,A=u+q*v;path.push({r,u,v,H,q,z,A});[H,r,u,v]=[r,z,v,A];sign=-sign;}
    return {path,H,r,u,v,sign,eps:BigInt(path.length%2)};
}
function payloadForward(p,S,Y){
    let d=Y,c=0n;for(const {r,u,v} of S.path){const e=d/r;d%=r;c=(e+1n)*v+u-1n-c;}
    if(d>=S.H||c>=S.v+(d<S.r?S.u:0n)||c<0n)throw Error("terminal digit range");
    const k=S.r===1n?0n:mod(-d*S.v*invMod(p,S.r),S.r),num=p*k+d*S.v;
    if(num%S.r||num/S.r>=p)throw Error("terminal quotient");
    return mod(S.sign*(num/S.r+S.u-c-S.eps),p);
}
function payloadBackward(p,S,value) {
    const {r,u,v,H,sign,eps}=S,q=H/r,z=H%r,A=u+q*v,J=mod(sign*value+v-1n+eps,p);
    const entry=k=>k*A+v*((k*z+r-1n)/r);
    let k=J*r/p;if(entry(k)>J)k--;
    if(k<0n||k>=r||entry(k)>J||entry(k+1n)<=J)throw Error("invalid inverse rank");
    let d=mod(-k*z,r),c=J-entry(k);
    const undo=(R,U,V)=>{const e=c<U?0n:(c-U)/V;c=(e+1n)*V+U-1n-c;d+=e*R;};
    undo(r,u,v);for(let i=S.path.length-1;i>=0;i--){const t=S.path[i];undo(t.r,t.u,t.v);}
    if(c!==0n||d<0n||d>=p)throw Error("uncleared inverse payload");return d;
}
function pointReference(p,P,B){
    if(P===null)return B;if(B===null)return P;
    const [x,y]=P,[a,b]=B;if(x===a&&mod(y+b,p)===0n)return null;
    const slope=x===a?mod(3n*x*x*invMod(2n*y,p),p):mod((y-b)*invMod(x-a,p),p),X=mod(slope*slope-x-a,p);
    return [X,mod(slope*(x-X)-y,p)];
}
function pointPayload(p,cut,P,B){
    if(B===null)return P;if(P===null)return B;const [x,y]=P,[a,b]=B;if(x===a&&mod(y+b,p)===0n)return null;
    if(b===0n)throw Error("two-torsion classical offset");
    const c=mod(3n*a*a,p),d=mod(x-a,p),n=mod(y-b,p),twob=mod(2n*b,p);
    const m=payloadForward(p,payloadRoute(p,cut,d===0n?twob:d),mod(n+(d===0n?c:0n),p)),t=mod(d+3n*a-m*m,p);
    const nd=payloadBackward(p,payloadRoute(p,cut,t===0n?twob:t),m);
    return [mod(a-t,p),mod(nd-(t===0n?c:0n)-b,p)];
}


function fieldInputs(){
    const d=(1n<<32n)+977n,p=(1n<<256n)-d,c=1n<<128n,fx=fieldRoutes();
    const arr=[0n,1n,2n,37n,p-1n,p-2n,p/2n,(p+1n)/2n,c-1n,c,c+1n,2n*c-1n,2n*c+1n,p-c,p-c-1n,p/((1n<<120n)+763n),...Object.values(fx),p-fx.slow,p-fx.ordinary];
    const xs=[...new Set(arr.map(x=>x.toString()))].map(BigInt),rng=rand(0x58d61337);
    while(xs.length<48){let a=0n;for(let i=0;i<8;i++)a=(a<<32n)|BigInt(rng());xs.push(a%p);}return xs;
}
function fieldStress(){
    const p=(1n<<256n)-(1n<<32n)-977n,C=1n<<128n,found=new Set(fieldInputs().map(String)),rng=rand(0x28df864f);
    for(let ell=129;ell<=255;ell++)for(const o of[0n,1n]){const r=(1n<<BigInt(ell-1))+o;found.add(String(r));found.add(String(p-r));}
    for(const h of[2,3,8,16,32,48,64,80,92,104,112,120,126,127,128]){
        const K=128-h;
        for(const e of new Set([0,1,7,8,Math.max(0,K-1),K].filter(e=>e<=K))){
            const v=(1n<<BigInt(h-1))|(h===2?1n:BigInt(rng())%(1n<<BigInt(h-1)))|1n;
            for(const u of[1n,v-1n])for(const upper of[false,true]){
                const tgt=(1n<<BigInt(upper?256-e:255-e))+(upper?-1n:1n),t=(tgt-u)/v;
                let r=t-mod(t-p*invMod(u,v),v),V=v,U=u,H=(p-r*U)/V;
                if(r<C||H<=r||H*V+r*U!==p||bits(V)!==h||bits(r*V+U)!==256-e)continue;
                while(U){const q=V/U;[H,r,U,V]=[r+q*H,H,V%U,U];}
                if(H!==p||r>p/2n||V!==1n)throw Error("directed source reconstruction");
                found.add(String(r));found.add(String(p-r));
            }
        }
    }
    return [...found].map(BigInt);
}
function replayPayload(field){
    const p=field?(1n<<256n)-(1n<<32n)-977n:251n,groups=new Map(),rng=rand(0x75429653);
    function add(row){const[r,u,v]=row,h=bits(v),a=bits(r),key=h+"/"+a,H=(p-r*u)/v,q=H/r,Z=H%r;
        if(!groups.has(key))groups.set(key,[]);const out=groups.get(key);
        if(!field){for(let d=0n;d<H;d++)for(let c=0n;c<v+(d<r?u:0n);c++)out.push([r,u,v,d,c]);return;}
        for(const d of[0n,r-1n,r,q*r-1n,q*r,H-1n,Z-1n,BigInt(rng())*(H>>32n)]){
            if(d<0n||d>=H)continue;const lim=v+(d<r?u:0n);
            for(const c of[0n,lim-1n,lim/2n])out.push([r,u,v,d,c]);
        }
    }
    if(field){const sets=selectedFieldData();for(const rows of sets.groups.values())add(rows[1]);
        for(const[h,l,u]of[[2,249,254],[16,238,242],[64,189,194],[92,160,165],[126,128,132],[128,128,130]])
            for(const row of[...sets.natural.values()].flat().filter(([r,U,V])=>bits(V)===h&&bits(r)>=l&&bits(r)<=u).slice(0,35))add(row);
    }else for(const row of toyPacked(8,p))add(row);
    const ret=[];for(const[key,rows]of groups){const[h,a]=key.split("/").map(Number);
        for(const b of[false,true])ret.push(payloadReplay(field?256:8,field?(1n<<32n)+977n:5,h,a,field?656:80,rows,field?(b?0x2a913741:0x221061f9):(b?0x71182c75:0x458e8790),b));}
    return ret;
}


function validateGroup(){
    const p=(1n<<256n)-(1n<<32n)-977n,C=1n<<128n,rng=rand(0x98c56517);
    const vals=[1n,2n,C-1n,C,C+1n,p-1n,...fieldInputs().filter(x=>x>0n)],toy=[];
    for(const [small,c]of[[17n,4n],[61n,8n],[127n,16n],[251n,16n]]){
        let n=0;for(let x=1n;x<small;x++){const s=payloadRoute(small,c,x),inv=invMod(x,small);
            for(let y=0n;y<small;y++){const z=payloadForward(small,s,y);
                if(z!==y*inv%small||payloadBackward(small,s,z)!==y)throw Error("toy quotient");n++;}}
        toy.push([Number(small),n]);}
    for(let j=0;j<2048;j++){let x=0n,y=0n;for(let k=0;k<8;k++){x=(x<<32n)|BigInt(rng());y=(y<<32n)|BigInt(rng());}
        x=j<vals.length?vals[j]:x%(p-1n)+1n;y%=p;
        const s=payloadRoute(p,C,x),z=payloadForward(p,s,y);if(z*x%p!==y||payloadBackward(p,s,z)!==y)throw Error("field quotient");}
    const G=[0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798n,0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8n],pts=[null,G];
    for(let i=0;i<143;i++)pts.push(pointReference(p,pts.at(-1),G));
    let pairs=0,tangent=0,reverseTangent=0;
    for(let i=1;i<=64;i++){const B=pts[i],neg=[B[0],p-B[1]],dbl=pointReference(p,B,B),negDbl=[dbl[0],p-dbl[1]];
        for(const P of[null,B,neg,negDbl,pts[rng()%pts.length],pts[rng()%pts.length]]){
            const e=pointReference(p,P,B),a=pointPayload(p,C,P,B);
            if(e===null?a!==null:!a||a[0]!==e[0]||a[1]!==e[1])throw Error("group law");
            pairs++;if(B===P)tangent++;if(P===negDbl)reverseTangent++;}}
    return {toy,scalar:2048,pairs,tangent,reverseTangent};
}
function run(mode="toy"){
    if(mode==="payload-toy"||mode==="payload-field")return replayPayload(mode==="payload-field");
    if(mode==="math")return validateGroup();
    const out=[];
    if(mode==="field"||mode==="stress"){
        const xs=mode==="stress"?fieldStress():fieldInputs();
        for(const b of[false,true])out.push(runFold(256,(1n<<32n)+977n,657,xs,b?0x9a4dedcd:0x334b312e,b));
    }else if(mode==="toy"){
        for(const[m,d]of[[8,5],[10,3],[12,3],[14,3],[16,15]]){
            const xs=Array.from({length:(1<<m)-d},(_,i)=>BigInt(i));
            for(const b of[false,true])out.push(runFold(m,d,80,xs,b?0xc2273:0x14753,b));}
    }else throw Error("choose toy, field, stress, payload-toy, payload-field, or math");
    return out;
}


class HornerSquare extends MixedArithmetic {
    constructor(m,delta) {
        super(m,delta);this.m=m;this.p=(1n<<BigInt(m))-this.delta;
        this.y=split(0,m);this.d=split(m,2*m);this.flag=2*m;this.top=2*m+1;this.sel=2*m+2;this.carry=2*m+3;
        this.terms=[];let v=this.delta;
        for(let j=0;v;j++){if(v&1n){const sign=(v&3n)===3n?-1n:1n;this.terms.push([j,Number(sign)]);v-=sign;}v>>=1n;}
    }
    bias(tape,word,ctrl,rev){
        stepList(this.terms,rev,([i,sign])=>this.inc(tape,word.slice(i),ctrl,sign<0?!rev:rev));
    }
    doubling(tape,rev){
        const D=this.d,W=[...D,this.top],f=this.flag;
        const mark=()=>{tape.out(NONE,NONE,f);this.constBelow(tape,D,(this.p+1n)/2n,[],[f]);};
        const seq=[mark,rv=>this.permute(tape,W,[W.at(-1),...W.slice(0,-1)],[],rv),
            rv=>this.bias(tape,W,[f],rv),()=>tape.out(NONE,f,this.top),()=>tape.out(NONE,D[0],f)];
        stepList(seq,rev,fn=>fn(rev));
    }
    addY(tape,idx,rev){
        const Y=this.y,D=this.d,g=this.sel,f=this.flag;
        const gate=()=>tape.out(NONE,Y[idx],g),flip=()=>tape.out(NONE,NONE,f);
        const seq=[gate,rv=>this.bias(tape,D,[],rv),rv=>tape.add(Y,[...D,f],[g],this.carry,rv),flip,
            rv=>this.bias(tape,D,[f],!rv),flip,()=>PayloadDigit.prototype.lt.call(this,tape,D,Y,[g],f),gate];
        stepList(seq,rev,fn=>fn(rev));
    }
    emit(tape,rev){
        const seq=[];for(let j=0;j<this.m-1;j++)seq.push(rv=>this.doubling(tape,!rv));
        for(let i=this.m-1;i>=0;i--){if(i!==this.m-1)seq.push(rv=>this.doubling(tape,rv));seq.push(rv=>this.addY(tape,i,rv));}
        stepList(seq,rev,fn=>fn(rev));
    }
}

class BlockConstant extends HornerSquare{
    constructor(m,delta){super(m,delta);this.block=16;this.local=split(2*m+4,2*m+4+this.block);
        this.bounds=split(2*m+4+this.block,2*m+4+this.block+Math.ceil((m+1)/this.block));}
    arithmetic(tape,D,on,kX,kCX,rev,comparison=null){
        const n=D.length,starts=[];for(let i=0;i<n;i+=this.block)starts.push(i);
        const carry=(i,src,dst,back)=>{
            const seq=[];if(src!==null)seq.push(()=>tape.out(D[i],src,dst));
            seq.push(()=>kCX(i,D[i],dst));if(src!==null)seq.push(()=>kCX(i,src,dst));
            stepList(seq,back,fn=>fn());
        };
        const edge=(j,flag,back)=>{
            const lo=starts[j],end=Math.min(n,lo+this.block),incoming=j?this.bounds[j-1]:null,ops=[];
            for(let i=lo;i<end-1;i++){const src=i===lo?incoming:this.local[i-lo-1],dst=this.local[i-lo];ops.push(rv=>carry(i,src,dst,rv));}
            const last=end-lo===1?incoming:this.local[end-lo-2];stepList(ops,false,fn=>fn(false));
            carry(end-1,last,flag,back);stepList(ops,true,fn=>fn(true));
        };
        const apply=(j,back)=>{
            const lo=starts[j],end=Math.min(n,lo+this.block),incoming=j?this.bounds[j-1]:null,ops=[];
            for(let i=lo;i<end-1;i++){const src=i===lo?incoming:this.local[i-lo-1],dst=this.local[i-lo];ops.push(rv=>carry(i,src,dst,rv));}
            if(j+1<starts.length){const src=end-1===lo?incoming:this.local[end-lo-2];ops.push(rv=>carry(end-1,src,this.bounds[j],rv));}
            for(let i=end-1;i>=lo;i--){
                const ci=i===lo?incoming:this.local[i-lo-1];
                ops.push(()=>{if(on===null)kX(i,D[i]);else kCX(i,on,D[i]);});
                if(ci!==null)ops.push(()=>{if(on===null)tape.out(NONE,ci,D[i]);else tape.out(on,ci,D[i]);});
                if(i>lo){const previous=i-1===lo?incoming:this.local[i-lo-2];ops.push(rv=>carry(i-1,previous,ci,!rv));}
            }
            stepList(ops,back,fn=>fn(back));
        };
        const ops=[];for(let j=0;j<starts.length-1;j++)ops.push(rv=>edge(j,this.bounds[j],rv));
        if(comparison!==null){stepList(ops,false,fn=>fn(false));edge(starts.length-1,comparison,false);stepList(ops,true,fn=>fn(true));}
        else{for(let j=starts.length-1;j>=0;j--)ops.push(rv=>apply(j,rv));stepList(ops,rev,fn=>fn(rev));}
    }
    bias(tape,word,ctrl,rev){
        const K=this.delta,on=ctrl.length?ctrl[0]:null;if(ctrl.length>1)throw Error("bias control count");
        this.arithmetic(tape,word,on,(i,q)=>{if((K>>BigInt(i))&1n)tape.out(NONE,NONE,q);},
            (i,u,q)=>{if((K>>BigInt(i))&1n)tape.out(NONE,u,q);},rev);
    }
    publicTranslate(t,bitX,bitCX,back){
        const D=this.d,f=this.flag,W=[...D,f],N=D.length;
        const cx=(i,u,q)=>{if(i<N)bitCX(i,u,q);},x=(i,q)=>{if(i<N)bitX(i,q);};
        const flip=()=>t.out(NONE,NONE,f);
        const compare=()=>{this.cnotList(t,[],D);this.arithmetic(t,D,null,x,cx,false,f);this.cnotList(t,[],D);};
        const ops=[rv=>this.bias(t,D,[],rv),rv=>this.arithmetic(t,W,null,x,cx,rv),flip,rv=>this.bias(t,D,[f],!rv),flip,compare];
        stepList(ops,back,fn=>fn(back));
    }
}
function squareReplay(m,delta,width,inputs,seed,rev){
    const l=new BlockConstant(m,delta),state=[],want=[],rng=rand(seed);
    for(let off=0;off<inputs.length;off+=32){
        const a=Uint32Array.from({length:width},rng),b=a.slice();
        for(let i=0;i<32;i++){const[y,d]=inputs[(off+i)%inputs.length];for(const st of[a,b]){
             put(st,[l.carry,l.sel,l.top,l.flag,...l.local,...l.bounds],0n,i);put(st,l.y,y,i);}
            put(a,l.d,d,i);put(b,l.d,(d+y*y)%l.p,i);}
        state.push(rev?b:a);want.push(rev?a:b);
    }
    const t=new Tape(width,state,null,NONE);l.emit(t,rev);
    for(let i=0;i<state.length;i++)for(let j=0;j<width;j++)if(state[i][j]!==want[i][j])throw Error("square mismatch "+[m,i,j]);
    return {m,width,touched:t.wireUse.size,pairs:inputs.length,ccx:t.count[2],cx:t.count[1],x:t.count[0],sig:t.sig.toString(16)};
}
class CoordinateArithmetic extends BlockConstant{
    translate(tape,bitX,back){
        const D=this.d,f=this.flag,g=this.sel,W=[...D,f],js=split(0,D.length);
        const transform=()=>{for(let j=0;j<D.length;j++)bitX(j,D[j]);};
        const compare=()=>{transform();for(const j of js){bitX(j,g);this.toggle(tape,[g,D[j]],D.slice(j+1),f);bitX(j,g);}transform();};
        const flip=()=>tape.out(NONE,NONE,f),ops=[rv=>this.bias(tape,D,[],rv),
            rv=>stepList(js,rv,j=>{bitX(j,g);this.inc(tape,W.slice(j),[g],rv);bitX(j,g);}),
            flip,rv=>this.bias(tape,D,[f],!rv),flip,compare];
        stepList(ops,back,fn=>fn(back));
    }
    negate(tape,enable=null){
        const f=this.flag,D=this.d,ctrl=enable===null?[]:[enable],mark=()=>{this.toggle(tape,ctrl,[],f);this.toggle(tape,ctrl,D,f);};
        const K=this.delta-1n;mark();this.cnotList(tape,[f],D);
        this.arithmetic(tape,D,f,(i,q)=>{if((K>>BigInt(i))&1n)tape.out(NONE,NONE,q);},(i,u,q)=>{if((K>>BigInt(i))&1n)tape.out(NONE,u,q);},true);mark();
    }
}
function coordReplay(m,delta,width,inputs,seed,kind,back){
 const h=new CoordinateArithmetic(m,delta),tgt=h.d,states=[],end=[],cs=[],rng=rand(seed);
 for(let off=0;off<inputs.length;off+=32){const a=Uint32Array.from({length:width},rng),b=a.slice(),tab=new Uint32Array(m);
  for(let j=0;j<32;j++){const [C,D]=inputs[(off+j)%inputs.length];for(const st of[a,b])put(st,[h.flag,h.top,h.sel,h.carry,...h.local,...h.bounds],0n,j);
   put(a,tgt,D,j);put(b,tgt,kind==="neg"?mod(-D,h.p):(D+C)%h.p,j);put(tab,split(0,m),C,j);}
  states.push(back?b:a);end.push(back?a:b);cs.push(tab);}
 const t=new Tape(width,states,null,NONE);let conditionalX=0;
 const bitX=(j,q)=>{conditionalX++;for(let i=0;i<states.length;i++)states[i][q]=(states[i][q]^cs[i][j])>>>0;};
 const bitCX=(j,u,q)=>{conditionalX++;for(let i=0;i<states.length;i++)states[i][q]=(states[i][q]^(states[i][u]&cs[i][j]))>>>0;};if(kind==="neg")h.negate(t);else h.publicTranslate(t,bitX,bitCX,back);
 for(let i=0;i<states.length;i++)for(let j=0;j<width;j++)if(states[i][j]!==end[i][j])throw Error("coordinate "+[i,j]);
 return {m,width,pairs:inputs.length,kind,back,ccx:t.count[2],cx:t.count[1],x:t.count[0],conditionalX};
}
function zeroSafeAffine(p,P,B){
    const [x,y]=P||[0n,0n],[a,b]=B,D=mod(x-a,p),N=mod(y-b,p);
    const lam=D===0n?N:mod(N*invMod(D,p),p),T=mod(D+3n*a-lam*lam,p);
    return [mod(a-T,p),mod((T===0n?lam:lam*T)-b,p)];
}
function exceptionTable(p,B){
    const eq=(a,b)=>a[0]===b[0]&&a[1]===b[1],enc=P=>P||[0n,0n],neg=P=>P?[P[0],mod(-P[1],p)]:null;
    if(B===null)return [];
    const inputs=[null,B,neg(B),neg(pointReference(p,B,B))],remaining=[],goals=[];
    for(let i=0;i<inputs.length;i++){
        if(inputs.slice(0,i).some(P=>eq(enc(P),enc(inputs[i]))))continue;
        remaining.push(zeroSafeAffine(p,inputs[i],B));goals.push(enc(pointReference(p,inputs[i],B)));
    }
    const plan=[];for(let i=0;i<remaining.length;i++){
        const A=remaining[i],B=goals[i];plan.push([A,B]);
        for(let j=i+1;j<remaining.length;j++){if(eq(remaining[j],A))remaining[j]=B;else if(eq(remaining[j],B))remaining[j]=A;}
    }
    return plan;
}
function corrected(p,P,B,table){
    if(B===null)return P;let q=zeroSafeAffine(p,P,B);const eq=(a,b)=>a[0]===b[0]&&a[1]===b[1];
    for(const[a,b]of table){if(eq(q,a))q=b;else if(eq(q,b))q=a;}
    return q[0]===0n&&q[1]===0n?null:q;
}
class BaseEnabledTape extends Tape {
    constructor(w,rows,mask){super(w,rows,null,NONE);this.mask=mask;this.conditional=[0,0];}
    out(a,b,q){if(q===a||q===b||(a!==NONE&&a===b))throw Error("alias");const k=a!==NONE?2:b!==NONE?1:0;
        this.count[k]++;this.sig=Math.imul(this.sig^codeGate(a,b,q),0x01000193)>>>0;
        for(let i=0;i<this.batches.length;i++){const r=this.batches[i],v=k===0?-1:k===1?r[b]:r[b]&r[a];r[q]=(r[q]^(v&this.mask[i]))>>>0;}}
    classical(key,bit,ctrl,q,tables){this.conditional[ctrl===null?0:1]++;
        for(let i=0;i<this.batches.length;i++){const r=this.batches[i],m=tables[i][key][bit]&this.mask[i];r[q]=(r[q]^(ctrl===null?m:m&r[ctrl]))>>>0;}}
}
class ClassicalProgram {
    constructor(n,points,sink=null){
        this.n=n;this.p=(1n<<BigInt(n))-points.delta;this.freelist=[];this.next=2*n;this.used=new Set();
        this.stat=[0,0,0,0,0];this.sink=sink;this.words=[];
        for(let i=0;i<Math.ceil(points.base.length/32);i++)this.words.push(new Uint32Array(32768));
        this.masks=this.words.map(()=>0xffffffff);this.stack=[];this.a=Array.from({length:n},(_,i)=>i);this.b=this.a.map(i=>i+n);
        for(let j=0;j<this.words.length*32;j++){const B=points.base[j%points.base.length]||[0n,0n],s=this.words[j>>5];
            for(let i=0;i<n;i++){if(B[0]>>BigInt(i)&1n)s[i]|=1<<(j&31);if(B[1]>>BigInt(i)&1n)s[i+n]|=1<<(j&31);}}
    }
    put(op,t,cond=-1){
        if(cond===t&&cond!==-1)throw Error("classical self control");
        this.stat[op]++;if(this.sink)this.sink(op,t,cond);
        for(let j=0;j<this.words.length;j++){
            const w=this.words[j],c=cond===-1?this.masks[j]:this.masks[j]&w[cond];
            if(op===0)w[t]&=~c;else if(op===1)w[t]|=c;else w[t]^=c;
        }
    }
    zero(t,c=-1){this.put(0,t,c);}
    one(t,c=-1){this.put(1,t,c);}
    flip(t,c=-1){this.put(2,t,c);}
    when(c,fn){
        this.stat[3]++;if(this.sink)this.sink(3,-1,c);this.stack.push(this.masks);
        this.masks=this.words.map((w,i)=>(this.masks[i]&w[c])>>>0);
        fn();this.masks=this.stack.pop();this.stat[4]++;if(this.sink)this.sink(4,-1,-1);
    }
    alloc(n=1,v=0n){const a=[];for(let i=0;i<n;i++){
        const t=this.freelist.length?this.freelist.pop():this.next++;
        if(t>=32768||this.used.has(t))throw Error("classical register space");this.used.add(t);a.push(t);
        if(v>>BigInt(i)&1n)this.one(t);else this.zero(t);
    }return a;}
    drop(a){for(let i=a.length-1;i>=0;i--){const t=a[i];if(!this.used.delete(t))throw Error("double release");this.zero(t);this.freelist.push(t);}}
    copyBit(t,u){if(t===u)return;this.zero(t);this.flip(t,u);}
    copy(a){const b=this.alloc(a.length);for(let i=0;i<a.length;i++)this.flip(b[i],a[i]);return b;}
    set(a,b){for(let i=0;i<a.length;i++)this.copyBit(a[i],b[i]);}
    swapWords(a,b){for(let i=0;i<a.length;i++){this.flip(a[i],b[i]);this.flip(b[i],a[i]);this.flip(a[i],b[i]);}}
    and(t,a,b){this.zero(t);this.when(a,()=>this.one(t,b));}
    any(a){const w=this.alloc();for(const x of a)this.one(w[0],x);return w;}
    geConst(a,k,flag){
        if(k<=0n){this.one(flag);return;}if(k>=(1n<<BigInt(a.length))){this.zero(flag);return;}
        this.one(flag);for(let i=0;i<a.length;i++){
            if((k>>BigInt(i))&1n){this.flip(a[i]);this.zero(flag,a[i]);this.flip(a[i]);}
            else this.one(flag,a[i]);
        }
    }
    lt(a,b,flag){
        const d=this.alloc();this.zero(flag);
        for(let i=0;i<a.length;i++){this.copyBit(d[0],a[i]);this.flip(d[0],b[i]);
            this.when(d[0],()=>this.copyBit(flag,b[i]));}
        this.drop(d);
    }
    equals(a,b,out){this.one(out);const f=this.alloc();for(let i=0;i<a.length;i++){
        this.copyBit(f[0],a[i]);this.flip(f[0],b[i]);this.zero(out,f[0]);}this.drop(f);}
    read(a,j){const w=this.words[j>>5],l=j&31;let v=0n;for(let i=a.length-1;i>=0;i--)v=(v<<1n)|BigInt(w[a[i]]>>>l&1);return v;}
    rawAdd(d,a,carryOut,sub=false){
        if(d.length!==a.length||d.some((q,i)=>q===a[i]))throw Error("classical add port overlap");
        const h=this.alloc(2);let c=h[0],n=h[1];if(sub)for(const q of d)this.flip(q);
        for(let i=0;i<d.length;i++){
            this.and(n,d[i],a[i]);this.flip(d[i],a[i]);this.when(c,()=>this.flip(n,d[i]));this.flip(d[i],c);
            const tmp=c;c=n;n=tmp;
        }
        if(sub)for(const q of d)this.flip(q);
        if(carryOut!==null)this.copyBit(carryOut,c);this.drop(h);
    }
    rawConst(d,value){
        const N=1n<<BigInt(d.length),K=(value%N+N)%N;if(!K)return;
        const h=this.alloc(2);let c=h[0],n=h[1];
        for(let i=0;i<d.length;i++){
            this.and(n,d[i],c);if(K>>BigInt(i)&1n){this.flip(n,d[i]);this.flip(n,c);this.flip(d[i]);}
            this.flip(d[i],c);const tmp=c;c=n;n=tmp;
        }this.drop(h);
    }
    modAdd(d,a,sub=false){
        const t=this.alloc(2),delta=(1n<<BigInt(this.n))-this.p;this.rawAdd(d,a,t[0],sub);
        if(!sub){this.geConst(d,this.p,t[1]);this.one(t[0],t[1]);}
        this.when(t[0],()=>this.rawConst(d,sub?-delta:delta));this.drop(t);
    }
    shiftDown(d){for(let i=0;i<d.length-1;i++)this.copyBit(d[i],d[i+1]);this.zero(d[d.length-1]);}
    dbl(d){
        const flag=this.alloc();this.geConst(d,(this.p+1n)/2n,flag[0]);for(let i=d.length-1;i>0;i--)this.copyBit(d[i],d[i-1]);this.zero(d[0]);
        this.when(flag[0],()=>this.rawConst(d,(1n<<BigInt(this.n))-this.p));this.drop(flag);
    }
    half(d){const f=this.alloc();this.flip(f[0],d[0]);this.shiftDown(d);this.when(f[0],()=>this.rawConst(d,(this.p+1n)/2n));this.drop(f);}
    mul(a,b){const out=this.alloc(this.n);
        for(let i=this.n-1;i>=0;i--){if(i!==this.n-1)this.dbl(out);this.when(b[i],()=>this.modAdd(out,a));}
        return out;
    }
    sum(a,b,sub=false){const r=this.copy(a);this.modAdd(r,b,sub);return r;}
    neg(a){const r=this.alloc(this.n);this.modAdd(r,a,true);return r;}
    inverse(d){
        const U=this.alloc(this.n,this.p),V=this.copy(d),X=this.alloc(this.n),Y=this.alloc(this.n,1n),flags=this.alloc(2);
        for(let j=0;j<2*this.n;j++){
            this.lt(V,U,flags[0]);this.and(flags[1],V[0],flags[0]);
            this.when(flags[1],()=>{this.swapWords(U,V);this.swapWords(X,Y);});
            // Capture the selector before V becomes even in the subtraction.
            this.copyBit(flags[0],V[0]);
            this.when(flags[0],()=>{this.rawAdd(V,U,null,true);this.modAdd(Y,X,true);});
            this.shiftDown(V);this.half(Y);
        }
        this.drop(flags);this.drop(Y);this.drop(V);this.drop(U);return X;
    }
    nzProduct(s,t){const p=this.mul(s,t),nz=this.any(t);this.flip(nz[0]);this.when(nz[0],()=>this.set(p,s));this.drop(nz);return p;}
    prepare(){
        const a=this.a,b=this.b,n=this.n,seven=this.alloc(n,7n%this.p);
        const finite=this.any([...a,...b]),zero=this.alloc(n);
        const twiceA=this.copy(a);this.dbl(twiceA);const thriceA=this.sum(twiceA,a),minusTwoA=this.neg(twiceA),minusB=this.neg(b);
        const S=this.mul(b,b),D=this.mul(a,b);this.dbl(D);
        // For a finite secp256k1 point both coordinates are nonzero; use denominator 1 for infinity.
        this.flip(finite[0]);this.when(finite[0],()=>this.one(D[0]));this.flip(finite[0]);
        const I=this.inverse(D);this.drop(D);
        const s0=this.mul(S,I);this.dbl(s0);
        const c3=this.sum(S,seven,true),c3copy=this.copy(c3);this.dbl(c3);this.modAdd(c3,c3copy);this.drop(c3copy);
        const s2=this.mul(c3,I);this.drop(c3);this.drop(I);
        const t0=this.copy(twiceA),s0sq=this.mul(s0,s0);this.modAdd(t0,s0sq,true);this.drop(s0sq);
        const x0=this.sum(a,t0,true),y0=this.nzProduct(s0,t0);this.modAdd(y0,b,true);this.drop(t0);this.drop(s0);
        const x2=this.mul(s2,s2);this.modAdd(x2,twiceA,true);const ax=this.sum(a,x2,true),y2=this.mul(s2,ax);this.modAdd(y2,b,true);this.drop(ax);
        const fourS=this.copy(S);this.dbl(fourS);this.dbl(fourS);const tn=this.sum(thriceA,fourS,true);this.drop(fourS);
        const xn=this.sum(a,tn,true),mn=this.copy(minusB);this.dbl(mn);const yn=this.nzProduct(mn,tn);this.modAdd(yn,b,true);this.drop(mn);this.drop(tn);
        const lastY=this.sum(s2,b,true);
        for(const w of[seven,S,s2,twiceA])this.drop(w);
        const raw=[[x0,y0],[minusTwoA,this.copy(minusB)],[xn,yn],[this.copy(a),lastY]];
        const goal=[[a,b],[x2,y2],[zero,zero],[a,minusB]],eq=this.alloc();
        // Images are pairwise distinct. When a target equals a later image, track its new value.
        for(let i=0;i<raw.length;i++)for(let j=i+1;j<raw.length;j++){
            this.equals([...raw[j][0],...raw[j][1]],[...goal[i][0],...goal[i][1]],eq[0]);
            this.when(eq[0],()=>{this.set(raw[j][0],raw[i][0]);this.set(raw[j][1],raw[i][1]);});
        }
        this.drop(eq);return {finite:finite[0],thriceA,raw,goal};
    }
}
function compileOffsetControls(n,delta,points,sink=null){
    const c=new ClassicalProgram(n,{delta,base:points},sink),plan=c.prepare(),ports={a:c.a,b:c.b,"3a":plan.thriceA};
    for(let i=0;i<4;i++){
        const left=plan.raw[i].flat(),right=plan.goal[i].flat(),l=c.copy(left),r=c.copy(right),d=c.copy(left);
        for(let j=0;j<l.length;j++){c.flip(l[j]);c.flip(r[j]);c.flip(d[j],right[j]);}
        ports["e"+i+"_0"]=l;ports["e"+i+"_1"]=r;ports["e"+i+"_2"]=d;
    }
    const views=c.words.map(w=>Object.fromEntries(Object.entries(ports).map(([k,v])=>[k,Uint32Array.from(v,id=>w[id])])));
    const finite=c.words.map(w=>w[plan.finite]>>>0);
    const spent=c.stat.slice(),peak=c.next;
    const release=()=>{for(const id of [...c.used])c.drop([id]);
        if(c.stack.length||c.used.size)throw Error("classical cleanup");
        for(const w of c.words)for(let j=2*n;j<peak;j++)if(w[j])throw Error("dirty classical scratch "+j);};
    return {c,plan,ports,views,finite,peak,spent,release};
}
class CompleteTape extends MeasuredNct {
    constructor(width,states,seed,policy,mask){super(width,states,seed,policy);this.valid=mask;this.conditional=[0,0];}
    out(a,b,q){
        if(q===a||q===b||(a!==NONE&&a===b)||q>=this.n||(a!==NONE&&a>=this.n)||(b!==NONE&&b>=this.n))throw Error("physical gate port");
        const k=a!==NONE?2:b!==NONE?1:0;this.count[k]++;if(this.current!==null)this.controlled[k]++;
        this.sig=Math.imul(this.sig^codeGate(a,b,q),0x01000193)>>>0;
        for(let i=0;i<this.batches.length;i++){const r=this.batches[i],g=this.current===null?this.valid[i]:this.valid[i]&this.current[i];r[q]=(r[q]^(g&(k===0?-1:k===1?r[b]:r[a]&r[b])))>>>0;}
    }
    hmr(q){
        if(this.current!==null)throw Error("nested HMR");const id=this.measured++,ms=[];
        for(let i=0;i<this.batches.length;i++){const r=this.batches[i],p=this.policy,g=this.valid[i];
            const m=(p==="zero"?0:p==="one"?0xffffffff:typeof p==="number"?(id===p?0xffffffff:0):this.draw())&g;
            this.phase[i]=(this.phase[i]^(r[q]&m))>>>0;r[q]&=~g;ms.push(m>>>0);}
        this.sig=Math.imul(this.sig^(0xffe00000+q),0x01000193)>>>0;return ms;
    }
    z(q){this.zCount++;for(let i=0;i<this.batches.length;i++)this.phase[i]=(this.phase[i]^(this.batches[i][q]&this.valid[i]&(this.current===null?-1:this.current[i])))>>>0;}
    classical(key,bit,ctrl,q,tables){this.conditional[ctrl===null?0:1]++;for(let i=0;i<this.batches.length;i++){const r=this.batches[i],m=tables[i][key][bit]&this.valid[i];r[q]=(r[q]^(ctrl===null?m:m&r[ctrl]))>>>0;}}
}
class PointFoldTape extends FoldTape{
    constructor(logical,l,output,d,y){
        super(logical,[],l.g);const b=l.bank.length,m=l.m;
        const map=[...d,2*m,...split(2*m+1,2*m+1+b),...y,...split(2*m+b+1,logical-1)];
        if(new Set(map).size!==logical-1||map.length!==logical-1)throw Error("point fold mapping");
        this.map=map;const wire=x=>x===NONE?NONE:map[x];
        this.physical={out:(a,b,t)=>output.out(wire(a),wire(b),wire(t))};
        this.toGlobal=x=>map[x>l.g?x-1:x];this.hmr=q=>output.hmr(this.toGlobal(q));
        this.z=q=>output.z(this.toGlobal(q));this.cond=(cond,fn)=>output.cond(cond,fn);this.hist=new Map();
    }
}
function upperSteps(t,m,delta,l,logical){
    const p=(1n<<BigInt(m))-BigInt(delta),g=[l.g];const classify=()=>{l.toggle(t,g,[],l.sig);l.constBelow(t,l.r,(p+1n)/2n,g,[l.sig]);};
    const ops=[classify,rv=>l.reflect(t,l.r,[l.g,l.sig],rv),()=>l.toggle(t,g,[],l.bank[0])];
    const width=l.bank.length;for(let k=0;k<width;k++){
        const row=new UnguardedGeneral(m,delta,k,logical);if(k>0&&k<width-1){const unit=new EarlyUnit(m,delta,k,logical);ops.push(rv=>unit.emit(t,rv));}
        ops.push(rv=>row.emit(t,rv),rv=>row.permute(t,[row.r.at(-1),...row.u],[...row.u,row.r.at(-1)],g,rv));
    }return ops;
}
function bracketMap(tape,m,delta,D,Y,div,backend){
    const logical=2*m+m/2+10+Math.ceil(Math.log2(m/2)),l=new UnguardedGeneral(m,delta,0,logical);
    const t=new PointFoldTape(logical,l,tape,D,Y),ops=upperSteps(t,m,delta,l,logical);stepList(ops,false,fn=>fn(false));
    const b=l.bank.length,R=D.slice(0,m-b),U=D.slice(m-b),V=l.bank.map(q=>t.toGlobal(q)),sign=t.toGlobal(l.sig);
    const occupied=new Set([...R,...U,...V,...Y,sign]),clean=tape.ids.filter(i=>!occupied.has(i));
    backend(tape,{R,U,V,Y,sign,clean},div,(1n<<BigInt(m))-BigInt(delta));
    const f=clean[0],mark=()=>{l.toggle(tape,[sign],[],f);l.toggle(tape,[sign],Y,f);};
    mark();l.reflect(tape,Y,[f],false);mark();
    stepList(ops,true,fn=>fn(true));if(t.hist.size)throw Error("unfinished deferred phases");
}
function nativeSink(tape,map){
    const measures=[];const C1=-2;
    function gate(a,b,q){const t=map[q];if(t<0||t===undefined)throw Error("backend target "+[q,t]);const u=a===NONE?C1:map[a],v=b===NONE?C1:map[b];
        if(u===undefined||v===undefined)throw Error("backend control "+[a,b]);
        if(u===C1)tape.out(NONE,v===C1?NONE:v,t);else if(v===C1)tape.out(NONE,u,t);else tape.out(u,v,t);
    }
    return(kind,buf)=>{
        if(kind==="packed"){for(const z of buf)gate(z>>>20,(z>>>10)&1023,z&1023);return;}
        if(kind==="nct"){for(const z of buf)gate(z.length===3?z[0]:NONE,z.length>1?z[z.length-2]:NONE,z[z.length-1]);return;}
        const q=map[buf[0]],id=kind==="cphase"?buf[2]:buf[1];if(q===undefined||q<0)throw Error("reserved phase/HMR slot");
        if(kind==="hmr"){measures[id]=tape.hmr(q);return;}
        if(!measures[id])throw Error("phase before measurement");
        if(kind==="phase"){tape.cond(measures[id],()=>tape.z(q));return;}
        if(kind==="cphase"){const b=map[buf[1]];tape.cond(measures[id],()=>{if(b===C1)tape.z(q);else for(let i=0;i<tape.batches.length;i++)tape.phase[i]=(tape.phase[i]^(tape.batches[i][q]&tape.batches[i][b]&tape.current[i]&tape.valid[i]))>>>0;});return;}
        throw Error("unknown native event "+kind);
    };
}
function rationalBackend(emitter,inverse,extraEnable=false){return(tape,G,divide,p)=>{
    const {R,U,V,Y,clean}=G,h=R.length,helper=new MixedArithmetic(2*h,(1n<<BigInt(2*h))-p);
    const outer=U.map(q=>tape.hmr(q));const recode=()=>{
        tape.out(NONE,R[1],V[0]);tape.out(NONE,R[1],V[1]);helper.toggle(tape,[V[0]],[...R.filter(q=>q!==R[1]),...V.slice(1)],R[1]);
        tape.out(NONE,R[1],V[1]);tape.out(NONE,R[1],V[0]);};
    const each=fn=>{for(let i=0;i<tape.batches.length;i++)for(let j=0;j<32;j++)if((tape.valid[i]>>>j)&1)fn(tape.batches[i],j);};
    recode();const small=divide?V:R,other=divide?R:V,rawR=[...U,...Y.slice(0,h)],rawZero=Y.slice(h);
    const fieldMap=(a,b)=>{const ids=[...a,...U,...Y,...b];let z=0;for(let i=640;i<657;i++)ids[i]=i===648?-2:clean[z++];return ids;};
    if(emitter){if(h!==128)throw Error("intrinsic factor width");emitter.forward(nativeSink(tape,fieldMap(small,other)));}
    else each((st,j)=>{const k=get(st,small,j),y=get(st,Y,j);if(!k||get(st,U,j))throw Error("forward entry");put(st,rawR,k*y%p,j);put(st,rawZero,0n,j);});
    if(inverse){const im=fieldMap(other,small);if(extraEnable){im[648]=clean[16];tape.out(NONE,NONE,im[648]);}
        inverse(nativeSink(tape,im));if(extraEnable)tape.out(NONE,NONE,im[648]);}
    else each((st,j)=>{const k=get(st,other,j),q=get(st,rawR,j);if(!k||get(st,rawZero,j))throw Error("inverse entry");put(st,U,0n,j);put(st,Y,q*invMod(k,p)%p,j);});
    recode();if(emitter){
        const ids=new Array(657);for(let i=0;i<128;i++){ids[129-i]=R[i];ids[259-i]=V[i];ids[260+i]=U[i];}
        for(let i=0;i<256;i++)ids[389+i]=Y[i];ids[645]=-2;let j=0;for(let i=0;i<ids.length;i++)if(ids[i]===undefined)ids[i]=clean[j++];
        const sink=nativeSink(tape,ids);emitter.regenerate(chunk=>sink("packed",chunk));
    }else each((st,j)=>{const r=get(st,R,j),v=get(st,V,j);if(get(st,U,j))throw Error("dirty U at return");put(st,U,v===1n?0n:p*invMod(r%v,v)%v,j);});
    for(let i=0;i<U.length;i++)tape.cond(outer[i],()=>tape.z(U[i]));
};}
function shellWithFieldOracles(m,delta,rows,back,emitter=null,inverse=null,policy='random',extraEnable=false){
 const width=Math.max(2*m+4+16+Math.ceil((m+1)/16)+3,2*m+m/2+10+Math.ceil(Math.log2(m/2))+(extraEnable?1:0)),arith=new CoordinateArithmetic(m,delta),shiftY=Object.create(arith);
 arith.d=split(0,m);arith.y=split(m,2*m);shiftY.y=arith.d;shiftY.d=arith.y;
 const {y,d}=arith,p=arith.p,controls=compileOffsetControls(m,BigInt(delta),rows.map(r=>r.B)),mask=controls.finite,tables=controls.views;
 const states=[],wants=[],rng=rand(0xf28549),both=[...d,...y];
 for(let off=0;off<rows.length;off+=32){const before=Uint32Array.from({length:width},rng),after=before.slice();
     for(let lane=0;lane<32;lane++){const {P,goal}=rows[(off+lane)%rows.length],src=P||[0n,0n],dst=goal||[0n,0n];
       put(before,d,src[0],lane);put(before,y,src[1],lane);put(after,d,dst[0],lane);put(after,y,dst[1],lane);
       for(const st of[before,after])put(st,split(2*m,width),0n,lane);}
     states.push(back?after:before);wants.push(back?before:after);}
 const tape=new CompleteTape(width,states,0x69b17,policy,mask),translate=(self,key,rv)=>self.publicTranslate(tape,(i,q)=>tape.classical(key,i,null,q,tables),(i,u,q)=>tape.classical(key,i,u,q,tables),rv);
 const field=(div)=>bracketMap(tape,m,BigInt(delta),d,y,div,rationalBackend(emitter,inverse,extraEnable));
 const chunks=[],flags=[],chunk=Math.min(128,Math.ceil(both.length/4));
 for(let i=0;i<both.length;i+=chunk){flags.push(2*m+chunks.length);chunks.push(both.slice(i,i+chunk));}
 const flag=2*m+chunks.length;
 const eq=(k,j)=>{const key="e"+k+"_"+j,flip=()=>both.forEach((q,i)=>tape.classical(key,i,null,q,tables));
      flip();for(let i=0;i<chunks.length;i++)arith.toggle(tape,chunks[i],[],flags[i]);arith.toggle(tape,flags,[],flag);
      for(let i=chunks.length-1;i>=0;i--)arith.toggle(tape,chunks[i],[],flags[i]);flip();};
 const swap=k=>{eq(k,0);eq(k,1);both.forEach((q,i)=>tape.classical("e"+k+"_2",i,flag,q,tables));eq(k,1);eq(k,0);};
 const steps=[rv=>translate(arith,"a",!rv),rv=>translate(shiftY,"b",!rv),rv=>field(!rv),
      rv=>translate(arith,"3a",rv),rv=>arith.emit(tape,!rv),rv=>field(rv),()=>arith.negate(tape),
      rv=>translate(arith,"a",rv),rv=>translate(shiftY,"b",!rv),rv=>stepList([0,1,2,3],rv,swap)];
 stepList(steps,back,fn=>fn(back));
 for(let i=0;i<states.length;i++)for(let j=0;j<width;j++)if(states[i][j]!==wants[i][j])throw Error("full coordinate topology "+[i,j]);
 if(tape.phase.some(v=>v!==0))throw Error('point phase '+[m,back,policy,tape.phase]);controls.release();return {m,width,points:rows.length,shortForwardOracles:emitter?0:2,shortInverseOracles:inverse?0:2,historyOracles:emitter?0:2,hmr:tape.measured,alwaysT:tape.count[2]-tape.controlled[2],branchT:tape.controlled[2],expectedT:tape.count[2]-tape.controlled[2]/2,classicalOffsetOps:controls.c.stat.reduce((a,b)=>a+b),classicalBits:controls.peak,ccx:tape.count[2],cx:tape.count[1],x:tape.count[0],conditionX:tape.conditional[0],conditionCX:tape.conditional[1],sig:tape.sig.toString(16)};
}
return {pointReference,exceptionTable,shellWithFieldOracles,coordReplay,squareReplay,run,runFold,payloadForward,payloadBackward,pointPayload,fieldInputs,fieldStress};
})();
if (typeof module !== 'undefined' && module.exports) {
    module.exports=midpoint656;
    if(require.main===module) console.log(JSON.stringify(midpoint656.run(process.argv[2]||'toy'),null,2));
}
