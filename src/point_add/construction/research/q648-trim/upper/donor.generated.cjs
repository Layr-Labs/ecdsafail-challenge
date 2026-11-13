const stageConfig={"width":648,"multiplyModule":"./m6-multiply-649.cjs","divideModule":"./divide-i.cjs","historyModule":"../q648w/r648-history.cjs","upperPatches":["./u-upper-649.cjs"],"historyNine":true,"stages":{"upper":{"logical":[256,642,643,644,645,646,648],"physical":[512,641,642,643,644,645,646]},"multiply":{"logical":[640,641,642,643,644,645,646],"physical":[512,641,642,643,644,645,646]},"divide":{"logical":[640,641,642,646,647,649,650],"physical":[512,641,642,643,644,645,646]},"history":{"logical":[0,1,130,131,646,647,648],"physical":[512,641,642,643,644,645,646]}},"helperSites":[512,641,642,643,644,645,646],"divideEntry":"./d14-divide-649.cjs","upperPackage":{"entry":"../U15/integration/upper-649.cjs","files":"../U15/INTEGRATION-U15.json","prices":"../U15/PRICES.json"},"expected":null,"expectedBasis":{"label":"q648 composition (hole): no expected count"},"signPhysical":647};
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
        this.tags=port(Math.ceil(Math.log2(m/2)));this.dv=[f1,(([[113,124,256],[125,127,643]]).find(([a,b])=>k>=a&&k<=b)||[0,0,f2])[2]];this.qtop=q1;
        this.ctrl=[this.g,this.take];this.v=this.bank.slice(0,this.h);
        this.q=[...this.bank.slice(this.h),q0,q1];this.A=[...this.q,...this.u];
        this.big=[...this.r,...this.u];this.n=this.big.slice(0,m);this.borrow=this.big[m];
        this.maxShift=this.half-this.h;
        this.tag=this.tags.slice(0,this.maxShift?Math.floor(Math.log2(this.maxShift))+1:0);
        this.aux=[this.pick,this.carry,...this.dv,q0,q1,this.take,...this.tags];
        if(at>width||this.h>m/2)throw Error("universal width");
    }
    normalize(tape,back){
        if(this.u39Trial){this.u39Normalize(tape,back);return;}
        if(this.u38NormLease){
            const H=Object.create(this);H.u38NormLease=false;
            const lease=()=>tape.out(NONE,this.take,this.v[this.k]);
            if(!back)lease();H.normalize(tape,back);if(back)lease();return;
        }
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
        const flag=this.k===127?this.pick:this.tags[0],on=[this.g,flag];
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
    flagProbe(tape,flag,i,rv){
        if(i===1&&[119,123,124].includes(this.k)){const layer=Object.create(this);layer.tags=this.tags.slice();layer.narrowProbe=true;layer.u648Narrow=true;layer.tags[2]=this.A.at(-1);if(layer.ab!==this.half+1)throw Error('q648 narrow '+this.k);layer.signProbe(tape,flag,rv);return;}
        if(i===0&&[113,114,115,116,117,118,120,121,122].includes(this.k)){const layer=Object.create(this);layer.tags=this.tags.slice();layer.tags[3]=this.dv[1];layer.narrowProbe=true;layer.u648Narrow=true;layer.u648Narrow0=true;if(layer.ab!==this.half+1)throw Error('q648 narrow0 '+this.k);layer.signProbe(tape,flag,rv);return;}
        const lg=x=>x>0?Math.floor(Math.log2(x))+1:0,a=this.r.length-(this.half+2);
        if(lg(a)===3 && (i===0 || this.k>=120)){
            const layer=Object.create(this);layer.tags=this.tags.slice();
            if(i===0)layer.tags[2]=this.dv[1];
            else{layer.narrowProbe=true;layer.tags[2]=this.A.at(-1);if(layer.ab!==this.half+1)throw Error("U second probe split");}
            layer.signProbe(tape,flag,rv);return;
        }
        if(lg(a)<4||typeof this.alignedSign!=="function"){this.signProbe(tape,flag,rv);return;}
        if(this.dv.length!==2||flag!==this.dv[i]||lg(a)!==4||lg(a+1)!==4||this.ab!==this.half+2)throw Error("unhosted two-flag probe");
        const layer=Object.create(this);layer.tags=this.tags.slice();
        if(i===0)layer.tags[3]=this.dv[1];
        else{layer.narrowProbe=true;layer.tags[3]=this.A.at(-1);if(layer.ab!==this.half+1)throw Error("narrow probe split");}
        layer.signProbe(tape,flag,rv);
    }
    select(tape){
        const high=this.bank.slice(this.h),g=[this.g,this.bank[this.k]];
        this.toggle(tape,g,high,this.take);
        this.toggle(tape,g,[...high,...this.r.slice(this.half)],this.take);
    }
    core(tape,back){
        const q=this.q,v=this.v,u=this.u,ctrl=this.ctrl,coef=rv=>this.mixed(tape,q,v,u,ctrl,rv);
        const seq=[rv=>this.estimate(tape,rv),coef];
        if((this.k>=113&&this.k<=127)&&process.env.R113_RELAY!=='0'){
          const f2=this.dv[1],P=this.pick,RT=this.r.at(-1),C=this.carry,T=this.take,twoPad=q.slice(-2);
          const sw=(a,b)=>()=>{if(a===b)return;this.toggle(tape,[T,a],[],b);this.toggle(tape,[T,b],[],a);this.toggle(tape,[T,a],[],b);};
          const D=Object.create(this);D.dv=[this.dv[0],C];
          // flag2 lives on carry from the end of flag probe 1 to threshold(dv1): add1 takes pick as its carry ancilla, and coef^-1 runs with
          // the single control [take] (g is the fixed enable), so mixed needs no carry selector.
          seq.push(rv=>this.flagProbe(tape,this.dv[0],0,rv),rv=>tape.add(v,this.A,[...ctrl,this.dv[0]],this.carry,!rv),
            rv=>this.flagProbe(tape,f2,1,rv),sw(f2,C),rv=>tape.add(v,this.A,[...ctrl,C],P,!rv),
            rv=>this.mixed(tape,q,v,u,[T],!rv),rv=>D.removeDebt(tape,rv),coef,rv=>this.affine(tape,rv),
            rv=>this.permute(tape,[...this.bank,...u,...twoPad],[...this.A.slice(0,this.half),...v,...this.A.slice(this.half)],ctrl,rv));
          stepList(seq,back,fn=>fn(back));return;
        }
        this.dv.forEach((flag,i)=>seq.push(rv=>this.flagProbe(tape,flag,i,rv),rv=>tape.add(v,this.A,[...ctrl,flag],this.carry,!rv)));
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
        const H=Object.create(this.hostRank((this.k>=113&&this.k<=127)?this.A[this.half+1]:this.dv[1]));H.tag=H.tag.slice();if(H.tag.length>=3)H.tag[2]=this.dv[0];if(this.k>=120&&this.k<=125)H.tag[1]=(this.k>=113&&this.k<=127)?this.A[this.half+1]:this.dv[1];if(this.k>=113&&this.k<=119){H.tag[1]=this.v[this.k];H.u38NormLease=true;}
        if(this.k>=113&&this.k<=126){H.tag[0]=this.pick;H.digit=H.digitDirty;}
        const D=this.topDivisor(),Q=this.q,g=this.ctrl,js=split(0,this.maxShift+1),seq=[
            rv=>this.packNumber(tape,rv),rv=>H.normalize(tape,rv),
            ()=>this.cnotList(tape,g,Q),
            ()=>{for(let i=0;i<Q.length;i++)this.toggle(tape,[...g,D[i]],[],Q[i]);}
        ];
        for(let j=this.maxShift-1;j>=0;j--)seq.push(rv=>H.middleDigit(tape,j,D,rv));
        seq.push(rv=>this.inc(tape,Q,g,rv));
        for(const j of js)seq.push(rv=>H.reducedTerm(tape,D,j,rv));
        for(const j of js)seq.push(rv=>H.moveQuotient(tape,j,rv));
        seq.push(rv=>H.normalize(tape,!rv),rv=>this.packNumber(tape,!rv));
        stepList(seq,back,fn=>fn(back));
    }
    installZeros(tape,back){
        if(this.uDebt){
            const Q=this.q;stepList(split(0,this.maxShift),back,j=>this.uSelect(tape,this.uLess(j+1),(tp,V)=>this.permute(tp,[this.n[j],Q[j+2]],[Q[j+2],this.n[j]],[V],back)));
            tape.out(NONE,NONE,this.n.at(-1));return;
        }
        const Q=this.q,sel=this.carry;
        stepList(split(0,this.maxShift),back,j=>{
            this.indicator(tape,j,"le",[],sel);
            this.permute(tape,[this.n[j],Q[j+2]],[Q[j+2],this.n[j]],[sel],back);
            this.indicator(tape,j,"le",[],sel);
        });
        tape.out(NONE,NONE,this.n.at(-1));
    }
    mixedHead(tape,D,C,back) {
        if(this.uDebt){
            const Q=this.q,stages=[rv=>this.mixed(tape,Q.slice(0,2),D,C,[],rv)];
            for(let i=2;i<Q.length;i++)stages.push(rv=>this.uSelect(tape,[{yes:[],no:[]},...this.uLess(i-1)],(tp,V)=>{
                const z=[...C,Q[i]],origins=[...z.slice(1),z[0]],seq=[rr=>this.digit(tp,z,D,[V],!rr),rr=>this.permute(tp,z,origins,[V],rr)];
                stepList(seq,rv,fn=>fn(rv));
            }));stepList(stages,back,fn=>fn(back));return;
        }
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
        if(this.k>=113&&this.k<=126){this.u7Debt(tape,back);return;}
        const g=this.ctrl,Q=this.q,H=Object.create(this.hostRank(this.pick));
        if(this.k>=113&&this.k<=119){H.tag=H.tag.slice();H.tag[2]=this.carry;H.uDebt=true;}
        if(this.k>=124&&this.k<=125){H.tag=H.tag.slice();H.tag[1]=this.pick;H.rankHost=this.pick;H.digit=this.digitDirty;}
        if(this.k>=113&&this.k<=123){H.tag=H.tag.slice();H.tag[1]=this.v[this.k];H.u38NormLease=true;}
        if(this.k>=120&&this.k<=123){H.tag=H.tag.slice();H.tag[0]=this.carry;H.uDebt=true;}
        if(this.k>=124&&this.k<=126){H.tag=H.tag.slice();H.tag[0]=this.v[this.k];H.u38NormLease=true;}
        const seq=[rv=>this.packNumber(tape,rv),rv=>H.normalize(tape,rv),
            rv=>this.inc(tape,Q,g,rv),()=>H.threshold(tape,this.dv[0]),
            rv=>this.inc(tape,Q,g,rv),()=>H.threshold(tape,this.dv[1]),
            rv=>this.inc(tape,Q,g,!rv),rv=>this.inc(tape,Q,g,!rv),
            rv=>H.normalize(tape,!rv),rv=>this.packNumber(tape,!rv)];
        stepList(seq,back,fn=>fn(back));
    }
}


class AlignedGeneral extends TruncatedGeneral {
    get ab(){
      if(!this.r)return undefined;if(this.u648Narrow)return this.half+1;if(this.u40Probe&&(this.k===62||this.k===95))return this.half+1;const wide=this.half+2,a=this.r.length-wide,mode="same-width";
      if(mode==='off'||a<0||!(this.narrowProbe||this.layouts()))return wide;
      const lg=x=>x>0?Math.floor(Math.log2(x))+1:0;
      if(mode==='same-width'&&lg(a+1)!==lg(a))return wide;
      return wide-1;
    }
    guardTop(){
      const all={b:this.A.at(-1),p:this.pick,c:this.carry};
      if(this.ab===this.half+2)return [all.b,all.p];
      return [all.p];
    }

    rank(tape,tag) {
        const high=this.r.slice(this.ab);if(!high.length)return;
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
        const base=this.ab,top=this.guardTop();
        const moving=rv=>stepList(split(base,this.r.length),rv,i=>{
            const a=D[i+this.h-1-base+(this.centeredFree?1:0)],b=this.r[i],mark=()=>this.constBelow(tape,tag,BigInt(i-base+1),[],[this.pick]);
            mark();this.permute(tape,[a,b],[b,a],[this.pick],rv);mark();
        });
        const extra=rv=>{const upper=D.slice(-top.length);this.permute(tape,[...upper,...top],[...top,...upper],[],rv);};
        const seq=[moving,extra];stepList(seq,back,fn=>fn(back));
    }
    alignedMix(tape,S,D,tag,back){
        const base=this.ab,layer=Object.create(this);layer.pick=this.g;layer.carry=this.take;
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
    // r35 probe: rank register of the aligned sign probe with its fourth bit re-hosted (rows 0..112 only).
    probeTag(base,tag,target){
        if(this.k===63){const out=tag.slice();out[2]=this.aux[3];tag=out;}
        if(this.k>112||tag.length<4)return tag;
        const f2=this.aux[3],borrow=this.A.at(-1),top=this.guardTop(),S=this.A.slice(0,this.half+1);
        if(f2!==this.take-1||borrow!==this.borrow||!this.layouts())throw Error("probe host ports");
        // ancilla of the clean tail digit (UnguardedGeneral.alignedMix/tailDigit), when that path is taken
        const tailAncilla=!this.wideBand?this.dv[1]:null;
        const busy=new Set([...tag,...top,...S,...this.r,...this.zword,target,this.take,this.g,this.pick,this.carry,this.v[this.k],tailAncilla]);
        const host=base===this.half+1?borrow:f2;
        if(busy.has(host))throw Error("probe rank host is busy "+[this.k,base,host]);
        const out=tag.slice();out[3]=host;if(this.u648VkHost){if(out.includes(this.v[this.k])&&out.indexOf(this.v[this.k])!==1)throw Error('U648 vk twice');return out.map((q,i)=>q===f2&&i!==3?this.v[this.k]:q);}return out;
    }
    alignedSign(tape,target){
        if(this.u5PhaseHost!==undefined&&this.k>=0&&this.k<=112&&!([]).includes(this.k)&&typeof this.u648FourSign==='function'){if(this.u648VkOk()){const H=Object.create(this);H.u40Probe=true;H.u648VkHost=true;H.u40Sign(tape,target);return;}this.u648FourSign(tape,target);return;}
        if(this.u40Probe){this.u40Sign(tape,target);return;}
        if(this.k>=119&&this.k<=122&&!this.u648Narrow0&&typeof this.u648FourSign==='function'){this.u648FourSign(tape,target);return;}
        if(this.u648Narrow&&[119,123].includes(this.k)&&!this.u40Probe&&typeof this.u648FourSign==='function'){this.u648FourSign(tape,target);return;}
        const base=this.ab,w=this.half+1;
        if(this.r.length<this.half+2){super.signProbe(tape,target,false);return;}
        const free=this.r.length-base,tag=this.probeTag(base,this.tags.slice(0,free?Math.floor(Math.log2(free))+1:0),target).map((q,i)=>{
          if(i===2)return this.carry;
          if(i!==1)return q;
          if(this.k===63)return this.aux[3];
          if(this.k===119)return target===this.dv[0]?this.dv[1]:q;
          if(this.k>=120&&this.k<=122)return target===this.dv[0]?this.dv[1]:this.A.at(-1);
          if(this.k>=123&&this.k<=124)return this.carry;
          return q;
        }),S=this.A.slice(0,w),a=S.slice(0,-1),D=this.zword.slice(0,w-1);
        const word=[...this.r.slice(0,base),...D];
        const seq=[
            ()=>this.rank(tape,tag),rv=>this.barrel(tape,S,tag,true,rv),rv=>this.inc(tape,this.r,[],!rv),
            rv=>this.parkTail(tape,D,tag,rv),()=>this.cnotList(tape,[],D),rv=>tape.add(a,D,[],this.carry,rv),
            rv=>this.alignedMix(tape,a,D,tag,rv),rv=>this.barrel(tape,this.r,tag,false,rv)
        ];
        const f1z=this.u5PhaseHost!==target&&target===this.dv[0]&&(this.measureTarget===target||!this.probeBack);this.f1Clean=f1z;
        stepList(seq,false,fn=>fn(false));this.f1Clean=false;
        phaseDeposit(this,tape,target,(target)=>{this.toggle(tape,this.ctrl,[],target);tape.out(NONE,NONE,S.at(-1));this.constBelow(tape,word,this.centeredFree?this.p-(1n<<BigInt(this.k)):this.p,[...this.ctrl,S.at(-1)],[target]);tape.out(NONE,NONE,S.at(-1));});
        this.f1Clean=f1z&&this.measureTarget===target;stepList(seq,true,fn=>fn(true));this.f1Clean=false;
    }
    signProbe(tape,target,back){this.probeBack=back;this.alignedSign(tape,target);}
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
        if(this.u38Implicit){
            const layer=Object.create(this);layer.digit=layer.digitTopOne;
            const tail=rv=>stepList(split(base,this.r.length),rv,i=>{
                const mark=()=>this.indicator(tape,i-base,'gt',ctrl,t),z=[...d,this.r[i]],orig=z.slice(1).concat(z[0]);
                const seq=[mark,rr=>layer.digit(tape,z,a,[t],!rr),rr=>this.permute(tape,z,orig,[t],rr),mark];stepList(seq,rv,fn=>fn(rv));
            });
            stepList([rv=>layer.mixed(tape,this.r.slice(0,base),a,d,[this.take],rv),tail],back,fn=>fn(back));return;
        }
        const tail=rv=>stepList(split(base,this.r.length),rv,i=>{
            const mark=()=>this.indicator(tape,i-base,"gt",ctrl,t),z=[...d,this.r[i]],orig=z.slice(1).concat(z[0]);
            const seq=[mark,rr=>this.digit(tape,z,a,[t],!rr),rr=>this.permute(tape,z,orig,[t],rr),mark];
            stepList(seq,rv,fn=>fn(rv));
        });
        const seq=[rv=>this.mixedHeld(tape,this.r.slice(0,base),a,d,ctrl,rv),tail];
        stepList(seq,back,fn=>fn(back));
    }
    affine(tape,back){
        if(this.u3Affine){this.u3AffineBody(tape,back);return;}
        const a=this.A.slice(0,this.half),r=this.r,v=this.v,D=this.zword.slice(0,this.half),d=D.slice(0,this.h);
        const base=this.half+1,word=[...r.slice(0,base),...D],tail=r.slice(base),g=this.ctrl;
        const canon=rv=>this.digit(tape,[...d,this.dv[0]],v,[],rv);
        const seq=[
            rv=>this.normalizeA(tape,a,rv),canon,
            rv=>this.guardedBarrel(tape,D,true,rv),rv=>this.parkAffine(tape,D,rv),
            rv=>this.affineProduct(tape,a,D,rv),rv=>this.guardedBarrel(tape,r,false,rv),
            rv=>this.reflect(tape,word,g,rv),rv=>this.inc(tape,word,g,!rv),
            rv=>this.guardedPermutation(tape,[...tail,...D],[...D,...tail],[],rv),
            rv=>this.mixedHeld(tape,r,v,d,g,!rv),()=>this.cnotList(tape,g,d),
            rv=>tape.add(v,d,g,this.carry,rv),rv=>this.inc(tape,r,g,rv),
            rv=>canon(!rv),rv=>this.normalizeA(tape,a,!rv)
        ];
        stepList(seq,back,fn=>fn(back));
    }
}


function phaseDeposit(o,tape,wire,write){
 if(o.u5PhaseHost===wire){
   const dirty=o.zword.at(-1);write(dirty);tape.z(dirty);write(dirty);tape.z(dirty);
   return;
 }
 write(wire);if(o.measureTarget===wire){tape.z(wire);write(wire);}
}
function retirePredicate(o,tape,wire,emit){const mask=tape.hmr(wire);tape.cond(mask,()=>{o.measureTarget=wire;o.u5CleanPhase=wire;emit();o.u5CleanPhase=null;o.measureTarget=null;});}
class EarlyUnit extends UnitPreparation {
    emit(tape,back){
        const QH=process.env.Q648_UNITQ?+process.env.Q648_UNITQ:this.pick;if(QH===undefined||QH===this["qu"+"al"])throw Error("q648 unit host");
        const r=this.r,v=this.v,a=this.a,c=this.fullV,g=[this.g],sel=[this.g,this.shape],active=[this.g,QH];
        const shape=()=>{const hi=this.bank.slice(this.k+1),pos=[this.g,this.bank[this.k]];
            this.toggle(tape,pos,hi,this.shape);this.toggle(tape,pos,[...hi,...r.slice(this.m/2)],this.shape);};
        const qual=()=>this.toggle(tape,sel,[a.at(-1)],QH);
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
    // r35: fused digit with one dirty loan instead of the clean pick ancilla (same map as digit()).
    digitDirty(tape,z,v,controls,back){
        if(!controls.length){MixedArithmetic.prototype.digit.call(this,tape,z,v,controls,back);return;}
        if(z.length!==v.length+1)throw Error("dirty digit width");
        const multi=controls.length>1,e=multi?this.carry:controls[0];
        if(multi)this.toggle(tape,controls,[],e);
        const loan=tape.loan([...z,...v,e],1)[0];
        stepList(dirtyDigit(v,z.slice(0,-1),z.at(-1),e,loan),back,op=>tape.out(op.length===3?op[0]:NONE,op.length>=2?op[op.length-2]:NONE,op.at(-1)));
        if(multi)this.toggle(tape,controls,[],e);
    }
    // r36 U: emit a body with virtual control V equal to a stable predicate.
    uControl(tape,yes,no,run){
        const V=-1001,owner=this,proxy=Object.create(tape);
        const hidden=[...yes,...no,...this.tag,...this.tags,this.take];
        proxy.loan=(used,n)=>tape.loan([...used,...hidden],n);
        proxy.out=(a,b,t)=>{
            if(t===V)throw Error("virtual selector written");
            if(a!==V&&b!==V){tape.out(a,b,t);return;}
            const more=[a,b].filter(w=>w!==V&&w!==NONE);
            owner.toggle(tape,[...yes,...more],no,t);
        };
        run(proxy,V);
    }
    uEq(j){const yes=[],no=[];for(let i=0;i<this.tag.length;i++)((j>>i)&1?yes:no).push(this.tag[i]);return {yes,no};}
    uTrialRank(witness){
        const layer=this.hostRank(this.pick);layer.tag=layer.tag.slice();layer.tag[2]=witness?this.carry:this.dv[0];layer.uLift=witness;layer.uSpare=!witness;if(this.k<=95){layer.u39Trial=true;layer.u39Temp=witness?this.qtop:this.carry;layer.tag[1]=this.n.at(-1);if(!witness){layer.tag[0]=this.qtop;layer.u8Relay=true;}else{layer.tag[0]=this.qtop;layer.u11Witness=true;}}if(this.k>=96&&this.k<=111){layer.tag[1]=this.borrow;layer.wideBand=true;}if(this.k===112){layer.tag[1]=this.v[this.k];layer.u38NormLease=true;}
 if(this.k>=96&&this.k<=112){layer.u39Trial=true;layer.u39Temp=witness?this.qtop:this.carry;layer.tag[0]=this.n.at(-1);layer.u6TrialSlot=0;}
 return layer;
    }
    // r36 U2: expand a stable rank comparison as disjoint binary prefix cubes.
    uLess(limit){
        const n=this.tag.length,out=[];
        if(limit<=0)return out;if(limit>=2**n)return [{yes:[],no:[]}];
        for(let i=0;i<n;i++)if((limit>>i)&1){const yes=[],no=[this.tag[i]];
            for(let j=i+1;j<n;j++)((limit>>j)&1?yes:no).push(this.tag[j]);out.push({yes,no});}
        return out;
    }
    uSelect(tape,cubes,run){
        const V=-1002,owner=this,tp=Object.create(tape),hidden=[...this.tag,...this.tags,this.take];
        tp.loan=(used,n)=>tape.loan([...used,...hidden,...cubes.flatMap(p=>[...p.yes,...p.no])],n);
        tp.out=(a,b,t)=>{if(t===V)throw Error('write virtual comparison');
            if(a!==V&&b!==V){tape.out(a,b,t);return;}
            const more=[a,b].filter(w=>w!==V&&w!==NONE);
            for(const p of cubes)owner.toggle(tape,[...p.yes,...more],p.no,t);
        };run(tp,V);
    }
    // r35: view of this row whose fourth rank bit lives on host; with host===pick every digit goes dirty.
    hostRank(host){
        if(this.tag.length<3)return this;
        const layer=Object.create(this);layer.tag=this.tag.slice();layer.tag[this.tag.length===3?2:3]=host;layer.rankHost=host;
        if(host===this.pick)layer.digit=this.digitDirty;
        return layer;
    }
    // r35: dest = src + dest with a one-wire top and no carry ancilla (same map as tape.add with a clean carry wire).
    addTop(tape,src,dest,base,inverse){
        const k=src.length,a=src,b=dest.slice(0,k),hi=dest[k];
        if(dest.length!==k+1||k<2)throw Error("top add shape");
        const loans=tape.loan([...a,...dest,...base],4),list=[],cx=(x,y)=>list.push([[x],y]),cc=(x,y,z)=>list.push([[x,y],z]);
        list.push([[...base,a[k-1]],hi]);
        for(let i=1;i<k;i++)cx(a[i],b[i]);
        for(let i=k-2;i>=1;i--)cx(a[i],a[i+1]);
        for(let i=0;i<k-1;i++)cc(a[i],b[i],a[i+1]);
        list.push([[...base,a[k-1],b[k-1]],hi]);
        for(let i=k-1;i>=1;i--){list.push([[...base,a[i]],b[i]]);cc(a[i-1],b[i-1],a[i]);}
        for(let i=1;i<k-1;i++)cx(a[i],a[i+1]);
        list.push([[...base,a[0]],b[0]]);
        for(let i=1;i<k;i++)cx(a[i],b[i]);
        stepList(list,inverse,g=>tape.mc(g[0],g[1],loans));
    }
    // r35: controlled mixed product while pick holds a rank bit. g is the fixed enable of the fold tape, so take alone
    // drives the digits and the idle carry wire is the clean digit ancilla (carry is zero around every digit of mixed()).
    mixedHeld(tape,q,v,rem,controls,back){
        const live=controls.filter(c=>c!==tape.one);
        if(this.rankHost!==this.pick||live.length!==1){this.mixed(tape,q,v,rem,controls,back);return;}
        const layer=Object.create(this);layer.pick=this.carry;layer.digit=MixedArithmetic.prototype.digit;
        layer.mixed(tape,q,v,rem,live,back);
    }

    normalizeTopLease(tape,a,back){
        if(this.u12){this.u12Normalize(tape,a,back);return;}
        const H=Object.create(this),carry=this.carry;H.tag=this.tag.slice();H.tag[this.u6TopSlot??1]=carry;
        const normalize=rv=>stepList(split(0,H.tag.length).reverse(),rv,j=>{
            const k=1<<j,orig=a.slice(-k).concat(a.slice(0,-k)),bit=H.tag[j];
            const seq=[()=>H.toggle(tape,[H.take],a.slice(-k),bit),rr=>H.permute(tape,a,orig,[H.take,bit],rr)];stepList(seq,rv,fn=>fn(rv));
        });
        const lease=rv=>{const seq=[()=>tape.out(NONE,this.take,a.at(-1)),rr=>this.permute(tape,[a.at(-1),carry],[carry,a.at(-1)],[this.take],rr)];stepList(seq,rv,fn=>fn(rv));};
        stepList([normalize,lease],back,fn=>fn(back));
    }
    // Restoring digit with implicit v[-1]=1; omitted wire may carry arbitrary data.
    digitTopOne(tape,z,v,controls,back){
        const B=z.slice(0,-1),h=z.at(-1),n=B.length,a=v.slice(0,-1),top=B.at(-1);
        if(controls.length!==1)throw Error('implicit digit needs one enable');
        const e=controls[0],pool=tape.loan([...z,...a,e],6);
        const mc=(cs,t)=>tape.mc(cs,t,pool);
        const compare=()=>{
            if(n===1){mc([e,top],h);return;}
            const b=B.slice(0,-1),last=a.length-1,ops=[];
            for(const q of b)tape.out(NONE,NONE,q);
            mc([e,top],h);
            if(a.length>1)mc([e,top,a[last]],h);
            for(let i=1;i<a.length;i++)ops.push([NONE,a[i],b[i]]);
            for(let i=a.length-2;i>=1;i--)ops.push([NONE,a[i],a[i+1]]);
            for(let i=0;i<a.length-1;i++)ops.push([b[i],a[i],a[i+1]]);
            stepList(ops,false,g=>tape.out(...g));mc([e,top,a[last],b[last]],h);
            stepList(ops,true,g=>tape.out(...g));
            for(const q of b)tape.out(NONE,NONE,q);
        };
        const subtract=rv=>{
            const seq=[];
            if(n===2){seq.push(()=>{tape.out(NONE,NONE,B[0]);mc([e,h,a[0],B[0]],top);tape.out(NONE,NONE,B[0]);},()=>mc([e,h,a[0]],B[0]));}
            else if(n>2)seq.push(rr=>this.addTop(tape,a,B,[e,h],!rr));
            seq.push(()=>mc([e,h],top));stepList(seq,rv,fn=>fn(rv));
        };
        stepList([compare,subtract],back,fn=>fn(back));
    }
    // U3: v[k] is the known active leading coefficient bit. Lease it as rank[2].
    u3AffineBody(tape,back){
        const a=this.A.slice(0,this.half),r=this.r,v=this.v,D=this.zword.slice(0,this.half),d=D.slice(0,this.h);
        const base=this.half+1,word=[...r.slice(0,base),...D],tail=r.slice(base),g=this.ctrl;
        const host=v.at(-1),carry=this.carry;
        if(this.tag[this.u37Slot??2]!==host||this.rankHost!==this.pick)throw Error('U3 affine ports');
        const canon=rv=>this.digit(tape,[...d,this.dv[0]],v,[],rv);
        const leading=()=>tape.out(NONE,this.take,host);
        // Carry is zero at these boundaries. Swapping makes the coefficient's top bit zero;
        // X restores the known active one. During the body carry is arbitrary rank data.
        const withV=(rv,body)=>{
            this.permute(tape,[host,carry],[carry,host],[],false);tape.out(NONE,NONE,host);
            body(rv);
            tape.out(NONE,NONE,host);this.permute(tape,[host,carry],[carry,host],[],true);
        };
        const mixedV=rv=>withV(rv,rr=>{
            const layer=Object.create(this);layer.digit=this.digitDirty;
            layer.mixed(tape,r,v,d,[this.take],!rr);
        });
        const addV=rv=>withV(rv,rr=>tape.add(v,d,g,this.carry,rr));
        
        const norm=rv=>{
            if(!this.u38Implicit){this.normalizeA(tape,a,rv);return;}
            this.normalizeTopLease(tape,a,rv);
        };
        const seq=[canon,leading,norm,
            rv=>this.guardedBarrel(tape,D,true,rv),rv=>this.parkAffine(tape,D,rv),
            rv=>this.affineProduct(tape,a,D,rv),rv=>this.guardedBarrel(tape,r,false,rv),
            rv=>this.reflect(tape,word,g,rv),rv=>this.inc(tape,word,g,!rv),
            rv=>this.guardedPermutation(tape,[...tail,...D],[...D,...tail],[],rv),
            mixedV,()=>this.cnotList(tape,g,d),addV,rv=>this.inc(tape,r,g,rv),
            rv=>norm(!rv),leading,rv=>canon(!rv)];
        stepList(seq,back,fn=>fn(back));
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
        if(this.uLift){
            this.uControl(tape,[...ctrl,...extra],[],(tp,V)=>{
                const layer=Object.create(this);layer.carry=V;layer.uLift=false;
                // The base method's two selector toggles become no-ops; V is supplied by uControl.
                layer.toggle=function(t,yes,no,target){if(target===V)return;this.__proto__.toggle.call(this,t,yes,no,target);};
                layer.onesBlock(tp,R,D,n,extra,ctrl,back);
            });return;
        }
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
        if(this.uLift){
            const seq=[()=>this.cnotList(tape,ctrl,T)];
            for(let j=0;j<T.length-w;j++)if(j<=this.maxShift)seq.push(rv=>{
                const e=this.uEq(j);this.uControl(tape,[...ctrl,...e.yes],e.no,(tp,V)=>this.inc(tp,T.slice(w+j),[V],rv));
            });stepList(seq,back,fn=>fn(back));return;
        }
        const seq=[()=>this.cnotList(tape,ctrl,T)];
        for(let j=0;j<T.length-w;j++)if(j<=this.maxShift)seq.push(rv=>{
            this.indicator(tape,j,"eq",ctrl,this.carry);
            this.inc(tape,T.slice(w+j),[this.carry],rv);
            this.indicator(tape,j,"eq",ctrl,this.carry);
        });
        stepList(seq,back,fn=>fn(back));
    }
    oddProduct(tape,T,D,ctrl,back){
        if(this.uLift){
            stepList(split(0,T.length-1).reverse(),back,i=>{
                this.uControl(tape,[...ctrl,T[i]],[],(tp,V)=>{
                    const src=D.slice(1,T.length-i),dst=T.slice(i+1);
                    if(this.rankHost===this.pick&&dst.length>src.length)this.addTop(tp,src,dst,[V],back);
                    else tp.add(src,dst,[V],this.pick,back);
                });
            });return;
        }
        stepList(split(0,T.length-1).reverse(),back,i=>{
            const on=[...ctrl,T[i]];
            this.toggle(tape,on,[],this.carry);
            const src=D.slice(1,T.length-i),dst=T.slice(i+1);
            if(this.rankHost===this.pick&&dst.length>src.length)this.addTop(tape,src,dst,[this.carry],back);else tape.add(src,dst,[this.carry],this.pick,back);
            this.toggle(tape,on,[],this.carry);
        });
    }
    oddQuotient(tape,B,back){
        if(this.uSpare){
            const layer=Object.create(this);layer.uSpare=false;layer.dv=[B.T.at(-1),this.dv[1]];
            layer.oddQuotient(tape,B,back);return;
        }
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
        const H=this.uTrialRank(witness);
        if(this.k===112&&process.env.R112P!=='0'){
          const temp=Object.create(this);temp.dv=[this.dv[0],this.carry];const cy=this.carry,tk=this.take;
          const dirC=()=>temp.direction(tape),flip=d=>()=>{if(d)tape.out(NONE,tk,cy);},park=()=>tape.out(NONE,cy,tk);
          const outer=[];
          if(process.env.R112P_DBG)outer.push(()=>{const B=tape.physical.batches,cv=x=>x>tape.one?x-1:x,bit=(q,l)=>(B[l>>5][cv(q)]>>>(l&31))&1;
            console.error('R112DBG',witness?'witness':'trial',back?'back':'fwd','take',bit(tk,0),'f1',bit(this.dv[0],0),'qtop',bit(this.qtop,0),'carry',bit(cy,0),'pick',bit(this.pick,0));});
          if(process.env.R112P_MODE==='carry'){const Hc=Object.create(H);Hc.dv=[this.dv[0],cy];const body=[rv=>this.packNumber(tape,rv),rv=>Hc.normalize(tape,rv)];
            for(const B of Bs)body.push(rv=>witness?Hc.oddWitness(tape,B,rv):Hc.oddQuotient(tape,B,rv));body.push(rv=>Hc.normalize(tape,!rv),rv=>this.packNumber(tape,!rv));
            stepList([dirC,...body,dirC],back,fn=>fn(back));return;}
          for(const d of [0,1]){
            const Hd=Object.create(H);
            Hd.roundedDivisor=function(tape,B,back){
              if(this.u39LowOne===undefined)throw Error('r112p: expected u39 divisor');
              const seq=[rv=>this.inc(tape,B.H,[],!rv),...(d?[rv=>this.inc(tape,B.H.slice(1),[],rv)]:[])];
              stepList(seq,back,fn=>fn(back));
            };
            const body=[rv=>this.packNumber(tape,rv),rv=>Hd.normalize(tape,rv)];
            for(const B of Bs)body.push(rv=>witness?Hd.oddWitness(tape,B,rv):Hd.oddQuotient(tape,B,rv));
            body.push(rv=>Hd.normalize(tape,!rv),rv=>this.packNumber(tape,!rv));
            // parking marker M (carry itself is touched ungated by the body on parked lanes, so it cannot hold the mark):
            //  forward trial: f1 (clean helper; F is not computed yet), witness: qtop (coef^-1 ran before the witness, so q holds the corrected
            //  quotient, whose top bit is clean on taken lanes; qtop is a clean helper on untaken lanes). M = [direction != d] on taken lanes, 0 elsewhere.
            const M=witness?this.qtop:this.dv[0],mk=()=>tape.out(NONE,cy,M),pk=()=>tape.out(NONE,M,tk);
            outer.push(dirC,flip(d),mk,flip(d),dirC,pk,...body,pk,dirC,flip(d),mk,flip(d),dirC);
          }
          stepList(outer,back,fn=>fn(back));return;
        }
        const seq=[()=>this.direction(tape),rv=>this.packNumber(tape,rv),rv=>H.normalize(tape,rv)];
        for(const B of Bs)seq.push(rv=>witness?H.oddWitness(tape,B,rv):H.oddQuotient(tape,B,rv));
        seq.push(rv=>H.normalize(tape,!rv),rv=>this.packNumber(tape,!rv),()=>this.direction(tape));
        stepList(seq,back,fn=>fn(back));
    }
    core(tape,back){
        if(!this.layouts()){super.core(tape,back);return;}
        const v=this.v,q=this.q,g=this.ctrl,flag=this.dv[0],coef=rv=>this.mixed(tape,q,v,this.u,g,rv);
        const seq=[rv=>this.trial(tape,false,rv),coef,rv=>{const probe=()=>this.signProbe(tape,flag,rv);if(rv)retirePredicate(this,tape,flag,probe);else probe();},
            rv=>tape.add(v,this.A,[...g,flag],this.carry,!rv),rv=>{if(tape.hist&&!rv)return;coef(!rv);},
            rv=>{const probe=()=>this.trial(tape,true,rv);
                if(!tape.hist){if(!rv)retirePredicate(this,tape,flag,probe);else probe();}
                else if(!rv){if(tape.hist.has(this.k))throw Error("history collision");tape.hist.set(this.k,tape.hmr(flag));}
                else{probe();if(!tape.hist.has(this.k))throw Error("missing history");const ms=tape.hist.get(this.k);tape.cond(ms,()=>tape.z(flag));tape.hist.delete(this.k);}
            },rv=>{if(tape.hist&&!rv)return;coef(rv);},rv=>this.affine(tape,rv),
            rv=>this.permute(tape,[...this.bank,...this.u,...q.slice(-2)],[...this.A.slice(0,this.half),...v,...this.A.slice(this.half)],g,rv)];
        stepList(seq,back,fn=>fn(back));
    }
}


function dirtyDigit(A,B,h,e,loan){
    const n=A.length,k=n-1,g=[];
    const x=q=>g.push([q]),cx=(a,b)=>g.push([a,b]),ccx=(a,b,c)=>g.push([a,b,c]);
    function togglePredicate(a,b,c,target){
        ccx(a,b,loan);ccx(loan,c,target);ccx(a,b,loan);ccx(loan,c,target);
    }
    for(const b of B)x(b);
    if(n===1){
        togglePredicate(e,A[0],B[0],h);x(B[0]);cx(e,h);
        togglePredicate(e,h,A[0],B[0]);return g;
    }
    for(let i=1;i<n;i++)cx(A[i],B[i]);
    ccx(e,A[k],h);
    for(let i=n-2;i>=1;i--)cx(A[i],A[i+1]);
    for(let i=0;i<n-1;i++)ccx(B[i],A[i],A[i+1]);
    togglePredicate(e,A[k],B[k],h);cx(e,h);
    for(let i=0;i<n;i++){ccx(loan,A[i],B[i]);if(i<k)cx(loan,B[i]);}
    ccx(e,h,loan);
    ccx(loan,A[k],B[k]);
    for(let i=n-2;i>=0;i--){
        ccx(B[i],A[i],A[i+1]);ccx(loan,A[i],B[i]);
    }
    ccx(e,h,loan);
    for(let i=0;i<k;i++)cx(loan,B[i]);
    for(let i=1;i<n-1;i++)cx(A[i],A[i+1]);
    for(let i=1;i<n;i++)cx(A[i],B[i]);
    for(const b of B)x(b);
    return g;
}

class UnguardedGeneral extends OddEstimateGeneral {
    u648Normalize(tape,a,back){
      const H=Object.create(this),carry=this.carry,top=a.at(-1),low=a[0],extra=a[1],a2=a[2],rtop=this.r.at(-1),take=this.take,T=this.tag;
      if(T[6]!==a2||T[0]!==low||T[1]!==top||T.length!==7)throw Error('u648 ports '+this.k);
      H.tag=T.slice();H.tag[1]=carry;H.tag[6]=rtop;
      const norm=rv=>stepList(split(1,H.tag.length).reverse(),rv,j=>{
        const k=1<<j,orig=a.slice(-k).concat(a.slice(0,-k)),bit=H.tag[j];
        const seq=[()=>H.toggle(tape,[H.take],a.slice(-k),bit),rr=>H.permute(tape,a,orig,[H.take,bit],rr)];stepList(seq,rv,fn=>fn(rv));
      });
      const last=rv=>{
        const lower=a.slice(0,-1),orig=lower.slice(-1).concat(lower.slice(0,-1));
        const seq=[rr=>this.permute(tape,[top,carry],[carry,top],[take],rr),()=>tape.out(NONE,take,carry),
          rr=>this.permute(tape,lower,orig,[take,carry],rr),()=>this.toggle(tape,[take,carry],[],low),
          rr=>this.permute(tape,[carry,low],[low,carry],[take],rr)];stepList(seq,rv,fn=>fn(rv));
      };
      const recode=rv=>{
        const map=new Map();
        for(let x=0;x<2;x++)for(let y=0;y<2;y++)map.set(x+16*y,16+2*x+4*y);
        for(let y=0;y<2;y++)map.set(2+16*y,16+8+2*y);
        for(let c=2;c<8;c++)map.set(2*c,2*c);
        const incoming=new Set(map.values());
        for(const start of [...map.keys()])if(!incoming.has(start)){let at=start;while(map.has(at))at=map.get(at);map.set(at,start);}
        const seen=new Set(),swaps=[];
        for(const start of map.keys())if(!seen.has(start)){const cycle=[];let at=start;while(!seen.has(at)){seen.add(at);cycle.push(at);at=map.get(at);}
          for(let i=1;i<cycle.length;i++)swaps.push([cycle[0],cycle[i]]);}
        const ports=[carry,low,top,T[2],extra],no=[T[3],T[4],T[5],rtop];
        stepList(swaps,rv,([x,y])=>this.u6Transpose(tape,ports,x,y,[take],no,false));
      };
      const pick=T[3],rest=[T[4],T[5],rtop];
      const c2=rv=>{
        const before=()=>this.toggle(tape,[take,top],[low,T[2],pick,...rest,extra],carry);
        const after=()=>this.toggle(tape,[take,extra,pick],[low,top,T[2],...rest],carry);
        const flip=()=>{tape.out(NONE,carry,extra);tape.out(NONE,carry,pick);tape.out(NONE,carry,top);};
        stepList([before,flip,after],rv,fn=>fn());
      };
      const mv=()=>{this.toggle(tape,[take,rtop],[extra],a2);this.toggle(tape,[take,a2],[extra],rtop);this.toggle(tape,[take,rtop],[extra],a2);};
      // code lanes (extra=1, counts 0..2): rank4 = 0, so the real B2 moves from A2 to A128 (weight 16 instead of 64 in the physical rank).
      const b2=rv=>this.permute(tape,[a2,T[4]],[T[4],a2],[take,extra],rv);
      stepList([norm,last,recode,c2,b2,()=>mv()],back,fn=>fn(back));
    }
    u12Normalize(tape,a,back){
      if(this.u648){this.u648Normalize(tape,a,back);return;}
      const H=Object.create(this),carry=this.carry,top=a.at(-1),low=a[0],extra=a[1];
      H.tag=this.tag.slice();H.tag[1]=carry;
      const norm=rv=>stepList(split(1,H.tag.length).reverse(),rv,j=>{
        const k=1<<j,orig=a.slice(-k).concat(a.slice(0,-k)),bit=H.tag[j];
        const seq=[()=>H.toggle(tape,[H.take],a.slice(-k),bit),rr=>H.permute(tape,a,orig,[H.take,bit],rr)];stepList(seq,rv,fn=>fn(rv));
      });
      const last=rv=>{
        const lower=a.slice(0,-1),orig=lower.slice(-1).concat(lower.slice(0,-1));
        const seq=[rr=>this.permute(tape,[top,carry],[carry,top],[this.take],rr),()=>tape.out(NONE,this.take,carry),
          rr=>this.permute(tape,lower,orig,[this.take,carry],rr),()=>this.toggle(tape,[this.take,carry],[],low),
          rr=>this.permute(tape,[carry,low],[low,carry],[this.take],rr)];stepList(seq,rv,fn=>fn(rv));
      };
      const recode=rv=>{
        // Partial injection on [temporary,rank0,rank1,rank2,extra].
        // c0 -> extra1 + original low2; c1 -> extra1 + 4 + original low1.
        const map=new Map();
        for(let x=0;x<2;x++)for(let y=0;y<2;y++)map.set(x+16*y,16+2*x+4*y);
        for(let y=0;y<2;y++)map.set(2+16*y,16+8+2*y);
        for(let c=2;c<8;c++)map.set(2*c,2*c);
        // Close each open path to obtain a permutation, then decompose cycles.
        const incoming=new Set(map.values());
        for(const start of [...map.keys()])if(!incoming.has(start)){
          let at=start;while(map.has(at))at=map.get(at);map.set(at,start);
        }
        const seen=new Set(),swaps=[];
        for(const start of map.keys())if(!seen.has(start)){
          const cycle=[];let at=start;while(!seen.has(at)){seen.add(at);cycle.push(at);at=map.get(at);}
          for(let i=1;i<cycle.length;i++)swaps.push([cycle[0],cycle[i]]);
        }
        const ports=[carry,low,top,this.tag[2],extra];
        stepList(swaps,rv,([a,b])=>this.u6Transpose(tape,ports,a,b,[this.take],this.tag.slice(3),false));
      };
      stepList([norm,last,recode],back,fn=>fn(back));
    }
    indicator(tape,j,kind,controls,target){
      if(!this.u12){super.indicator(tape,j,kind,controls,target);return;}
      if(this.u648){
        super.indicator(tape,j,kind,controls,target);
        const pred=c=>kind==='eq'?c===j:kind==='gt'?c>j:c<=j,T=this.tag,extra=this.A[1];
        // [true rank, fixed tag bits, free tag bits]; on code lanes tag bit 4 (A128) is the real B2, bits 5 and 6 are zero.
        for(const [rank,fixed,free] of [[0,{2:0,3:0},[0,1,4]],[1,{0:null,1:0,2:1,3:0},[0,4]],[2,{0:0,1:0,2:0,3:1},[4]]]){
          for(let y=0;y<(1<<free.length);y++){
            const bit=i=>{const f=free.indexOf(i);if(f>=0)return (y>>f)&1;if(i in fixed&&fixed[i]!==null)return fixed[i];return 0;};
            let phys=0;for(let i=0;i<7;i++)phys+=bit(i)<<i;
            if(pred(phys)===pred(rank))continue;
            const yes=[...controls,extra],no=[];for(let i=0;i<7;i++)(bit(i)?yes:no).push(T[i]);
            this.toggle(tape,yes,no,target);
          }
        }
        return;
      }
      super.indicator(tape,j,kind,controls,target);
      const pred=c=>kind==='eq'?c===j:kind==='gt'?c>j:c<=j;
      for(let code=0;code<6;code++){
        const rank=code<4?0:1;if(pred(code)===pred(rank))continue;
        const yes=[...controls,this.A[1]],no=[];
        this.tag.forEach((q,i)=>((code>>i)&1?yes:no).push(q));this.toggle(tape,yes,no,target);
      }
    }
    guardedBarrel(tape,word,left,back){
      if(!this.u12){super.guardedBarrel(tape,word,left,back);return;}
      if(this.u648){
        const T=this.tag,extra=this.A[1],c=this.ctrl,cy=this.carry;
        stepList(split(0,T.length),back,j=>{
          const k=(1<<j)%word.length;if(!k)return;
          const origin=left?word.slice(-k).concat(word.slice(0,-k)):word.slice(k).concat(word.slice(0,k));
          const mark=()=>{
            if(j===5||j===6)this.toggle(tape,[...c,T[j]],[],cy);else this.toggle(tape,[...c,T[j]],[extra],cy);
            if(j===0)this.toggle(tape,[...c,extra,T[2]],[],cy);
            if(j===1)this.toggle(tape,[...c,extra,T[3]],[],cy);
          };
          mark();this.permute(tape,word,origin,[cy],back);mark();
        });
        return;
      }
      const extra=this.A[1];
      stepList(split(0,this.tag.length),back,j=>{
        const k=(1<<j)%word.length;if(!k)return;
        const origin=left?word.slice(-k).concat(word.slice(0,-k)):word.slice(k).concat(word.slice(0,k));
        const mark=()=>{
          if(j<3)this.toggle(tape,[...this.ctrl,this.tag[j]],[extra],this.carry);
          else this.toggle(tape,[...this.ctrl,this.tag[j]],[],this.carry);
          if(j===0)this.toggle(tape,[...this.ctrl,extra,this.tag[2]],[],this.carry);
        };
        mark();this.permute(tape,word,origin,[this.carry],back);mark();
      });
    }
    digitTopOne(tape,z,v,controls,back){
      if(!this.u12){super.digitTopOne(tape,z,v,controls,back);return;}
      const tp=this.u12VirtualTape(tape);super.digitTopOne(tp,z,v,controls,back);tp.u12Check();
    }
    u12VirtualTape(tape){
      const H=this,tag=this.tag,extra=this.A[1],host=this.A.slice(0,this.u648?3:2),tp=Object.create(tape);
      tp.ids=tape.ids.filter(q=>!tag.includes(q)&&q!==extra);
      const cube=(yes=[],no=[])=>({yes:[...new Set(yes)].sort((a,b)=>a-b),no:[...new Set(no)].sort((a,b)=>a-b)});
      const key=c=>c.yes.join(',')+'!'+c.no.join(',');
      const norm=ts=>{const m=new Map();for(const c of ts){if(c.yes.some(q=>c.no.includes(q)))continue;const k=key(c);if(m.has(k))m.delete(k);else m.set(k,c);}return [...m.values()];};
      const base=[[cube([extra,tag[0]],[tag[2]])],[cube([extra,tag[1]],[tag[2]]),cube([extra,tag[2],tag[0]])]];if(H.u648)base.push([cube([extra,tag[4]])]);
      let expressions=base.map(x=>x.slice()),dependencies=new Set();
      const deps=()=>{dependencies=new Set(expressions.flatMap(e=>e.flatMap(c=>c.yes.concat(c.no))));};deps();
      const expr=q=>q===NONE?[cube()]:host.includes(q)?expressions[host.indexOf(q)]:[cube([q])];
      const mul=(a,b)=>norm(a.flatMap(x=>b.map(y=>cube(x.yes.concat(y.yes),x.no.concat(y.no)))));
      tp.out=(a,b,t)=>{
        if(!host.includes(a)&&!host.includes(b)&&!host.includes(t)&&!dependencies.has(t)){tape.out(a,b,t);return;}
        const terms=mul(expr(a),expr(b));
        if(host.includes(t)){const i=host.indexOf(t);expressions[i]=norm(expressions[i].concat(terms));deps();return;}
        if(terms.some(c=>c.yes.includes(t)||c.no.includes(t)))throw Error('U12 implicit self target '+[H.k,a,b,t]);
        expressions=expressions.map(e=>norm(e.concat(mul(e.filter(c=>c.yes.includes(t)||c.no.includes(t)).map(c=>cube(c.yes.filter(q=>q!==t),c.no.filter(q=>q!==t))),terms))));deps();
        if(expressions.some(e=>e.length>10000))throw Error('U12 symbolic cap');
        for(const c of terms)H.toggle(tape,c.yes,c.no,t);
      };
      tp.u12Check=()=>{for(let i=0;i<base.length;i++)if(norm(expressions[i].concat(base[i])).length)throw Error('U12 virtual not restored '+H.k);};return tp;
    }

    u11Normalize(tape,back){
      const H=Object.create(this),n=this.n,top=n.at(-1),low=n.slice(0,-1),q=this.tag[0];
      H.tag=this.tag.slice();H.tag[1]=q;
      const large=rv=>stepList(split(1,H.tag.length).reverse(),rv,j=>{
        const d=1<<j,t=H.tag[j],orig=n.slice(-d).concat(n.slice(0,-d));
        const hk=this.__hk,seq=[...(hk?[rr=>hk(tape,'pre',j,t,rr)]:[]),()=>H.toggle(tape,[this.take],n.slice(-d),t),rr=>H.permute(tape,n,orig,[this.take,t],rr),...(hk?[rr=>hk(tape,'post',j,t,rr)]:[])];
        stepList(seq,rv,fn=>fn(rv));
      });
      const seq=[large,()=>tape.out(NONE,this.take,top),
        rv=>this.permute(tape,[top,q],[q,top],[this.take],rv),
        rv=>this.permute(tape,low,low.slice(-1).concat(low.slice(0,-1)),[this.take,q],rv),...(this.__hk?[rv=>this.__hk(tape,'rest',0,q,rv)]:[]),
        ()=>this.toggle(tape,[this.take,q],[],low[0])];
      stepList(seq,back,fn=>fn(back));
    }
    u11Band(tape,B,back){
      const host=B.T.at(-1),H=Object.create(this);H.tag=this.tag.slice();H.tag[0]=host;H.u11Witness=false;
      const swap=rv=>this.permute(tape,[this.tag[0],host],[host,this.tag[0]],[],rv);
      swap(false);
      H.u39Divisor(tape,B,(J,rv)=>J.u11Predicate(tape,B),back);
      swap(true);
    }
    u11Predicate(tape,B){
      const top=-1101,T=B.T.slice(0,-1).concat(top),flag=this.dv[0],ctrl=[this.g,this.take,-19],owner=this;
      const phase=this.measureTarget===flag,target=phase?this.zword.at(-1):flag;
      const hidden=[...this.tag,...this.tags,flag,target,this.take,this.g];
      const tp=Object.create(tape);tp.loan=(used,n)=>tape.loan([...used,...hidden],n);
      const flips=new Set(),tags=new Set(this.tag),guards=[];
      if(this.inUpperHalf)guards.push({yes:[this.g,this.take],no:[]});
      guards.push({yes:[this.g,this.take],no:this.tag.slice(3)});
      if(this.packedShort)guards.push({yes:[this.g,this.take,this.tag[3]],no:this.tag.filter((q,i)=>i!==3)});
      const accumulate=(a,b)=>{
        for(const guard of guards){
          const yes=[a,b].filter(q=>q!==NONE),no=[];
          for(const q of guard.yes)(flips.has(q)?no:yes).push(q);
          for(const q of guard.no)(flips.has(q)?yes:no).push(q);
          if(yes.some(q=>no.includes(q)))continue;
          owner.toggle(tape,[...new Set(yes)],[...new Set(no)],target);
        }
      };
      let deposit=true;
      tp.out=(a,b,t)=>{
        if(a===top||b===top)throw Error('U11 virtual high read');
        if(t!==top){
          if(tags.has(t)){
            if(a!==NONE||b!==NONE)throw Error('U11 non-X rank mutation');
            if(flips.has(t))flips.delete(t);else flips.add(t);
          }
          tape.out(a,b,t);return;
        }
        if(deposit)accumulate(a,b);
      };
      const pre=[rv=>this.inc(tp,T,[],rv),rv=>this.oddProduct(tp,T,B.D,[],rv),rv=>this.lowReflect(tp,T,B.w,[],rv)];
      this.toggle(tape,ctrl,[],target);
      stepList(pre,false,fn=>fn(false));
      if(phase)tape.z(target);
      deposit=phase;
      stepList(pre,true,fn=>fn(true));
      if(flips.size)throw Error('U11 rank frame not restored');
      if(phase){this.toggle(tape,ctrl,[],target);tape.z(target);tape.z(flag);}
    }

    u9Category(rank){
      if(this.u648C){const t=this.u40Tag,f=t[t.length-1],R=this.u648C.Pr.map(i=>t[i]),yes=[f],no=[];R.forEach((q,b)=>((rank>>b)&1?yes:no).push(q));return {yes,no};}
      if(this.u9H){const t=this.u40Tag,h=this.u9H,P=[];for(let x=h;x>=2;x--)P.push(t[x]);const yes=[t[t.length-1],...P.slice(0,rank)],no=rank<h-1?[P[rank]]:[];return {yes,no};}
      const t=this.u40Tag,n=t.length-1,yes=[t[n]],no=[];
      if(rank===0)no.push(t[3]);
      if(rank===1){yes.push(t[3]);no.push(t[2]);}
      if(rank===2)yes.push(t[3],t[2]);
      return {yes,no};
    }
    u648VkOk(){if(process.env.Q648_P4R1==='0'||!this.u38ProbeLease||this.tags[1]!==this.v[this.k])return false;const free=this.r.length-this.ab,bits=Math.floor(Math.log2(free))+1;return free!==(1<<bits)-1;}
    u648FourSign(tape,target){
      const FREE=+(process.env.Q648_P4FREE||647);
      const base=this.ab,w=this.half+1,free=this.r.length-base,bits=Math.floor(Math.log2(free))+1,h=bits>=4?4:3;
      const ext=(bits<6&&this.u38ProbeLease&&(this.tags[1]===this.v[this.k]||this.tags[0]===this.v[this.k])&&process.env.Q648_P4EXT!=='0')?[this.v[this.k]]:[];
      if(bits+ext.length<6&&this.u5PhaseHost===target&&this.tags[0]===target&&process.env.Q648_P4F1!=='0')ext.push(target);
      if(2**(h+1)-2>2**(bits+ext.length)||bits+ext.length<h||free>=2**bits)throw Error('U648 capacity '+[this.k,free,h]);
      const S=this.A.slice(0,w),a=S.slice(0,-1),D=this.zword.slice(0,w-1),word=[...this.r.slice(0,base),...D];
      const rankTag=this.probeTag(base,this.tags.slice(0,bits),target).map((q,i)=>i===0?S[1]:i===1?S[0]:i===2?this.carry:(i===3&&h===4)?S[3]:(FREE===647&&q===this.aux[3]&&i===bits-1)?this.A.at(-1):q).concat(ext),tag=rankTag.concat(S[2]),L=rankTag.length;
      if(new Set(tag).size!==tag.length)throw Error('U648 tag collision '+this.k);if(tag.includes(FREE))throw Error('U648 freed helper in tag '+[this.k,tag]);
      if(process.env.Q648_P4LOG&&!globalThis.__P4L?.has(this.k)){(globalThis.__P4L=globalThis.__P4L||new Set()).add(this.k);console.error('P4',this.k,free,JSON.stringify(tag));}
      const CMPX=process.env.Q648_P4C==='0'||L<6?null:{Pc:[1,0,4,3],Pr:L>=7?[5,6]:[5,2]};
      const H=Object.create(this);Object.assign(H,{u40Low:S[0],u40Tag:tag,u6Code:[],u6S:S,u6Tapes:[],u9Three:true,u9H:h,u648C:CMPX});
      const high=this.r.slice(base),top=2**L,off=h===4?[0,16,24,28]:[0,8,12];
      const rotate=rv=>{
        const partial=[...Array(h).fill(this.pick),...rankTag.slice(h)];
        const hiR=()=>this.u10RankHigh(tape,partial,h);
        hiR();stepList(split(0,bits),rv,j=>{const q=j<h?this.pick:rankTag[j];if(j<h)this.u6RankBit(tape,j,q);const k=(1<<j)%S.length,src=S.slice(-k).concat(S.slice(0,-k));this.permute(tape,S,src,[q],rv);if(j<h)this.u6RankBit(tape,j,q);});hiR();
      };
      const swaps=[];
      for(let rank=0;rank<h;rank++){
        const inputs=[],outputs=[];
        for(let low=0;low<2**(h-rank);low++){
          const c=low<<rank;
          inputs.push(rank^((c>>1&1)<<0)^((c&1)<<1)^((c>>2&1)*top)^((c>>3&1)<<3));
          outputs.push(CMPX?top+CMPX.Pc.reduce((v,p,j)=>v|((c>>j&1)<<p),0)+((rank&1)<<CMPX.Pr[0])+((rank>>1&1)<<CMPX.Pr[1]):top+off[rank]+low);
        }
        const positions=inputs.slice(),seq=[];
        for(let i=0;i<inputs.length;i++)if(positions[i]!==outputs[i]){
          const from=positions[i],to=outputs[i];seq.push([from,to]);
          for(let j=0;j<positions.length;j++)positions[j]=positions[j]===from?to:positions[j]===to?from:positions[j];
        }
        const yes=rank?[high[rank-1]]:[],no=high.slice(rank);
        swaps.push(rv=>{const mark=()=>this.toggle(tape,yes,no,this.pick);mark();stepList(seq,rv,([from,to])=>this.u6Transpose(tape,tag,from,to,[this.pick],[],rv));mark();});
      }
      const recode=rv=>stepList(swaps,rv,fn=>fn(rv));
      const seq=[rotate,()=>this.rank(tape,rankTag),recode,
        rv=>this.inc(tape,this.r,[],!rv),rv=>H.parkTail(tape,D,tag,rv),()=>this.cnotList(tape,[],D),
        rv=>H.u6VirtualTape(tape).add(a,D,[],this.carry,rv),rv=>H.alignedMix(tape,a,D,tag,rv),rv=>H.barrel(tape,this.r,tag,false,rv)];
      stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);stepList(seq,true,fn=>fn(true));
      for(const tp of H.u6Tapes)tp.u6Check();
    }
    u9ThreeSign(tape,target){
      const base=this.ab,w=this.half+1,free=this.r.length-base,bits=Math.floor(Math.log2(free))+1;
      if(bits<4||free+12>=2**(bits+1))throw Error('U9 capacity '+this.k);
      const S=this.A.slice(0,w),a=S.slice(0,-1),D=this.zword.slice(0,w-1),word=[...this.r.slice(0,base),...D];
      const rankTag=this.probeTag(base,this.tags.slice(0,bits),target).map((q,i)=>i===0?S[1]:i===1?S[0]:i===2?this.carry:q),tag=rankTag.concat(S[2]);
      if(new Set(tag).size!==tag.length)throw Error('U9 tag collision');
      const H=Object.create(this);Object.assign(H,{u40Low:S[0],u40Tag:tag,u6Code:[],u6S:S,u6Tapes:[],u9Three:true});
      const high=this.r.slice(base),top=2**bits;
      const rotate=rv=>{
        const partial=[this.pick,this.pick,this.pick,...rankTag.slice(3)];
        const hi=()=>this.u10RankHigh(tape,partial,3);
        hi();stepList(split(0,bits),rv,j=>{const q=j<3?this.pick:rankTag[j];if(j<3)this.u6RankBit(tape,j,q);const k=(1<<j)%S.length,src=S.slice(-k).concat(S.slice(0,-k));this.permute(tape,S,src,[q],rv);if(j<3)this.u6RankBit(tape,j,q);});hi();
      };
      // For each rank0/1/2 support, synthesize a permutation of the code word.
      // Input low bits are xor'd into rankTag0/1 and the additional high code bit.
      const swaps=[];
      for(let rank=0;rank<3;rank++){
        const inputs=[],outputs=[];
        for(let low=0;low<2**(3-rank);low++){
          const coeff=low<<rank;
          inputs.push(rank^((coeff>>1&1)<<0)^((coeff&1)<<1)^((coeff>>2&1)*top));
          outputs.push(top+(rank===0?0:rank===1?8:12)+low);
        }
        const positions=inputs.slice(),seq=[];
        for(let i=0;i<inputs.length;i++)if(positions[i]!==outputs[i]){
          const from=positions[i],to=outputs[i];seq.push([from,to]);
          for(let j=0;j<positions.length;j++)positions[j]=positions[j]===from?to:positions[j]===to?from:positions[j];
        }
        const yes=rank?[high[rank-1]]:[],no=high.slice(rank);
        swaps.push(rv=>{const mark=()=>this.toggle(tape,yes,no,this.pick);mark();stepList(seq,rv,([from,to])=>this.u6Transpose(tape,tag,from,to,[this.pick],[],rv));mark();});
      }
      const recode=rv=>stepList(swaps,rv,fn=>fn(rv));
      const seq=[rotate,()=>this.rank(tape,rankTag),recode,
        rv=>this.inc(tape,this.r,[],!rv),rv=>H.parkTail(tape,D,tag,rv),()=>this.cnotList(tape,[],D),
        rv=>H.u6VirtualTape(tape).add(a,D,[],this.carry,rv),rv=>H.alignedMix(tape,a,D,tag,rv),rv=>H.barrel(tape,this.r,tag,false,rv)];
      stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);stepList(seq,true,fn=>fn(true));
      for(const tp of H.u6Tapes)tp.u6Check();
    }

    onesBlock(tape,R,D,n,extra,ctrl,back){
      if(!this.u8Ones){super.onesBlock(tape,R,D,n,extra,ctrl,back);return;}
      const t=this.carry,origin=[...R,this.dv[0]],active=[...ctrl,...extra];
      if(this.tag[0]!==this.dv[0])throw Error('U8 recurrence host');
      this.toggle(tape,active,[],t);
      let remain=R.slice(),spare=this.dv[0];const seq=[];
      for(let j=0;j<n;j++){
        const input=spare,z=[input,...remain],high=z.at(-1);
        seq.push(rv=>{
          const v=D.slice(1),zz=z.slice(1),loan=tape.loan([...zz,...v,t,input],1)[0];
          stepList(dirtyDigit(v,zz.slice(0,-1),high,t,loan),rv,op=>tape.out(op.length===3?op[0]:NONE,op.length>=2?op.at(-2):NONE,op.at(-1)));
        },()=>tape.out(NONE,t,high),rv=>this.permute(tape,[input,high],[high,input],[],rv));
        remain=z.slice(0,-1);spare=high;
      }
      seq.push(rv=>this.permute(tape,origin,[...remain,spare],[],rv));
      const shift=n%R.length,unrotate=R.slice(shift).concat(R.slice(0,shift));
      seq.push(rv=>{tape.out(NONE,NONE,t);this.permute(tape,R,unrotate,[t],rv);tape.out(NONE,NONE,t);});
      stepList(seq,back,fn=>fn(back));this.toggle(tape,active,[],t);
    }

    // Enumerate only the small threshold body. Pack/unpack and Q changes stay shared.
    u7Threshold(tape,target){
      for(let count=0;count<=this.maxShift;count++){
        const H=Object.create(this),sel=this.pick,n=this.n;
        H.tag=[];H.uDebt=false;H.digit=H.digitDirty;H.ctrl=[this.g,sel];
        if(process.env.U7_OFF!=='1'){
          const pred=(kind,j)=>kind==='eq'?count===j:kind==='gt'?count>j:count<=j;
          H.installZeros=function(tape,back){const Q=this.q;
            stepList(split(0,this.maxShift),back,j=>{if(pred('le',j))this.permute(tape,[this.n[j],Q[j+2]],[Q[j+2],this.n[j]],[],back);});
            tape.out(NONE,NONE,this.n.at(-1));};
          H.mixedHead=function(tape,D,C,back){const Q=this.q,stages=[rv=>this.mixed(tape,Q.slice(0,2),D,C,[],rv)];
            for(let i=2;i<Q.length;i++){if(!pred('gt',i-2))continue;const z=[...C,Q[i]],origins=[...z.slice(1),z[0]];
              stages.push(rv=>{const seq=[rr=>this.digit(tape,z,D,[this.g],!rr),rr=>this.permute(tape,z,origins,[],rr)];stepList(seq,rv,fn=>fn(rv));});}
            stepList(stages,back,fn=>fn(back));};
        }
        H.indicator=(tp,j,kind,controls,dest)=>{
          if(kind==='eq'?count===j:kind==='gt'?count>j:count<=j)H.toggle(tp,controls,[],dest);
        };
        const mark=()=>this.toggle(tape,[...this.ctrl,n[this.m-1-count]],n.slice(this.m-count),sel);
        const origins=count?n.slice(-count).concat(n.slice(0,-count)):n;
        mark();this.permute(tape,n,origins,[],false);
        H.threshold(tape,target);
        this.permute(tape,n,origins,[],true);mark();
      }
    }
    u7Debt(tape,back){
      const g=this.ctrl,Q=this.q,seq=[rv=>this.packNumber(tape,rv),
        rv=>this.inc(tape,Q,g,rv),()=>this.u7Threshold(tape,this.dv[0]),
        rv=>this.inc(tape,Q,g,rv),()=>this.u7Threshold(tape,this.dv[1]),
        rv=>this.inc(tape,Q,g,!rv),rv=>this.inc(tape,Q,g,!rv),
        rv=>this.packNumber(tape,!rv)];
      stepList(seq,back,fn=>fn(back));
    }

    u10Terms(tape,terms,t){
      const cost=(p,n)=>2*n+(p+n<3?1:4*(p+n)-8);
      const raw=terms.reduce((v,c)=>v+cost(c.yes.length,c.no.length),0);
      const common={yes:terms.length?terms[0].yes.filter(q=>terms.every(c=>c.yes.includes(q))):[],no:terms.length?terms[0].no.filter(q=>terms.every(c=>c.no.includes(q))):[]};
      const rest=terms.map(c=>({yes:c.yes.filter(q=>!common.yes.includes(q)),no:c.no.filter(q=>!common.no.includes(q))}));
      const fact=2*cost(common.yes.length,common.no.length)+2*rest.reduce((v,c)=>v+cost(c.yes.length+1,c.no.length),0);
      if(fact<raw){const used=[t,...terms.flatMap(c=>c.yes.concat(c.no))],d=tape.loan(used,1)[0];const mark=()=>this.toggle(tape,common.yes,common.no,d),body=()=>{for(const c of rest)this.toggle(tape,[d,...c.yes],c.no,t);};mark();body();mark();body();}
      else for(const c of terms)this.toggle(tape,c.yes,c.no,t);
    }
    u10RankHigh(tape,tag,first=2){
      const high=this.r.slice(this.ab),n=high.length,d=tape.loan([...high,...tag],n+1),coeff=Array(n+1).fill(0);
      for(let i=0;i<n;i++){coeff[i]^=i+1;coeff[i+1]^=i+1;}
      for(const q of high)tape.out(NONE,NONE,q);
      for(let e=0;e<2;e++){tape.out(NONE,NONE,d[n]);for(let i=n-1;i>=0;i--)tape.out(high[i],d[i+1],d[i]);for(let i=0;i<=n;i++)for(let j=first;j<tag.length;j++)if(coeff[i]>>j&1)tape.out(NONE,d[i],tag[j]);for(let i=0;i<n;i++)tape.out(high[i],d[i+1],d[i]);}
      for(const q of high)tape.out(NONE,NONE,q);
    }
    u10ControlledPermutation(tape,word,src,controls,back){
      // Each permutation is two involutions. Dirty control echo is exact for each.
      const pos=new Map(word.map((q,i)=>[q,i])),p=src.map(q=>pos.get(q)),seen=new Set(),layers=[[],[]];
      for(let i=0;i<p.length;i++)if(!seen.has(i)){const cyc=[];let j=i;while(!seen.has(j)){seen.add(j);cyc.push(word[j]);j=p[j];}const n=cyc.length;
        for(let j=0;j<n;j++){const a=(n-j)%n;if(j<a)layers[0].push([cyc[j],cyc[a]]);const b=(n-1-j)%n;if(j<b)layers[1].push([cyc[j],cyc[b]]);}}
      const d=tape.loan([...word,...controls],1)[0],mark=()=>this.toggle(tape,controls,[],d);
      stepList(layers,back,pairs=>{const body=()=>{for(const [a,b]of pairs)this.gatedSwap(tape,a,b,[d],[]);};body();mark();body();mark();});
    }
    u6RankBit(tape,j,target){
      const high=this.r.slice(this.ab),n=high.length,d=tape.loan([...high,target],n+1),coeff=Array(n+1).fill(0);
      for(let i=0;i<n;i++){coeff[i]^=(i+1)>>j&1;coeff[i+1]^=(i+1)>>j&1;}
      for(const q of high)tape.out(NONE,NONE,q);
      for(let e=0;e<2;e++){tape.out(NONE,NONE,d[n]);for(let i=n-1;i>=0;i--)tape.out(high[i],d[i+1],d[i]);for(let i=0;i<=n;i++)if(coeff[i])tape.out(NONE,d[i],target);for(let i=0;i<n;i++)tape.out(high[i],d[i+1],d[i]);}
      for(const q of high)tape.out(NONE,NONE,q);
    }
    u6Transpose(tape,tag,a,b,yes,no,back){
      const path=[],v=a;let at=v;
      for(let j=0;j<tag.length;j++)if(((a^b)>>j)&1){const p=yes.slice(),n=no.slice();tag.forEach((q,i)=>{if(i!==j)((at>>i)&1?p:n).push(q);});path.push(()=>this.toggle(tape,p,n,tag[j]));at^=1<<j;}
      const ops=path.concat(path.slice(0,-1).reverse());stepList(ops,back,fn=>fn());
    }
    u6DoubleSign(tape,target){
      const base=this.ab,w=this.half+1,free=this.r.length-base,bits=Math.floor(Math.log2(free))+1;
      const S=this.A.slice(0,w),a=S.slice(0,-1),D=this.zword.slice(0,w-1),word=[...this.r.slice(0,base),...D];
      const tag=this.probeTag(base,this.tags.slice(0,bits),target).map((q,i)=>i===0?S[1]:i===1?S[0]:i===2?this.carry:q);
      const max=2**bits-1,codes=[max-2,max-1,max,max-3];if(codes[3]<=free)throw Error('U6 code capacity '+this.k);
      const H=Object.create(this);H.u40Low=S[0];H.u40Tag=tag;H.u6Code=codes;H.u6S=S;H.u6Tapes=[];
      const high=this.r.slice(base),low=high[0];
      const rotate=rv=>{
        const partial=[this.pick,this.pick,...tag.slice(2)];
        // Higher rank bits fit their final helpers before the coefficient rotates.
        const hi=()=>this.u10RankHigh(tape,partial);
        hi();stepList(split(0,bits),rv,j=>{const q=j<2?this.pick:tag[j];if(j<2)this.u6RankBit(tape,j,q);const k=(1<<j)%S.length,src=S.slice(-k).concat(S.slice(0,-k));this.permute(tape,S,src,[q],rv);if(j<2)this.u6RankBit(tape,j,q);});hi();
      };
      const recode=rv=>{
        const zero=rr=>{const mark=()=>this.toggle(tape,[],high,this.pick);mark();const ops=codes.slice(0,3).map((c,i)=>bb=>this.u6Transpose(tape,tag,i+1,c,[this.pick],[],bb));stepList(ops,rr,fn=>fn(rr));mark();};
        const unit=rr=>{const mark=()=>this.toggle(tape,[low],high.slice(1),this.pick);mark();this.u6Transpose(tape,tag,0,codes[3],[this.pick],[],rr);mark();};
        stepList([zero,unit],rv,fn=>fn(rv));
      };
      const seq=[rotate,()=>this.rank(tape,tag),recode,
        rv=>this.inc(tape,this.r,[],!rv),rv=>H.parkTail(tape,D,tag,rv),()=>this.cnotList(tape,[],D),
        rv=>H.u6VirtualTape(tape).add(a,D,[],this.carry,rv),rv=>H.alignedMix(tape,a,D,tag,rv),rv=>H.barrel(tape,this.r,tag,false,rv)];
      stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);stepList(seq,true,fn=>fn(true));
      for(const tp of H.u6Tapes)tp.u6Check();
    }
    u6VirtualTape(tape){
      const H=this,tag=this.u40Tag,[q0,q1]=this.u6S,host=this.u9Three?this.u6S.slice(0,this.u9H||3):[q0,q1],tp=Object.create(tape);
      tp.ids=tape.ids.filter(q=>!tag.includes(q));
      const cube=(yes=[],no=[])=>({yes:[...new Set(yes)].sort((a,b)=>a-b),no:[...new Set(no)].sort((a,b)=>a-b)});
      const key=c=>c.yes.join(',')+'!'+c.no.join(',');
      const norm=ts=>{const m=new Map();for(const c of ts){if(c.yes.some(q=>c.no.includes(q)))continue;const k=key(c);if(m.has(k))m.delete(k);else m.set(k,c);}return [...m.values()];};
      const eq=c=>cube(tag.filter((q,j)=>c>>j&1),tag.filter((q,j)=>!(c>>j&1)));
      const base=this.u648C?this.u648C.Pc.map(i=>[cube([tag[tag.length-1],tag[i]])]):this.u9Three?Array.from({length:this.u9H||3},(_,j)=>Array.from({length:j+1},(_,r)=>r)).map((ranks,j)=>ranks.map(rank=>{const p=this.u9Category(rank);return cube(p.yes.concat(tag[j-rank]),p.no);})): [[cube(tag.slice(2).concat(tag[1]))],[cube(tag.slice(2).concat(tag[0])),eq(this.u6Code[3])]];let expressions=base.map(x=>x.slice());
      let dependencies=new Set();const deps=()=>{dependencies=new Set(expressions.flatMap(e=>e.flatMap(c=>c.yes.concat(c.no))));};deps();
      const expr=q=>q===NONE?[cube()]:host.includes(q)?expressions[host.indexOf(q)]:[cube([q])];
      const mul=(a,b)=>norm(a.flatMap(x=>b.map(y=>cube(x.yes.concat(y.yes),x.no.concat(y.no)))));
      tp.out=(a,b,t)=>{if(!host.includes(a)&&!host.includes(b)&&!host.includes(t)&&!dependencies.has(t)){tape.out(a,b,t);return;}
        const terms=mul(expr(a),expr(b));if(host.includes(t)){const i=host.indexOf(t);expressions[i]=norm(expressions[i].concat(terms));deps();return;}
        if(terms.some(c=>c.yes.includes(t)||c.no.includes(t)))throw Error('U6 implicit self target '+[H.k,a,b,t]);
        expressions=expressions.map(e=>norm(e.concat(mul(e.filter(c=>c.yes.includes(t)||c.no.includes(t)).map(c=>cube(c.yes.filter(q=>q!==t),c.no.filter(q=>q!==t))),terms))));
        deps();
        H.u10Terms(tape,terms,t);
      };
      tp.u6Check=()=>{for(let i=0;i<host.length;i++)if(norm(expressions[i].concat(base[i])).length)throw Error('U6 virtual not restored '+H.k);};
      H.u6Tapes.push(tp);return tp;
    }

    signProbe(tape,target,back){
      if(this.k>=120&&this.k<=126 || this.k===119&&target===this.dv[0]){
        const H=Object.create(this);H.tags=this.tags.slice();H.tags[0]=this.v[this.k];H.u9Lead=true;H.u38ProbeLease=true;
        const tp=Object.create(tape);tp.ids=tape.ids.filter(q=>q!==this.v[this.k]);
        tape.out(NONE,this.take,this.v[this.k]);super.signProbe.call(H,tp,target,back);tape.out(NONE,this.take,this.v[this.k]);return;
      }
      if(this.u5CleanPhase===target&&this.k<=112){
        const H=Object.create(this);H.tags=this.tags.slice();H.tags[0]=target;H.u5PhaseHost=target;
        const tp=Object.create(tape);tp.ids=tape.ids.filter(q=>q!==target&&q!==this.zword.at(-1));
        H.alignedSign(tp,target);return;
      }
      super.signProbe(tape,target,back);
    }

    u40Tape(tape){
      if(this.u6Code)return this.u6VirtualTape(tape);
      if(!this.u40Tag)return tape;
      const H=this,low=this.u40Low,tag=this.u40Tag,tp=Object.create(tape);
      tp.ids=tape.ids.filter(q=>!tag.includes(q));
      tp.out=(a,b,t)=>{
        if(t===low)throw Error('U4 coefficient low written');
        const cs=[a,b].filter(q=>q!==NONE);
        if(!cs.includes(low)){tape.out(a,b,t);return;}
        if(H.u40NoCode)return;
        const controls=[...tag,...cs.filter(q=>q!==low)];
        tape.mc(controls,t,tape.loan([...controls,t],Math.max(1,controls.length-2)));
      };
      return tp;
    }
    mixed(tape,q,v,rem,controls,back){
      super.mixed(this.u40Tag&&v[0]===this.u40Low?this.u40Tape(tape):tape,q,v,rem,controls,back);
    }
    constBelow(tape,word,limit,controls,targets){
      if(this.u9Three&&word.length===this.u40Tag.length&&word.every((q,i)=>q===this.u40Tag[i])){
        MixedArithmetic.prototype.constBelow.call(this,tape,word,limit,controls,targets);
        for(let rank=0;rank<(this.u9H||3);rank++)if(BigInt(rank)<limit){const p=this.u9Category(rank);for(const t of targets)this.toggle(tape,controls.concat(p.yes),p.no,t);}return;
      }
      if(this.u6Code&&word.length===this.u40Tag.length&&word.every((q,i)=>q===this.u40Tag[i])){
        MixedArithmetic.prototype.constBelow.call(this,tape,word,limit,controls,targets);
        if(limit>1n&&limit<=BigInt(this.u6Code[3])){for(const t of targets)this.toggle(tape,controls.concat(word.slice(2)),[],t);return;}
        if(limit===1n){for(const t of targets){this.toggle(tape,controls.concat(word.slice(2),word[0]),[],t);this.toggle(tape,controls.concat(word.slice(2),word[1]),[word[0]],t);}return;}
        this.u6Code.forEach((c,i)=>{if((BigInt(i===3?1:0)<limit)!==(BigInt(c)<limit))for(const t of targets){const yes=controls.slice(),no=[];word.forEach((q,j)=>((c>>j)&1?yes:no).push(q));this.toggle(tape,yes,no,t);}});return;
      }
      if(this.u40FixedRank!==undefined&&word.length===0){if(BigInt(this.u40FixedRank)<limit)this.cnotList(tape,controls,targets);return;}
      super.constBelow(tape,word,limit,controls,targets);
      if(this.u40Tag&&!this.u40NoCode&&word.length===this.u40Tag.length&&word.every((q,i)=>q===this.u40Tag[i])&&limit>0n&&limit<=BigInt((1<<word.length)-1))
        for(const t of targets)this.toggle(tape,[...controls,...word],[],t);
    }
    barrel(tape,word,tag,left,back){
      if(this.u9Three){
        const extra=tag.at(-1);
        stepList(split(0,tag.length-1),back,j=>{
          const k=(1<<j)%word.length,src=left?word.slice(-k).concat(word.slice(0,-k)):word.slice(k).concat(word.slice(0,k));
          const terms=[{yes:[tag[j]],no:[extra]}];if(this.u648C){if(j<2)terms.push({yes:[extra,tag[this.u648C.Pr[j]]],no:[]});}else if(this.u9H){for(let r=1;r<this.u9H;r++)if((r>>j)&1)terms.push(this.u9Category(r));}else if(j<2)terms.push(this.u9Category(j===0?1:2));
          stepList(terms,back,p=>{for(const q of p.no)tape.out(NONE,NONE,q);this.u10ControlledPermutation(tape,word,src,p.yes.concat(p.no),back);for(const q of p.no)tape.out(NONE,NONE,q);});
        });return;
      }
      if(this.u6Code){
        const seq=[rv=>AlignedGeneral.prototype.barrel.call(this,tape,word,tag,left,rv)];
        this.u6Code.forEach((c,i)=>{const rank=i===3?1:0,k=((c-rank)%word.length+word.length)%word.length;
          const src=left?word.slice(k).concat(word.slice(0,k)):word.slice(-k).concat(word.slice(0,-k));
          const yes=[],no=[];tag.forEach((q,j)=>((c>>j)&1?yes:no).push(q));
          seq.push(rv=>{for(const q of no)tape.out(NONE,NONE,q);this.u10ControlledPermutation(tape,word,src,tag,rv);for(const q of no)tape.out(NONE,NONE,q);});
        });stepList(seq,back,fn=>fn(back));return;
      }
      if(this.u40FixedRank!==undefined){const k=this.u40FixedRank%word.length,src=left?word.slice(-k).concat(word.slice(0,-k)):word.slice(k).concat(word.slice(0,k));this.permute(tape,word,src,[],back);return;}
      if(!this.u40Tag||this.u40NoCode){super.barrel(tape,word,tag,left,back);return;}
      const k=((1<<tag.length)-1)%word.length;
      const src=left?word.slice(k).concat(word.slice(0,k)):word.slice(-k).concat(word.slice(0,-k));
      const ops=[rv=>super.barrel(tape,word,tag,left,rv),rv=>this.permute(tape,word,src,tag,rv)];
      stepList(ops,back,fn=>fn(back));
    }
    u40Sign(tape,target){
      if(this.k>=0&&this.k<=112&&(this.u5PhaseHost===undefined||true)&&!this.u648VkHost&&!(this.k>=113&&process.env.Q648_P4T113&&!(process.env.Q648_P4T113==='both'||(process.env.Q648_P4T113==='dv1')===(target===this.dv[1])))){this.u648FourSign(tape,target);return;}
      if(this.k>=113&&this.k<=119&&!this.u648Narrow0&&typeof this.u648FourSign==='function'){this.u648FourSign(tape,target);return;}
      if((this.k<=2||this.k>=63&&this.k<=67)&&this.u5PhaseHost===undefined){this.u9ThreeSign(tape,target);return;}
      if((this.k>=3&&this.k<=62||this.k>=68&&this.k<=95)&&this.u5PhaseHost===undefined){this.u6DoubleSign(tape,target);return;}
      if((this.k===64||(this.u6ProbeSlot===0&&(this.k===96||this.k===111||this.k===112||this.k===119)))&&!this.u40Split){this.u40SplitSign(tape,target);return;}
      const base=this.ab,w=this.half+1,free=this.r.length-base;
      const tag=this.probeTag(base,this.tags.slice(0,Math.floor(Math.log2(free))+1),target).map((q,i)=>i===2?this.carry:i===(this.u6ProbeSlot??1)?this.pick:q);
      if(!this.u40NoCode&&free===(1<<tag.length)-1)throw Error('U4 no reserved rank '+this.k);
      const S=this.A.slice(0,w),a=S.slice(0,-1),D=this.zword.slice(0,w-1),word=[...this.r.slice(0,base),...D];
      const H=Object.create(this);H.u40Low=S[0];H.u40Tag=tag.slice();H.u40Tag[this.u6ProbeSlot??1]=S[0];
      const swap=()=>{tape.out(NONE,this.pick,S[0]);tape.out(NONE,S[0],this.pick);tape.out(NONE,this.pick,S[0]);};
      // Exact transposition (rank=0,low=1) <-> (rank=all-ones,low=0).
      const recode=()=>{
        const ports=[...tag,S[0]],values=ports.map((q,i)=>i===tag.length?1:0),edges=[];
        for(let i=0;i<ports.length;i++){
          const yes=[],no=[];for(let j=0;j<ports.length;j++)if(j!==i)(values[j]?yes:no).push(ports[j]);
          edges.push(()=>this.toggle(tape,yes,no,ports[i]));values[i]^=1;
        }
        for(const fn of edges)fn();for(let i=edges.length-2;i>=0;i--)edges[i]();
      };
      const lease=rv=>stepList(this.u40NoCode?[swap]:[recode,swap],rv,fn=>fn());
      const seq=[()=>this.rank(tape,tag),rv=>super.barrel(tape,S,tag,true,rv),lease,
        rv=>this.inc(tape,this.r,[],!rv),rv=>H.parkTail(tape,D,H.u40Tag,rv),()=>this.cnotList(tape,[],D),
        rv=>H.u40Tape(tape).add(a,D,[],this.carry,rv),rv=>H.alignedMix(tape,a,D,H.u40Tag,rv),rv=>H.barrel(tape,this.r,H.u40Tag,false,rv)];
      stepList(seq,false,fn=>fn(false));
      (this.u40NoCode?H:this).u40Deposit(tape,target,S,word);
      stepList(seq,true,fn=>fn(true));
    }
    u40Deposit(tape,target,S,word){
      const phaseTarget=target;if(this.u5PhaseHost===target)target=this.zword.at(-1);
      const high=this.u40ExcludedTop,c=high===undefined?this.ctrl:[...this.ctrl,high];
      const write=cs=>{
        if(high!==undefined)tape.out(NONE,NONE,high);
        this.toggle(tape,cs,[],target);tape.out(NONE,NONE,S.at(-1));this.constBelow(tape,word,this.centeredFree?this.p-(1n<<BigInt(this.k)):this.p,[...cs,S.at(-1)],[target]);tape.out(NONE,NONE,S.at(-1));
        if(high!==undefined)tape.out(NONE,NONE,high);
      };
      phaseDeposit(this,tape,phaseTarget,()=>{
        write(c);
        if(this.u40NoCode){
          for(const q of this.u40Tag)tape.out(NONE,NONE,q);
          write([...c,...this.u40Tag]);
          for(const q of this.u40Tag)tape.out(NONE,NONE,q);
        }
      });
    }
    u40SplitSign(tape,target){
      const H=Object.create(this);H.u40Split=true;H.u40NoCode=true;
      H.u40Sign(tape,target);
      const F=Object.create(this);F.u40FixedRank=0;F.take=this.k===119?this.v[this.k]:this.u6ProbeSlot===0?this.aux[3]:this.tags[0];F.ctrl=this.k===119?[this.g,this.take,F.take]:[this.g,F.take];
      const select=()=>this.toggle(tape,this.ctrl,this.r.slice(this.ab),F.take);
      select();F.u40FixedSign(tape,target);select();
      // Two phaseDeposit calls each include incoming target phase; retain exactly one.
      if(this.measureTarget===target)tape.z(target);
    }
    u40FixedSign(tape,target){
      const base=this.ab,w=this.half+1,tag=[],S=this.A.slice(0,w),a=S.slice(0,-1),D=this.zword.slice(0,w-1),word=[...this.r.slice(0,base),...D];
      const seq=[rv=>this.barrel(tape,S,tag,true,rv),rv=>this.inc(tape,this.r,[],!rv),
        rv=>this.parkTail(tape,D,tag,rv),()=>this.cnotList(tape,[],D),rv=>tape.add(a,D,[],this.carry,rv),
        rv=>this.alignedMix(tape,a,D,tag,rv),rv=>this.barrel(tape,this.r,tag,false,rv)];
      stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);stepList(seq,true,fn=>fn(true));
    }

    u39Normalize(tape,back){
      if(this.u11Witness){this.u11Normalize(tape,back);return;}

      if(this.u6TrialSlot===0&&this.u38NormLease){const H=Object.create(this);H.u38NormLease=false;
        if(!back)tape.out(NONE,this.take,this.v[this.k]);H.u39Normalize(tape,back);if(back)tape.out(NONE,this.take,this.v[this.k]);return;}
      const H=Object.create(this),tmp=this.u39Temp,top=this.n.at(-1),n=this.n;
      if(globalThis.__u39Host)globalThis.__u39Host(tape,this,back?'normalizer-inverse-entry':'normalizer-forward-entry',{tmp,top});
      H.tag=this.tag.slice();H.tag[this.u6TrialSlot??1]=tmp;
      const norm=rv=>stepList(split(0,H.tag.length).reverse(),rv,j=>{
        const s=1<<j,t=H.tag[j],origins=n.slice(-s).concat(n.slice(0,-s));
        const hk=this.__hk,seq=[...(hk?[rr=>hk(tape,'pre',j,t,rr)]:[]),()=>H.toggle(tape,[this.take],n.slice(-s),t),rr=>H.permute(tape,n,origins,[this.take,t],rr),...(hk?[rr=>hk(tape,'post',j,t,rr)]:[])];
        stepList(seq,rv,fn=>fn(rv));
      });
      const lease=rv=>{
        if(globalThis.__u39Host)globalThis.__u39Host(tape,this,rv?'norm-out':'norm-in',{tmp,top});
        const seq=[()=>tape.out(NONE,this.take,top),rr=>this.permute(tape,[top,tmp],[tmp,top],[this.take],rr)];
        stepList(seq,rv,fn=>fn(rv));
      };
      stepList([norm,lease],back,fn=>fn(back));
    }
    u39Divisor(tape,B,run,back){
      if(this.u8Relay){
        const host=B.T.at(-1);
        if(host===this.tag[0]||B.D.includes(host))throw Error('U8 band relay alias');
        const H=Object.create(this);H.u8Relay=false;H.u8Ones=true;H.tag=this.tag.slice();H.tag[0]=host;
        const swap=rv=>this.permute(tape,[this.tag[0],host],[host,this.tag[0]],[],rv);
        if(globalThis.__u8Host)globalThis.__u8Host(tape,this,B,host,back);
        const body=(J,rv)=>{const clear=()=>{if(B.lo)J.toggle(tape,[J.g,J.take,-19],J.q.slice(0,-1),J.qtop);};
          if(rv)clear();run(J,rv);if(!rv)clear();};
        swap(false);H.u39Divisor(tape,B,body,back);swap(true);return;
      }

      const H=Object.create(this),slot=this.u6TrialSlot??1,top=this.tag[slot];H.tag=this.tag.slice();H.tag[slot]=B.d0;
      if(globalThis.__u39Host)globalThis.__u39Host(tape,this,'band-entry',{B,top});
      H.u39Trial=false;H.u39LowOne=B.d0;
      const swap=rv=>{
        const seq=[rr=>this.permute(tape,[top,B.d0],[B.d0,top],[],rr),()=>tape.out(NONE,NONE,top)];
        stepList(seq,rv,fn=>fn(rv));
      };
      swap(false);
      H.roundedDivisor(tape,B,false);H.inUpperHalf=B.lo!==0;
      // run is a lexical closure over the original row: use an inner body supplied by caller.
      run(H,back);
      H.inUpperHalf=null;H.roundedDivisor(tape,B,true);swap(true);
    }
    roundedDivisor(tape,B,back){
      if(this.u39LowOne===undefined){super.roundedDivisor(tape,B,back);return;}
      const seq=[rv=>this.inc(tape,B.H,[],!rv),rv=>this.inc(tape,B.H.slice(1),[this.dv[1]],rv)];
      stepList(seq,back,fn=>fn(back));
    }
    digit(tape,z,v,controls,back){
      if(this.u39LowOne===undefined){super.digit(tape,z,v,controls,back);return;}
      this.u39Digit(tape,z,v,controls,back);
    }
    u39Digit(tape,z,v,controls,back){
      if(v[0]!==this.u39LowOne||controls.length!==1)throw Error('U1 implicit low-one ports');
      const loan=tape.loan([...z,...v,...controls],1)[0],ops=dirtyDigit(v,z.slice(0,-1),z.at(-1),controls[0],loan);
      stepList(ops,back,op=>{
        if(op.at(-1)===v[0])throw Error('U1 low divisor written');
        const cs=op.slice(0,-1).filter(q=>q!==v[0]);
        tape.out(cs.length===2?cs[0]:NONE,cs.length?cs.at(-1):NONE,op.at(-1));
      });
    }
    oddQuotient(tape,B,back){
      if(!this.u39Trial){super.oddQuotient(tape,B,back);return;}
      this.u39Divisor(tape,B,(H,rv)=>{H.digit=H.u39Digit;H.withDivisor=(tp,band,fn,rr)=>fn([H.g,H.take,-19],rr);OddEstimateGeneral.prototype.oddQuotient.call(H,tape,B,rv);},back);
    }
    oddWitness(tape,B,back){
      if(this.u11Witness){this.u11Band(tape,B,back);return;}
      if(!this.u39Trial){super.oddWitness(tape,B,back);return;}
      this.u39Divisor(tape,B,(H,rv)=>{H.withDivisor=(tp,band,fn,rr)=>fn([H.g,H.take,-19],rr);OddEstimateGeneral.prototype.oddWitness.call(H,tape,B,rv);},back);
    }

    withDivisor(tape,band,run,back){
      if(!this.wideBand){super.withDivisor(tape,band,run,back);return;}
      this.roundedDivisor(tape,band,false);
      this.inUpperHalf=band.lo!==0;
      run([this.g,this.take,-19],back);
      this.inUpperHalf=null;
      this.roundedDivisor(tape,band,true);
    }
    toggle(tape,yes,no,target){
      if(!yes.includes(-19)){super.toggle(tape,yes,no,target);return;}
      if(this.inUpperHalf==null)throw Error('unresolved band');
      const base=yes.filter(q=>q!==-19),high=this.tag.slice(3),hasOne=high.some(q=>base.includes(q));
      if(this.inUpperHalf)super.toggle(tape,base,no,target);
      if(!hasOne)super.toggle(tape,base,no.concat(high.filter(q=>!no.includes(q))),target);
      if(this.packedShort){const pos=this.tag[3],neg=this.tag.filter((v,i)=>i!==3);
        if(!no.includes(pos)&&!neg.some(q=>base.includes(q)))super.toggle(tape,base.includes(pos)?base:base.concat(pos),no.concat(neg.filter(q=>!no.includes(q))),target);
      }
    }
    cnotList(tape,controls,word){
      if(!controls.includes(-19)){super.cnotList(tape,controls,word);return;}
      for(const q of word)this.toggle(tape,controls,[],q);
    }
    alignedSign(tape,target){
      if(!this.wideBand){
        if(!this.u9Lead&&this.k>=96&&this.k<=119){
            const H=Object.create(this);H.tags=this.tags.slice();H.tags[1]=this.v[this.k];H.u38ProbeLease=true;
 if(this.k<=119&&this.u5PhaseHost===undefined){H.u40Probe=true;H.u6ProbeSlot=0;}
            tape.out(NONE,this.take,this.v[this.k]);super.alignedSign.call(H,tape,target);tape.out(NONE,this.take,this.v[this.k]);return;
        }
        super.alignedSign(tape,target);return;
      }
      const layer=Object.create(this),q=this.v[this.k];
      layer.u40Probe=this.k<=95&&(this.k!==63||this.u5PhaseHost===undefined);layer.tags=this.tags.slice();layer.tags[this.tag.length-2]=q;if(this.deep){layer.tags[4]=this.r.at(-1);layer.r=this.r.slice(0,-1);layer.centeredFree=true;}
      tape.out(NONE,this.take,q);super.alignedSign.call(layer,tape,target);tape.out(NONE,this.take,q);
    }
    layouts(){
      if(!this.packedShort)return super.layouts();
      const out=[];
      for(const [lo,hi] of [[0,8],[9,this.maxShift]]){
        const w=hi+6,W=w+1,spare=this.n.slice(1,Math.max(1,lo));
        const T=[...this.q,...spare.splice(0,Math.max(0,W+1-this.q.length))].slice(0,W+1),free=[...this.q.slice(W+1),...spare];
        if(T.length!==W+1||free.length<2)throw Error('unfunded positive rank');
        const H=[...this.n.slice(this.m-w+1),free[1]],D=[free[0],...H];
        if(new Set([...T,...D]).size!==T.length+D.length)throw Error('short divisor overlaps quotient');
        out.push({lo,hi,w,W,T,D,H,d0:free[0]});
      }return out;
    }
    affine(tape,back){
      const H=Object.create(this.hostRank(this.useCoefficientDirection?this.pick:this.dv[1]));
      if(this.k>=64&&this.k<=119){H.tag=H.tag.slice();H.tag[2]=this.A[this.k<=95?this.half:this.half+1];}
      if(this.k<64){H.tag=H.tag.slice();H.tag[2]=this.v[this.k];H.tag[1]=this.A[this.half-1];H.u3Affine=true;H.u38Implicit=true;H.u12=true;H.tag[0]=this.A[0];}
      if(this.k>=64&&this.k<=95){H.tag=H.tag.slice();H.tag[1]=this.v[this.k];H.u3Affine=true;H.u37Slot=1;}
      if(this.k>=96&&this.k<=125){H.tag=H.tag.slice();H.tag[1]=this.A[this.k<=119?this.half:this.half+1];}
      if(this.k>=96&&this.k<=119){H.tag=H.tag.slice();H.tag[0]=this.v[this.k];H.u37Slot=0;H.u3Affine=true;
        if(this.k>=112){const R=this.hostRank(this.pick);H.tag[3]=R.tag[3];H.rankHost=R.rankHost;H.digit=R.digit;}
      }
      if(this.k>=120&&this.k<=126){H.tag=H.tag.slice();H.tag[0]=this.A[this.half];}
      if(this.k>=64&&this.k<=95){H.tag=H.tag.slice();H.tag[0]=this.A[this.half-1];H.u38Implicit=true;H.u6TopSlot=0;}
      if(this.k>=64&&this.k<=123&&((this.k>=64&&this.k<=111)||(this.k>=120&&this.k<=123))){const n=H.tag.length;if(n<3||n>6||(n<5&&this.k<120))throw Error('b648 tag '+this.k);H.tag=[this.A[0],this.A[this.half-1],this.v[this.k],this.pick,this.A[this.half],256].slice(0,n);H.u3Affine=true;H.u38Implicit=true;H.u12=true;H.u37Slot=undefined;H.u6TopSlot=undefined;if(this.k>=120){H.rankHost=this.pick;H.digit=this.digitDirty;}}
      if(!this.deep){super.affine.call(H,tape,back);return;}
      const layer=Object.create(H);layer.tag=H.tag.slice();layer.tag[4]=this.A[this.half];if(this.k>=0&&this.k<=63&&this.k<64&&layer.u12){if(layer.tag.length!==7||layer.tag[6]!==647)throw Error('a648 tag '+this.k+' '+JSON.stringify(layer.tag));layer.tag[6]=this.A[2];layer.u648=true;}super.affine.call(layer,tape,back);
    }
    tailDigit(tape,layer,z,S,back){
      if(this.u6Code){
        // The tail enable is rank >= i-ab+1. Active digits therefore have
        // i-ab+1 zero low divisor bits. Disabled fused digits are identity.
        const i=this.r.indexOf(z.at(-1)),cut=i-this.ab+1;
        if(cut<1)throw Error('U10 tail threshold');
        const V=S.slice(cut),Z=z.slice(cut),loan=tape.loan([...z,...S,this.take],1)[0];
        const tp=cut>=(this.u9Three?(this.u9H||3):2)?tape:this.u6VirtualTape(tape);
        stepList(dirtyDigit(V,Z.slice(0,-1),Z.at(-1),this.take,loan),back,op=>tp.out(op.length===3?op[0]:NONE,op.length>=2?op[op.length-2]:NONE,op.at(-1)));
        return;
      }
      if(!this.u38ProbeLease&&!this.wideBand&&this.layouts()){layer.digit(tape,z,S,[this.take],back);return;}
      if(this.f1Clean){const L2=Object.create(layer);L2.pick=this.dv[0];MixedArithmetic.prototype.digit.call(L2,tape,z,S,[this.take],back);return;}
      const loan=tape.loan([...z,...S,this.take],1)[0];
      const ops=dirtyDigit(S,z.slice(0,-1),z.at(-1),this.take,loan);
      if(this.u40Tag)tape=this.u40Tape(tape);
      stepList(ops,back,op=>tape.out(op.length===3?op[0]:NONE,op.length>=2?op[op.length-2]:NONE,op.at(-1)));
    }

    constructor(m,delta,k,width){
      super(m,delta,k,width);
      if(m!==256)throw Error("this release targets the full field");
      this.deep=this.tag.length===7;this.wideBand=this.tag.length>=6;this.useCoefficientDirection=this.tag.length>=5;
      if(this.useCoefficientDirection){
        if(!this.layouts())throw Error("missing rounded-quotient layout");
        const top=this.tag.length-1,free=this.dv[1];if(this.wideBand){this.tags[top-1]=this.borrow;this.tag[top-1]=this.borrow;} if(this.deep){this.tags[4]=this.n.at(-1);this.tag[4]=this.n.at(-1);}
        this.tag[top]=free;this.tags[top]=free;
        this.dv=[this.dv[0],this.v[this.k]];
      }
    }
    t648(tape,rank,nn,P,M,witness,work){
      if(this.k<0||this.k>63)return null;
      if(rank.length!==7||rank[6]!==647)throw Error('t648 rank '+this.k+' '+JSON.stringify(rank));
      const take=this.take,l=rank.slice(0,3),b=rank.slice(3,6),c=nn.slice(P,P+3),mk=nn[M],X=q=>tape.out(NONE,NONE,q);
      const q0=this.q.at(-2),qt=this.qtop,f1=this.dv[0];
      if(q0!==645||qt!==646||f1!==644)throw Error('t648 hosts '+this.k+' '+[q0,qt,f1]);
      const cfg=witness?{pre:{F:qt,J:1},post:{F:f1,J:null}}:{pre:{F:q0,J:null},post:{F:qt,J:0}};
      for(const q of [...c,mk,nn[M+1],nn[M+2],nn[P-1]])if(!(q>=0)||rank.includes(q)||q===take)throw Error('t648 ports '+this.k);
      const run=(ops,rv)=>stepList(ops,rv,fn=>fn());
      const encOps=F=>{const o=[];
        for(let i=0;i<3;i++)o.push(()=>this.toggle(tape,[take,F,b[i]],[],c[i]));
        for(let i=0;i<3;i++)o.push(()=>this.toggle(tape,[take,F,c[i]],[],b[i]));
        for(let i=0;i<3;i++)o.push(()=>this.toggle(tape,[take,F],[],b[i]));
        o.push(()=>this.toggle(tape,[take,F],[],mk));
        o.push(()=>this.toggle(tape,[take,...b,mk],[],F));return o;};
      // copies (marker at M+d still in place as the P witness), then the marker itself.
      const restash=(d,x)=>{const o=[];
        for(let i=0;i<3;i++){const lo=nn[P+i],hi=nn[P+i+d],cs=[take,x,...b,nn[M+d]];
          o.push(()=>{if(nn[M+d]===lo||nn[M+d]===hi)throw Error('t648 restash overlap');this.toggle(tape,[...cs,hi],[],lo);},()=>this.toggle(tape,[...cs,lo],[],hi));}
        const cm=[take,x,...b];o.push(()=>this.toggle(tape,[...cm,nn[M+d]],[],mk),()=>this.toggle(tape,[...cm,mk],[],nn[M+d]));
        return o;};
      // biasE: rank+1 on the code. lz = low bits 000 after the low increment (the carry). On lz lanes with b=111: P lanes
      // (mk=1) c += 1; former rank-63 lanes (mk=0, c=000) get mk := 1 (now P with c=0; c=000 is the discriminator, P lanes
      // have c >= 1 after their increment). Then P lanes park b at 110 ([lz,b4,b5,mk]: natural v=6 lanes have mk=0) and one
      // 3-bit increment on lz lanes moves P lanes back to 111 and every natural v<=6 to v+1.
      const biasOps=[
        rr=>this.inc(tape,l,[take],rr),
        rr=>{l.forEach(X);this.inc(tape,c,[take,...l,...b,mk],rr);l.forEach(X);},
        ()=>{l.forEach(X);this.toggle(tape,[take,...l,...b],[...c],mk);l.forEach(X);},
        ()=>{l.forEach(X);this.toggle(tape,[take,...l,b[1],b[2],mk],[],b[0]);l.forEach(X);},
        rr=>{l.forEach(X);this.inc(tape,b,[take,...l],rr);l.forEach(X);}];
      const biasE=rv=>stepList(biasOps,rv,fn=>fn(rv));
      const side=({F,J})=>{const S=Object.create(work);S.tag=rank.slice();S.tag[6]=F;
        if(J!==null)S.__hk=(tp,phase,j,t,rr)=>{
          if(phase==='pre'&&j===J)run(encOps(F),rr);
          else if(phase==='post'&&j<=J)run(restash(1<<j,t),rr);
          else if(phase==='rest')run(restash(1,t),rr);};
        return S;};
      const SP=side(cfg.pre),SQ=side(cfg.post);
      const pre=[rv=>SP.normalize(tape,rv)];if(cfg.pre.J===null)pre.push(rv=>run(encOps(cfg.pre.F),rv));pre.push(rv=>biasE(rv));
      const post=[rv=>biasE(!rv)];if(cfg.post.J===null)post.push(rv=>run(encOps(cfg.post.F),!rv));post.push(rv=>SQ.normalize(tape,!rv));
      const view=o=>{const v=Object.create(o);v.tag=rank.slice(0,6);v.t648=true;
        // oddQuotient applies onesBlock(2^j,[tag[j]]) for 2^j <= B.hi (rank bits as VALUES). On P lanes bits 3..5 give 56
        // steps instead of 64 + 8c: add onesBlock(8,[P]) and onesBlock(8*2^i,[P,c_i]).
        v.oddQuotient=function(tp,B,back){const prev=v.__B648;v.__B648=B;try{return o.oddQuotient.call(this,tp,B,back);}finally{v.__B648=prev;}};
        v.onesBlock=function(tp,R,D,n,extra,ctrl,back){
          const B=v.__B648,fix=B&&B.hi>=64&&n===32&&extra.length===1&&extra[0]===b[2];
          const Pc=[...b,mk],seq=[rr=>o.onesBlock.call(this,tp,R,D,n,extra,ctrl,rr)];
          if(fix){seq.push(rr=>o.onesBlock.call(this,tp,R,D,8,Pc,ctrl,rr));for(let i=0;i<3;i++)seq.push(rr=>o.onesBlock.call(this,tp,R,D,8<<i,[...Pc,c[i]],ctrl,rr));}
          stepList(seq,back,fn=>fn(back));};
        return v;};
      return {pre,post,view};
    }
    trial(tape,witness,back){

      if(this.k<=95&&!witness&&!this.u8Entered){
        const H=Object.create(this);H.u8Entered=true;
        const high=()=>this.toggle(tape,this.ctrl,this.q.slice(0,-1).concat(this.r.slice(this.half+1)),this.qtop);
        if(back)high();H.trial(tape,witness,back);if(!back)high();return;
      }
      if(!this.useCoefficientDirection){super.trial(tape,witness,back);return;}
      const temp=Object.create(this);temp.dv=[this.dv[0],this.carry];
      const coeff=this.v[this.k],c=this.ctrl;
      const moved=rv=>{
        const steps=[r=>this.permute(tape,[this.carry,coeff],[coeff,this.carry],c,r),
          ()=>this.toggle(tape,c,[],this.carry)];
        stepList(steps,rv,fn=>fn(rv));
      };
      const dirs=()=>temp.direction(tape);
      if(!this.deep&&((this.k>=64&&this.k<=111&&this.k>=64&&this.k<=111)||(false&&this.k===112))){
        const short=this.r.slice(0,-1),free=this.r.at(-1),packed=short.concat(this.u),hi=packed.at(-1),H=this.uTrialRank(witness),low=Object.create(H),work=Object.create(H);
        const rank=H.tag.slice(),top=rank.length-1;
        if(this.k===112){if(rank.length!==4||rank[1]!==this.v[this.k])throw Error('t648 rank112 '+JSON.stringify(rank));rank[1]=hi;const dv=[this.dv[0],this.v[this.k]];low.dv=dv;work.dv=dv;
          // band [0,8] needs one more free wire than row 112's 17-wire quotient leaves: r's top (zero on active lanes; the parked hi lanes are
          // take-cleared, so every band write is identity for them and the band's inverses restore their marker).
          low.layouts=function(){const out=[];for(const [lo,hi] of [[0,8],[9,this.maxShift]]){const w=hi+6,W=w+1,spare=lo===0?[free]:this.n.slice(1,lo);
            const T=[...this.q,...spare.splice(0,Math.max(0,W+1-this.q.length))].slice(0,W+1),fr=[...this.q.slice(W+1),...spare];
            if(T.length!==W+1||fr.length<2)throw Error('t648 112 unfunded');const Hh=[...this.n.slice(this.m-w+1),fr[1]],Dd=[fr[0],...Hh];
            if(new Set([...T,...Dd]).size!==T.length+Dd.length)throw Error('t648 112 overlap');out.push({lo,hi,w,W,T,D:Dd,H:Hh,d0:fr[0]});}return out;};}
        else{if(!((rank.length===5&&rank[1]===hi)||(rank.length===6&&rank[4]===hi))||rank[top]!==647)throw Error('t648 rank '+this.k+' '+JSON.stringify(rank));rank[top]=free;}
        low.tag=rank;work.tag=rank;
        low.packedShort=true;low.n=[-23,...packed.slice(0,-1)];work.n=packed.slice(0,-1);if(H.u39Trial){rank[H.u6TrialSlot??1]=work.n.at(-1);}
        const choose=rv=>{const ops=[()=>this.toggle(tape,[this.g,this.take,hi],[],free),()=>this.toggle(tape,[this.g,free],[],this.take)];stepList(ops,rv,fn=>fn());};
        const setOne=()=>{if(!witness)this.toggle(tape,[this.g,this.take,hi],[],this.q[0]);};
        const pack=rv=>this.mixed(tape,short,this.v,this.u,[],rv);
        const norm=rv=>work.normalize(tape,rv),bias=rv=>this.inc(tape,rank,[],rv);
        const steps=[dirs,pack,moved,setOne,choose,norm,bias];
        for(const band of low.layouts())steps.push(rv=>witness?low.oddWitness(tape,band,rv):low.oddQuotient(tape,band,rv));
        steps.push(rv=>bias(!rv),rv=>norm(!rv),rv=>choose(!rv),rv=>moved(!rv),rv=>pack(!rv),dirs);
        stepList(steps,back,fn=>fn(back));return;
      }
      if(this.deep){
        const short=this.r.slice(0,-1),free=this.r.at(-1),packed=short.concat(this.u),hi=packed.at(-1),H=this.uTrialRank(witness),low=Object.create(H),work=Object.create(H);
        const rank=H.tag.slice();rank[4]=hi;rank[5]=free;low.tag=rank;work.tag=rank;
        low.packedShort=true;low.n=[-23,...packed.slice(0,-1)];work.n=packed.slice(0,-1);if(H.u39Trial){rank[1]=work.n.at(-1);}
        const choose=rv=>{const ops=[()=>this.toggle(tape,[this.g,this.take,hi],[],free),()=>this.toggle(tape,[this.g,free],[],this.take)];stepList(ops,rv,fn=>fn());};
        const setOne=()=>{if(!witness)this.toggle(tape,[this.g,this.take,hi],[],this.q[0]);};
        const pack=rv=>this.mixed(tape,short,this.v,this.u,[],rv);
        const norm=rv=>work.normalize(tape,rv),bias=rv=>this.inc(tape,rank,[],rv);
        const E648=this.t648(tape,rank,work.n,8,11,witness,work),LB=E648?E648.view(low):low;
        const steps=[dirs,pack,moved,setOne,choose];if(E648)steps.push(...E648.pre);else steps.push(norm,bias);
        for(const band of low.layouts())steps.push(rv=>witness?LB.oddWitness(tape,band,rv):LB.oddQuotient(tape,band,rv));
        if(E648)steps.push(...E648.post);else steps.push(rv=>bias(!rv),rv=>norm(!rv));steps.push(rv=>choose(!rv),rv=>moved(!rv),rv=>pack(!rv),dirs);
        stepList(steps,back,fn=>fn(back));return;
      }
      const H=this.uTrialRank(witness);
      const steps=[dirs,rv=>this.packNumber(tape,rv),moved,rv=>H.normalize(tape,rv)];
      for(const band of H.layouts())steps.push(rv=>witness?H.oddWitness(tape,band,rv):H.oddQuotient(tape,band,rv));
      steps.push(rv=>H.normalize(tape,!rv),rv=>moved(!rv),rv=>this.packNumber(tape,!rv),dirs);
      stepList(steps,back,fn=>fn(back));
    }
    alignedMix(tape,S,D,tag,back){
        const base=this.ab,layer=Object.create(this);
        layer.pick=this.layouts()?this.dv[1]:this.tags.at(-4);layer.carry=this.take;
        const flip=()=>tape.out(NONE,NONE,this.take);
        const extra=rv=>stepList(split(base,this.r.length),rv,i=>{
            const z=[...D,this.r[i]],dest=z.slice(1).concat(z[0]);
            const mark=()=>{tape.out(NONE,NONE,this.take);this.constBelow(tape,tag,BigInt(i-base+1),[],[this.take]);};
            const ops=[mark,rr=>this.tailDigit(tape,layer,z,S,!rr),rr=>this.permute(tape,z,dest,[this.take],rr),mark];
            stepList(ops,rv,fn=>fn(rv));
        });
        const lease=()=>{if(!this.u38ProbeLease&&this.useCoefficientDirection&&!this.wideBand)tape.out(NONE,this.take,this.v[this.k]);};const ops=[lease,rv=>this.mixed(tape,this.r.slice(0,base),S,D,[],rv),flip,extra,flip,lease];
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
const S1CreatePeep=function combined(out,options={}){
 const stats={input:0,output:0,inputCCX:0,outputCCX:0,removed:0,removedCCX:0};
 const final=(function createPeep(out,{window=65536,mode='commute'}={}){
 if(!Number.isInteger(window)||window<1)throw Error('window');
 const N=window+1,A=new Int32Array(N),B=new Int32Array(N),Z=new Int32Array(N),live=new Uint8Array(N);
 const wp=new Float64Array(N),wn=new Float64Array(N),ap=new Float64Array(N),an=new Float64Array(N),bp=new Float64Array(N),bn=new Float64Array(N);
 const R=new Float64Array(1024),W=new Float64Array(1024),keys=new Map();let first=1,end=1;
 const stats={input:0,output:0,removed:0,removedCCX:0,window,mode:'indexed'};
 const key=(a,b,z)=>a*1048576+b*1024+z;
 function rnext(id,q,value){const j=id%N;if(A[j]===q)an[j]=value;else if(B[j]===q)bn[j]=value;else throw Error('read link');}
 function rprev(id,q,value){const j=id%N;if(A[j]===q)ap[j]=value;else if(B[j]===q)bp[j]=value;else throw Error('read link');}
 function unlink(id){const j=id%N,a=A[j],b=B[j],z=Z[j];
  if(wp[j])wn[wp[j]%N]=wn[j];if(wn[j])wp[wn[j]%N]=wp[j];else W[z]=wp[j];
  if(a!==1023){if(ap[j])rnext(ap[j],a,an[j]);if(an[j])rprev(an[j],a,ap[j]);else R[a]=ap[j];}
  if(b!==1023){if(bp[j])rnext(bp[j],b,bn[j]);if(bn[j])rprev(bn[j],b,bp[j]);else R[b]=bp[j];}
  const k=key(a,b,z);if(keys.get(k)===id)keys.delete(k);live[j]=0;
 }
 function emit(id){const j=id%N;if(live[j]){out(A[j],B[j],Z[j]);stats.output++;unlink(id);}}
 function flush(){while(first<end)emit(first++);first=end=1;keys.clear();}
 function gate(a,b,z){
  if(z===1023||a===z||b===z||(a===b&&a!==1023))throw Error('peep alias');
  if(a>b){const q=a;a=b;b=q;}stats.input++;
  if(end-first===window)emit(first++);
  const k=key(a,b,z),id=keys.get(k);
  if(id!==undefined&&W[a]<id&&W[b]<id&&R[z]<id){unlink(id);stats.removed+=2;if(b!==1023)stats.removedCCX+=2;return;}
  const j=end%N;A[j]=a;B[j]=b;Z[j]=z;live[j]=1;
  wp[j]=W[z];wn[j]=0;if(W[z])wn[W[z]%N]=end;W[z]=end;
  ap[j]=a===1023?0:R[a];an[j]=0;if(a!==1023){if(R[a])rnext(R[a],a,end);R[a]=end;}
  bp[j]=b===1023?0:R[b];bn[j]=0;if(b!==1023){if(R[b])rnext(R[b],b,end);R[b]=end;}
  keys.set(k,end);end++;
 }
 return {gate,flush,stats};
})((a,b,z)=>{if(b===1023){b=a;a=1023;}out(a,b,z);stats.output++;if(a!==1023&&b!==1023)stats.outputCCX++;},{window:65536});
 const frame=(function createPeep(out,{window=4096,mode='commute',merge=true}={}){
 if(!Number.isInteger(window)||window<1)throw Error('window');
 const N=window+1,A=new Int32Array(N),B=new Int32Array(N),Z=new Int32Array(N),P=new Uint8Array(N),live=new Uint8Array(N);
 const F=new Uint8Array(1024),O=new Uint8Array(1024),writes=new Float64Array(1024);
 const stats={input:0,output:0,inputCCX:0,outputCCX:0,removed:0,removedCCX:0,cancel:0,merge:0,window,mode:'frame'};
 let first=0,end=0;
 function raw(a,b,z){out(a,b,z);stats.output++;if(a!==1023&&b!==1023)stats.outputCCX++;}
 function polarity(q,p){if(q!==1023&&O[q]!==p){raw(1023,1023,q);O[q]=p;}}
 function emit(i){const j=i%N;if(!live[j])return;const a=A[j],b=B[j],z=Z[j],p=P[j];polarity(a,p&1);polarity(b,p>>1&1);raw(a,b,z);live[j]=0;}
 function flush(){while(first<end)emit(first++);first=end=0;for(let q=0;q<1023;q++){if(O[q]!==F[q])raw(1023,1023,q);O[q]=F[q]=0;}stats.removed=stats.input-stats.output;stats.removedCCX=stats.inputCCX-stats.outputCCX;}
 function gate(a,b,z){
  if(z===1023||a===z||b===z||(a===b&&a!==1023))throw Error('peep alias');
  stats.input++;if(a!==1023&&b!==1023)stats.inputCCX++;
  if(a===1023&&b===1023){F[z]^=1;return;}
  if(a>b){const t=a;a=b;b=t;}
  let p=F[a]|F[b]<<1;
  if(end-first===window)emit(first++);
  for(let i=end-1;i>=first;i--){const j=i%N;if(!live[j])continue;const x=A[j],y=B[j],t=Z[j],r=P[j];
   if(z===t){
    if(a===x&&b===y){
     if(p===r){live[j]=0;stats.cancel++;return;}
     const d=p^r;
     if(merge&&(d===1||d===2)){
      live[j]=0;stats.merge++;
      if(d===1){a=b;b=1023;p=p>>1&1;}else{b=1023;p&=1;}
      if(a===1023){F[z]^=1;return;}
      continue;
     }
    }
    // Product XOR subset product: c*d XOR c = c*!d.
    if(false){
     let aa=-1,bb=-1,pp=0;
     if(b===1023&&y!==1023){if(a===x&&(p&1)===(r&1)){aa=x;bb=y;pp=r^2;}else if(a===y&&(p&1)===(r>>1&1)){aa=x;bb=y;pp=r^1;}}
     else if(y===1023&&b!==1023){if(x===a&&(r&1)===(p&1)){aa=a;bb=b;pp=p^2;}else if(x===b&&(r&1)===(p>>1&1)){aa=a;bb=b;pp=p^1;}}
     if(aa>=0&&writes[aa]!==stats.input&&writes[bb]!==stats.input){live[j]=0;stats.merge++;a=aa;b=bb;p=pp;continue;}
    }
   }
   if(t===a||t===b||z===x||z===y)break;
   writes[t]=stats.input;
  }
  const j=end++%N;A[j]=a;B[j]=b;Z[j]=z;P[j]=p;live[j]=1;
 }
 return {gate,flush,stats};
})(final.gate,{window:4096});
 const first=(function frameFactory(out,options={}){
 const stats={swaps:0,restoreSwaps:0,input:0,output:0,removed:0,removedCCX:0};
 const core=(function createPeep(out,{window=4096,mode='strict'}={}){
 if(!Number.isInteger(window)||window<1||!['strict','commute'].includes(mode))throw Error('peep config');
 const N=window+1,A=new Int32Array(N),B=new Int32Array(N),Z=new Int32Array(N),live=new Uint8Array(N);
 const stats={input:0,output:0,removed:0,removedCCX:0,window,mode};let first=0,end=0;
 function emit(i){const j=i%N;if(live[j]){out(A[j],B[j],Z[j]);live[j]=0;stats.output++;}}
 function flush(){while(first<end)emit(first++);first=end=0;}
 function gate(a,b,z){
  if(z===1023||a===z||b===z||(a===b&&a!==1023))throw Error('peep alias');
  stats.input++;if(end-first===window)emit(first++);
  let hit=-1;
  for(let i=end-1;i>=first;i--){const j=i%N;if(!live[j])continue;
   const x=A[j],y=B[j],t=Z[j];
   if(a===x&&b===y&&z===t){hit=j;break;}
   if(mode==='commute') {if(t===a||t===b||z===x||z===y)break;}
   else if(z===t||z===x||z===y||a!==1023&&(a===x||a===y||a===t)||b!==1023&&(b===x||b===y||b===t))break;
  }
  if(hit>=0){live[hit]=0;stats.removed+=2;if(a!==1023&&b!==1023)stats.removedCCX+=2;return;}
  const j=end++%N;A[j]=a;B[j]=b;Z[j]=z;live[j]=1;
 }
 return {gate,flush,stats};
})((a,b,z)=>{out(a,b,z);stats.output++;},options);
 const map=Int32Array.from({length:1024},(_,i)=>i),inv=Int32Array.from(map),pending=[];
 function send(g){core.gate(map[g[0]],map[g[1]],map[g[2]]);}
 function gate(a,b,z){
  stats.input++;
  if(a!==1023&&b===1023){b=a;a=1023;}
  pending.push([a,b,z]);
  if(pending.length===3){const [u,v,w]=pending;
   if(u[0]===1023&&v[0]===1023&&w[0]===1023&&u[1]!==1023&&v[1]===u[2]&&v[2]===u[1]&&u[1]===w[1]&&u[2]===w[2]){
    const x=u[1],y=u[2],p=map[x],q=map[y];map[x]=q;map[y]=p;inv[p]=y;inv[q]=x;pending.length=0;stats.swaps++;return;
   }
   send(pending.shift());
  }
 }
 function flush(){
  while(pending.length)send(pending.shift());
  for(let i=0;i<1023;i++)if(map[i]!==i){const j=map[i],other=inv[i];core.gate(1023,i,j);core.gate(1023,j,i);core.gate(1023,i,j);map[i]=i;map[other]=j;inv[i]=i;inv[j]=other;stats.restoreSwaps++;}
  core.flush();stats.removed=stats.input-stats.output;stats.removedCCX=core.stats.removedCCX;
 }
 return {gate,flush,stats};
})(frame.gate,{mode:'commute',window:4096});
 function gate(a,b,z){stats.input++;if(a!==1023&&b!==1023)stats.inputCCX++;first.gate(a,b,z);}
 function flush(){first.flush();frame.flush();final.flush();stats.removed=stats.input-stats.output;stats.removedCCX=stats.inputCCX-stats.outputCCX;}
 return {gate,flush,stats};
};
class PointFoldTape extends FoldTape{
    constructor(logical,l,output,d,y){
        super(logical,[],l.g);
        const original=output,peep=S1CreatePeep((a,b,z)=>original.out(a,b,z),{mode:'commute',window:4096});
        output=Object.create(original);output.out=peep.gate;this.s1Flush=peep.flush;
        for(const name of ['hmr','z'])output[name]=(...args)=>{peep.flush();const r=original[name](...args);peep.flush();return r;};
        output.cond=(mask,fn)=>{peep.flush();return original.cond(mask,()=>{fn();peep.flush();});};
        this.ids=this.ids.slice(0,-5);this.ids=this.ids.filter(q=>q<651||q>656);const b=l.bank.length,m=l.m;
        const map=[...d,2*m,...split(2*m+1,2*m+1+b),...y,...split(2*m+b+1,logical-6)];for(const q of [256,642,643,644,645,646,647,648,650,651]){const j=stageConfig.stages.upper.logical.indexOf(q);map[q>l.g?q-1:q]=j<0?undefined:stageConfig.stages.upper.physical[j];}map[649>l.g?648:649]=647;this.ids=this.ids.filter(q=>q!==650&&q!==651&&q!==647&&(![256,642,643,644,645,646,647,648,650,651].includes(q)||stageConfig.stages.upper.logical.includes(q)));
        if(new Set(map.filter(q=>q!==undefined)).size!==641+stageConfig.stages.upper.logical.length||map.filter(q=>q!==undefined).length!==641+stageConfig.stages.upper.logical.length)throw Error("point fold mapping");
        this.map=map;const wire=x=>{if(x===NONE)return NONE;if(map[x]===undefined)throw Error("upper used removed physical site "+x);return map[x];};
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
    }return [()=>t.s1Flush&&t.s1Flush(),...ops,()=>t.s1Flush&&t.s1Flush()];
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
    const stageClean=name=>{const x=stageConfig.stages[name];if(x.physical.some(q=>!clean.includes(q)))throw Error("occupied helper "+name);return x;};const fieldMap=(a,b,name)=>{const ids=[...a,...U,...Y,...b],cfg=stageClean(name);for(let i=640;i<657;i++)ids[i]=(i===648||i>=652)?-2:undefined;cfg.logical.forEach((q,j)=>ids[q]=cfg.physical[j]);return ids;};
    if(emitter){if(h!==128)throw Error("intrinsic factor width");emitter.forward(nativeSink(tape,fieldMap(small,other,"multiply")));}
    else each((st,j)=>{const k=get(st,small,j),y=get(st,Y,j);if(!k||get(st,U,j))throw Error("forward entry");put(st,rawR,k*y%p,j);put(st,rawZero,0n,j);});
    if(inverse){const im=fieldMap(other,small,"divide");if(extraEnable){im[648]=clean[16];tape.out(NONE,NONE,im[648]);}
        inverse(nativeSink(tape,im));if(extraEnable)tape.out(NONE,NONE,im[648]);}
    else each((st,j)=>{const k=get(st,other,j),q=get(st,rawR,j);if(!k||get(st,rawZero,j))throw Error("inverse entry");put(st,U,0n,j);put(st,Y,q*invMod(k,p)%p,j);});
    recode();if(emitter){
        const ids=new Array(657);for(let i=0;i<128;i++){ids[129-i]=R[i];ids[259-i]=V[i];ids[260+i]=U[i];}
        for(let i=0;i<256;i++)ids[389+i]=Y[i];ids[645]=-2;ids[651]=-2;ids[652]=-2;ids[653]=-2;ids[655]=-2;ids[656]=-2;let j=0;for(let i=0;i<ids.length;i++)if(ids[i]===undefined){const hcfg=stageClean("history"),ix=hcfg.logical.indexOf(i);if(ix>=0){ids[i]=hcfg.physical[ix];j++;}}
        if(j!==stageConfig.stages.history.logical.length)throw Error("configured history geometry");const sink=nativeSink(tape,ids);emitter.regenerate(chunk=>sink("packed",chunk));
    }else each((st,j)=>{const r=get(st,R,j),v=get(st,V,j);if(get(st,U,j))throw Error("dirty U at return");put(st,U,v===1n?0n:p*invMod(r%v,v)%v,j);});
    for(let i=0;i<U.length;i++)tape.cond(outer[i],()=>tape.z(U[i]));
};}
function shellWithFieldOracles(m,delta,rows,back,emitter=null,inverse=null,policy='random',extraEnable=false){
 const width=Math.max(2*m+4+16+Math.ceil((m+1)/16)+3,stageConfig.width+(extraEnable?1:0)),arith=new CoordinateArithmetic(m,delta),shiftY=Object.create(arith);
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
