
function runRound(m,delta,logical,inputs,seed,policy='random'){
    const l=new UnguardedGeneral(m,delta,0,logical),rng=rand(seed),g=[l.g];
    const A0=[],B0=[],physicalWidth=logical-1,physical=word=>word.map(q=>q>l.g?q-1:q);
    const qR=physical(l.r),qV=physical(l.bank),qSig=physical([l.sig]),data=physical(l.big),work=physical(l.aux);
    for(let off=0;off<inputs.length;off+=32){
        const a=Uint32Array.from({length:physicalWidth},rng),b=a.slice();
        for(let lane=0;lane<32;lane++){
            const input=inputs[(off+lane)%inputs.length],res=ordinaryPath(m,delta,input);
            for(const ar of[a,b]){put(ar,work,0n,lane);put(ar,data,0n,lane);}
            put(a,qR,input,lane);put(a,qV,0n,lane);put(a,qSig,0n,lane);
            put(b,data.slice(0,m/2),res.r,lane);put(b,data.slice(m/2,m),res.u,lane);put(b,qV,res.v,lane);put(b,qSig,BigInt(res.sign),lane);
        }
        A0.push(a);B0.push(b);
    }
    const st=A0.map(x=>x.slice()),tape=new MeasuredFold(logical,st,l.g,seed^0x872eadb1,policy);tape.hist=new Map();
    const p=(1n<<BigInt(m))-BigInt(delta),ops=[];
    const classify=()=>{l.toggle(tape,g,[],l.sig);l.constBelow(tape,l.r,(p+1n)/2n,g,[l.sig]);};
    ops.push(classify,rv=>l.reflect(tape,l.r,[l.g,l.sig],rv),()=>l.toggle(tape,g,[],l.bank[0]));
    for(let k=0;k<m/2;k++){
        const row=new UnguardedGeneral(m,delta,k,logical);
        if(globalThis.__CAP)ops.push(rv=>{if(!rv)globalThis.__CAP(tape,row,k,'entry');});
        if(k>0&&k<m/2-1){const unit=new EarlyUnit(m,delta,k,logical);ops.push(rv=>{globalThis.__K="u"+k;unit.emit(tape,rv);});}
        ops.push(rv=>{if(globalThis.__CAP&&!rv)globalThis.__CAP(tape,row,k,'mid');globalThis.__K=k;row.emit(tape,rv);},rv=>row.permute(tape,[row.r.at(-1),...row.u],[...row.u,row.r.at(-1)],g,rv));
    }
    const t=tape.physical,c0=t.count.slice();
    stepList(ops,false,fn=>fn(false));
    const fwd=t.count.map((v,i)=>v-c0[i]);
    for(let i=0;i<st.length;i++)for(let j=0;j<physicalWidth;j++)if(st[i][j]!==B0[i][j])throw Error("round forward data "+[i,j]);
    stepList(ops,true,fn=>fn(true));
    const rev=t.count.map((v,i)=>v-c0[i]-fwd[i]);
    for(let i=0;i<st.length;i++)for(let j=0;j<physicalWidth;j++)if(st[i][j]!==A0[i][j])throw Error("round back data "+[i,j]);
    if(t.phase.some(x=>x!==0))throw Error("round phase");if(tape.hist.size)throw Error("round history left");
    return {fwdOps:fwd[0]+fwd[1]+fwd[2],revOps:rev[0]+rev[1]+rev[2],fwd,rev,lanes:32*st.length,hmr:t.measured,sig:t.sig.toString(16)};
}
