'use strict';
const {Values}=require('../q651-symbolic/values.cjs');
const N=1023,WINDOW=256;
function install(tape,cleanFrom){
    const v=new Values(tape.n,cleanFrom),raw=tape.out.bind(tape),measure=tape.hmr.bind(tape),
        conditional=tape.cond.bind(tape),classical=tape.classical.bind(tape);
    // The stock writer emits HMR, conditioned CZ and a reset of one reusable
    // classical bit. The private all-wire simulator explicitly applies their
    // action, including the condition stack and the measurement phase.
    const erase=tape.eraseProduct?tape.eraseProduct.bind(tape):(a,b,t)=>{
        const id=tape.measured++,policy=tape.policy;
        for(let i=0;i<tape.batches.length;i++){
            const w=tape.batches[i],on=tape.valid[i]&(tape.current===null?-1:tape.current[i]);
            const bits=policy==='zero'?0:policy==='one'?-1:typeof policy==='number'?(id===policy?-1:0):tape.draw();
            const feedback=on&bits;
            tape.phase[i]=(tape.phase[i]^((w[t]^(w[a]&w[b]))&feedback))>>>0;
            w[t]&=~on;
        }
    };
    const buf=new Uint32Array(WINDOW),group=new Int16Array(WINDOW),last=new Int16Array(WINDOW),
        size=new Int16Array(WINDOW),slot=new Int16Array(WINDOW),pre=new Int16Array(WINDOW),ref=new Int16Array(WINDOW);
    const nextUse=new Int16Array(tape.n),nextWrite=new Int16Array(tape.n),lastWrite=new Int16Array(tape.n),
        nextA=new Int16Array(WINDOW),nextB=new Int16Array(WINDOW),nextT=new Int16Array(WINDOW),nextOut=new Int16Array(WINDOW);
    const table=new Uint32Array(1<<20),owner=new Uint8Array(tape.n),pin=new Uint16Array(tape.n);
    let used=0,epoch=1,cursor=0;
    const capStats={opened:0,paired:0,regenerated:0,cleanUsed:0,duplicateUsed:0};
    function gate(a,b,t){
        if(a!==N&&b!==N&&v.w[t]>1){
            v.room();const product=v.and(v.w[a],v.w[b]);
            if(product===v.w[t]&&v.other(product,t)<0){erase(a,b,t);v.put(t,0);capStats.regenerated++;return;}
        }
        v.gate(a,b,t,raw);
    }
    function acquire(i,a,b,t){
        v.room();const value=v.and(v.w[a],v.w[b]);if(value<2||v.other(value,t)>=0)return;
        const end=last[i];let q=-1,r=-1,flip=0;
        for(let w=v.rep[0];w>=0;w=v.next[w]){
            if(nextUse[w]>end&&!pin[w]&&!owner[w]){q=w;flip=v.w[w];break;}
        }
        if(q<0){
            for(let j=0;j<32;j++){
                if(++cursor===tape.n)cursor=0;
                if(nextUse[cursor]<=end||pin[cursor]||owner[cursor])continue;
                const h=v.other(v.w[cursor],cursor);
                if(h<0||owner[h]||nextWrite[h]<=end)continue;
                q=cursor;r=h;flip=(v.w[q]^v.w[r])&1;break;
            }
        }
        if(q<0)return;
        if(r>=0){pin[r]++;gate(N,r,q);capStats.duplicateUsed++;}else capStats.cleanUsed++;
        if(flip)gate(N,N,q);
        if(v.w[q]!==0)throw Error('uncleared product scratch');
        gate(a,b,q);slot[i]=q;ref[i]=r;pre[i]=flip;owner[q]=1;capStats.opened++;
    }
    function flush(){
        if(!used)return;
        if(epoch+used>0xffffff00){table.fill(0);epoch=1;}
        lastWrite.fill(-1);slot.fill(-1,0,used);size.fill(0,0,used);
        for(let i=0;i<used;i++){
            const word=buf[i],a=word>>>20,b=word>>>10&N,t=word&N;
            if(b!==N){
                const key=(a<<10)|b,j=table[key]-epoch;
                const first=j>=0&&lastWrite[a]<=j&&lastWrite[b]<=j?group[j]:i;
                group[i]=first;size[first]++;last[first]=i;table[key]=epoch+i;
            }
            lastWrite[t]=i;
        }
        epoch+=used;
        nextUse.fill(used);nextWrite.fill(used);
        for(let i=used-1;i>=0;i--){
            const word=buf[i],a=word>>>20,b=word>>>10&N,t=word&N;
            nextT[i]=nextUse[t];nextUse[t]=i;nextOut[i]=nextWrite[t];nextWrite[t]=i;
            if(a!==N){nextA[i]=nextUse[a];nextUse[a]=i;}
            if(b!==N){nextB[i]=nextUse[b];nextUse[b]=i;}
        }
        for(let i=0;i<used;i++){
            const word=buf[i],a=word>>>20,b=word>>>10&N,t=word&N;
            if(b===N)gate(N,a,t);
            else{
                const f=group[i];
                if(f===i&&size[f]>1)acquire(f,a,b,t);
                const q=slot[f];
                if(q<0)gate(a,b,t);
                else{
                    gate(N,q,t);capStats.paired++;
                    if(last[f]===i){
                        erase(a,b,q);v.put(q,0);
                        if(pre[f])gate(N,N,q);
                        const r=ref[f];if(r>=0){gate(N,r,q);pin[r]--;}
                        owner[q]=0;
                    }
                }
            }
            nextUse[t]=nextT[i];nextWrite[t]=nextOut[i];
            if(a!==N)nextUse[a]=nextA[i];if(b!==N)nextUse[b]=nextB[i];
        }
        used=0;
    }
    tape.out=(a,b,t)=>{
        if(a>b)[a,b]=[b,a];buf[used++]=(a<<20)|(b<<10)|t;if(used===WINDOW)flush();
    };
    tape.hmr=q=>{flush();const result=measure(q);v.put(q,0);return result;};
    tape.cond=(c,fn)=>{flush();return conditional(c,()=>{v.push();try{return fn();}finally{flush();v.pop();}});};
    for(const name of ['z','cz'])if(tape[name]){
        const f=tape[name].bind(tape);tape[name]=(...args)=>{flush();return f(...args);};
    }
    tape.classical=(key,i,c,t,views)=>{
        flush();if(c!==null&&v.w[c]===0)return;
        classical(key,i,c,t,views);v.unknown(t);
    };
    flush.stats=capStats;return flush;
}
module.exports={install};
