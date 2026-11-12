'use strict';

// Same insertion ages, raw control order, and cancellation choice as S1.
// Each access list stores its nearest older insertion. Tombstones are skipped
// on demand and timestamps below the live ring cannot reappear.
function createPeep(out, {window=4096,mode='commute'}={}) {
    if(!Number.isInteger(window)||window<1||!['strict','commute'].includes(mode))throw Error('peep config');
    const n=window+1,A=new Int32Array(n),B=new Int32Array(n),Z=new Int32Array(n),live=new Uint8Array(n);
    const prevA=new Float64Array(n),prevB=new Float64Array(n),prevW=new Float64Array(n),prevKey=new Float64Array(n);
    const reader=new Float64Array(1024),writer=new Float64Array(1024),keys=new Map();
    const stats={input:0,output:0,removed:0,removedCCX:0,window,mode};
    const key=(a,b,z)=>a*1048576+b*1024+z;
    let first=1,end=1;
    function read(q){
        let p=reader[q];
        while(p>=first&&!live[p%n]){const j=p%n;p=A[j]===q?prevA[j]:prevB[j];}
        return reader[q]=p<first?0:p;
    }
    function write(q){
        let p=writer[q];
        while(p>=first&&!live[p%n])p=prevW[p%n];
        return writer[q]=p<first?0:p;
    }
    function unlink(p){
        const j=p%n,k=key(A[j],B[j],Z[j]);live[j]=0;
        if(keys.get(k)!==p)return;
        let prev=prevKey[j];
        while(prev>=first&&!live[prev%n])prev=prevKey[prev%n];
        if(prev>=first)keys.set(k,prev);else keys.delete(k);
    }
    function emit(i){const j=i%n;if(live[j]){out(A[j],B[j],Z[j]);unlink(i);stats.output++;}}
    function flush(){while(first<end)emit(first++);first=end=1;reader.fill(0);writer.fill(0);keys.clear();}
    function gate(a,b,z){
        if(z===1023||a===z||b===z||(a===b&&a!==1023))throw Error('peep alias');
        stats.input++;if(end-first===window)emit(first++);
        const k=key(a,b,z),p=keys.get(k);
        if(p!==undefined){
            let last=Math.max(write(a),write(b),read(z));
            if(mode==='strict')last=Math.max(last,write(z),read(a),read(b));
            if(p>=last){unlink(p);stats.removed+=2;if(a!==1023&&b!==1023)stats.removedCCX+=2;return;}
        }
        const j=end%n;A[j]=a;B[j]=b;Z[j]=z;live[j]=1;
        prevW[j]=writer[z];writer[z]=end;prevKey[j]=p||0;keys.set(k,end);
        if(a!==1023){prevA[j]=reader[a];reader[a]=end;}
        if(b!==1023){prevB[j]=reader[b];reader[b]=end;}
        end++;
    }
    function pending(){const gates=[];for(let p=first;p<end;p++){const j=p%n;if(live[j])gates.push([A[j],B[j],Z[j]]);}return gates;}
    return {gate,flush,stats,pending};
}

function install(owner) {
    const fs=require('node:fs'),path=require('node:path'),Module=require('node:module');
    for(const name of ['m6-peep.cjs','d14-peep.cjs','r6-peep.cjs','u-peep-s1.cjs']){
        const file=require.resolve(path.join(owner,name)),original=fs.readFileSync(file,'utf8');
        const a=original.indexOf('function createPeep('),b=original.indexOf('function wrapSparse(',a);
        if(a<0||b<0)throw Error('Q649 compiler window '+name);
        const rebuilt=new Module(file,module);rebuilt.filename=file;rebuilt.paths=Module._nodeModulePaths(owner);
        rebuilt._compile(original.slice(0,a)+createPeep.toString()+'\n'+original.slice(b),file);
        require.cache[file]=rebuilt;
    }
}
module.exports={createPeep,install};
