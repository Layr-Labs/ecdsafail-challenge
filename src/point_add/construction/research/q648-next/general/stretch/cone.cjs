'use strict';
// Gate IDs are the fixed-enable FoldTape's native lowered IDs. Restore the
// original sink before publishing a partially reduced or unchanged bracket.
function witnessCone(fold,left,deposit,right){
    const e=1023,Z=1073741824,encode=(a,b,t)=>a*1048576+b*1024+t;
    const oldG=fold.physical.out,oldZ=fold.z,oldH=fold.hmr,oldC=fold.cond;
    const chunks=[[],[],[]];let current=chunks[0];
    fold.physical.out=(a,b,t)=>{current.push(encode(a,b,t));};
    fold.z=q=>{current.push(Z+q);};
    fold.hmr=fold.cond=()=>{throw Error('measurement inside witness cone');};
    try{left();current=chunks[1];deposit();current=chunks[2];right();}
    finally{fold.physical.out=oldG;fold.z=oldZ;fold.hmr=oldH;fold.cond=oldC;}
    const [L,M,R]=chunks,support=new Uint8Array(1024),written=new Uint8Array(1024);
    const decode=q=>q>fold.one?q-1:q,read=gate=>{
        if(gate>=Z){support[decode(gate-Z)]=1;return;}
        const a=gate>>>20,b=gate>>>10&1023,t=gate&1023;
        support[t]=1;written[t]=1;if(a!==e)support[a]=1;if(b!==e)support[b]=1;
    };
    const emit=gate=>{if(gate>=Z)oldZ(gate-Z);else oldG(gate>>>20,gate>>>10&1023,gate&1023);};
    for(const gate of M)read(gate);
    let i=L.length-1,j=0,saved=0,savedCCX=0;
    // The short virtual carry routine changes a few target writes between
    // the two halves. Keep the unmatched center intact and continue only
    // through exact gate pairs.
    const commutes=(a,b)=>{
        if(a>=Z||b>=Z)return false;
        const at=a&1023,bt=b&1023;
        return at!==(b>>>20)&&at!==(b>>>10&1023)&&bt!==(a>>>20)&&bt!==(a>>>10&1023);
    };
    const bring=(rows,pos,dir,want)=>{
        if(want>=Z)return false;
        for(let u=pos,v=0;u>=0&&u<rows.length&&v<384;u+=dir,v++){
            const op=rows[u];
            if(op===want){
                for(let z=u;z!==pos;z-=dir)rows[z]=rows[z-dir];rows[pos]=want;return true;
            }
            if(!commutes(op,want))return false;
        }
        return false;
    };
    for(;i>=0&&j<R.length;i--,j++){
        if(L[i]!==R[j]&&!bring(R,j,1,L[i])&&!bring(L,i,-1,R[j]))break;
        const g=L[i];if(g>=Z)break;
        const a=g>>>20,b=g>>>10&1023,t=g&1023;
        if(!support[t]&&!written[a]&&!written[b]){L[i]=R[j]=-1;saved+=2;if(a!==e)savedCCX+=2;continue;}
        support[t]=1;if(a!==e)support[a]=1;if(b!==e)support[b]=1;
        if(written[a]||written[b])written[t]=1;
    }
    fold.q648ConeAudit?.({saved,savedCCX,left:L.length,right:R.length,middle:M.length,paired:j,
        leftEdge:L.slice(Math.max(0,i-12),i+1).reverse(),rightEdge:R.slice(j,j+13)});
    for(const part of chunks)for(const gate of part)if(gate>=0)emit(gate);
}
function patch(s){
    const add=(old,change,n=1)=>{const chunks=s.split(old);if(chunks.length!==n+1)throw Error('witness cone anchor '+old);s=chunks.join(change);};
    add('class Tape {',witnessCone.toString()+'\nclass Tape {');
    const hook='this.cond=(cond,fn)=>output.cond(cond,fn);this.hist=new Map();';
    add(hook,hook+'this.q648Cone=(l,m,r)=>witnessCone(this,l,m,r);');
    const ordinary='stepList(pre,false,fn=>fn(false));\n            phaseDeposit(this,tape,this.dv[0],()=>this.toggle(tape,ctrl,[T.at(-1)],this.dv[0]));\n            stepList(pre,true,fn=>fn(true));';
    add(ordinary,`if(tape.q648Cone){tape.q648Cone(()=>stepList(pre,false,fn=>fn(false)),()=>phaseDeposit(this,tape,this.dv[0],()=>this.toggle(tape,ctrl,[T.at(-1)],this.dv[0])),()=>stepList(pre,true,fn=>fn(true)));}else{${ordinary}}`);
    const virt='stepList(pre,false,fn=>fn(false));\n      if(phase)tape.z(target);\n      deposit=phase;\n      stepList(pre,true,fn=>fn(true));';
    add(virt,`if(tape.q648Cone){tape.q648Cone(()=>stepList(pre,false,fn=>fn(false)),()=>{if(phase)tape.z(target);},()=>{deposit=phase;stepList(pre,true,fn=>fn(true));});}else{${virt}}`);
    return s;
}
module.exports={witnessCone,patch};
