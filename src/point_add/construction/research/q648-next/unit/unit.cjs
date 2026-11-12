'use strict';

// The shared product opens a pair of Takahashi ripple gates around an
// unchanged AND. Move that product to a clean site so the output compiler
// can replace its cleanup with a measurement and a phase correction.
function retainedUnitAdder(tape,A,B,H,P,back){
    const eligible=this.unitProduct==='predicate'?[this.carry,this.norm]:
        this.unitProduct==='body'?[this.carry,this.pick,...(this.unitShapeAvailable?[this.shape]:[]),this.spare]:[];
    const sites=eligible.filter(q=>!A.includes(q)&&!B.includes(q)&&q!==H&&q!==P);
    if(new Set(sites).size!==sites.length)throw Error('Live unit-AND site collision');
    const count=Math.min(sites.length,A.length-1),none=1023;
    if(!count)return MixedArithmetic.prototype.nrAdder.call(this,tape,A,B,H,P,back);
    const tp=Object.create(tape),hits=Array(count).fill(0);
    tp.out=(u,v,target)=>{
        const bit=A.indexOf(target)-1;
        if(bit<0||bit>=count||!((u===A[bit]&&v===B[bit])||(u===B[bit]&&v===A[bit]))){tape.out(u,v,target);return;}
        const work=sites[bit];
        if(hits[bit]++===0){tape.out(u,v,work);tape.out(none,work,target);}
        else{tape.out(none,work,target);tape.out(u,v,work);}
    };
    MixedArithmetic.prototype.nrAdder.call(this,tp,A,B,H,P,back);
    if(hits.some(h=>h!==2))throw Error('Unpaired unit ripple AND');
}

function unitThreshold(owner,s=0){
    const base=1n<<BigInt(s),capacity=(1n<<BigInt(owner.k+1))-base*(base-1n),ceiling=1n<<BigInt(owner.m);
    if(ceiling-owner.prime<=capacity)return {low:owner.m,w:1n};
    let low=capacity.toString(2).length-1;
    const shift=BigInt(low),limit=((owner.prime>>shift)+1n)<<shift;
    let w=limit>>shift;
    while((w&1n)===0n){w>>=1n;low++;}
    return {low,w};
}

function coinProduct(owner,tape,r,a,c,back,low,s=0){
    if(!back){
        if(owner.unitCone)throw Error('Unclosed unit product cone');
        const ops=[],trace=Object.create(tape),rem=r.slice(0,s).concat(c.slice(s)),word=r.slice(s).concat(rem),live=new Uint8Array(tape.n),none=1023;
        trace.out=(x,y,z)=>ops.push((x<<20)|(y<<10)|z);
        if(s)owner.mixed(trace,r.slice(0,s),a.slice(s),c.slice(s),[],false);
        owner.mixed(trace,r.slice(s),a,rem,[],false);
        for(const q of word.slice(low-s))live[q]=1;
        const selected=[];
        for(let i=ops.length-1;i>=0;i--){
            const op=ops[i],z=op&none;
            if(!live[z])continue;
            selected.push(op);const y=op>>>10&none,x=op>>>20;
            if(y!==none)live[y]=1;if(x!==none)live[x]=1;
        }
        owner.unitCone=selected;
    }
    const rows=owner.unitCone;
    if(!rows)throw Error('Missing active unit product cone');
    for(let j=0;j<rows.length;j++){
        const row=rows[back?j:rows.length-1-j];tape.out(row>>>20,row>>>10&1023,row&1023);
    }
    if(back)owner.unitCone=null;
}

function patch(s,mode='cone'){
    if(mode==='actual'||mode==='raw')return s;
    if(!['retained','gap','cone','split'].includes(mode))throw Error('Unit mode '+mode);
    const cls='class EarlyUnit extends UnitPreparation {',begin=s.indexOf(cls),end=s.indexOf('\nclass ',begin+cls.length);
    if(begin<0||end<begin)throw Error('Refined unit class');
    let cut=s.slice(begin,end);
    const replace=(a,b,n=1)=>{if(cut.split(a).length!==n+1)throw Error('Unit anchor '+a);cut=cut.split(a).join(b);};
    const six=cut.includes('U28 unit shape used');
    if(mode!=='retained'){
        const useCone=mode==='cone'||mode==='split';
        replace('const mark=()=>phaseDeposit', `const s=${mode==='split'?'this.k>>1':'0'},threshold=unitThreshold(this,s),watch=r.slice(s).concat(r.slice(0,s),c.slice(s)).slice(threshold.low-s);\n        const mark=()=>phaseDeposit`);
        replace('this.constBelow(tape,[...r,...c],this.prime+1n,active,[this.fired]);',`if(threshold.w===1n)this.toggle(tape,active,watch,this.fired);else this.constBelow(tape,watch,threshold.w,active,[this.fired]);`);
        replace('rv=>this.inc(tape,c,[],!rv),','');replace('rv=>this.inc(tape,c,[],rv),','');
        if(useCone){
            replace('this.mixed(tape,r,a,c,[],rv)','coinProduct(this,tape,r,a,c,rv,threshold.low,s)');
            replace('this.mixed(tape,r,a,c,[],!rv)','coinProduct(this,tape,r,a,c,!rv,threshold.low,s)');
        }
        return s.slice(0,begin)+unitThreshold.toString()+'\n'+(useCone?coinProduct.toString()+'\n':'')+cut+s.slice(end);
    }
    replace(cls,cls+`\n    nrAdder(t,A,B,H,P,back){return retainedUnitAdder.call(this,t,A,B,H,P,back);}\n    unitAndMixed(t,r,v,d,back,kind){const local=Object.create(this);local.unitProduct=kind;local.unitShapeAvailable=${!six};return local.mixed(t,r,v,d,[],back);}`);
    replace('this.mixed(tape,this.r,v,d,[],rv)','this.unitAndMixed(tape,this.r,v,d,rv,\'body\')');
    replace('this.mixed(tape,this.r,v,d,[],!rv)','this.unitAndMixed(tape,this.r,v,d,!rv,\'body\')');
    replace('this.mixed(tape,r,a,c,[],rv)','this.unitAndMixed(tape,r,a,c,rv,\'predicate\')');
    replace('this.mixed(tape,r,a,c,[],!rv)','this.unitAndMixed(tape,r,a,c,!rv,\'predicate\')');
    return s.slice(0,begin)+retainedUnitAdder.toString()+'\n'+cut+s.slice(end);
}
module.exports={patch};
