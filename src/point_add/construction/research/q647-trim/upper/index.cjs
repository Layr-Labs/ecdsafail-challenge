'use strict';
function replace(s,a,b,n=1){const parts=s.split(a);if(parts.length!==n+1)throw Error('Q647 probe source '+a);return parts.join(b);}

// A U34 low bit is its payload if the earlier tag bits contain a zero.
// Before the first zero, all outgoing ripple gates cancel. The first zero
// therefore stays fixed, as does every prefix test used in the ripple.
function prefixAdder(owner,tape,a,b,high,cond,rv){
    const tag=owner.u40Tag,h=owner.u34Low,none=1023,base=-1250;
    const qs=tag.slice(0,h+1),flag=owner.u34Unary?[]:tag.slice(h+1);
    const virtual=Array.from({length:h},(_,i)=>base-i),low=x=>x<=base&&x>base-h,wire=x=>low(x)?qs[base-x+1]:x;
    const plain=cond===null,occ=Array(h).fill(0),proxy=Object.create(tape);
    proxy.out=(x,y,z)=>{
        const vx=low(x),vy=low(y),vz=low(z);
        if(!vx&&!vy&&!vz){tape.out(x,y,z);return;}
        if(Number(vx)+Number(vy)!==1)throw Error('Q647 unexpected prefix ripple gate');
        const i=base-(vx?x:y),other=vx?y:x,target=wire(z),bits=[qs[i+1]];
        if(other!==none)bits.push(other);
        let permanent=z===a[h];
        if(!permanent&&!vz){
            if(b[i]!==z)throw Error('Q647 prefix ripple output');
            if(x===none){occ[i]++;permanent=plain&&(i===0||occ[i]===2);}else permanent=true;
        }
        if(permanent)bits.push(...flag);
        const pivot=owner.q647Pivot,split=owner.q647Split;
        const prefix=pivot!==null&&pivot!==undefined&&i+1>=split?[pivot,...qs.slice(split,i+1)]:qs.slice(0,i+1);
        owner.toggle(tape,bits,[],target);owner.toggle(tape,bits.concat(prefix),[],target);
    };
    MixedArithmetic.prototype.nrAdder.call(owner,proxy,virtual.concat(a.slice(h)),b,high,cond,rv);
    for(let i=0;i<h;i++)if(occ[i]!==2*(i>0)+Number(plain))throw Error('Q647 prefix occurrence');
}
function prefixWork(owner,tape,fn){
    const loan=owner.q647Loan,tag=owner.u40Tag,h=owner.u34Low,local=Object.create(owner),protectedTape=Object.create(tape);
    local.q647Pivot=null;local.q647Split=0;
    const blocked=loan===null||loan===undefined?tag:[...tag,loan];
    protectedTape.loan=(used,n)=>tape.loan(used.concat(blocked),n);
    if(loan===null||loan===undefined){fn(local,protectedTape);return;}
    const split=Math.max(1,Math.ceil(h/2)),bits=tag.slice(0,split);
    local.q647Pivot=loan;local.q647Split=split;
    if(tape.q647Observe)tape.q647Observe(loan,owner,'before');
    owner.toggle(protectedTape,bits,[],loan);fn(local,protectedTape);owner.toggle(protectedTape,bits,[],loan);
    if(tape.q647Observe)tape.q647Observe(loan,owner,'after');
}
function prefixMixed(owner,tape,q,v,rem,back){
    prefixWork(owner,tape,(local,tp)=>{
        local.nrAdder=(t,a,b,h,c,rv)=>prefixAdder(local,t,a,b,h,c,rv);
        local.unguardedMixed(tp,q,v,rem,back);
    });
}
function prefixAdd(owner,tape,a,d,back){prefixWork(owner,tape,(local,tp)=>prefixAdder(local,tp,a,d,null,null,back));}
function patch(s,mode='joint'){
    if(mode==='joint')return require('./dense.cjs').extend(patch(s,'loan'));
    if(!['prefix','loan'].includes(mode))throw Error('Q647 probe mode');
    s=replace(s,'class Tape {',[prefixAdder,prefixWork,prefixMixed,prefixAdd].map(f=>f.toString()).join('\n')+'\nclass Tape {');
    const begin=s.indexOf('    u34UnarySign(inputTape,target){'),end=s.indexOf('    u36',begin);
    if(begin<0||end<begin)throw Error('U34 probe window');
    let cut=s.slice(begin,end);
    const add='rv=>H.u6VirtualTape(tape).add(a,D,[],this.carry,rv)';
    cut=replace(cut,add,'rv=>prefixAdd(H,tape,a,D,rv)',2);
    const bracket='stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);stepList(seq,true,fn=>fn(true));';
    const known=mode==='loan'?'this.u5PhaseHost!==target&&target===this.dv[0]&&(this.measureTarget===target||!this.probeBack)&&!tag.includes(target)':'false';
    cut=replace(cut,bracket,`const q647Known=${known};H.q647Loan=q647Known?target:null;stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);H.q647Loan=q647Known&&this.measureTarget===target?target:null;stepList(seq,true,fn=>fn(true));`,2);
    s=s.slice(0,begin)+cut+s.slice(end);
    const mix='    mixed(tape,q,v,rem,controls,back){\n      super.mixed(this.u40Tag';
    return replace(s,mix,`    mixed(tape,q,v,rem,controls,back){\n      if(this.u34Low&&v[0]===this.u40Low&&!controls.length){prefixMixed(this,tape,q,v,rem,back);return;}\n      super.mixed(this.u40Tag`);
}
module.exports={patch};
