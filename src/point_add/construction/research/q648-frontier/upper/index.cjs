'use strict';

// Adjacent controlled tail operations used to compute and erase each rank
// threshold separately. At the boundary their two marks XOR into an equality.
// Corrections for special rank encodings come from the frozen threshold emitter.
function rankBoundary(owner, tape, bits, low, target) {
    const terms = new Map();
    function toggle(pos, neg) {
        const key = pos.slice().sort((a,b)=>a-b).join(',') + '/' + neg.slice().sort((a,b)=>a-b).join(',');
        if (terms.has(key)) terms.delete(key);
        else terms.set(key, [pos.slice(),neg.slice()]);
    }
    const probe = Object.create(owner), capture = Object.create(tape);
    const raw = [];
    capture.frontierThreshold = (word, limit, controls, targets) => {
        if (word !== bits || controls.length || targets.length !== 1 || targets[0] !== target) throw Error('rank comparison ports');
        raw.push(limit);
    };
    probe.toggle = (t,pos,neg,dest) => {
        if(t!==capture||dest!==target)throw Error('rank correction ports');
        toggle(pos,neg);
    };
    probe.cnotList = (t,cs,word) => {
        if(t!==capture||word.length!==1||word[0]!==target)throw Error('rank constant ports');
        toggle(cs,[]);
    };
    probe.constBelow(capture,bits,BigInt(low),[],[target]);
    probe.constBelow(capture,bits,BigInt(low+1),[],[target]);
    if (raw.length) {
        if (raw.length!==2||raw[0]!==BigInt(low)||raw[1]!==BigInt(low+1))throw Error('rank boundary source');
        if (low<2**bits.length) {
            const pos=[],neg=[];
            bits.forEach((q,j)=>((low>>j)&1?pos:neg).push(q));
            toggle(pos,neg);
        }
    }
    for(const [pos,neg] of terms.values())owner.toggle(tape,pos,neg,target);
}

function rankSweep(owner, tape, tag, base, stop, target, complement, back, body) {
    if (stop<=base)return;
    const first=back?stop-1:base, last=back?base:stop-1, dir=back?-1:1;
    const edge=i=>{
        if(complement)tape.out(NONE,NONE,target);
        owner.constBelow(tape,tag,BigInt(i-base+1),[],[target]);
    };
    edge(first);
    for(let i=first;;i+=dir){
        body(i);
        if(i===last)break;
        rankBoundary(owner,tape,tag,Math.min(i,i+dir)-base+1,target);
    }
    edge(last);
}

function patch(source) {
    let s=source;
    function once(before, after){
        if(s.split(before).length!==2)throw Error('Q648 rank-sweep source mismatch: '+before.slice(0,64));
        s=s.replace(before,()=>after);
    }
    once('class Tape {',rankBoundary.toString()+'\n'+rankSweep.toString()+'\nclass Tape {');
    const cap='    constBelow(tape,word,limit,controls,targets) {';
    once(cap,cap+'\n        if(tape.frontierThreshold){tape.frontierThreshold(word,limit,controls,targets);return;}');
    const park=`const moving=rv=>stepList(split(base,this.r.length),rv,i=>{
            const a=D[i+this.h-1-base+(this.centeredFree?1:0)],b=this.r[i],mark=()=>this.constBelow(tape,tag,BigInt(i-base+1),[],[this.pick]);
            mark();this.permute(tape,[a,b],[b,a],[this.pick],rv);mark();
        });`;
    once(park,`const moving=rv=>rankSweep(this,tape,tag,base,this.r.length,this.pick,false,rv,i=>{
            const a=D[i+this.h-1-base+(this.centeredFree?1:0)],b=this.r[i];
            this.permute(tape,[a,b],[b,a],[this.pick],rv);
        });`);
    const extra=`const extra=rv=>stepList(split(base,this.r.length),rv,i=>{
            const z=[...D,this.r[i]],dest=z.slice(1).concat(z[0]);
            const mark=()=>{tape.out(NONE,NONE,this.take);this.constBelow(tape,tag,BigInt(i-base+1),[],[this.take]);};
            const ops=[mark,rr=>this.tailDigit(tape,layer,z,S,!rr),rr=>this.permute(tape,z,dest,[this.take],rr),mark];
            stepList(ops,rv,fn=>fn(rv));
        });`;
    once(extra,`const extra=rv=>rankSweep(this,tape,tag,base,this.r.length,this.take,true,rv,i=>{
            const z=[...D,this.r[i]],dest=z.slice(1).concat(z[0]);
            const ops=[rr=>this.tailDigit(tape,layer,z,S,!rr),rr=>this.permute(tape,z,dest,[this.take],rr)];
            stepList(ops,rv,fn=>fn(rv));
        });`);
    return s;
}
module.exports={patch,rankBoundary,rankSweep};
