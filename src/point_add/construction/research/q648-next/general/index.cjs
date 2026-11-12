'use strict';
function reflectMinusOne(owner,tape,word,controls,back,mode){
    // The joined map is w -> p-1-w modulo 2^n, hence it is its own inverse.
    const n=word.length,flag=owner.carry;
    if(owner.fieldBits!==256||owner.delta!==4294968273n||word.includes(flag)||controls.includes(flag))throw Error('Q648 joined reflection domain');
    owner.cnotList(tape,controls,word);
    if(n>256)owner.inc(tape,word.slice(256),controls,false);
    const signed=(w,cs)=>{
        for(const [bit,sub] of [[0,true],[4,false],[5,false],[10,true],[32,true]]){
            if(bit<w.length)owner.inc(tape,w.slice(bit),cs,sub);
        }
    };
    if(mode==='sparse'){signed(word,controls);return;}
    const lo=word.slice(0,33),high=word.slice(33);
    tape.q648ReflectAudit?.(flag,controls,owner);
    // The top high word loses one exactly when the 33-bit low word borrows.
    // Read the predicate before mutating the low bits, then erase it.
    owner.constBelow(tape,lo,owner.delta,controls,[flag]);
    owner.inc(tape,high,[flag],true);
    owner.constBelow(tape,lo,owner.delta,controls,[flag]);
    signed(lo,controls);
    tape.q648ReflectAudit?.(flag,controls,owner);
}
function patch(source,mode='all'){
    if(!['split','sparse','tail','both','all'].includes(mode))throw Error('Q648 general optimization '+mode);
    const anchor='rv=>this.reflect(tape,word,g,rv),rv=>this.inc(tape,word,g,!rv)';
    if(source.split(anchor).length!==3||source.split('class Tape {').length!==2)throw Error('Q648 joined reflection anchors');
    let result=source;
    if(mode!=='tail'){
        result=result.replace('class Tape {',()=>reflectMinusOne.toString()+'\nclass Tape {');
        result=result.split(anchor).join('rv=>reflectMinusOne(this,tape,word,g,rv,'+JSON.stringify(mode==='sparse'?'sparse':'split')+')');
    }
    if(mode==='tail'||mode==='both'||mode==='all'){
        const line='const tp=cut>=(this.u9Three?(this.u9H||3):2)?tape:this.u6VirtualTape(tape);';
        if(result.split(line).length!==2)throw Error('Q648 sign tail anchor');
        result=result.replace(line,()=>`const retired=this.k<=96&&this.u5PhaseHost===644&&this.measureTarget===644?644:null;
        const loanedFlag=this.q649Loan??retired;
        if(${mode==='all'?'true':'this.u9H&&cut>=this.u9H'}&&loanedFlag!=null&&![...S,...z,...this.u40Tag,this.take].includes(loanedFlag)){
            tape.q648TailAudit?.(loanedFlag,this.take,this,loanedFlag===retired);
            const L=Object.create(layer);L.pick=loanedFlag;
            const inner=cut>=(this.u9Three?(this.u9H||3):2)?tape:this.u6VirtualTape(tape);
            MixedArithmetic.prototype.digit.call(L,inner,Z,V,[this.take],back);
            return;
        }
        `+line);
    }
    return result;
}
module.exports={patch,reflectMinusOne};
