'use strict';
function refineProbeCode(source){
    const replace=(from,to)=>{if(source.split(from).length!==2)throw Error('probe code anchor '+from);source=source.replace(from,()=>to);};
    // In the selected active probe, ranks range over [0,free]; the unique
    // exceptional low bit is encoded as the all-ones code. The top prefix
    // through the first zero of free distinguishes that code from every rank.
    replace('H.u40Tag[1]=S[0];',
        'H.u40Tag[1]=S[0];let shift=H.u40Tag.length-1;while(shift>0&&(free&(1<<shift)))shift--;H.u40Exceptional=H.u40Tag.slice(shift);');
    replace('const controls=[...tag,...cs.filter(q=>q!==low)];',
        'const controls=[...H.u40Exceptional,...cs.filter(q=>q!==low)];');
    replace('tape.mc(controls,t,tape.loan([...controls,t],Math.max(1,controls.length-2)));',
        'tape.mc(controls,t,tape.loan([...tag,...controls,t],Math.max(1,controls.length-2)));');
    replace('for(const t of targets)this.toggle(tape,[...controls,...word],[],t);',
        'for(const t of targets)this.toggle(tape,[...controls,...this.u40Exceptional],[],t);');
    replace('rv=>this.permute(tape,word,src,tag,rv)];',
        'rv=>this.permute(tape,word,src,this.u40Exceptional,rv)];');
    const start='      const recode=()=>{\n        const ports=[...tag,S[0]]';
    const a=source.indexOf(start),b=source.indexOf('\n      const lease=rv=>',a);
    if(a<0||b<a||source.indexOf(start,a+1)>=0)throw Error('probe recode window');
    source=source.slice(0,a)+`      const recode=()=>{
        // Conjugating the all-ones control by the low-bit fanout swaps
        // exactly (rank=0,low=1) and (rank=all-ones,low=0).
        for(const q of tag)tape.out(NONE,S[0],q);
        this.toggle(tape,tag,[],S[0]);
        for(const q of tag)tape.out(NONE,S[0],q);
      };`+source.slice(b);
    return source;
}
module.exports={refineProbeCode};
