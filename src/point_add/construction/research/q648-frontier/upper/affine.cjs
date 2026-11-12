'use strict';

// The affine representation supplies indicators for <, > and equality in
// exactly the same rank code, including the exceptional payload encodings.
function affineRankSweep(owner,tape,begin,end,kind,controls,flag,back,body){
    if(begin>=end)return;
    const dir=back?-1:1,first=back?end-1:begin,last=back?begin:end-1;
    owner.indicator(tape,first-begin,kind,controls,flag);
    for(let i=first;;i+=dir){
        body(i);
        if(i===last)break;
        owner.indicator(tape,Math.max(i,i+dir)-begin,'eq',controls,flag);
    }
    owner.indicator(tape,last-begin,kind,controls,flag);
}

function patch(source){
    let s=source;
    function once(before,after){
        if(s.split(before).length!==2)throw Error('Affine rank source mismatch '+before.slice(0,60));
        s=s.replace(before,()=>after);
    }
    once('class Tape {',affineRankSweep.toString()+'\nclass Tape {');
    once(`stepList(split(this.h,this.half),back,i=>{
            const mark=()=>this.indicator(tape,i-this.h,"le",this.ctrl,t);
            mark();this.permute(tape,[D[i],this.r[off+i]],[this.r[off+i],D[i]],[t],back);mark();
        });`,`affineRankSweep(this,tape,this.h,this.half,'le',this.ctrl,t,back,i=>{
            this.permute(tape,[D[i],this.r[off+i]],[this.r[off+i],D[i]],[t],back);
        });`);
    const beg='    affineProduct(tape,a,d,back) {',start=s.indexOf(beg),stop=s.indexOf('\n    affine(tape,back)',start);
    if(start<0||stop<=start)throw Error('Affine product');
    let old=s.slice(start,stop),cut=old;
    function both(before,after){if(cut.split(before).length!==3)throw Error('Both affine tails '+before);cut=cut.split(before).join(after);}
    both('const tail=rv=>stepList(split(base,this.r.length),rv,i=>{',"const tail=rv=>affineRankSweep(this,tape,base,this.r.length,'gt',ctrl,t,rv,i=>{");
    for(const quote of ["'",'"']){
        const pred='const mark=()=>this.indicator(tape,i-base,'+quote+'gt'+quote+',ctrl,t),z=';
        if(cut.split(pred).length!==2)throw Error('Affine threshold selector');cut=cut.replace(pred,'const z=');
    }
    both('const seq=[mark,rr=>','const seq=[rr=>');both('orig,[t],rr),mark]','orig,[t],rr)]');
    once(old,cut);
    return s;
}
module.exports={patch,affineRankSweep};
