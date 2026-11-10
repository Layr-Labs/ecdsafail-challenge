'use strict';
// q650 upper: affine rows 0..6 (u3 layout) without rank bit 1 (logical tags[1]=651). Apply after p650-trial.js and papers'
// p650-affv.js + p650-aff4.js. Ordering as papers' u4: canon, leading (CX take->v[k]), window, early normalizeA^-1, leading, rest.
// The window [normalizeA .. guardedBarrel(r)] runs once per pass with rank bit 1 a compile-time constant: rankGH over a's top
// maxShift bits writes G(s), a barrel replaces normalizeA, and taken lanes outside the pass are parked (take cleared, q650Fold).
// With bit 1 constant, carry is free, so the window keeps the original carry-based guardedBarrel / parkAffine / affineProduct.
// Every write in the window is take-gated, so parked and untaken lanes see an identity window.
module.exports=[
 ['    affine(tape,back){\n        if(this.u4Affine){this.u4AffineBody(tape,back);return;}',
`    u5AffineBody(tape,back){
        const a=this.A.slice(0,this.half),r=this.r,v=this.v,D=this.zword.slice(0,this.half),d=D.slice(0,this.h);
        const base=this.half+1,word=[...r.slice(0,base),...D],tail=r.slice(base),g=this.ctrl,host=v.at(-1);
        if(this.tag[2]!==host||this.tag[1]!==651||this.rankHost!==this.pick)throw Error('U5 affine ports');
        const canon=rv=>this.digit(tape,[...d,this.dv[0]],v,[],rv);
        const leading=()=>tape.out(NONE,this.take,host);
        const M=this.maxShift,high=a.slice(a.length-M),win=[];
        const PS=(process.env.Q650_U5SINGLE||(process.env.Q650_U5K&&!process.env.Q650_U5K.split(',').includes(String(this.k))))?[{tag:this.tag,wires:this.tag,G:Array.from({length:M+1},(_,s)=>s),single1:true}]:this.q650PassesS(this.tag,M,s=>s);
        for(const ps of PS){
            const L=Object.create(this);L.tag=ps.tag;
            const Gbl=Array.from({length:M+1},(_,bl)=>ps.G[M-bl]);
            const N=rv=>{
                if(!rv){this.rankGH(tape,high,ps.wires,Gbl,ps.single1?undefined:this.take);this.barrel(tape,a,ps.tag,true,false);if(!ps.single1)this.q650Fold(tape,ps,false);}
                else{if(!ps.single1)this.q650Fold(tape,ps,true);this.barrel(tape,a,ps.tag,true,true);this.rankGH(tape,high,ps.wires,Gbl,ps.single1?undefined:this.take);}
            };
            win.push(rv=>N(rv),rv=>L.guardedBarrel(tape,D,true,rv),rv=>L.parkAffine(tape,D,rv),
                rv=>L.affineProduct(tape,a,D,rv),rv=>L.guardedBarrel(tape,r,false,rv),rv=>N(!rv));
        }
        const mixedV=rv=>{const layer=Object.create(this);layer.digit=this.digitDirty;layer.mixed(tape,r,v,d,[this.take],!rv);};
        const seq=[canon,leading,...win,leading,
            rv=>this.reflect(tape,word,g,rv),rv=>this.inc(tape,word,g,!rv),
            rv=>this.guardedPermutation(tape,[...tail,...D],[...D,...tail],[],rv),
            mixedV,()=>this.cnotList(tape,g,d),rv=>tape.add(v,d,g,this.carry,rv),rv=>this.inc(tape,r,g,rv),rv=>canon(!rv)];
        stepList(seq,back,fn=>fn(back));
    }
    affine(tape,back){
        if(this.u5Affine){this.u5AffineBody(tape,back);return;}
        if(this.u4Affine){this.u4AffineBody(tape,back);return;}`],
 ['layer.u4Affine=true;layer.u4d=this.zword[this.m-1];}super.affine.call(layer,tape,back);',
  'layer.u4Affine=true;layer.u4d=this.zword[this.m-1];}else if(this.k<7&&layer.tag[1]===651)layer.u5Affine=true;super.affine.call(layer,tape,back);'],
];
