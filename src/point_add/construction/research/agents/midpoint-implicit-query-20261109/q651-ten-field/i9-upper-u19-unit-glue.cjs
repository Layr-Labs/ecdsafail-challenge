'use strict';
// Source-only overlay after U16, before final allocator and the sole W4096 sink.
exports.upper=(s,options={})=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U19 anchor '+a);s=s.replace(a,()=>b);};
 one('this.clean=[this.pick,this.carry,this.norm,this.spare,this.shape,this.qual,this.fired];this.width=width;',
     'this.qual=this.norm; // U19: pre qualification ends before unit normalizer begins.\n        this.clean=[this.pick,this.carry,this.norm,this.spare,this.shape,this.fired];this.width=width;');
 // A dirty loan need not be clean, but the absent site cannot occur in its gates.
 if(!s.includes('this.ids=this.ids.filter(q=>q!==647&&q!==650&&q!==651);'))throw Error('U19 requires U16 loan exclusion');
 if(options.lastRow!==false&&s.slice(s.indexOf('class UnguardedGeneral extends OddEstimateGeneral {'),s.indexOf('class FoldTape extends Tape {')).includes('    core(tape,back){'))throw Error('U19 merge requires review of another UnguardedGeneral.core override');
 if(options.lastRow!==false)one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    core(tape,back){
      if(this.k!==127){super.core(tape,back);return;}
      // Active last row: V>=2^127, r>=2^128 and p=H V+r U,
      // 0<=U<V, H>=r imply H<2^129<=2r. Hence floor(H/r)=1.
      const q=this.q,v=this.v,g=this.ctrl;
      const seq=[()=>this.toggle(tape,g,[],q[0]),
        rv=>this.mixed(tape,q,v,this.u,g,rv),rv=>this.affine(tape,rv),
        rv=>this.permute(tape,[...this.bank,...this.u,...q.slice(-2)],
          [...this.A.slice(0,this.half),...v,...this.A.slice(this.half)],g,rv)];
      stepList(seq,back,fn=>fn(back));
    }
`);
 return s;
};
