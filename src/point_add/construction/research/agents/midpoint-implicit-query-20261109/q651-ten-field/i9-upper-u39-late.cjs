'use strict';
// Incremental original-ABI source overlay after U30. No allocator or sink.
exports.wholeStageFreed=false;
exports.select=w=>w.kind==='trial'&&w.args[0]===true&&w.k===112?{evict:642,reason:'late witness rank3 qtop/high relay'}:null;
exports.upper=s=>{
 if(!s.includes('    u35Direction(tape){')){
   s=require('./i9-upper-u35-direction.cjs').upper(s);
   s=s.replace('if(witness&&this.k<=112&&!this.u35DirectionOnly){','if(witness&&this.k===112&&!this.u35DirectionOnly){');
 }
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U39 anchor '+a);s=s.replace(a,()=>b);};
 one('      if(!witness&&this.k<=112&&!this.u30Trial){',`      if(witness&&this.k===112&&!this.u39LateWitness){
        const H=Object.create(this),tp=Object.create(tape);H.u39LateWitness=true;H.u35DirectionOnly=true;
        tp.ids=tape.ids.filter(q=>q!==this.pick);tp.loan=(used,n)=>tape.loan([...used,this.pick],n);
        tp.out=(a,b,t)=>{if([a,b,t].includes(this.pick))throw Error('U39 evicted pick '+[this.k,a,b,t]);tape.out(a,b,t);};
        H.trial(tp,witness,back);return;
      }
      if(!witness&&this.k<=112&&!this.u30Trial){`);
 one(' if(this.k===112&&this.u17DirectionRelay){layer.u17LateNorm=true;layer.dv=[this.dv[0],this.borrow];}',` if(this.k===112&&this.u17DirectionRelay){layer.u17LateNorm=true;layer.dv=[this.dv[0],this.borrow];
   if(witness&&this.u39LateWitness){layer.tag[3]=this.qtop;layer.u11Witness=true;layer.u17BandSlot=3;}}
`);
 return s;
};
