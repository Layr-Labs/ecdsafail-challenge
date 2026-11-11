'use strict';
// Incremental U28 source overlay. The affine method consumes/returns the U31
// frame; u31AffineFramed supplies reversible boundary transport for staging.
exports.rows=Array.from({length:16},(_,i)=>112+i);
exports.wholeStageFreed=false;
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U31 anchor '+a);s=s.replace(a,()=>b);};
 one('if(this.k>=112){const R=this.hostRank(this.pick);H.tag[3]=R.tag[3];H.rankHost=R.rankHost;H.digit=R.digit;}',
     'if(this.k>=112){const R=this.hostRank(this.pick);H.tag[3]=this.A[this.half-1];H.rankHost=R.rankHost;H.digit=R.digit;H.u38Implicit=true;H.u6TopSlot=3;}');
 const call='rv=>this.affine(tape,rv)';
 if(s.split(call).length!==6)throw Error('U31 affine call coverage');
 s=s.split(call).join('rv=>this.u31AffineFramed(tape,rv)');
 one('    affine(tape,back){\n      const H=Object.create(this.hostRank(this.useCoefficientDirection?this.pick:this.dv[1]));',String.raw`
    u31AffineFramed(tape,back){
      if(this.k<112){this.affine(tape,back);return;}
      // Boundary glue: pick is clean in the donor interface. A's qtop limb
      // moves into pick. The unaddressed old qtop now carries clean zero.
      // Both transpositions are kept outside the affine window proper.
      const swap=()=>{tape.out(NONE,this.pick,this.qtop);tape.out(NONE,this.qtop,this.pick);tape.out(NONE,this.pick,this.qtop);};
      swap();this.affine(tape,back);swap();
    }
    affine(tape,back){
      if(this.k<112){this.u31AffineBody(tape,back);return;}
      // Frame ABI: qtop's value resides on pick, and logical qtop is absent.
      // The underlying body must not use pick semantically. Exclude both
      // names from all dirty-loan pools; reject any unexpected use of pick.
      const H=this,tp=Object.create(tape);
      tp.ids=tape.ids.filter(q=>q!==H.pick&&q!==H.qtop);
      const map=q=>{if(q===H.pick)throw Error('U31 unexpected pick use row '+H.k);return q===H.qtop?H.pick:q;};
      tp.out=(a,b,z)=>tape.out(map(a),map(b),map(z));
      this.u31AffineBody(tp,back);
    }
    u31Digit(tape,z,v,controls,back){
      const live=controls.filter(q=>q!==tape.one);
      // Rows124..127 retain no rank on carry. At ordinary mixed digits it
      // is clean; after folding the fixed g control, take is the only enable.
      // At tail digits carry itself holds the count>j predicate: use a dirty
      // digit there, retaining the full count range and cropped zero suffix.
      if(live.length===1&&live[0]!==this.carry){
        const L=Object.create(this);L.pick=this.carry;
        MixedArithmetic.prototype.digit.call(L,tape,z,v,live,back);
      }else this.digitDirty(tape,z,v,live,back);
    }
    u31AffineBody(tape,back){
      const H=Object.create(this.hostRank(this.useCoefficientDirection?this.pick:this.dv[1]));
      if(this.k>=124)H.digit=H.u31Digit;`);
 return s;
};
