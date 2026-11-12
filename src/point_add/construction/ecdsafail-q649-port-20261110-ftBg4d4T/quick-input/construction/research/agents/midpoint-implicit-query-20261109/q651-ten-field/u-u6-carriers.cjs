'use strict';
// U6 partial: source transformations only, applied after U5.
exports.upper=(s,{affineMin=84}={})=>{
 if(!Number.isInteger(affineMin)||affineMin<64||affineMin>96)throw Error('U6 affine minimum');
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U6 anchor '+a);s=s.replace(a,()=>b);};
 // S1's clean f1 tail loan is invalid when U5 carries rank0 there.
 if(s.includes('const f1z=target===this.dv[0]&&'))one('const f1z=target===this.dv[0]&&','const f1z=this.u5PhaseHost!==target&&target===this.dv[0]&&');
 one('const H=Object.create(this),carry=this.carry;H.tag=this.tag.slice();H.tag[1]=carry;',
     'const H=Object.create(this),carry=this.carry;H.tag=this.tag.slice();H.tag[this.u6TopSlot??1]=carry;');
 one('if(!this.deep){super.affine.call(H,tape,back);return;}',
 `if(this.k>=${affineMin}&&this.k<=95){H.tag=H.tag.slice();H.tag[0]=this.A[this.half-1];H.u38Implicit=true;H.u6TopSlot=0;}
      if(!this.deep){super.affine.call(H,tape,back);return;}`);
 one('if(this.k===112){layer.tag[1]=this.v[this.k];layer.u38NormLease=true;}return layer;',
 `if(this.k===112){layer.tag[1]=this.v[this.k];layer.u38NormLease=true;}
 if(this.k>=96&&this.k<=112){layer.u39Trial=true;layer.u39Temp=witness?this.qtop:this.carry;layer.tag[0]=this.n.at(-1);layer.u6TrialSlot=0;}
 return layer;`);
 one('H.tag=this.tag.slice();H.tag[1]=tmp;', 'H.tag=this.tag.slice();H.tag[this.u6TrialSlot??1]=tmp;');
 one('u39Normalize(tape,back){', `u39Normalize(tape,back){
      if(this.u6TrialSlot===0&&this.u38NormLease){const H=Object.create(this);H.u38NormLease=false;
        if(!back)tape.out(NONE,this.take,this.v[this.k]);H.u39Normalize(tape,back);if(back)tape.out(NONE,this.take,this.v[this.k]);return;}`);
 one('const H=Object.create(this),top=this.tag[1];H.tag=this.tag.slice();H.tag[1]=B.d0;',
     'const H=Object.create(this),slot=this.u6TrialSlot??1,top=this.tag[slot];H.tag=this.tag.slice();H.tag[slot]=B.d0;');
 return s;
};
