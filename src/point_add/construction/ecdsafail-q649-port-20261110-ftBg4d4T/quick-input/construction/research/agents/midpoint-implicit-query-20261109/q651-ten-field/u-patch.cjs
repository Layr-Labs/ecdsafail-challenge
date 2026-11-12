'use strict';
// Apply AFTER q651-ten-field/upper.cjs. Partial coverage, not a 650-stage claim.
function upper(s){
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U37 anchor '+a);s=s.replace(a,()=>b);};
 one('if(this.k<64){H.tag=H.tag.slice();H.tag[2]=this.v[this.k];H.u3Affine=true;}',
 `if(this.k<64){H.tag=H.tag.slice();H.tag[2]=this.v[this.k];H.u3Affine=true;}
      if(this.k>=64&&this.k<=95){H.tag=H.tag.slice();H.tag[1]=this.v[this.k];H.u3Affine=true;H.u37Slot=1;}
      if(this.k>=96&&this.k<=125){H.tag=H.tag.slice();H.tag[1]=this.A[this.k<=119?this.half:this.half+1];}`);
 one("if(this.tag[2]!==host||this.rankHost!==this.pick)throw Error('U3 affine ports');","if(this.tag[this.u37Slot||2]!==host||this.rankHost!==this.pick)throw Error('U3 affine ports');");
 one('target).map((q,i)=>i===2?this.carry:q),S=',
 `target).map((q,i)=>{
          if(i===2)return this.carry;
          if(i!==1)return q;
          if(this.k===63)return this.aux[3];
          if(this.k===119)return target===this.dv[0]?this.aux[3]:q;
          if(this.k>=120&&this.k<=122)return target===this.dv[0]?this.aux[3]:this.A.at(-1);
          if(this.k>=123&&this.k<=124)return this.carry;
          return q;
        }),S=`);
 one('if(H.tag.length>=3)H.tag[2]=this.dv[0];','if(H.tag.length>=3)H.tag[2]=this.dv[0];if(this.k>=120&&this.k<=125)H.tag[1]=this.dv[1];');
 one('if(this.k>=113&&this.k<=119){H.tag=H.tag.slice();H.tag[2]=this.carry;H.uDebt=true;}',
 `if(this.k>=113&&this.k<=119){H.tag=H.tag.slice();H.tag[2]=this.carry;H.uDebt=true;}
        if(this.k>=124&&this.k<=125){H.tag=H.tag.slice();H.tag[1]=this.pick;H.rankHost=this.pick;H.digit=this.digitDirty;}`);
 return s;
}
module.exports={upper};
