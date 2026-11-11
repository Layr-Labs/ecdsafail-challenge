'use strict';
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U18 lease anchor '+a);s=s.replace(a,()=>b);};
 one('        const D=this.topDivisor(),Q=this.q,g=this.ctrl,js=',`        H.tag=H.tag.map(q=>q===647?this.borrow:q);
        const D=this.topDivisor(),Q=this.q,g=this.ctrl,js=`);
 one('      if(!this.deep){super.affine.call(H,tape,back);return;}',`      if(this.k>=64&&this.k<=95){H.tag=H.tag.slice();H.tag[5]=this.v[this.k];H.tag[1]=this.A[this.half-1];H.tag[0]=this.A[0];H.u37Slot=5;H.u12=true;}
      if(this.k>=96&&this.k<=111){H.tag=H.tag.slice();H.tag[4]=this.A[this.half-1];H.u38Implicit=true;H.u6TopSlot=4;}
      if(this.k>=120&&this.k<=123){H.tag=H.tag.slice();H.tag[2]=this.v[this.k];H.u3Affine=true;H.u37Slot=2;H.rankHost=this.pick;H.digit=H.digitDirty;}
      if(!this.deep){super.affine.call(H,tape,back);return;}`);
 return s;
};


