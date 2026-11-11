'use strict';

function once(s,a,b) {
    const pos=s.indexOf(a);
    if(pos<0||s.indexOf(a,pos+a.length)>=0)throw Error('upper source anchor '+a);
    return s.slice(0,pos)+b+s.slice(pos+a.length);
}

// At an enabled tail digit, the normalized numerical coefficient is
// divisible by 2^cut. Both the restoration comparison and its subtraction
// are independent of the saved low accumulator bits.
function patch(s) {
    const first='rr=>layer.digit(tape,z,a,[t],!rr)';
    s=once(s,first,`rr=>{
      const cut=i-base+1, v=a.slice(cut), w=z.slice(cut);
      if(!v.length)throw Error('affine tail divisor width');
      if(this.u12&&cut>=2){
        const native=Object.create(layer);native.u12=false;
        native.digitTopOne(tape,w,v,[t],!rr);
      }else layer.digit(tape,w,v,[t],!rr);
    }`);
    const second='rr=>this.digit(tape,z,a,[t],!rr)';
    s=once(s,second,'rr=>this.digit(tape,z.slice(i-base+1),a.slice(i-base+1),[t],!rr)');
    const start='    tailDigit(tape,layer,z,S,back){';
    s=once(s,start,start+`
      if(!this.u6Code){
        const cut=this.r.indexOf(z.at(-1))-this.ab+1;
        if(cut<1||cut>=S.length)throw Error('aligned tail divisor width');
        z=z.slice(cut); S=S.slice(cut);
      }`);
    return s;
}
module.exports={patch};
