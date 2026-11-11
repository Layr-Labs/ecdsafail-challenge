"use strict";
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('S5 crop anchor '+a);s=s.replace(a,b);};
 one('const cut=this.u22?i-base+1:0;', 'const cut=i-base+1;');
 one('const seq=[mark,rr=>this.digit(tape,z,a,[t],!rr),rr=>this.permute(tape,z,orig,[t],rr),mark];',
     'const cut=i-base+1;const seq=[mark,rr=>this.digit(tape,z.slice(cut),a.slice(cut),[t],!rr),rr=>this.permute(tape,z,orig,[t],rr),mark];');
 return s;
};
