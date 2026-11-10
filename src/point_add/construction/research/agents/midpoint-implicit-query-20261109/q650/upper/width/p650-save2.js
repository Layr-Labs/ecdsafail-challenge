'use strict';
// q650 upper savings on top of the WIDTH stack (apply last).
// (1) affine rows 0..63 (u4/u5 bodies): mixedV runs after the early normalizeA^-1, when pick holds no rank bit; it is zero
//     there, so the fused digits use the clean digit with pick as ancilla (same map as digitDirty), not digitDirty.
// (2) probe: the v[k]-host lease switch only needs to disable the clean tail digit in coefficient-direction rows (96..111);
//     row 112's tail ancilla is f2, which stays clean.
module.exports=[
 ['const mixedV=rv=>{const layer=Object.create(this);layer.digit=this.digitDirty;layer.mixed(tape,r,v,d,[this.take],!rv);};\n        const seq=[canon,leading,normT,',
  'const mixedV=rv=>{const layer=Object.create(this);layer.digit=MixedArithmetic.prototype.digit;layer.mixed(tape,r,v,d,[this.take],!rv);};\n        const seq=[canon,leading,normT,'],
 ['const mixedV=rv=>{const layer=Object.create(this);layer.digit=this.digitDirty;layer.mixed(tape,r,v,d,[this.take],!rv);};\n        const seq=[canon,leading,...win,leading,',
  'const mixedV=rv=>{const layer=Object.create(this);layer.digit=MixedArithmetic.prototype.digit;layer.mixed(tape,r,v,d,[this.take],!rv);};\n        const seq=[canon,leading,...win,leading,'],
 ['      if(!this.wideBand&&this.layouts()&&!this.noLease){layer.digit(tape,z,S,[this.take],back);return;}',
  '      if(!this.wideBand&&this.layouts()&&!(this.noLease&&this.useCoefficientDirection)){layer.digit(tape,z,S,[this.take],back);return;}'],
];
