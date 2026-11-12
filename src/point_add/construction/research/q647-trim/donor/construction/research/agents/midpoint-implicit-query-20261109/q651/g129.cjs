'use strict';
// g129 overlay (ours): balance the aligned sign probe split on top of nasqret's 653 (centerfix) upper overlay.
// Rows whose quotient estimate is within one (single-flag core, layouts() != null) have r*V' < 2p < 2^257,
// so the compared word fits 258 wires: base = half+1 (129) low wires of r times S (129 wires).
// Then D needs 129-k-L clean wires and r supplies 127-k-L zero wires: 2 guard wires instead of 3.
// Rows where the rank register would need one more bit (127-k a power of two) and two-flag rows keep base 130.
const path=require('path');
const Q=process.env.N653||path.join(__dirname,'../q653-centerfix');
const prev=require(path.join(Q,'upper.cjs'));
const MODE=process.env.G129_MODE||'same-width',TOP=process.env.G129_TOP||'pc';
function one(src,from,to){if(src.split(from).length!==2)throw Error('g129 site '+JSON.stringify(from));return src.replace(from,to);}
function upper(src){
  src=prev.upper(src);
  const extra=`
    get ab(){
      if(!this.r)return undefined;const wide=this.half+2,a=this.r.length-wide,mode=${JSON.stringify(MODE)};
      if(mode==='off'||a<0||!this.layouts())return wide;
      const lg=x=>x>0?Math.floor(Math.log2(x))+1:0;
      if(mode==='same-width'&&lg(a+1)!==lg(a))return wide;
      return wide-1;
    }
    guardTop(){
      const all={b:this.A.at(-1),p:this.pick,c:this.carry};
      if(this.ab===this.half+2)return [all.b,all.p,all.c];
      return ${JSON.stringify(TOP)}.split('').map(x=>all[x]);
    }
`;
  src=one(src,'class AlignedGeneral extends TruncatedGeneral {','class AlignedGeneral extends TruncatedGeneral {'+extra);
  src=one(src,'const high=this.r.slice(this.half+2);if(!high.length)return;','const high=this.r.slice(this.ab);if(!high.length)return;');
  src=one(src,'const base=this.half+2,top=[this.A.at(-1),this.pick,this.carry];','const base=this.ab,top=this.guardTop();');
  src=one(src,'const extra=rv=>{const upper=D.slice(-3);','const extra=rv=>{const upper=D.slice(-top.length);');
  src=one(src,'const base=this.half+2,layer=Object.create(this);layer.pick=this.g;layer.carry=this.take;','const base=this.ab,layer=Object.create(this);layer.pick=this.g;layer.carry=this.take;');
  src=one(src,'const base=this.half+2,layer=Object.create(this);\n','const base=this.ab,layer=Object.create(this);\n');
  src=one(src,'const base=this.half+2,w=this.half+1;','const base=this.ab,w=this.half+1;');
  src=one(src,'if(this.r.length<base){super.signProbe(tape,target,false);return;}','if(this.r.length<this.half+2){super.signProbe(tape,target,false);return;}');
  if(src.includes('this.half+2')){const rest=src.split('this.half+2').length-1;if(rest!==3)throw Error('unexpected remaining half+2 sites '+rest);}
  return src;
}
module.exports={upper};
