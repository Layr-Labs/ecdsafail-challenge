'use strict';
const src=`
class R9Scale extends R37Scale {
 plan(){
  const blocks=[],push=(fn,rev=false)=>blocks.push({fn,rev}),tag=0;
  const valuationBit=j=>{
   const prior=this.y;this.y=[...this.D,...prior];
   // v2(gcd(M,S)) bit j is XOR of joint-prefix-zero thresholds at
   // every positive multiple of 2^j. M != 0 bounds that valuation below m.
   for(let h=1<<j;h<this.m;h+=1<<j)this.zer([],this.M.slice(0,h).concat(this.S.slice(0,h)),tag);
   this.y=prior;
  };
  const norm=j=>{const d=1<<j;this.zer([],this.M.slice(this.m-d),tag);
   for(const word of [this.M,this.S,this.T])this.rot([tag],word,d);
   valuationBit(j);
  };
  for(let j=Math.log2(this.m);j--;)push(()=>norm(j));
  const core=new TopHost(this.m,this.pol,this.digits);
  for(const key of ['M','S','T','D','y','E','sg','f'])core[key]=this[key];
  core.tag=[];core.yq=646;
  core.add=function(c,a,b,unused,h){Signed.prototype.add.call(this,c,a,b,0,h);};
  for(const b of Terminal.prototype.plan.call(core))push(()=>{core.g=[];b.fn();this.g.push(...core.g);},!!b.rev);
  for(let j=0;j<Math.log2(this.m);j++)push(()=>norm(j),true);
  return blocks;
 }
}
`;
const patches=require('./i9-history-p-r648-final.js').map(([a,b])=>[a,b]);
const anchor='function emitRegenerateSparse(sink,erase=false){';
patches.push([anchor,src+anchor]);
patches.push(['scale=new R37Scale(n,true,terms(p));scale.releaseTags=true;','scale=new R9Scale(n,true,terms(p));']);
// park band4 is the only repeated-body premium outside the walks.
patches.push(['const band=this.band||8,k=Math.log2(band);','const band=this.band||4,k=Math.log2(band);']);
patches.push(['this.tag=[647,0,1].slice(0,k);','this.tag=[0,1].slice(0,k);']);
module.exports=patches;module.exports.source=src;
