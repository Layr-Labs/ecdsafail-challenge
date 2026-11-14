'use strict';
const path=require('path'),Module=require('module');
const {checkedSource}=require('../field128-height-experiment/pinned.cjs');
function previous(name,sha,addition){const f=path.join(__dirname,'../q654-next',name);const m=new Module(f,module);m.filename=f;m.paths=module.paths;m._compile(checkedSource(f,sha)+'\n'+addition,f);return m.exports;}
const B=previous('backend.cjs','7e89dd4fa21e39d40a795e0251dd918559d2151bb47610af7d6ac8fd768817e1','module.exports={f,d,replace,dirtyDigit,dirtyMdg,dirtyBlock,lowValuationSweep,plusOneMod};');
const W=previous('walks.cjs','74eb60d467f44b87459935fe6be697075ce3d53bd6d9440618e493ed707294dd','module.exports={Signed,Reduced,SectorCanonical,emitWalk,split,make,base};');
const sectorEnd=W.SectorCanonical;
class SectorSigned extends W.make(W.split,'UnitWalk'){
  constructor(n,j=6){super(n);this.tag=this.tag.slice(0,Math.min(j,this.tag.length));}
}
let g=B.replace(W.split,'this.zer([],A.slice(1),this.tst)','this.zer([],r,this.tst)');
g=B.replace(g,'one(all,()=>this.op([L[n-k]],this.tst));','one(all,()=>this.op([this.fire,L[n-k]],this.tst));');
g=B.replace(g,'if(base===0&&hi===m-1)this.op([L[n-k]],this.fire);else match([L[n-k]],L.slice(0,m),this.fire);',
 'const non=()=>{this.zer([],R.slice(0,m+1),this.tst);this.raw(-1,-1,this.tst);};non();if(base===0&&hi===m-1)this.op([this.tst,L[n-k]],this.fire);else match([this.tst,L[n-k]],L.slice(0,m),this.fire);this.reverse(non);');
class SectorReduced extends W.make(g,'UnitWalk'){
  constructor(n,j=6){super(n);this.tag=this.tag.slice(0,Math.min(j,this.tag.length));}
  plan(){
    const all=super.plan(),n=this.n,L=this.L,R=this.R,c=[this.fire],push=fn=>all.push({fn,rev:false});
    for(let bits=1;bits<=n;bits++){
      const gap=n+1-bits,mark=()=>this.zer([R[n-bits+1]],R.slice(1,n-bits+1),this.fire);
      push(mark);push(()=>{for(let j=n;j>=gap;j--)this.swap(c,L[j],L[j+1]);});push(mark);
    }
    push(()=>{for(let j=n;j>=1;j--)this.swap([],R[j],R[j+1]);});return all;
  }
}
const VirtualCanonical=W.make(W.base,'FlatUnit');
module.exports=Object.assign({},B,W,{SectorReduced,SectorSigned,VirtualCanonical});
