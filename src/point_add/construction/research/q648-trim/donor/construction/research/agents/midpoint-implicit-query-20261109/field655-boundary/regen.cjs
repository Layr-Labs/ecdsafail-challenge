'use strict';
const path=require('path');
const {joined,checkedSource}=require('../field128-height-experiment/pinned.cjs');
const {CanonicalUnit}=require('../field128-height-experiment/walks.cjs');
const source=checkedSource(path.join(joined,'field/forward.cjs'),
  '7e7ac506467480fd3e2e064af32f98f11cd1cf177319178406a553d4ddf90239');
const {UnitPark,Terminal,terms}=Function('module',source+'\nreturn {UnitPark,Terminal,terms};')({exports:{}});
const HeightWalk=Object.getPrototypeOf(CanonicalUnit);
class SignedWalk extends HeightWalk{
  constructor(n){super(n);this.aux=this.L[n+1];}
  plan(){
    const blocks=super.plan(),n=this.n;
    blocks.push({rev:false,fn:()=>{
      // On a completed coprime walk all low remainder bits except left
      // g=1 are zero. Keep these physical low pads for the signed shear.
      for(const bank of [this.L,this.R])for(let j=n;j>=1;j--) this.swap([],bank[j],bank[j+1]);
    }});
    return blocks;
  }
}
function emitRegenerateSparse(sink,erase=false){
  const n=128,p=(1n<<256n)-(1n<<32n)-977n;
  const park=new UnitPark(n,false,[]),walk=new SignedWalk(n),scale=new Terminal(n,true,terms(p));
  park.yq=walk.R[0];scale.yq=walk.R[0];
  const exchange={rev:false,fn:()=>{for(let i=0;i<n+2;i++)walk.swap([],walk.L[i],walk.R[n+1-i]);}};
  const stages=[
    [park,park.parking(),false],[walk,[exchange],false],[walk,walk.plan(),false],
    [scale,scale.plan(),false],[walk,walk.plan(),true],[walk,[exchange],true],
    [park,park.parking(),true]
  ];
  if(!erase)stages.reverse();
  for(const [g,blocks,back] of stages){
    const inverse=back!==!erase;if(inverse)blocks.reverse();
    for(const block of blocks){
      g.g=[];block.fn();if(inverse!==block.rev)g.g.reverse();
      for(const op of g.g){
        if((op>>>20&1023)===656||(op>>>10&1023)===656||(op&1023)===656)throw Error('removed regen wire touched');
        if((op&1023)===645)throw Error('write to fixed-one regen port');
      }
      sink(g.g);
    }
  }
}
module.exports={emitRegenerateSparse};
