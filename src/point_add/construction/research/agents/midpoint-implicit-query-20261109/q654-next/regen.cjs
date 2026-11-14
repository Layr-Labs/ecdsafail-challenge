'use strict';
const path=require('path');
const {joined,checkedSource}=require('../field128-height-experiment/pinned.cjs');
const {Signed}=require('./walks.cjs');
const source=checkedSource(path.join(joined,'field/forward.cjs'),'7e7ac506467480fd3e2e064af32f98f11cd1cf177319178406a553d4ddf90239');
const {UnitPark,Terminal,terms}=Function('module',source+'\nreturn {UnitPark,Terminal,terms};')({exports:{}});
function emitRegenerateSparse(sink,erase=false){
  const n=128,p=(1n<<256n)-(1n<<32n)-977n;
  const walk=new Signed(n),park=new UnitPark(n,false,[]),scale=new Terminal(n,true,terms(p));
  for(const x of [park,scale]){x.yq=walk.R[0];x.f=walk.R[1];x.tag[6]=walk.L[1];}
  walk.aux=walk.L[n+1];walk.tst=walk.R[n+1];
  const exchange={fn:()=>{for(let i=0;i<n+2;i++)walk.swap([],walk.L[i],walk.R[n+1-i]);}};
  const shifts={fn:()=>{for(const bank of [walk.L,walk.R])for(let j=n;j>=1;j--)walk.swap([],bank[j],bank[j+1]);}};
  const stages=[[park,park.parking(),false],[walk,[exchange],false],[walk,walk.plan().concat([shifts]),false],
    [scale,scale.plan(),false],[walk,walk.plan().concat([shifts]),true],[walk,[exchange],true],[park,park.parking(),true]];
  if(!erase)stages.reverse();
  for(const [g,blocks,back] of stages){
    const rev=back!==!erase;if(rev)blocks.reverse();
    for(const block of blocks){
      g.g=[];block.fn();if(rev!==!!block.rev)g.g.reverse();
      const port=q=>{if(q===walk.tag[6]&&g===walk){if(block.topPort==null)throw Error('height outside walk');q=block.topPort;}if(q===653||q===655||q===656)throw Error('unused regeneration site '+q);return q;};
      for(let i=0;i<g.g.length;i++){
        const x=g.g[i],a=port(x>>>20&1023),b=port(x>>>10&1023),t=port(x&1023);
        if(t===645||a===t||b===t||a!==1023&&a===b)throw Error('bad physical history gate');
        g.g[i]=(a<<20)|(b<<10)|t;
      }
      sink(g.g);
    }
  }
}
module.exports={emitRegenerateSparse};
