'use strict';
// Apply to final q654 regen source AFTER q651-ten-field/regen.cjs extra().
const scale=String.raw`
class R37Park extends R36Park {
 parking(){
  const band=this.band||32,k=Math.log2(band);
  this.tag=[647,648,649,0,1].slice(0,k);
  const blocks=[],push=(fn,rev=false)=>blocks.push({fn,rev});
  const norm=j=>{const s=1<<j;
   for(let h=band;h<=this.m;h+=band){this.zer([],this.M.slice(h-s),this.tag[j]);this.zer([],this.M.slice(h-band),this.tag[j]);}
   this.rot([this.tag[j]],this.M,s);
  };
  for(let j=k;j--;)push(()=>norm(j));
  for(let h=band;h<=this.m;h+=band){
   const M=this.M.slice(0,h),S=this.S.slice(0,h),e=[646];
   const higher=[];for(let t=h+band;t<=this.m;t+=band)higher.push(this.M[t-1]);
   const mark=()=>this.zer([this.M[h-1]],higher,646);
   push(mark);
   for(let k=this.m-h;k>=0;k--)push(()=>this.restore(e,M,this.S.slice(k,k+h),0,k===this.m-h?this.Jtop:this.S[k+h]));
   for(let i=0;i<band-1;i++)push(()=>{
    this.less(e,this.tag,i,this.f);const c=[this.f];
    for(const b of S)this.swap(c,this.yq,b);
    this.restore(c,M,S,0,this.yq);
    this.op(c.concat(this.yq),S[0]);this.op(c.concat(S[0]),this.yq);
    this.less(e,this.tag,i,this.f);
   });
   for(let j=0;j<k;j++)push(()=>this.rot(e.concat(this.tag[j]),S,-(1<<j)));
   for(let i=h-band+1;i<h;i++)push(()=>{this.less(e,this.tag,h-1-i,this.f);this.swap([this.f],this.S[i],this.T[i]);this.less(e,this.tag,h-1-i,this.f);});
   push(()=>{for(let i=h;i<this.m;i++)this.swap(e,this.S[i],this.T[i]);});
   push(mark);
  }
  for(let j=0;j<k;j++)push(()=>norm(j),true);
  return blocks;
 }
}
// R38: on the history's coprime coefficient/modulus domain, erase the residual
// shift from v2(M OR S), reuse its sites, and run one ordinary full-width core.
// The generic fallback retains the separately tested arbitrary-coefficient map.
class R37Scale extends TopHost {
 plan(){
  const band=this.band||32,k=Math.log2(band);
  const blocks=[],push=(fn,rev=false)=>blocks.push({fn,rev});
  this.tag=[647,648,649,0,1].slice(0,k);
  const norm=j=>{
   const s=1<<j;
   for(let h=band;h<=this.m;h+=band){
    this.zer([],this.M.slice(h-s),this.tag[j]);
    this.zer([],this.M.slice(h-band),this.tag[j]);
   }
   for(const word of [this.M,this.S,this.T])this.rot([this.tag[j]],word,s);
  };
  for(let j=k;j--;)push(()=>norm(j));
  const retag=()=>{for(let j=0;j<k;j++)for(let i=1;i<band;i++)if(i&(1<<j)){
   this.zer([],this.M.slice(0,i).concat(this.S.slice(0,i)),this.tag[j]);
   this.zer([],this.M.slice(0,i+1).concat(this.S.slice(0,i+1)),this.tag[j]);
  }};
  if(this.releaseTags){
   // At this boundary gcd(M,S)=2^s, 0<=s<band. No runtime branching on data.
   push(retag);
   const high=[];
   for(let j=Math.log2(this.m)-1;j>=k;j--){
    const port=[647,648][j-k];if(port===undefined)throw Error('high normalization tag budget');
    const normHigh=()=>{const d=1<<j;this.zer([],this.M.slice(this.m-d),port);
     for(const word of [this.M,this.S,this.T])this.rot([port],word,d);
    };
    high.push(normHigh);push(normHigh);
   }
   const core=new TopHost(this.m,this.pol,this.digits);
   for(const key of ['M','S','T','D','y','E','sg','f'])core[key]=this[key];
   core.tag=[];core.yq=649; // freed low-count bit; the full modulus stays intact
   core.add=function(c,a,b,unused,h){Signed.prototype.add.call(this,c,a,b,0,h);};
   for(const b of Terminal.prototype.plan.call(core))push(()=>{core.g=[];b.fn();this.g.push(...core.g);},!!b.rev);
   for(let i=high.length;i--;)push(high[i],true);
   push(retag);
   for(let j=0;j<k;j++)push(()=>norm(j),true);
   return blocks;
  }
  for(let h=band;h<=this.m;h+=band){
   const core=new TopHost(h,this.pol,this.digits);
   for(const key of ['M','S','T','D'])core[key]=this[key].slice(0,h);
   core.y=this.y;core.E=646;core.sg=this.sg;core.f=this.f;core.tag=[];
   const top=this.M[h-1],higher=[];
   for(let t=h+band;t<=this.m;t+=band)higher.push(this.M[t-1]);
   const controls=[646];core.yq=top;
   const mark=()=>this.zer([top],higher,646),clear=()=>this.op([646],top);
   push(mark);push(clear);
   // Only the deposit and separating reflection use E. Inactive W/W^-1 cancel.
   for(const b of Terminal.prototype.plan.call(core))push(()=>{
    core.g=[];b.fn();
    for(const gate of core.g){
     const a=gate>>>20&1023,b=gate>>>10&1023,t=gate&1023;
     if(controls.includes(t))throw Error('class selector targeted by core '+[h,a,b,t]);
     this.g.push(gate);
    }
   },!!b.rev);
   push(clear);push(mark);
  }
  for(let j=0;j<k;j++)push(()=>norm(j),true);
  return blocks;
 }
}
`;
module.exports=[
 ['function emitRegenerateSparse(sink,erase=false){',scale+'\nfunction emitRegenerateSparse(sink,erase=false){'],
 ['walk=new Signed(n,5),walk6=new Signed(n,6)','walk=new Signed(n,4),walk6=new Signed(n,6)'],
 ['scale=new TopHost(n,true,terms(p));','scale=new R37Scale(n,true,terms(p));scale.releaseTags=true;'],
 ['park=new R36Park(n,false,[])','park=new R37Park(n,false,[])'],
 ['walk.tag[3]=walk.L[n+1];walk6.tag[4]=walk6.L[n+1];walk.fire=650;',
  'walk.tag[2]=walk.L[n+1];walk.tag[3]=651;walk6.tag[3]=scale.T[1];walk6.tag[4]=walk6.L[n+1];walk.fire=649;'],
 ['if(q===651||q===652||q===653||q===654||q===655||q===656)',
  'if(q===650||q===651||q===652||q===653||q===654||q===655||q===656)'],
];
