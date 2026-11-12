'use strict';
module.exports=function transform(s){
 const edit=(a,b)=>{if(s.split(a).length!==2)throw Error('M9 anchor '+a);s=s.replace(a,()=>b);};
 const a=s.indexOf(' lifts(K){',s.indexOf('class LiftKit extends UnitWalk{')),b=s.indexOf('\n lengths(){',a),e=s.indexOf('\n}\nfunction unitMap',b);
 if(a<0||b<0||e<0)throw Error('M9 lift bounds');
 s=s.slice(0,a)+`
 lifts(K){const out=[],n=this.n,M=this.modw,U=this.dat,h=this.outerTag[0],en=this.outerTag[1];
  for(let i=0;i<n-1;i++)out.push({rev:false,fn:()=>{
   // M is the original unnormalized modulus throughout this whole lift.
   this.zer([],M.slice(n-i-1),en);
   for(let j=i;j<n-1;j++){
    const low=M.slice(0,j-i),neg=[...low];
    if((K>>BigInt(j))&1n)neg.push(U[j]);
    for(const q of neg)this.raw(-1,-1,q);
    this.op([en,...low,U[j]],h);
    for(const q of neg.slice().reverse())this.raw(-1,-1,q);
   }
   this.rows(plus(M.slice(0,n-i),U.slice(i),null,h));
   this.raw(en,-1,h);
   this.lt([en],M.slice(0,n-i),U.slice(i),h);
   this.zer([],M.slice(n-i-1),en);
  }});return out;
 }
 lengths(){const ops=[],M=this.modw,h=this.outerTag;
  for(let j=h.length;j--;)ops.push({rev:false,fn:()=>{const d=1<<j;this.zer([],M.slice(M.length-d),h[j]);this.rot([h[j]],M,d);}});
  return ops;
 }
`+s.slice(e);
 edit('all=[[l,l.lifts(p&mask),true,null],[l,nrm,true,null],[w,w.plan(),false,wm],[l,nrm,false,null],[l,l.lifts(z),false,null]]',
      'all=[[l,nrm,true,null],[l,l.lifts(p&mask),true,null],[w,w.plan(),false,wm],[l,l.lifts(z),false,null],[l,nrm,false,null]]');
 return s;
};
