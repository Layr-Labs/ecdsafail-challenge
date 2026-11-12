'use strict';
// Count high bit hosts choice. The retained enable protects the inactive bank.
module.exports=s=>{
 const a=s.indexOf(' lifts(K){',s.indexOf('class LiftKit extends UnitWalk{')),b=s.indexOf('\n lengths(){',a);
 if(a<0||b<0)throw Error('lift-count source anchor');
 return s.slice(0,a)+`
 lifts(K){const a=[],n=this.n,U=this.dat,M=this.modw,H=this.outerTag,active=this.on,b=H.at(-1),half=n/2;
  const flip=U.filter((_,j)=>Boolean((K>>BigInt(j))&1n));
  const zero=d=>this.zer([],M.slice(n-d),b);
  for(let i=0;i<n-1;i++)a.push({rev:false,fn:()=>{
   this.less([],H,i,active);
   if(i<half-1)zero(half-i);else this.op([active],b);
   for(const z of flip)this.raw(-1,-1,z);
   this.tick(active,U,M,b);this.reverse(()=>this.incmod());this.tick(active,U,M,b);this.incmod();
   for(const z of flip)this.raw(-1,-1,z);
   // plus's unconditional skeleton cancels on disabled branches; only b-controls need active.
   const g=plus(M,U,null,b);
   for(const r of g){const cs=r.slice(0,-1),z=r.at(-1);
    if(i>=half-1&&cs.includes(b)){const controls=[active,...cs];for(const row of MCX(controls,z,this.y))this.raw(row.length>1?row[0]:-1,row.length>2?row[1]:-1,row.at(-1));}
    else this.raw(r.length>1?r[0]:-1,r.length>2?r[1]:-1,z);
   }
   this.op([active],b);this.lt([active],M,U,b);this.rot([active],M,1);
   if(i<half-1)zero(half-i-1);else this.op([active],b);
   this.less([],H,i,active);
  }});return a;
 }
`+s.slice(b);
};
