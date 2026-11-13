'use strict';
module.exports=s=>{
 const a=s.indexOf(' lifts(K){',s.indexOf('class LiftKit extends UnitWalk{')),b=s.indexOf('\n lengths(){',a);
 if(a<0||b<0)throw Error('lift seven anchor');
 return s.slice(0,a)+`
 lifts(K){const out=[],n=this.n,M=this.modw,U=this.dat,S=this.outerTag,h=S.at(-1),top=M.at(-1),half=n/2;
  for(let i=0;i<n-1;i++)out.push({rev:false,fn:()=>{
   const emit=(cs,z,negative=[])=>{for(const q of negative)this.raw(-1,-1,q);this.op(cs,z);for(const q of negative.slice().reverse())this.raw(-1,-1,q);};
   const active=(cs,z,negative=[])=>emit([top,...cs],z,[top,...negative]);
   const zero=()=>this.zer([],M.slice(n-(half-i)),h);
   if(i<half-1)zero();else active([],h);
   // M XOR (M-1) has ones exactly through v2(M), inclusive. M is never zero.
   // Active iteration i has i low zeros after the preceding left shifts.
   for(let j=0;j<n-1;j++){
    const low=M.slice(i,Math.max(i,j)),neg=[...low];
    if((K>>BigInt(j))&1n)neg.push(U[j]);
    active([...low,U[j]],h,neg);
   }
   // Add M (virtual top zero) under active AND h. Ripple skeletons undo when disabled.
   const loM=M.slice(0,-1),loU=U.slice(0,-1),uTop=U.at(-1);
   for(const r of plus(loM,loU,null,h)){const cs=r.slice(0,-1),z=r.at(-1);if(cs.includes(h))active(cs,z);else this.raw(r.length>1?r[0]:-1,r.length>2?r[1]:-1,z);}
   for(const r of lt(loM,loU,uTop)){const cs=r.slice(0,-1),z=r.at(-1);if(z===uTop)active([h,...cs],z);else this.raw(r.length>1?r[0]:-1,r.length>2?r[1]:-1,z);}
   active([],h);
   for(const r of lt(loM,loU,h)){const cs=r.slice(0,-1),z=r.at(-1);if(z===h)active([uTop,...cs],z,[uTop]);else this.raw(r.length>1?r[0]:-1,r.length>2?r[1]:-1,z);}
   // Restore the original count before rotation. Arithmetic no longer touches M.top.
   if(i<half-1)zero();else active([],h);
   // Expand the stable S>i predicate only at the final rotation.
   for(let j=0;j<S.length;j++)if(!(i>>j&1)){
    const cs=[S[j],...S.slice(j+1)],neg=S.slice(j+1).filter((q,k)=>!(i>>(j+1+k)&1));
    for(const q of neg)this.raw(-1,-1,q);this.rot(cs,M,1);for(const q of neg.slice().reverse())this.raw(-1,-1,q);
   }
  }});return out;
 }
`+s.slice(b);
};
