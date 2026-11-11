'use strict';
// Source overlay: the immutable count predicate is expanded at each use.
module.exports=s=>{
 const anchor='class LiftKit extends UnitWalk{';
 if(s.split(anchor).length!==2)throw Error('lift-eight anchor');
 return s.replace(anchor,()=>anchor+`
 less(c,arr,value,z){
  if(z!==this.on)return super.less(c,arr,value,z);
  if(c.length||arr!==this.outerTag)throw Error('virtual lift predicate contract');
  if(this.activePredicate!==undefined){if(this.activePredicate!==value)throw Error('lift predicate mismatch');delete this.activePredicate;}
  else this.activePredicate=value;
 }
 raw(a,b,z){
  const cs=[a,b].filter(q=>q>=0),physical=q=>q===this.choice?this.on:q;
  if(z===this.on)throw Error('unexpected virtual active target');
  if(!cs.includes(this.on))return super.raw(a<0?-1:physical(a),b<0?-1:physical(b),physical(z));
  if(this.activePredicate===undefined)throw Error('active use outside lease');
  const other=cs.filter(q=>q!==this.on),value=this.activePredicate;
  for(let j=0;j<this.outerTag.length;j++)if(!(value>>j&1)){
   const ctl=[this.outerTag[j],...this.outerTag.slice(j+1),...other],neg=this.outerTag.slice(j+1).filter((q,k)=>!(value>>(j+1+k)&1));
   const cphys=ctl.map(physical),target=physical(z),used=new Set([...cphys,target,...this.outerTag]);
   const dirty=Array.from({length:5*this.n},(_,i)=>i).filter(q=>!used.has(q));
   for(const q of neg)super.raw(-1,-1,q);
   for(const row of MCX(cphys,target,dirty))super.raw(row.length>1?row[0]:-1,row.length>2?row[1]:-1,row.at(-1));
   for(const q of neg)super.raw(-1,-1,q);
  }
 }
 `);
};
