'use strict';
module.exports=s=>{
 const edit=(a,b)=>{if(s.split(a).length!==2)throw Error('power7 '+a);s=s.replace(a,()=>b);};
 edit('const groupBit=M[n-1],guard=gt(s,i,e,null,dirty);','const groupBit=M[n-1],guard=[];');
 edit('return gates.concat(guard.slice().reverse());',`const expanded=[];
 for(const row of gates){const cs=row.slice(0,-1),z=row.at(-1);if(z===e)throw Error('virtual power target');
  if(!cs.includes(e)){expanded.push(row);continue;}
  for(let j=0;j<s.length;j++)if(!(i>>j&1)){
   const ctl=[s[j],...s.slice(j+1),...cs.filter(q=>q!==e)],neg=s.slice(j+1).filter((q,k)=>!(i>>(j+1+k)&1));
   const loans=dirty.filter(q=>q!==z&&!ctl.includes(q));
   expanded.push(...neg.map(q=>[q]),...MCX(ctl,z,loans),...neg.slice().reverse().map(q=>[q]));
  }
 }return expanded;`);
 return s;
};
