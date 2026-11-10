'use strict';
const old=require('./upper652.cjs').upper;
exports.upper=src=>{
 const w=process.env.R35_WIDTH;let s;
 try{process.env.R35_WIDTH='652';s=old(src);}finally{process.env.R35_WIDTH=w;}
 for(const [a,b]of [...require('./p-map651.js'),...require('./p-small-as-is.js')]){if(s.split(a).length!==2)throw Error('q651 map anchor '+a);s=s.replace(a,()=>b);}
 // Logical 652..656 have been evicted and cannot be dirty loans.
 const a='this.ids=this.ids.slice(0,-5);';
 if(s.split(a).length!==2)throw Error('q651 loan pool anchor');
 s=s.replace(a,a+'this.ids=this.ids.filter(q=>q<652||q>656);');
 return s;
};
