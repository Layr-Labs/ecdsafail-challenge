const fs=require('fs');let s=require('./i9-history-walk3-base.cjs');
const one=(a,b)=>{if(s.split(a).length!==2)throw Error('S5 triple anchor '+a);s=s.replace(a,b);};
one('norm(a,w,controls,base);rot(a,w,controls,-1,base);one(a,()=>this.bias(controls,bias));',
'norm(a,w,controls,base);if(second&&base){one(a,()=>this.rot(controls,w,-base));relay2Port=w[w.length-base];if(third)relay3Port=w[w.length-base+1];}one(a,()=>this.bias(controls,bias));');
one('rot(all,r,c,-1,base);','if(second&&base){one(all,()=>this.rot(c,r,-base));relay2Port=r[r.length-base];if(third)relay3Port=r[r.length-base+1];}');
fs.writeFileSync(__dirname+'/walk3-source.cjs','module.exports='+JSON.stringify(s)+';\n');
