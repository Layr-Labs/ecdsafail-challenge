
'use strict';module.exports=s=>{
 s=require('./d14-p-d5.cjs')(s);
 s=require('./d14-d7-p-suffix.cjs')(require('./d14-d7-p-prefix-extended.cjs')(require('./d14-d7-p-partial.cjs')(s)));
 s=require('./d14-d12-p-tail.cjs')(require('./d14-d12-p-alpha-xor.cjs')(s));
 s=s.replace('new SectorCanonical(n,2)','new SectorCanonical(n,3)').replace('w.tag=w.tag.slice(0,3)','w.tag=w.tag.slice(0,4)');
 return require('./d14-d14-p-winding.cjs')(require('./d14-d14-p-middle.cjs')(s));
};
