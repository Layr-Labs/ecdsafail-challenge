
'use strict';module.exports=s=>{
 s=require('./i9-divide-p-d5.cjs')(s);
 s=require('./i9-divide-d7-p-suffix.cjs')(require('./i9-divide-d7-p-prefix-extended.cjs')(require('./i9-divide-d7-p-partial.cjs')(s)));
 s=require('./i9-divide-d12-p-tail.cjs')(require('./i9-divide-d12-p-alpha-xor.cjs')(s));
 s=s.replace('new SectorCanonical(n,2)','new SectorCanonical(n,3)').replace('w.tag=w.tag.slice(0,3)','w.tag=w.tag.slice(0,4)');
 return require('./i9-divide-d14-p-winding.cjs')(require('./i9-divide-d14-p-middle.cjs')(s));
};
