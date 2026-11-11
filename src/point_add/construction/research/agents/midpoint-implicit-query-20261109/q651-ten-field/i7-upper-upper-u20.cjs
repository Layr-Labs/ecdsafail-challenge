'use strict';
// Apply once after n651a q651-ten-field/upper(raw). No environment-dependent production source.
exports.wholeStageFreed=false;
exports.extensionOrder=['U21','U22','U23','U24'];
exports.sourceUpper=(s,options={})=>{
 s=require('./i7-upper-u15-upper-649.cjs').sourceUpper(s);
 s=require('./i7-upper-probe-compact.cjs').upper(s);
 if(!options.base){
  if(!options.skipU17)s=require('./i7-upper-trials-u17.cjs').upper(s);
  if(!options.skipU18){
   s=require('./i7-upper-dense-probes.cjs').upper(s);
   s=require('./i7-upper-late-leases-u18.cjs').upper(s);
   s=require('./i7-upper-probe-lead.cjs').upper(s);
  }
  if(!options.skipU19)s=require('./i7-upper-u19-unit-glue.cjs').upper(s);
 }
 // Source-only extensions; never pass a complete entry that installs another sink.
 for(const name of exports.extensionOrder){const hook=options.extensions?.[name];if(hook)s=hook(s);}
 for(const hook of options.overlays||[])s=hook(s);
 if(options.s3!==false)s=require('./i7-upper-s3-u-s3-arithmetic.cjs').upper(s,['perm','wide','top']);
 if(options.strict648)s=require('./i7-upper-helper-map-648.cjs').upper(s);
 return s;
};
exports.upper=(s,options={})=>{
 s=exports.sourceUpper(s,options);
 s=require('./i7-upper-s3-u-p-upper-peep.cjs').upper(s);
 if(options.strict648){
  const a='for(const q of [512,641,642,643,644,645,646,647])v.put(q,0);';
  if(s.split(a).length!==2)throw Error('U20 symbolic clean-set anchor');
  s=s.replace(a,'for(const q of [512,641,642,643,644,645,646])v.put(q,0);');
 }
 if((s.match(/const S1CreatePeep=/g)||[]).length!==1)throw Error('U20 requires exactly one final sink');
 return s;
};
