'use strict';
// Source-derived from nasqret 5c8969d (n650c); experiments select prefixes.
exports.upper=(s,parts=['perm','wide','inc','top'])=>{
 for(const p of parts){
  if(p==='perm')s=require('./i9-upper-s3-shared-controls.cjs').patchPermutation(s);
  else if(p==='wide')s=require('./i9-upper-s3-wide.cjs').addWideTransforms(s);
  else if(p==='inc')s=require('./s3-increment.cjs').patchIncrement(s);
  else if(p==='top'){
   const body='    digitTopOne(tape,z,v,controls,back){\n        const B=z.slice(0,-1)';
   if(s.split(body).length!==2)throw Error('S3 base digitTopOne anchor');
   s=s.replace('class Tape {',()=>require('./i9-upper-s3-implicit-top.cjs').implicitTopDigit.toString()+'\nclass Tape {');
   s=s.replace(body,()=>body.replace('\n        const B','\n        if(v.length>=8){implicitTopDigit(tape,z,v,controls,back);return;}\n        const B'));
  }
  else if(p!=='base')throw Error('unknown variant '+p);
 }
 return s;
};
