'use strict';
// q650 upper overlay (ringhole). Applied to the final q651 upper source (q651/upper651.cjs output). Each anchor must be unique.
//   SAVINGS: op savings that keep the 651 geometry (-30.26M, pipeline PASS at 651).
//   WIDTH:   the upper never touches logical tags[1]=651 (physical 650). Geometry for 650 is added by hole.
const path=require('path');
const SAVINGS=['p650-coef.js','p650-tail.js'];
const WIDTH=['p650-coef.js','width/p650-probe3.js','width/p650-v112.js','width/p650-trial.js','width/p650-affv.js','width/p650-aff4.js','width/p650-aff0.js','width/p650-save2.js'];
function apply(s,lists=SAVINGS){
  for(const f of lists)for(const e of require(path.join(__dirname,f))){const [a,b]=e.length===3?e.slice(1):e;
    if(s.split(a).length!==2)throw Error('q650 upper anchor '+f+' '+JSON.stringify(a.slice(0,70)));s=s.replace(a,()=>b);}
  return s;
}
// Install over q651/upper651.cjs before q651/point.cjs is loaded.
function install(lists=SAVINGS){const u=require(path.join(__dirname,'../../q651/upper651.cjs'));if(u.__q650)return;const old=u.upper;u.upper=src=>apply(old(src),lists);u.__q650=true;}
module.exports={apply,install,SAVINGS,WIDTH,LISTS:SAVINGS};
