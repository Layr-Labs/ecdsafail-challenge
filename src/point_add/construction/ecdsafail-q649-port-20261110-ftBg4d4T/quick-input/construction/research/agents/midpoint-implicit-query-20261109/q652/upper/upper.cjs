'use strict';
// r35/upper overlay (ours): g129 upper + patch lists that keep the upper stage off logical tags[3] (physical 652).
// upper(src) takes nasqret's pinned centered-point source (as q653-centerfix/upper.cjs does) and returns the patched source.
// env R35_UPPER_GROUPS=comma list restricts the applied groups (testing); R35_UPPER_NARROW=0 keeps PointFoldTape at 12 helpers.
const path=require('path'),fs=require('fs');
const g129=require('../g129.cjs').upper;
const one=(src,from,to,what)=>{const i=src.indexOf(from);if(i<0)throw Error('r35/upper anchor missing: '+what+' '+JSON.stringify(from.slice(0,70)));
  if(src.indexOf(from,i+1)>=0)throw Error('r35/upper anchor not unique: '+what+' '+JSON.stringify(from.slice(0,70)));return src.slice(0,i)+to+src.slice(i+from.length);};
const lists=()=>{const out=[];for(const f of fs.readdirSync(__dirname).filter(f=>/^p-.*\.js$/.test(f)).sort()){
  for(const e of require(path.join(__dirname,f)))out.push(e.length===3?e:[f.replace(/^p-|\.js$/g,''),...e]);}return out;};
// the upper never maps logical tags[3]: drop one more physical site from the point fold
const narrow=[
  ["super(logical,[],l.g);this.ids=this.ids.slice(0,-3);const b=l.bank.length,m=l.m;","super(logical,[],l.g);this.ids=this.ids.slice(0,-4);const b=l.bank.length,m=l.m;"],
  ["...y,...split(2*m+b+1,logical-4)];","...y,...split(2*m+b+1,logical-5)];"],
  ["if(new Set(map).size!==logical-4||map.length!==logical-4)throw Error(\"point fold mapping\");","if(new Set(map).size!==logical-5||map.length!==logical-5)throw Error(\"point fold mapping\");"],
];
exports.upper=src=>{
  let s=g129(src);const only=process.env.R35_UPPER_GROUPS?new Set(process.env.R35_UPPER_GROUPS.split(',')):null;
  for(const [group,from,to] of lists()){if(only&&group!=='helpers'&&!only.has(group))continue;s=one(s,from,to,group);}
  if(process.env.R35_UPPER_NARROW==='1')for(const [from,to] of narrow)s=one(s,from,to,'narrow');
  return s;
};
exports.narrow=narrow;
