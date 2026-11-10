'use strict';
// r35 upper integration overlay (ours). Order: nasqret's 653 centerfix upper -> our g129 overlay -> optional helper
// patch list (env R35_UPATCH: file exporting [from,to] pairs, each anchor unique) -> width edits.
//  R35_FIELD11=1 : tape stays 653 wide, but the field stages and the regenerate stage are handed only the first 11
//                  clean wires (validation of the field/regen side alone: physical 652 must then be idle there).
//  R35_WIDTH=652 : the point fold tape loses one more physical site (wires 0..651), field/regen get 11 clean wires.
const path=require('path');
// R35_UBASE=path of an overlay module exporting upper(src) (e.g. upper/upper.cjs = g129 + the tags[3] group lists); default g129 only
const base=process.env.R35_UBASE?require(path.resolve(process.env.R35_UBASE)).upper:require('./g129.cjs').upper;
function one(s,a,b){if(s.split(a).length!==2)throw Error('r35 upper site '+JSON.stringify(a));return s.replace(a,b);}
function upper(s){
  s=base(s);
  if(process.env.R35_UPATCH)for(const [a,b] of require(path.resolve(process.env.R35_UPATCH)))s=one(s,a,b);
  const W=process.env.R35_WIDTH,F=process.env.R35_FIELD11==='1';
  if(W&&W!=='652'&&W!=='653')throw Error('R35_WIDTH');
  if(W==='652'){
    s=one(s,'this.ids=this.ids.slice(0,-3);','this.ids=this.ids.slice(0,-4);');
    s=one(s,'...split(2*m+b+1,logical-4)];','...split(2*m+b+1,logical-5)];');
    s=one(s,'new Set(map).size!==logical-4||map.length!==logical-4','new Set(map).size!==logical-5||map.length!==logical-5');
    s=one(s,'2*m+m/2+6+Math.ceil(Math.log2(m/2))','2*m+m/2+5+Math.ceil(Math.log2(m/2))');
  }
  if(W==='652'||F){
    const n=W==='652'?11:12;
    s=one(s,'(i===648||i>=653)?-2:clean[z++];if(clean.length!==12||z!==12)','(i===648||i>=652)?-2:clean[z++];if(clean.length!=='+n+'||z!==11)');
    s=one(s,'ids[645]=-2;ids[652]=-2;ids[653]=-2;','ids[645]=-2;ids[651]=-2;ids[652]=-2;ids[653]=-2;');
    s=one(s,'if(j!==12)throw Error("Q653 history geometry");','if(j!==11||clean.length!=='+n+')throw Error("Q652 history geometry");');
  }
  return s;
}
module.exports={upper};
