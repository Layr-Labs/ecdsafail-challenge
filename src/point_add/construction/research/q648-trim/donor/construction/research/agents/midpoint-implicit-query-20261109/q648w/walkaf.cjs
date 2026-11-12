'use strict';
// Aux-free sector walk for the regen: the regen's own SectorSigned source (q654-next walks `split`) with the six
// aux-elimination edits the 651 divide made for its D2 walks (q651/p-divide-d4.js, D2Flat). Nothing else differs.
const P=require('../q653-next/parts.cjs');
function one(s,a,b){if(s.split(a).length!==2)throw Error('walkaf anchor '+a.slice(0,60));return s.replace(a,()=>b);}
let s=P.split;
const r0=s.indexOf(' restore(c,a,b,unused,h){'),r1=s.indexOf(' multag(');
if(r0<0||r1<r0||s.indexOf(' restore(c,a,b,unused,h){',r0+1)>=0)throw Error('walkaf restore anchor');
s=s.slice(0,r0)+" restore(c,a,b,unused,h){if(c.length!==1)throw Error('control');for(const z of dirtyDigit(a,b,h,c[0],this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));}\n"+s.slice(r1);
s=one(s,'one(all,()=>{const qcond=()=>{this.op([r[m-1]],this.aux);this.raw(-1,-1,r[m-1]);this.lt([r[m-1]],r.slice(0,-1),A.slice(1),this.aux);this.raw(-1,-1,r[m-1]);};qcond();this.op([this.fire,this.aux],this.tst);for(const z of u)this.raw(-1,-1,z);this.lt([this.fire,this.aux],v,u,this.tst);',
 'one(all,()=>{const qa=this.tag[0],qcond=()=>{this.op([r[m-1]],qa);this.raw(-1,-1,r[m-1]);this.lt([r[m-1]],r.slice(0,-1),A.slice(1),qa);this.raw(-1,-1,r[m-1]);};qcond();this.op([this.fire,qa],this.tst);for(const z of u)this.raw(-1,-1,z);this.lt([this.fire,qa],v,u,this.tst);');
s=one(s,'match(c,r,this.aux);select(this.fire);this.op([this.aux],this.fire);this.op(c,this.aux);','match(c,r,tag[0]);select(this.fire);this.op([tag[0]],this.fire);this.op(c,tag[0]);');
s=one(s,'this.raw(-1,-1,this.aux);for(const z of digit(m,r.slice(0,-1).concat(this.aux),A,r[m-1],this.fire,this.tst))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));this.raw(-1,-1,this.aux);',
 'this.raw(-1,-1,this.tst);for(const z of dirtyDigit(r.slice(0,-1).concat(this.tst),A,r[m-1],this.fire,this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));this.raw(-1,-1,this.tst);');
s=one(s,'const en=[this.tst],rh=r.slice(i+1),ah=A.slice(i+1);for(const z of A.slice(i))this.swap(en,this.aux,z);this.raw(-1,-1,r[0]);this.restore(en,rh.slice(0,-1).concat(r[0]),ah,0,this.aux);this.raw(-1,-1,r[0]);this.op(en.concat(this.aux),A[i]);this.op(en.concat(A[i]),this.aux);',
 'const en=[this.tst],rh=r.slice(i+1),ah=A.slice(i+1),carry=r[i];for(const z of A.slice(i))this.swap(en,carry,z);for(const z of dirtyDigit(rh.slice(0,-1).concat(this.fire),ah,carry,this.tst,this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));this.op(en.concat(carry),A[i]);this.op(en.concat(A[i]),carry);');
if(/this\.aux\b(?!=)/.test(s.slice(s.indexOf(' plan(){'),s.indexOf('class FlatUnit'))))throw Error('walkaf: aux left in plan');
const Base=Function('module','dirtyDigit',s+'\nreturn UnitWalk;')({exports:{}},P.dirtyDigit);
class SignedAF extends Base{constructor(n,j=6){super(n);this.tag=this.tag.slice(0,Math.min(j,this.tag.length));}}
module.exports={SignedAF,source:s};
