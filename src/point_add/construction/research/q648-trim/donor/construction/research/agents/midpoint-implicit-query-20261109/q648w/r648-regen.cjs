'use strict';
// ledger q648: regeneration on SEVEN helper sites (0,1,130,131,646,647,648; logical 388 evicted) for jackylee0424's R6.
// Shared walk component: ./walktf.cjs (TstRelay). Edits (applied by r648-load.cjs when Q648_REGEN=1):
//  park  : yq moves onto the active band's normalized M top (constant-one band arithmetic; cleared under the band
//          marker 646), so 130 (old yq) is Jtop: the top quotient digit b.
//  b     : 130 --exchange--> L[129] (walk6) --shifts6--> wire 1 --scale hops 1/131--> wire 1 --shifts^-1--> L[129]
//          (stage-4 walk) --exchange--> 130 (exit park). TstRelay walks never touch L[n+1].
//  walk6 : TstRelay(5) on real tags 647,648,R[129] + row top, fire T[0] (their small-v remap is not needed).
//  scale : b hops 1->131 before exec block 1, 131->1 before block 6, 1->131 before block 1695, 131->1 after the last
//          (per-block free-wire map of their scale: wire 1 free in blocks 6..1694, 131 free in 0..5 and 1690..1700).
//  walk  : TstRelay(4) on real tags 647,R[129] + row top, fire 648.
const path=require('path');
function walkTF(){return require(path.join(__dirname,'walktf.cjs'));}
function parkOverride(park){
  const plainAdd=Object.getPrototypeOf(park).add,vtop=new Set();
  park.add=function(c,a,b,unused,h){
    if(!vtop.has(a))return plainAdd.call(this,c,a,b,unused,h);
    // a's top is a virtual constant one (its wire hosts yq); add the low word and the constant (TopHost rule).
    const lo=a.slice(0,-1),bl=b.slice(0,-1),z=b.at(-1);
    if(h!==null)this.op(c.concat(z),h);
    plainAdd.call(this,c,lo,bl,0,z);
    this.op(c,z);
    if(h!==null){this.raw(-1,-1,z);this.lt(c.concat(z),lo,bl,h);this.raw(-1,-1,z);}
  };
  park.parking=function(){
    const band=this.band||16,k=Math.log2(band);
    this.tag=[647,648,0,1].slice(0,k);this.Jtop=130;
    const blocks=[],push=(fn,rev=false)=>blocks.push({fn,rev});
    const norm=j=>{const s=1<<j;
      for(let h=band;h<=this.m;h+=band){this.zer([],this.M.slice(h-s),this.tag[j]);this.zer([],this.M.slice(h-band),this.tag[j]);}
      this.rot([this.tag[j]],this.M,s);};
    for(let j=k;j--;)push(()=>norm(j));
    for(let h=band;h<=this.m;h+=band){
      const M=this.M.slice(0,h),S=this.S.slice(0,h),e=[646],yq=M[h-1];vtop.add(M);
      const higher=[];for(let t=h+band;t<=this.m;t+=band)higher.push(this.M[t-1]);
      const mark=()=>this.zer([this.M[h-1]],higher,646);
      push(mark);push(()=>this.op(e,yq));
      for(let kk=this.m-h;kk>=0;kk--)push(()=>this.restore(e,M,this.S.slice(kk,kk+h),0,kk===this.m-h?this.Jtop:this.S[kk+h]));
      for(let i=0;i<band-1;i++)push(()=>{
        this.less(e,this.tag,i,this.f);const c=[this.f];
        for(const b of S)this.swap(c,yq,b);
        this.restore(c,M,S,0,yq);
        this.op(c.concat(yq),S[0]);this.op(c.concat(S[0]),yq);
        this.less(e,this.tag,i,this.f);});
      for(let j=0;j<k;j++)push(()=>this.rot(e.concat(this.tag[j]),S,-(1<<j)));
      for(let i=h-band+1;i<h;i++)push(()=>{this.less(e,this.tag,h-1-i,this.f);this.swap([this.f],this.S[i],this.T[i]);this.less(e,this.tag,h-1-i,this.f);});
      push(()=>{for(let i=h;i<this.m;i++)this.swap(e,this.S[i],this.T[i]);});
      push(()=>this.op(e,yq));push(mark);
    }
    for(let j=0;j<k;j++)push(()=>norm(j),true);
    return blocks;};
  return park;
}
function walk6Plan(w6,scale,n){const {TstRelay}=walkTF();const tw=new TstRelay(n,[647,648,w6.R[n+1]],scale.T[0]);
  if(tw.sign!==w6.sign||tw.y[0]!==w6.y[0])throw Error('layout6');return tw.plan().map(b=>({...b,fn:()=>{tw.g=w6.g;b.fn();}}));}
function walk4Plan(walk,n){const {TstRelay}=walkTF();const tw=new TstRelay(n,[647,walk.R[n+1]],648);
  if(tw.sign!==walk.sign||tw.y[0]!==walk.y[0])throw Error('layout4');return tw.plan().map(b=>({...b,fn:()=>{tw.g=walk.g;b.fn();}}));}
function scalePlan(blocks,scale){
  if(blocks.length!==1701)throw Error('scale block count '+blocks.length);
  const E=blocks.slice().reverse(),sw=(a,b)=>({fn:()=>scale.swap([],a,b),rev:false});
  const out=[];for(let e=0;e<E.length;e++){if(e===1)out.push(sw(1,131));if(e===6)out.push(sw(131,1));if(e===1695)out.push(sw(1,131));out.push(E[e]);}
  out.push(sw(131,1));return out.reverse();}
const EDITS=[
  ["park=new R37Park(n,false,[])","park=require("+JSON.stringify(__filename)+").parkOverride(new R37Park(n,false,[]))"],
  ["[walk6,r42HostPlan(walk6,scale).concat([shifts6]),true]","[walk6,require("+JSON.stringify(__filename)+").walk6Plan(walk6,scale,n).concat([shifts6]),true]"],
  ["[scale,[{fn:mv}].concat(scale.plan(),[{fn:mv,rev:true}]),false]","[scale,require("+JSON.stringify(__filename)+").scalePlan([{fn:mv}].concat(scale.plan(),[{fn:mv,rev:true}]),scale),false]"],
  ["[walk,r43RelayPlan(walk).concat([shifts]),false]","[walk,require("+JSON.stringify(__filename)+").walk4Plan(walk,n).concat([shifts]),false]"],
];
// 649-width SAVING (8 sites, b stays on 388): stage-4 walk -> TstRelay(5) on 647,L[129],R[129] + fire 648.
function walk5Plan(walk,n){const {TstRelay}=walkTF();const tw=new TstRelay(n,[647,walk.L[n+1],walk.R[n+1]],648);
  if(tw.sign!==walk.sign||tw.y[0]!==walk.y[0])throw Error('layout5');return tw.plan().map(b=>({...b,fn:()=>{tw.g=walk.g;b.fn();}}));}
const EDITS_SAVE649=[["[walk,r43RelayPlan(walk).concat([shifts]),false]","[walk,require("+JSON.stringify(__filename)+").walk5Plan(walk,n).concat([shifts]),false]"]];
// Mode 1k: as EDITS but both walks are TstRelayK (two-relayed-bit sectors): walk6 k=3 {647,648,R[129]} fire T[0];
// stage-4 k=2 {647,R[129]} fire 648. Same seven sites and the same b route.
function walkK(w,n,real,fire,opts={}){const {TstRelayK}=require(path.join(__dirname,'walkt1.cjs'));const tw=new TstRelayK(n,real,fire,Object.assign({flat:false},opts));
  if(tw.sign!==w.sign||tw.y[0]!==w.y[0])throw Error('layoutK');return tw.plan().map(b=>({...b,fn:()=>{tw.g=w.g;b.fn();}}));}
function walk6K(w6,scale,n){return walkK(w6,n,[647,648,w6.R[n+1]],scale.T[0]);}
function walk4K(walk,n){return walkK(walk,n,[647,walk.R[n+1]],648);}
// Mode 1kr: as 1k, with per-row relay caps (highJ sectors, J<=6) measured by w648-rowopt (relayAt-rg6/rg4.json).
const RA=f=>JSON.parse(require('fs').readFileSync(path.join(__dirname,f),'utf8'));
function walk6KR(w6,scale,n){return walkK(w6,n,[647,648,w6.R[n+1]],scale.T[0],{maxRelay:6,relayAt:RA('relayAt-rg6.json')});}
function walk4KR(walk,n){return walkK(walk,n,[647,walk.R[n+1]],648,{maxRelay:6,relayAt:RA('relayAt-rg4.json')});}
const F=JSON.stringify(__filename);
const EDITS_1K=EDITS.map(([a,b])=>[a,b.replace(".walk6Plan(walk6,scale,n)",".walk6K(walk6,scale,n)").replace(".walk4Plan(walk,n)",".walk4K(walk,n)")]);
const EDITS_1KR=EDITS.map(([a,b])=>[a,b.replace(".walk6Plan(walk6,scale,n)",".walk6KR(walk6,scale,n)").replace(".walk4Plan(walk,n)",".walk4KR(walk,n)")]);
module.exports={EDITS,EDITS_1K,EDITS_1KR,walk6KR,walk4KR,walk6K,walk4K,EDITS_SAVE649,parkOverride,walk6Plan,walk4Plan,walk5Plan,scalePlan};
