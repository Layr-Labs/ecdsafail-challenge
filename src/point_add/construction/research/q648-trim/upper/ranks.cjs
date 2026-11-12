'use strict';
const {source,compiler}=require('./build.cjs'),{patch}=require('./index.cjs'),{createHash}=require('node:crypto');
const k=Number(process.argv[2]),width=657,none=1023;
if(!Number.isInteger(k)||k<0||k>123)throw Error('Q648 affine row');
const ordinary=source();
function environment(s) {
    const m={exports:{}},pre='return {pointReference,exceptionTable,';
    s=s.replace(pre,'return {Tape,UnguardedGeneral,main:typeof mainDigits==="undefined"?null:mainDigits,pointReference,exceptionTable,');
    return Function('module','require',s+'\nreturn module.exports;')(m,require);
}
const base=environment(ordinary),next=environment(patch(ordinary,compiler,'mask'));
function context(E){
    const row=new E.UnguardedGeneral(256,(1n<<32n)+977n,k,width);
    let H;row.u3AffineBody=function(){H=this;};row.affine({},false);
    if(!H||!H.u12)throw Error('affine owner');return H;
}
const ref=context(base),candidate=context(next),a=ref.A.slice(0,128),d=ref.zword.slice(0,128),r=ref.r.slice(0,129);
const two=n=>1n<<BigInt(n);
let seed=0x674189a3;function rand32(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return seed>>>0;}
function random(n){let v=0n;for(let j=0;j<n;j+=32)v=(v<<32n)|BigInt(rand32());return v%two(n);}
const rows=[];
for(let s=0;s<=ref.maxShift;s++) {
    const prefix=two(127);
    for(const suffix of [0n,1n,2n,3n,4n,5n,6n,7n,random(127-s)])for(const en of [0,1]) {
        const A=prefix|((suffix%two(127-s))<<BigInt(s));
        rows.push({s,A,en,x:random(129),y:random(128)});
    }
}
const words=Array.from({length:Math.ceil(rows.length/32)},()=>Uint32Array.from({length:width},rand32));
const put=(st,w,v,l)=>{const mask=1<<(l&31);for(const q of w){st[q]=(st[q]&~mask)|(v&1n?mask:0);v>>=1n;}};
for(let i=0;i<words.length*32;i++){
    const st=words[i>>5],{s,A,en,x,y}=rows[i%rows.length],take=BigInt(en);
    put(st,a,A,i);put(st,r,x,i);put(st,d,y,i);put(st,[ref.carry],0n,i);put(st,[ref.take],take,i);
    const low=Number(A&1n),next=Number((A>>1n)&1n);
    const z=Number((A>>2n)&1n),h=ref.u648?3:2;
    const tag=s>=h?s:(s===0?low+2*next:s===1?4+next:8)+(ref.u648?16*z:0);
    put(st,ref.tag,BigInt(tag),i);put(st,[a[1]],BigInt(s<h),i);
}
function run(E,H,flag,back) {
    const state=words.map(w=>w.slice()),t=new E.Tape(width,state,null,none),layer=Object.create(H);
    // The source fold excludes these absent logical helper sites.
    t.ids=t.ids.filter(q=>q!==H.g&&q!==647&&q<650);
    layer.digit=layer.digitTopOne;
    if(flag)E.main(H,t,layer,r,a,d,back,'clean');
    else layer.mixed(t,r,a,d,[H.take],back);
    return {state,counts:t.count};
}
const receipt={row:k,cases:rows.length,lowBits:ref.u648?3:2,rankInterval:[0,ref.maxShift],direction:{}};
for(const back of [false,true]){
    const old=run(base,ref,false,back),fresh=run(next,candidate,true,back);
    const h=createHash('sha256');
    for(let g=0;g<old.state.length;g++){
        for(let q=0;q<width;q++)if(fresh.state[g][q]!==old.state[g][q])throw Error('rank disagreement '+[k,back,q,g]);
        h.update(new Uint8Array(fresh.state[g].buffer));
    }
    receipt.direction[back?'reverse':'forward']={old:old.counts,fresh:fresh.counts,sha256:h.digest('hex')};
}
console.log(JSON.stringify(receipt,null,2));
