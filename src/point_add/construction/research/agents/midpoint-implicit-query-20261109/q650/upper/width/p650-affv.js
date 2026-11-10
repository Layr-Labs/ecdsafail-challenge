'use strict';
// papers: affine rows 64..123 (and 124..125 via A[128], see below) host the rank bit tags[1] on v[k] (the coefficient's top bit: 1 on every taken lane,
// since take requires bank[k]=1; the 651 leases v[k] only in rows 0..63). Inside affine, v is read only by canon,
// mixedHeld(r,v,d) and add(v,d); canon is moved before normalizeA and normalizeA^-1 is moved up to just after
// guardedBarrel(r) (the second half touches neither a nor the tags), so v is never read while it holds tags[1].
// Taken lanes: CX(take,v[k]) clears the known one, the rank bit lives there, CX restores it.
// Untaken lanes: every rank reader between normalizeA and normalizeA^-1 is ctrl-gated, and normalizeA^-1 is the exact
// reverse, so arbitrary v[k] data is restored (the 651's U3 argument).
const V1MAX=+(process.env.V1MAX||123),A1MIN=+(process.env.A1MIN||124),A1MAX=+(process.env.A1MAX||125);
const body=String.raw`
    v1AffineBody(tape,back){
        const a=this.A.slice(0,this.half),r=this.r,v=this.v,D=this.zword.slice(0,this.half),d=D.slice(0,this.h);
        const base=this.half+1,word=[...r.slice(0,base),...D],tail=r.slice(base),g=this.ctrl,host=v.at(-1);
        if(this.tag[1]!==host||this.tag.includes(this.tags[1]))throw Error('v1 affine ports');
        const canon=rv=>this.digit(tape,[...d,this.dv[0]],v,[],rv);
        const leading=()=>tape.out(NONE,this.take,host);
        const seq=[canon,leading,rv=>this.normalizeA(tape,a,rv),
            rv=>this.guardedBarrel(tape,D,true,rv),rv=>this.parkAffine(tape,D,rv),
            rv=>this.affineProduct(tape,a,D,rv),rv=>this.guardedBarrel(tape,r,false,rv),
            rv=>this.normalizeA(tape,a,!rv),leading,
            rv=>this.reflect(tape,word,g,rv),rv=>this.inc(tape,word,g,!rv),
            rv=>this.guardedPermutation(tape,[...tail,...D],[...D,...tail],[],rv),
            rv=>this.mixedHeld(tape,r,v,d,g,!rv),()=>this.cnotList(tape,g,d),
            rv=>tape.add(v,d,g,this.carry,rv),rv=>this.inc(tape,r,g,rv),
            rv=>canon(!rv)];
        stepList(seq,back,fn=>fn(back));
    }
    affine(tape,back){
        if(this.v1Affine){this.v1AffineBody(tape,back);return;}
`;
module.exports=[
 ['    affine(tape,back){\n        if(this.u3Affine){this.u3AffineBody(tape,back);return;}', body+'        if(this.u3Affine){this.u3AffineBody(tape,back);return;}'],
 ['if(this.k>=64&&this.k<=119){H.tag=H.tag.slice();H.tag[2]=this.A[this.k<=95?this.half:this.half+1];}',
  'if(this.k>=64&&this.k<=119){H.tag=H.tag.slice();H.tag[2]=this.A[this.k<=95?this.half:this.half+1];}if(this.k>=64&&this.k<='+V1MAX+'&&!['+(process.env.V1SKIP||'')+'].includes(this.k)){H.tag[1]=this.v[this.k];H.v1Affine=true;}'+
   'if(this.k>='+A1MIN+'&&this.k<='+A1MAX+'&&this.tag.length===2){H.tag=H.tag.slice();H.tag[1]=this.A[this.half];}'],
];
// Rows 124..125 (2-bit rank, no tag[2] host): tags[1] on A[128], zero on taken lanes (A<2^128) and outside a, the 651's own
// rows-64..95 host for rank[2]; the original affine body is kept. (The v[k] body fails the production reverse there.)
