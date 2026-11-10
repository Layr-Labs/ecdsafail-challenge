'use strict';
// r35/upper PROBE group (ours): [group, from, to] over the composed generator (pinned centered-point + centerfix + g129
// + snap1 helpers/trial). Scope: single-flag rows 0..112 only. Rows 113..127 are left exactly as received
// (the integrator re-hosts the two-flag probes at the loop level through a layer whose tags[3] is already the host).
//
// The aligned sign probe uses logical tags[3] (id 653) only as the fourth bit of its rank register `tag`
// (rank, both barrels, the parkTail marks and the alignedMix marks all receive the same `tag` array).
// probeTag() swaps that one entry for an idle clean wire:
//   base 129 rows (g129 mode, 0..61, 63..94, 96..110, 112): the borrow wire A.at(-1); guardTop() does not use it there.
//   base 130 rows (62, 95, 111): f2 (logical 647 = aux[3]); the rank is one bit narrower there, so f2 is not a rank bit.
const P=[];
const add=(group,from,to)=>P.push([group,from,to]);

// helper, injected in front of AlignedGeneral.alignedSign (anchor inside a method this group owns)
add('probe',
"    alignedSign(tape,target){\n        const base=this.ab,w=this.half+1;",
`    // r35 probe: rank register of the aligned sign probe with its fourth bit re-hosted (rows 0..112 only).
    probeTag(base,tag,target){
        if(this.k>112||tag.length<4)return tag;
        const f2=this.aux[3],borrow=this.A.at(-1),top=this.guardTop(),S=this.A.slice(0,this.half+1);
        if(f2!==this.take-1||borrow!==this.borrow||!this.layouts())throw Error("probe host ports");
        // ancilla of the clean tail digit (UnguardedGeneral.alignedMix/tailDigit), when that path is taken
        const tailAncilla=!this.wideBand?this.dv[1]:null;
        const busy=new Set([...tag,...top,...S,...this.r,...this.zword,target,this.take,this.g,this.pick,this.carry,this.v[this.k],tailAncilla]);
        const host=base===this.half+1?borrow:f2;
        if(busy.has(host))throw Error("probe rank host is busy "+[this.k,base,host]);
        const out=tag.slice();out[3]=host;return out;
    }
    alignedSign(tape,target){
        const base=this.ab,w=this.half+1;`);

// the single place where the probe's rank register is formed
add('probe',
"const free=this.r.length-base,tag=this.tags.slice(0,free?Math.floor(Math.log2(free))+1:0),S=this.A.slice(0,w),D=this.zword.slice(0,w);",
"const free=this.r.length-base,tag=this.probeTag(base,this.tags.slice(0,free?Math.floor(Math.log2(free))+1:0),target),S=this.A.slice(0,w),D=this.zword.slice(0,w);");

module.exports=P;
