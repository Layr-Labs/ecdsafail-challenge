'use strict';
// r35/upper TWOFLAG group (ours): [group, from, to] over the composed generator (pinned centered-point + centerfix + g129
// + the 'helpers' group of snap1/p-wip-frozen.js, whose hostRank()/digitDirty() are CALLED here, never redefined).
// Rows 113..119 (two-flag core, tag.length===4): no gate under core/core/(estimate|removeDebt) touches logical tags[3] (653).
// Rows 120..127 have tag.length<4, hostRank() returns `this`, nothing changes there. Rows 0..112 never call these methods.
const P=[];
const add=(from,to)=>P.push(['twoflag',from,to]);

// ---- sub-step 1: TruncatedGeneral.estimate, rank window normalize..~normalize: fourth rank bit on f2 = this.dv[1] ----
// f1/f2 are zero and untouched from row entry until the sign probes; estimate is the first step of UniversalGeneral.core.
// Every reader of this.tag inside the window (normalize, middleDigit, reducedTerm, moveQuotient -> indicator) runs on H.
// pick keeps its role as the clean digit ancilla (middleDigit), so no digit changes: the gate list is the old one with 653 -> 647.
add(
`        const D=this.topDivisor(),Q=this.q,g=this.ctrl,js=split(0,this.maxShift+1),seq=[
            rv=>this.packNumber(tape,rv),rv=>this.normalize(tape,rv),
            ()=>this.cnotList(tape,g,Q),
            ()=>{for(let i=0;i<Q.length;i++)this.toggle(tape,[...g,D[i]],[],Q[i]);}
        ];
        for(let j=this.maxShift-1;j>=0;j--)seq.push(rv=>this.middleDigit(tape,j,D,rv));
        seq.push(rv=>this.inc(tape,Q,g,rv));
        for(const j of js)seq.push(rv=>this.reducedTerm(tape,D,j,rv));
        for(const j of js)seq.push(rv=>this.moveQuotient(tape,j,rv));
        seq.push(rv=>this.normalize(tape,!rv),rv=>this.packNumber(tape,!rv));`,
`        const H=this.hostRank(this.dv[1]);
        const D=this.topDivisor(),Q=this.q,g=this.ctrl,js=split(0,this.maxShift+1),seq=[
            rv=>this.packNumber(tape,rv),rv=>H.normalize(tape,rv),
            ()=>this.cnotList(tape,g,Q),
            ()=>{for(let i=0;i<Q.length;i++)this.toggle(tape,[...g,D[i]],[],Q[i]);}
        ];
        for(let j=this.maxShift-1;j>=0;j--)seq.push(rv=>H.middleDigit(tape,j,D,rv));
        seq.push(rv=>this.inc(tape,Q,g,rv));
        for(const j of js)seq.push(rv=>H.reducedTerm(tape,D,j,rv));
        for(const j of js)seq.push(rv=>H.moveQuotient(tape,j,rv));
        seq.push(rv=>H.normalize(tape,!rv),rv=>this.packNumber(tape,!rv));`);

// ---- sub-step 2: TruncatedGeneral.removeDebt, rank window normalize..~normalize: fourth rank bit on pick ----
// f1/f2 are the threshold targets here, so the host is pick. The only use of pick inside the window is the clean ancilla of
// the mixedHead digits (control carry). hostRank(pick) returns a layer whose digit() is digitDirty(): same map on (z,D,carry),
// one restored dirty loan (lowest free id, never a helper) instead of pick, 6 CCX per bit instead of 3.
// normalize and both thresholds (installZeros, mixedHead, indicator) run on H; inc(Q) never reads the rank.
add(
`        const g=this.ctrl,Q=this.q;
        const seq=[rv=>this.packNumber(tape,rv),rv=>this.normalize(tape,rv),
            rv=>this.inc(tape,Q,g,rv),()=>this.threshold(tape,this.dv[0]),
            rv=>this.inc(tape,Q,g,rv),()=>this.threshold(tape,this.dv[1]),
            rv=>this.inc(tape,Q,g,!rv),rv=>this.inc(tape,Q,g,!rv),
            rv=>this.normalize(tape,!rv),rv=>this.packNumber(tape,!rv)];`,
`        const g=this.ctrl,Q=this.q,H=this.hostRank(this.pick);
        const seq=[rv=>this.packNumber(tape,rv),rv=>H.normalize(tape,rv),
            rv=>this.inc(tape,Q,g,rv),()=>H.threshold(tape,this.dv[0]),
            rv=>this.inc(tape,Q,g,rv),()=>H.threshold(tape,this.dv[1]),
            rv=>this.inc(tape,Q,g,!rv),rv=>this.inc(tape,Q,g,!rv),
            rv=>H.normalize(tape,!rv),rv=>this.packNumber(tape,!rv)];`);

module.exports=P;
