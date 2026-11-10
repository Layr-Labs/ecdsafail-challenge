'use strict';
// q650 upper: rows without the coefficient-direction lease (k>=112: trial/witness of row 112, estimate and removeDebt of
// rows 113..125) host rank bit 1 (logical tags[1]=651) on v[k]. v[k] is V's top bit, 1 on taken lanes; CX(take->v[k]) clears
// it right after packNumber and restores it right before the unpack. Nothing between those points reads v. Untaken lanes:
// every writer in the window is ctrl-gated or compute/uncompute paired, so arbitrary v[k] data is restored.
module.exports=[
 ['    hostRank(host){',
  `    q650vHost(H){
        if(this.useCoefficientDirection||H.tag.length<2||H.tag[1]!==651)return false;
        H.tag=H.tag.slice();H.tag[1]=this.v[this.k];return true;
    }
    hostRank(host){`],
 // estimate
 ['if(H.tag.length>=3)H.tag[2]=this.dv[0];\n        const D=this.topDivisor(),Q=this.q,g=this.ctrl,js=split(0,this.maxShift+1),seq=[\n            rv=>this.packNumber(tape,rv),rv=>H.normalize(tape,rv),',
  'if(H.tag.length>=3)H.tag[2]=this.dv[0];\n        const vh=this.q650vHost(H),vl=()=>{if(vh)tape.out(NONE,this.take,this.v[this.k]);};\n        const D=this.topDivisor(),Q=this.q,g=this.ctrl,js=split(0,this.maxShift+1),seq=[\n            rv=>this.packNumber(tape,rv),vl,rv=>H.normalize(tape,rv),'],
 ['seq.push(rv=>H.normalize(tape,!rv),rv=>this.packNumber(tape,!rv));','seq.push(rv=>H.normalize(tape,!rv),vl,rv=>this.packNumber(tape,!rv));'],
 // removeDebt
 ['if(this.k>=113&&this.k<=119){H.tag=H.tag.slice();H.tag[2]=this.carry;H.uDebt=true;}\n        const seq=[rv=>this.packNumber(tape,rv),rv=>H.normalize(tape,rv),',
  'if(this.k>=113&&this.k<=119){H.tag=H.tag.slice();H.tag[2]=this.carry;H.uDebt=true;}\n        const vh=this.q650vHost(H),vl=()=>{if(vh)tape.out(NONE,this.take,this.v[this.k]);};\n        const seq=[rv=>this.packNumber(tape,rv),vl,rv=>H.normalize(tape,rv),'],
 ['            rv=>H.normalize(tape,!rv),rv=>this.packNumber(tape,!rv)];','            rv=>H.normalize(tape,!rv),vl,rv=>this.packNumber(tape,!rv)];'],
 // OddEstimate trial (reached by row 112 only)
 ['        const H=this.uTrialRank(witness);\n        const seq=[()=>this.direction(tape),rv=>this.packNumber(tape,rv),rv=>H.normalize(tape,rv)];',
  '        const H=Object.create(this.uTrialRank(witness));H.tag=H.tag.slice();const vh=this.q650vHost(H),vl=()=>{if(vh)tape.out(NONE,this.take,this.v[this.k]);};\n        const seq=[()=>this.direction(tape),rv=>this.packNumber(tape,rv),vl,rv=>H.normalize(tape,rv)];'],
 ['seq.push(rv=>H.normalize(tape,!rv),rv=>this.packNumber(tape,!rv),()=>this.direction(tape));','seq.push(rv=>H.normalize(tape,!rv),vl,rv=>this.packNumber(tape,!rv),()=>this.direction(tape));'],
];
