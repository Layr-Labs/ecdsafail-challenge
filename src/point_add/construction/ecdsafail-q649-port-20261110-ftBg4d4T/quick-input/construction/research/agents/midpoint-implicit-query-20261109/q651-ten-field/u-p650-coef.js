'use strict';
// q650 upper saving: in the production forward ladder (PointFoldTape has tape.hist) rows 0..112 run
// coef^-1 ; hmr(f1) ; coef with nothing else between. coef=mixed(q,v,u,ctrl) never touches f1, so the pair cancels.
module.exports=[
 ['rv=>tape.add(v,this.A,[...g,flag],this.carry,!rv),rv=>coef(!rv),','rv=>tape.add(v,this.A,[...g,flag],this.carry,!rv),rv=>{if(tape.hist&&!rv)return;coef(!rv);},'],
 ['},coef,rv=>this.affine(tape,rv),','},rv=>{if(tape.hist&&!rv)return;coef(rv);},rv=>this.affine(tape,rv),'],
];
