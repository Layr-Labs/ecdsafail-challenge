'use strict';
const path=require('node:path');
const baseline=require(path.resolve(process.argv[2],'d14-peep.cjs')).createPeep, indexed=require('./fast-window.cjs').createPeep;
let seed=0x61404;
const draw=()=>seed=(Math.imul(seed,1664525)+1013904223)>>>0;
let gates=0, snapshots=0;
for(const mode of ['strict','commute'])for(const window of [1,2,3,7,16,35,128,4096]){
    const left=[],right=[],a=baseline((x,y,z)=>left.push(x,y,z),{window,mode}),b=indexed((x,y,z)=>right.push(x,y,z),{window,mode});
    const history=[];
    const round=()=>{if(left.length!==right.length||left.some((x,i)=>x!==right[i]))throw Error('output mismatch '+[mode,window,gates]);
        if(JSON.stringify(a.stats)!==JSON.stringify(b.stats)||JSON.stringify(a.pending())!==JSON.stringify(b.pending()))throw Error('state mismatch '+[mode,window,gates]);
        left.length=right.length=0;snapshots++;};
    for(let i=0;i<20000;i++){
        const kind=draw()>>>12;let g;
        if(history.length&&(kind%5===0||i%17===0))g=history[(draw()>>>8)%history.length].slice();
        else{
            const wires=4+((i>>10)%23),z=(draw()>>>8)%wires;let x=(draw()>>>8)%wires,y=(draw()>>>8)%wires;
            if(x===z)x=(x+1)%wires;
            while(y===z||y===x)y=(y+1)%wires;
            if(kind%3!==0)x=1023;if(kind%7===0)y=1023;
            g=[x,y,z];
        }
        if(i%11===0)[g[0],g[1]]=[g[1],g[0]];
        a.gate(...g);b.gate(...g);gates++;history.push(g);if(history.length>53)history.shift();
        if(i%71===0)round();
        if((draw()>>>8)%617===0){a.flush();b.flush();round();}
    }
    a.flush();b.flush();round();
}
console.log(JSON.stringify({gates,snapshots,allPendingAndEmittedGatesAndCountersIdentical:true}));
