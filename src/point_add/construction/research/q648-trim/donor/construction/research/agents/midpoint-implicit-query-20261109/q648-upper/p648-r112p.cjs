'use strict';
// ringhole (q648): row 112's ORIGINAL trial/witness without logical 647 (its direction bit dv[1]). Two passes, d = 0 then 1:
// direction -> carry (take-gated), carry ^= d on taken lanes, so carry = [direction != d] there and 0 on untaken lanes; lanes with carry=1 are
// parked (take cleared); the ORIGINAL trial body (packNumber, normalize, bands, inverse) runs with the direction as the constant d in
// roundedDivisor; unpark; carry ^= d; direction^-1. Every lane executes exactly the original function, so it is equivalent on every state.
// Parked lanes are marked on f1 (forward) / qtop (witness), see below.
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('r112p anchor '+a.slice(0,60));s=s.replace(a,()=>b);};
 one("        const seq=[()=>this.direction(tape),rv=>this.packNumber(tape,rv),rv=>H.normalize(tape,rv)];",
 String.raw`        if(this.k===112&&process.env.R112P!=='0'){
          const temp=Object.create(this);temp.dv=[this.dv[0],this.carry];const cy=this.carry,tk=this.take;
          const dirC=()=>temp.direction(tape),flip=d=>()=>{if(d)tape.out(NONE,tk,cy);},park=()=>tape.out(NONE,cy,tk);
          const outer=[];
          if(process.env.R112P_DBG)outer.push(()=>{const B=tape.physical.batches,cv=x=>x>tape.one?x-1:x,bit=(q,l)=>(B[l>>5][cv(q)]>>>(l&31))&1;
            console.error('R112DBG',witness?'witness':'trial',back?'back':'fwd','take',bit(tk,0),'f1',bit(this.dv[0],0),'qtop',bit(this.qtop,0),'carry',bit(cy,0),'pick',bit(this.pick,0));});
          if(process.env.R112P_MODE==='carry'){const Hc=Object.create(H);Hc.dv=[this.dv[0],cy];const body=[rv=>this.packNumber(tape,rv),rv=>Hc.normalize(tape,rv)];
            for(const B of Bs)body.push(rv=>witness?Hc.oddWitness(tape,B,rv):Hc.oddQuotient(tape,B,rv));body.push(rv=>Hc.normalize(tape,!rv),rv=>this.packNumber(tape,!rv));
            stepList([dirC,...body,dirC],back,fn=>fn(back));return;}
          for(const d of [0,1]){
            const Hd=Object.create(H);
            Hd.roundedDivisor=function(tape,B,back){
              if(this.u39LowOne===undefined)throw Error('r112p: expected u39 divisor');
              const seq=[rv=>this.inc(tape,B.H,[],!rv),...(d?[rv=>this.inc(tape,B.H.slice(1),[],rv)]:[])];
              stepList(seq,back,fn=>fn(back));
            };
            const body=[rv=>this.packNumber(tape,rv),rv=>Hd.normalize(tape,rv)];
            for(const B of Bs)body.push(rv=>witness?Hd.oddWitness(tape,B,rv):Hd.oddQuotient(tape,B,rv));
            body.push(rv=>Hd.normalize(tape,!rv),rv=>this.packNumber(tape,!rv));
            // parking marker M (carry itself is touched ungated by the body on parked lanes, so it cannot hold the mark):
            //  forward trial: f1 (clean helper; F is not computed yet), witness: qtop (coef^-1 ran before the witness, so q holds the corrected
            //  quotient, whose top bit is clean on taken lanes; qtop is a clean helper on untaken lanes). M = [direction != d] on taken lanes, 0 elsewhere.
            const M=witness?this.qtop:this.dv[0],mk=()=>tape.out(NONE,cy,M),pk=()=>tape.out(NONE,M,tk);
            outer.push(dirC,flip(d),mk,flip(d),dirC,pk,...body,pk,dirC,flip(d),mk,flip(d),dirC);
          }
          stepList(outer,back,fn=>fn(back));return;
        }
        const seq=[()=>this.direction(tape),rv=>this.packNumber(tape,rv),rv=>H.normalize(tape,rv)];`);
 return s;
};
