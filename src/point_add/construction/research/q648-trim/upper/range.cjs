'use strict';
const path=require('node:path'),fs=require('node:fs'),{createHash}=require('node:crypto');
const {check}=require('./row.cjs');
const B=require('./build.cjs'),{patch}=require('./index.cjs'),source=B.source();
const sha=s=>createHash('sha256').update(s).digest('hex');
const expected=[sha(source),sha(patch(source,B.compiler,'both')),sha(patch(source,B.compiler))];
const save=f=>path.join(__dirname,f),acc=[];
const pending=save('rows-all.partial.jsonl');
const prior=fs.existsSync(pending)?fs.readFileSync(pending,'utf8').trimEnd().split('\n').filter(Boolean).map(x=>JSON.parse(x)):[];
for(let k=0;k<128;k++){
    const cached=save('row'+k+'-mask.json'),second=save('row'+k+'-both.json');
    let result;
    if(prior[k]&&prior[k].row===k)result=prior[k];
    else if(fs.existsSync(cached)&&fs.existsSync(second)){
        const old=JSON.parse(fs.readFileSync(second));
        result=JSON.parse(fs.readFileSync(cached));
        if(old.candidate[0].sha!==result.candidate[0].sha||old.candidate[1].sha!==result.candidate[1].sha)throw Error('stale row '+k);
        result.ported=old.candidate;result.previousSha256=old.candidateSha256;
    }else {
        result=check(k,'mask',true,true);
    }
    if(result.donorSha256!==expected[0]||result.previousSha256!==expected[1]||result.candidateSha256!==expected[2])throw Error('source mismatch at row '+k);
    acc.push(result);
    if(!prior[k])fs.appendFileSync(pending,JSON.stringify(result)+'\n');
    if((k&15)===15)console.error('passed Q648 general rows 0..'+k);
}
const totals={};
for(const name of ['original','ported','candidate']){
 const sums=[[0,0,0],[0,0,0]];
 for(const r of acc)for(let i=0;i<3;i++){sums[0][i]+=r[name][0].counts[i];sums[1][i]+=r[name][1].counts[i]-r[name][0].counts[i];}
 totals[name]={forward:sums[0],reverse:sums[1],pair:sums[0].map((v,j)=>v+sums[1][j])};
}
const rows=acc.map(r=>JSON.stringify(r)).join('\n')+'\n';
fs.writeFileSync(save('rows-all.jsonl'),rows);
const output={scope:'All independently initialized general upper rows before stream peepholes; omits the EarlyUnit rows and the rest of the point circuit.',width:648,rows:128,lanes:4096,sourceSha256:{donor:expected[0],conservative:expected[1],candidate:expected[2]},rowsSha256:sha(rows),totals};
fs.writeFileSync(save('rows-totals.json'),JSON.stringify(output,null,2)+'\n');fs.unlinkSync(pending);console.log(JSON.stringify(output,null,2));
