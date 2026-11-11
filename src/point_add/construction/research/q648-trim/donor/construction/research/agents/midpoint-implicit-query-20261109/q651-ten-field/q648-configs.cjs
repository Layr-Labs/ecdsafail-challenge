'use strict';
// hole (q648): generate the 648 and the per-stage tight (649, 7-site ban) stage configs from stage-config.json + q648-drops.json.
//   stage-config-649p.json           public 649 geometry + landed pieces' module overrides (q648-pieces.json)
//   stage-config-648.json            width 648, helpers 512,641..646, sign physical 647, every stage 7 logicals
//   stage-config-649t-<stage>.json   width 649 (public geometry), ONE stage on 7 logicals -> physical 512,641..646 (647 unused by it)
const fs=require('fs'),path=require('path');const here=f=>path.join(__dirname,f);
const base=JSON.parse(fs.readFileSync(here('stage-config.json'),'utf8')),drops=JSON.parse(fs.readFileSync(here('q648-drops.json'),'utf8'));
const pieces=JSON.parse(fs.readFileSync(here('q648-pieces.json'),'utf8'));const withMods=c=>{Object.assign(c,pieces.modules||{});return c;};
const seven=[512,641,642,643,644,645,646];
const drop=(st)=>{const l=base.stages[st].logical.filter(q=>q!==drops[st]);if(l.length!==7)throw Error('drop for '+st+' ('+drops[st]+') is not one of '+base.stages[st].logical);return {logical:l,physical:seven};};
const out={};
{const c=withMods(JSON.parse(JSON.stringify(base)));c.expected=null;c.expectedBasis={label:'q648 649p: public 649 geometry + landed pieces'};out['stage-config-649p.json']=c;}
{const c=JSON.parse(JSON.stringify(base));c.width=648;c.helperSites=seven;c.signPhysical=647;for(const st of Object.keys(c.stages))c.stages[st]=drop(st);
 withMods(c);c.expected=null;c.expectedBasis={label:'q648 composition (hole): no expected count'};out['stage-config-648.json']=c;}
for(const st of Object.keys(base.stages)){const c=withMods(JSON.parse(JSON.stringify(base)));c.stages[st]=drop(st);c.expected=null;c.expectedBasis={label:'q648 tight check of '+st+' at width 649 (7-site ban)'};out['stage-config-649t-'+st+'.json']=c;}
{const c=withMods(JSON.parse(JSON.stringify(base)));for(const st of (pieces.tight||[]))c.stages[st]=drop(st);c.expected=null;c.expectedBasis={label:'q648 tight check of every landed stage at width 649: '+(pieces.tight||[]).join(',')};out['stage-config-649t-landed.json']=c;}
for(const [f,c] of Object.entries(out)){fs.writeFileSync(here(f),JSON.stringify(c,null,2)+'\n');require('./stage-map.cjs').validate(c);console.log('wrote',f,'validate OK');}
