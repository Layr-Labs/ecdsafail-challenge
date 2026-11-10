'use strict';
// q650 stage selection (hole, integrator). One entry per stage owner. To drop a stage in: point its list at the
// stage's file and set the logical it frees (stage-local numbering, see q650_pipeline.md "650 geometry").
// null / false = that stage still uses the site that becomes physical 650; the 650 geometry then fails closed there.
const path=require('path'),q651=f=>path.join(__dirname,'../q651',f),here=f=>path.join(__dirname,f);
module.exports={
  // field = multiply + divide. multiply: q650/mul (papers) frees field logical 650. divide: q650/div (evict c6e2152):
  // bucketed alpha + full Htop chain incl. winding (ledger's count/trailing-zero encoding); under STAGE=full its sparse map
  // conjugates ids[650]->640 and removes 640, so field logical 650 is unused by the divide too.
  field:here('p-field650.js'),
  // divide env, pinned here (point.cjs sets/clears these before anything loads): Q650_HTOP_STAGE selects the Htop chain.
  divideEnv:{Q650_HTOP_STAGE:'full'},
  fieldFree:[650],        // field logicals made removed ports in fieldMap, besides 651 (already removed at 651)
  divideFree:true,       // true once the divide no longer touches fieldFree
  // history.regenerate: q650/regen (ledger v2, bf85d6b in ecdsafail-650regen; -4.70M ops/call vs 651): evicts logical 388 (park Jtop).
  regen:here('regen/p-regen650.js'),
  histFree:388,           // history logical freed by regen (besides 654)
  // upper fwd+rev: q651 base + q650/upper (ringhole hand-off 12ef380: WIDTH list incl. papers' affine rows 7..125) via upper650.cjs.
  // Frees upper logical 651 (tags[1] = map[650]) in the whole upper stage.
  ubase:q651('upper/upper.cjs'),
  upperApply:here('upper650.cjs'),      // module exporting apply(src), run on the final q651 upper source before geometry
  upperFree:true,
};
