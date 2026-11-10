'use strict';
const previous=require('../q651-fusion-cache/upper.cjs');
const {patchPermutation}=require('./shared-controls.cjs');
module.exports={upper:source=>patchPermutation(previous.upper(source))};
