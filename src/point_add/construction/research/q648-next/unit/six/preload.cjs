'use strict';
require('../../../q647-trim/hybrid.cjs');
const upper=require('../../../q647-trim/upper/integrated.cjs');
const {patch}=require('./index.cjs');
const previous=upper.patch;
upper.patch=(...args)=>patch(previous(...args));
