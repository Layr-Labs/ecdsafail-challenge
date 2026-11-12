'use strict';

require('./base.cjs');
const sharedUnit = require('../../q648-trim/alternate/unit/unit.cjs');
const original = sharedUnit.patch;
const {patch} = require('./upper.cjs');
sharedUnit.patch = (...args) => patch(original(...args));
