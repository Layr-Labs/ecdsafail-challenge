# q648 upper (ringhole): harness on jackylee's U15 upper (q649j)
`node h649.cjs ../q651-ten-field round|fwd|rev few|stress|field [ban=650,651] [out=..]` (round_inj.js must sit next to it).
Source = centered-point.cjs -> q651-ten-field/upper.cjs -> u-upper-649.cjs sourceUpper (pre-sink; SINK=1 applies their peephole sink,
which does not change the harness's op count: the harness counts tape.out before the sink). UEXTRA=a.cjs,.. applies extra upper(s) overlays.
Modes as in the q650 harness: CENSUS, OCC/OCCH, OWN, DEAD (OCCH = helper list), WIN, FAST, LIVE.
Baseline (production round, 32 lanes, ban=650,651): fwd 281,291,826 / rev 321,273,285, sig bb735108.

## p648-affine.cjs (ringhole): the U15 affine without logical 647 (f2), all rows. Use as UEXTRA (after U15).
- Rows 0..63 (u12 code, f2 = rank bit 6): the u12 code grows by one wire, A2.
  - During normalization, rank6 sits on r's top wire (zero on taken lanes by I(k); all writes take-gated).
  - Count 2 joins the code (extra=1, pick marker), and code lanes move the real B2 to A128.
  - rank6 then moves into A2. A2 becomes a third virtual host of the implicit-top digits (B2 = extra & A128), and compares/barrels decode the new code.
- Rows 64..111 and 120..123: switched to u12 with tag [A0, A127, v[k], pick, A128, 256].slice(0, bits). The A0 host plus the A1 code flag replaces f2.
- Also removes 647 from the dirty-loan pool (A648_NOPOOL=1 keeps it).
Checks (production round, ban=650,651): few 32 lanes and stress 832 lanes PASS with identical counts; runFold fwd few, rev field PASS.
CENSUS=647: 0 affine touches (baseline: rows 0..123).
Cost per ladder (fwd = rev): +10,581,648, i.e. +42.3M whole circuit, pre-sink. Rows 0..63 alone: +4,531,264.

## p648-trial96.cjs (ringhole): quotient trial + witness, rows 96..111, without 647
Their deep rows' short packing (N = R*V+U over [r without top, u]; R < 2^(255-k) by I(k)) frees r's top wire, which hosts rank bit 4 (f2's role).
The packed top (256) is the other host; its lanes are parked on r-top with take cleared (their 'choose').
Checks (UEXTRA=p648-affine.cjs,p648-trial96.cjs, ban=650,651): round few + stress 832 identical counts PASS; fold fwd/rev field PASS;
CENSUS=647: 0 trial touches in rows 96..111.
Cost vs the affine-only stack: fwd +78,896, rev +60,256 per round, i.e. **+0.28M whole circuit**.
Update: p648-trial96.cjs now covers rows 64..111 (T648_LO/T648_HI). The 6-bit tag in 64..95 is [qtop, ntop, f1|carry, pick, 256, f2]: this is the
deep path's own layout (rank4 = packed top 256, rank5 = r-top), so r-top replaces f2 directly. Round few + stress 832 identical, folds fwd/rev field
PASS, CENSUS=647: 0 trial touches in rows 64..111. Cost vs affine-only: fwd +405,872, rev +647,296 per round = **+2.1M whole**.

## p648-u7.cjs + p648-r113.cjs (ringhole): rows 113..127 without 647 outside the flag probes
- p648-u7: removeDebt in rows 113..126 uses the u7Debt form. u7Threshold's per-count selector is compile-time, so its carry-controlled ops
  become uncontrolled or skipped, and carry is untouched inside the thresholds. Cheaper: about -0.31M per ladder net.
- p648-r113: dv[1] (the second correction flag, was 647):
  - the estimate's rank host -> 256 (N = R*V+U < 2^256 by I(k), so 256 is zero after packNumber and untouched by the estimate body);
  - after flag probe 1 the flag moves (take-gated swap) onto carry and stays there to threshold(dv1): add1 uses pick as its ancilla,
    coef^-1 runs mixed with the single control [take], and the thresholds don't touch carry.
  - The flag probes still use dv[1] (rank host in probe 0, deposit target in probe 1): papers' part.
    Test hook R113_DV1=650 (with ban=651) stands in for it.
- Harness TOUCH mode (h649.cjs): input-independent helper-touch map per ordered code segment (TOUCH=1 TSEG=1 TMIN=k TDEPTH=3).
Checks (composition affine + trial96 + ledger trial + probe4 + unit + u7 + r113, R113_DV1=650, ban=651): round few + stress 832 identical,
folds fwd/rev field PASS; CENSUS=647: 0 in rows 113+. Only 650 remains, in flagProbe (the stand-in) and the 90-gate swap.

## Row 112 + the whole upper at 7 helpers (ringhole)
- p648-trial96.cjs now also covers row 112. Its trial runs on the coefficient-direction path: direction -> carry -> v[k] ('moved'), short packing,
  rank bit 1 moves from v[k] to the packed top 256, and band [0,8] borrows r's top as its second free wire (zero on active lanes; parked lanes are
  take-cleared). Cost +2,816 fwd / +1,306 rev per ladder.
- p648-r113.cjs: the dv[1] wire map is papers' p648-flag (Q648_F113=1): 256 on 113..124, carry on 125..127; the relay swap is skipped when the
  flag is already on carry. R113_DV1 / R113_CARRY are test hooks only.
- FULL UPPER, overlay order (UEXTRA order = composition order before the sink):
  p648-affine, p648-trial96, ledger q648w/p648-trial (ac6a7ab), papers p648-probe4, p648-unit, p648-flag (d55425b, Q648_F113=1), p648-u7, p648-r113.
- Checks with **ban=650,651,647** (any touch of 647 throws): production round few 32 + stress 832 exact (identical counts, sig 2aaf2719);
  runFold fwd few/field, rev few/field PASS. So 0 touches of 647 over the entire round, both directions.
- Pre-sink: fwd 291,982,412 / rev 329,972,142 vs U15 281,291,826 / 321,273,285 = +19.39M per round = **+38.8M whole circuit**.

## ROOT CAUSE of the 648 fasteval failures (shots 6596 fwd, 1875/2399 rev): the row-112 trial in p648-trial96 (07b1021)
Row 112 on the short-packing coefficient-direction path computes a wrong quotient estimate on some lanes. For shot 6596, row 112 has rank 7, biased 8
(band [0,8]): estimate 0x170 vs the original 0x52f5. The packed-short band layout the deep rows use ([0,8]/[9,M], bias +1, packedShort cube) was only
ever exercised by their 7-bit and my 5/6-bit tags; row 112's 4-bit tag with a 17-wire quotient breaks it. 832 stress lanes missed the class.
FIX (this commit): row 112 is back on its ORIGINAL trial path by default (T648_R112=1 re-enables the broken variant, for debugging only).
Verified: shot 6596 inputs (both signs) PASS, stress 832 PASS, 4,096 random lanes PASS (ban=650,651). Rows 64..111 short packing unchanged.
CONSEQUENCE: row 112 again uses logical 647 (dv[1] = the direction bit, 402 touches/round), so the upper is NOT 647-free. A 648 map with the 647
port ban will reject it until row 112 gets a correct 647-free trial (open).

## p648-r112p.cjs (ringhole): row 112 without 647, exact by construction (2-pass of the ORIGINAL trial on its direction bit)
Row 112 runs its ORIGINAL trial/witness body twice (d = 0, 1) with the direction as a compile-time constant in roundedDivisor.
- The direction is computed into carry (take-gated); the marker [direction != d] goes on f1 (forward trial) / qtop (witness: the corrected
  quotient's clean top). Marked lanes are parked by clearing take.
- carry itself cannot carry the mark: the body touches it ungated on parked lanes (bisected).
- Each lane executes exactly the original row-112 function.
Apply right after p648-trial96 (whose broken row-112 variant is now off by default).
Checks with ban=650,651,647: shot 6596 inputs (both signs), stress 832, 4,096 random lanes, runFold fwd/rev field: all PASS.
Cost vs the reverted original row 112: fwd +324,451 / rev +645,658 per ladder, about +1.9M whole.
NOT gated in my harness: shots 1875/2399 (reverse). Decoding hole's reverse start states gives r, v, sign consistent with the ladder but not u
(regen leaves u differently encoded), so explicit-state replays are invalid. Gate them with the forced-shot fasteval.
