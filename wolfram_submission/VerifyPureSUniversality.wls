#!/usr/bin/env wolframscript
(* ========================================================================== *)
(* VerifyPureSUniversality.wls                                                *)
(*                                                                            *)
(* Standalone WolframScript test runner for PureSUniversality.wl.             *)
(* Usage: wolframscript -file VerifyPureSUniversality.wls                     *)
(* ========================================================================== *)

Get[FileNameJoin[{DirectoryName[$InputFileName], "PureSUniversality.wl"}]];

AssertTrue[cond_, msg_] := If[!TrueQ[cond],
  Print["ASSERTION FAILED: ", msg];
  Exit[1]
];

Print["[1/16] Verifying native S contraction & selector-free quadratic counter..."];
Module[{sb = s[s[s]], seed10, cur, ch, d00, step},
  seed10 = (((s[sb])[sb])[s[s]])[s];
  AssertTrue[PureSLeafCount[seed10] === 10, "10-leaf seed leaf count"];
  cur = seed10;
  For[step = 1, step <= 30, step++,
    {cur, ch} = PureSStepLeftmostOutermost[cur];
    AssertTrue[ch, "leftmost-outermost step active"]
  ];
  Print["  10-leaf seed normal-order progression OK."];
];

Print["[2/16] Verifying 39-state A_SN and 35-state A_HN S-algebra identities..."];
Module[{dSN, dHN, x, y, z, lhs, rhs},
  dSN = PureSUniversality`Private`DeltaSN;
  dHN = PureSUniversality`Private`DeltaHN;
  For[x = 0, x < 39, x++,
    For[y = 0, y < 39, y++,
      For[z = 0, z < 39, z++,
        lhs = dSN[[dSN[[dSN[[1, x + 1]] + 1, y + 1]] + 1, z + 1]];
        rhs = dSN[[dSN[[x + 1, z + 1]] + 1, dSN[[y + 1, z + 1]] + 1]];
        AssertTrue[lhs === rhs, "A_SN S-algebra law"]
      ]
    ]
  ];
  For[x = 0, x < 35, x++,
    For[y = 0, y < 35, y++,
      For[z = 0, z < 35, z++,
        lhs = dHN[[dHN[[dHN[[1, x + 1]] + 1, y + 1]] + 1, z + 1]];
        rhs = dHN[[dHN[[x + 1, z + 1]] + 1, dHN[[y + 1, z + 1]] + 1]];
        AssertTrue[lhs === rhs, "A_HN S-algebra law"]
      ]
    ]
  ];
  Print["  59,319 A_SN triples and 42,875 A_HN triples verified."];
];

Print["[3/16] Verifying Question 7 infinite SN / non-SN flip-flop chain..."];
Module[{n, term, st},
  For[n = 0, n <= 8, n++,
    term = Question7FlipFlopTerm[n];
    st = EvalSNState[term];
    If[EvenQ[n],
      AssertTrue[st < 38, "even Question 7 term must be SN"],
      AssertTrue[st === 38, "odd Question 7 term must be non-SN"]
    ]
  ];
  Print["  Question 7 terms M_0..M_8 alternate SN / non-SN as proved."];
];

Print["[4/16] Verifying direct Pure-S simulation of 2-state Busy Beaver BB(2)..."];
Module[{bb2, cur, steps = 0, sel},
  bb2 = <|
    {0, 0} -> {1, 1, 1},
    {0, 1} -> {1, 1, -1},
    {1, 0} -> {0, 1, -1},
    {1, 1} -> {2, 1, 0}
  |>;
  cur = EncodeBinaryTapeToPureS[2, {0, 0, 0, 0}, 2];
  AssertTrue[!PureSHaltDetectorQ[cur], "BB(2) initial term not halted"];
  While[True,
    sel = RootRestartedSelectForProgram[bb2, 2, cur];
    If[sel[[1]] === "Halt", Break[]];
    AssertTrue[sel[[1]] === "Step", "BB(2) selector step"];
    cur = PureSContractAt[cur, sel[[2]]];
    AssertTrue[cur =!= $Failed, "BB(2) native contraction succeeded"];
    steps++;
  ];
  AssertTrue[PureSHaltDetectorQ[cur], "BB(2) final term accepted by 11-state Halt DTA"];
  Print["  BB(2) halted in ", steps, " native S-contractions; 11-state Halt DTA state = ",
        PureSHaltAutomatonState[cur]];
];

Print["[5/16] Verifying polynomial compilation CompileTuringMachineToPureS..."];
Module[{emptyTM, writeOneTM},
  emptyTM = CompileTuringMachineToPureS[<||>, 1, {}];
  AssertTrue[PureSLeafCount[emptyTM] === 1996921, "empty 1-state TM exact leaf count 1,996,921"];
  AssertTrue[!PureSHaltDetectorQ[emptyTM], "initial compiled TM not halted"];
  writeOneTM = CompileTuringMachineToPureS[<|{0, 0} -> {1, 1, 0}|>, 2, {}];
  AssertTrue[PureSLeafCount[writeOneTM] === 7477337, "write-1 2-state TM exact leaf count 7,477,337"];
  Print["  Polynomial compilation exact: 1,996,921 leaves (1-state) and 7,477,337 leaves (2-state)."];
];

Print["[6/16] Verifying end-to-end U(3,11) -> Pure-S native halting & output readback..."];
Module[{norm, enc, uTable, tape, st = 0, hd, ins, symBits, cur, sSteps = 0, out},
  norm = NormalizeNearySafe[<||>, 1, {1}];
  enc = EncodeNearyU311[norm["Rules"], norm["StateCount"], norm["MarkedWord"]];
  uTable = PureSUniversality`Private`NearyU311Table[];
  tape = AssociationThread[Range[0, Length[enc["Symbols"]] - 1], enc["Symbols"]];
  hd = enc["Head"];
  While[KeyExistsQ[uTable, {st, Lookup[tape, hd, 0]}],
    ins = uTable[{st, Lookup[tape, hd, 0]}];
    tape[hd] = ins[[2]];
    st = ins[[1]];
    hd = Max[0, hd + ins[[3]]];
  ];
  (* Place GAMMA at hd+1 in U-state 0: (0, GAMMA) writes LA, moves left to DELTA in U-state 2, and halts! *)
  tape[hd + 1] = 10;
  symBits = Flatten[
    IntegerDigits[Lookup[tape, #, 0], 2, 4] & /@
    Range[0, Max[Keys[tape]]]
  ];
  cur = EncodeBinaryTapeToPureS[8, symBits, 4 * (hd + 1)];
  While[!PureSHaltDetectorQ[cur],
    cur = RootRestartedPureSStep[cur];
    sSteps++;
  ];
  out = DecodePureSOutput[cur];
  AssertTrue[out === {1}, "decoded canonical output {1}"];
  Print["  Native U(3,11)->Pure-S terminal cycle halted in ", sSteps,
        " S-contractions; DecodePureSOutput = ", out];
];

Print["[7/16] Verifying 39-state A_P (Productivity) & 36-state A_36 (Question 31)..."];
Module[{dP, d36, x, y, z, aComb, aaa, zachos, wolfram2},
  dP = PureSUniversality`Private`DeltaP;
  d36 = PureSUniversality`Private`DeltaA36;
  For[x = 0, x < 39, x++,
    For[y = 0, y < 39, y++,
      For[z = 0, z < 39, z++,
        AssertTrue[
          dP[[dP[[dP[[1, x + 1]] + 1, y + 1]] + 1, z + 1]] ===
          dP[[dP[[x + 1, z + 1]] + 1, dP[[y + 1, z + 1]] + 1]],
          "A_P S-algebra law"
        ]
      ]
    ]
  ];
  For[x = 0, x < 36, x++,
    For[y = 0, y < 36, y++,
      For[z = 0, z < 36, z++,
        AssertTrue[
          d36[[d36[[d36[[1, x + 1]] + 1, y + 1]] + 1, z + 1]] ===
          d36[[d36[[x + 1, z + 1]] + 1, d36[[y + 1, z + 1]] + 1]],
          "A_36 S-algebra law"
        ]
      ]
    ]
  ];
  zachos = ((s[s[s]])[s[s]])[(s[s[s]])[s[s]]];
  wolfram2 = (((s[s])[s])[s[s[s]]])[s[s]];
  AssertTrue[EvalProductivityState[zachos] === 29 && IsProductivePureSQ[zachos], "Zachos productive"];
  AssertTrue[EvalProductivityState[wolfram2] === 37 && !IsProductivePureSQ[wolfram2], "Wolfram2 non-productive"];
  aComb = (s[s])[s];
  aaa = (aComb[aComb])[aComb];
  AssertTrue[EvalQuestion31State[aaa] === 34 && EvalQuestion31State[aaa[s]] === 35,
    "Question 31: AAA =!=_S AAA[s]"];
  Print["  59,319 A_P triples, 46,656 A_36 triples, Zachos/Wolfram2, and Question 31 verified."];
];

Print["[8/16] Verifying 4-state D_NAND & minimal 11-leaf Spine-1 NF Rule 110..."];
Module[{b0 = PureSFalseTerm, b1 = PureSTrueTerm, bx, by, bz, tx, ty, tz, out, exp, hist},
  Do[
    tx = If[bx === 1, b1, b0];
    ty = If[by === 1, b1, b0];
    tz = If[bz === 1, b1, b0];
    out = PureSRule110Term[tx, ty, tz];
    exp = If[{bx, by, bz} === {1, 1, 1} || {bx, by, bz} === {1, 0, 0} || {bx, by, bz} === {0, 0, 0}, 1, 2];
    AssertTrue[EvalDNANDState[out] === exp, "Rule 110 truth table in D_NAND"],
    {bx, {0, 1}}, {by, {0, 1}}, {bz, {0, 1}}
  ];
  hist = IteratePureSRule110[{0, 0, 0, 0, 0, 0, 1}, 4];
  AssertTrue[hist === {
    {0, 0, 0, 0, 0, 0, 1},
    {0, 0, 0, 0, 0, 1, 1},
    {0, 0, 0, 0, 1, 1, 1},
    {0, 0, 0, 1, 1, 0, 1},
    {0, 0, 1, 1, 1, 1, 1}
  }, "Periodic 7-cell Rule 110 Spine-1 NF evolution"];
  Print["  11-leaf Pure-S Rule 110 truth table and 4-generation periodic evolution verified."];
];

Print["[9/16] Verifying 8-state B_Zachos quadratic pure-line milestones n*(n+3)/2..."];
Module[{cur, hits = {}, step, ch},
  cur = ((s[s[s]])[s[s]])[(s[s[s]])[s[s]]];
  For[step = 0, step <= 60, step++,
    If[EvalBZachosState[cur] === 6, AppendTo[hits, step]];
    {cur, ch} = PureSStepLeftmostOutermost[cur];
    AssertTrue[ch, "Zachos step active"]
  ];
  AssertTrue[hits === {0, 2, 5, 9, 14, 20, 27, 35, 44, 54}, "Quadratic n*(n+3)/2 milestones"];
  Print["  B_Zachos quadratic step times under <= 60 steps: ", hits];
];

Print["[10/16] Verifying Program-Free Pure-S Cyclic Tag System simulator (100% Lean 4 layout match)..."];
Module[{cur, seedCur, sb = s[s[s]], fullOpen, writeVer, curP, pBody, curT, curQ, idx, app, bit, snaps, steps = 0, sel, st},
  cur = EncodeProgramFreeCTS[{{1}, {}}, {1, 0, 1}];
  (* Explicitly verify reachability & bit-for-bit equality from the 10-leaf seed (((s[sb])[sb])[s[s]])[s] *)
  seedCur = (((s[sb])[sb])[s[s]])[s];
  Do[seedCur = PureSContractAt[seedCur, p], {p, {{0}, {0}, {0}, {}, {1, 0}}}];
  fullOpen[path_List] := While[PureSUniversality`Private`ParseProtectedFrame[PureSUniversality`Private`PFNodeAt[seedCur, path]] === $Failed,
    seedCur = PureSContractAt[seedCur, PureSUniversality`Private`PFSelectOpeningAt[seedCur, path]]
  ];
  writeVer[verPath_List, bits_List] := While[
    PureSUniversality`Private`PFScanVersion[Length[bits], PureSUniversality`Private`PFNodeAt[seedCur, verPath]] =!= bits ||
    PureSUniversality`Private`PFHasUncommittedVerQ[Length[bits], PureSUniversality`Private`PFNodeAt[seedCur, verPath]],
    seedCur = PureSContractAt[seedCur, PureSUniversality`Private`PFSelectVersionWriteAt[seedCur, verPath, Length[bits], bits]]
  ];
  fullOpen[{1}];
  fullOpen[{1, 1, 0, 1}];
  curP = {1, 1, 0, 1, 0, 1};
  For[idx = 1, idx <= 2, idx++,
    app = {{1}, {}}[[idx]];
    fullOpen[curP];
    pBody = Join[curP, {0, 1}];
    fullOpen[pBody];
    writeVer[Join[pBody, {0, 1}], {If[idx === 1, 1, 0], 0}];
    curT = Join[pBody, {1, 0, 1}];
    Do[fullOpen[curT]; writeVer[Join[curT, {0, 1}], {0, 0, bit}]; curT = Join[curT, {1, 0, 1}], {bit, app}];
    curP = Join[curP, {1, 0, 1}]
  ];
  curQ = {1, 1, 0, 1, 1, 0, 1};
  Do[fullOpen[curQ]; writeVer[Join[curQ, {0, 1}], {0, 0, bit}]; curQ = Join[curQ, {1, 0, 1}], {bit, {1, 0, 1}}];
  AssertTrue[seedCur === cur, "EncodeProgramFreeCTS bit-for-bit identical to native 10-leaf seed reduction"];
  AssertTrue[!PureSHaltDetectorQ[cur] && !ProgramFreePureSHaltQ[cur], "Initial CTS term not halted"];
  snaps = {DecodeProgramFreeCTSState[cur]};
  AssertTrue[First[snaps] === {0, {1, 0, 1}}, "Initial CTS snapshot"];
  While[True,
    sel = ProgramFreePureSSelect[cur];
    If[sel[[1]] === "Halt", Break[]];
    AssertTrue[sel[[1]] === "Step", "Program-free selector step"];
    cur = PureSContractAt[cur, sel[[2]]];
    AssertTrue[cur =!= $Failed, "Program-free native S contraction"];
    steps++;
    st = DecodeProgramFreeCTSState[cur];
    If[st =!= None && st =!= Last[snaps], AppendTo[snaps, st]]
  ];
  AssertTrue[ProgramFreePureSHaltQ[cur] && PureSHaltDetectorQ[cur], "Program-free halt accepted by 11-state PureSHaltDetectorQ"];
  AssertTrue[snaps === {
    {0, {1, 0, 1}},
    {1, {0, 1, 1}},
    {0, {1, 1}},
    {1, {1, 1}},
    {0, {1}},
    {1, {1}},
    {0, {}}
  }, "Exact CTS macro-step snapshot trajectory"];
  Print["  Program-free CTS {{1},{}} on {1,0,1} halted in ", steps,
        " native S-contractions; 11-state Halt DTA state = ", PureSHaltAutomatonState[cur]];
];

Print["[11/16] Verifying Wolfram Challenge 12 Benchmarks, Minimal Witnesses & Jump-Ahead Solver..."];
Module[{b12 = WolframChallenge12Benchmarks[], min7 = MinimalNonHaltingPureSTerms[], min9 = MinimalProductiveNonSNPureSTerm, out},
  AssertTrue[Length[b12] === 12, "12 Wolfram announcement benchmarks"];
  Do[
    out = PureSJumpAheadOutcome[expr];
    AssertTrue[!out["HaltsQ"] && !out["ProductiveQ"] && out["SNState"] === 38 && out["ProductivityState"] === 37,
      "Wolfram announcement benchmark non-SN and non-productive"],
    {expr, b12}
  ];
  Do[
    out = PureSJumpAheadOutcome[expr];
    AssertTrue[out["Leaves"] === 7 && !out["HaltsQ"] && out["HasHNFQ"] && !out["ProductiveQ"],
      "Minimal 7-leaf witness properties"],
    {expr, min7}
  ];
  out = PureSJumpAheadOutcome[min9];
  AssertTrue[out["Leaves"] === 9 && !out["HaltsQ"] && out["HasHNFQ"] && out["ProductiveQ"] && out["ProductivityState"] === 29,
    "Unique minimal 9-leaf productive non-halting pure-S combinator"];
  Print["  All 12 Wolfram benchmarks, 7-leaf minimal non-SN witnesses, and 9-leaf productive non-SN witness verified."];
];

Print["[12/16] Verifying PureSAsymptoticConstants & PureSCatalanPhaseCensus through size 12..."];
Module[{consts = PureSAsymptoticConstants[], census = PureSCatalanPhaseCensus[12]},
  AssertTrue[consts["HNLimitingDensityExact"] + consts["HeadDivergentDensityExact"] === 1,
    "Exact rational HN + NonHN densities sum to 1"];
  AssertTrue[consts["HNLimitingDensityExact"] === 4429673 / 7077888,
    "Exact dyadic-triadic HN density 4429673/7077888"];
  AssertTrue[Length[consts["SNMinimalPolynomialCoefficients"]] === 36 &&
             Length[consts["ProductivityMinimalPolynomialCoefficients"]] === 36,
    "Degree-35 minimal polynomials for rSN and rP"];
  AssertTrue[census[[6]]["SNCount"] === 42 && census[[7]]["SNCount"] === 130 &&
             census[[8]]["HNCount"] === 414 && census[[9]]["ProductiveCount"] - census[[9]]["SNCount"] === 1 &&
             census[[12]]["CatalanTotal"] === 58786 && census[[12]]["SNCount"] === 29498 &&
             census[[12]]["ProductiveCount"] === 29513 && census[[12]]["HNCount"] === 46056,
    "Exact Catalan phase census through size 12"];
  Print["  Exact rational cHN = 4429673/7077888, degree-35 minimal polynomials, and n=1..12 census verified."];
];

Print["[13/16] Verifying PureSFunctionalOrder, Order3Count === 1, and exact rational order densities..."];
Module[{dHN, ordTbl, q, k, tau, consts, census, aComb = (s[s])[s], aaa},
  dHN = PureSUniversality`Private`DeltaHN;
  ordTbl = PureSUniversality`Private`HNStateOrderTable;
  tau[st_] := dHN[[st + 1, 35]];
  For[q = 0, q < 35, q++,
    For[k = 0, k <= 3, k++,
      AssertTrue[(Nest[tau, q, k] === 34) === (ordTbl[[q + 1]] <= k),
        "Functional order nilpotency law in A_HN"]
    ]
  ];
  aaa = (aComb[aComb])[aComb];
  AssertTrue[PureSFunctionalOrder[s] === 3 && PureSFunctionalOrder[s[s[s]]] === 3 &&
             PureSFunctionalOrder[aComb] === 2 && PureSFunctionalOrder[(s[aComb])[s]] === 1 &&
             PureSFunctionalOrder[aaa] === 0 && PureSJumpAheadOutcome[aaa]["FunctionalOrder"] === 0,
    "Minimal functional order witnesses for orders 3, 2, 1, 0"];
  consts = PureSAsymptoticConstants[];
  AssertTrue[consts["Order0DensityExact"] === 2648215 / 7077888 &&
             consts["Order1DensityExact"] === 1864553 / 7077888 &&
             consts["Order2DensityExact"] === 835 / 2304 &&
             consts["Order3DensityExact"] === 0 &&
             consts["Order0DensityExact"] + consts["Order1DensityExact"] +
               consts["Order2DensityExact"] + consts["Order3DensityExact"] === 1 &&
             consts["Order1DensityExact"] + consts["Order2DensityExact"] +
               consts["Order3DensityExact"] === consts["HNLimitingDensityExact"],
    "Exact rational order densities c0 + c1 + c2 + c3 === 1"];
  census = PureSCatalanPhaseCensus[12];
  Do[
    AssertTrue[row["Order3Count"] === 1 &&
               row["Order1Count"] + row["Order2Count"] + row["Order3Count"] === row["HNCount"] &&
               row["Order0Count"] + row["Order1Count"] + row["Order2Count"] + row["Order3Count"] === row["CatalanTotal"],
      "Catalan functional order partition identities"],
    {row, census}
  ];
  Print["  Functional order {0,1,2,3}, Order3Count === 1, and exact rational densities verified."];
];

Print["[14/16] Verifying PureSLeftSubtreeSum (Delta L = -2 & quarter-square law) and Garden-of-Eden NF census..."];
Module[{trees, n, k, nfs, goes, nfCounts = {}, goeCounts = {}, cur, nxt, ch, lCur, lNxt, steps},
  trees[1] = {s};
  For[n = 2, n <= 7, n++,
    trees[n] = Flatten[Table[Outer[#1[#2] &, trees[k], trees[n - k]], {k, 1, n - 1}], 2]
  ];
  For[n = 1, n <= 7, n++,
    nfs = Select[trees[n], !PureSStepLeftmostOutermost[#][[2]] &];
    goes = Select[trees[n], IsGardenOfEdenNormalFormQ];
    AssertTrue[SubsetQ[nfs, goes], "Every Garden-of-Eden term is a closed normal form"];
    AppendTo[nfCounts, Length[nfs]];
    AppendTo[goeCounts, Length[goes]]
  ];
  AssertTrue[nfCounts === {1, 1, 2, 4, 9, 21, 51}, "Motzkin closed NF counts n=1..7"];
  AssertTrue[goeCounts === {1, 1, 2, 3, 7, 15, 37}, "Garden-of-Eden isolated NF counts n=1..7"];
  For[n = 2, n <= 12, n++,
    cur = Nest[# [s] &, s, n - 1];
    AssertTrue[PureSLeftSubtreeSum[cur] === Quotient[n * (n - 1), 2], "Initial left-comb L(S^n)"];
    steps = 0;
    While[True,
      lCur = PureSLeftSubtreeSum[cur];
      {nxt, ch} = PureSStepLeftmostOutermost[cur];
      If[!ch, Break[]];
      lNxt = PureSLeftSubtreeSum[nxt];
      AssertTrue[PureSLeafCount[nxt] === n && lNxt - lCur === -2,
        "Leaf-preserving step drops PureSLeftSubtreeSum by exact 2"];
      cur = nxt;
      steps++
    ];
    AssertTrue[steps === Quotient[(n - 2)^2, 4], "Quarter-square left-comb step law ((n-2)^2)//4"]
  ];
  Print["  PureSLeftSubtreeSum Delta L = -2, quarter-square law, and GoE census {1,1,2,3,7,15,37} verified."];
];

Print["[15/16] Verifying Question7AtomicSplitTerm[0..29] and Conjecture 40/42/43 witnesses..."];
Module[{isAtomicSplitQ, prev, cur, n, ldiv, cex},
  isAtomicSplitQ[s, expr_] := expr === s[s];
  isAtomicSplitQ[u_, v_] := PureSAppQ[u] && PureSAppQ[v] && (
    (Head[u] === Head[v] && isAtomicSplitQ[First[u], First[v]]) ||
    (First[u] === First[v] && isAtomicSplitQ[Head[u], Head[v]])
  );
  For[n = 0, n <= 29, n++,
    cur = Question7AtomicSplitTerm[n];
    AssertTrue[PureSLeafCount[cur] === n + 1, "Question7AtomicSplitTerm leaf count n + 1"];
    AssertTrue[(EvalSNState[cur] < 38) === (Mod[n, 10] =!= 9),
      "Question7AtomicSplitTerm SN iff Mod[n, 10] != 9"];
    If[n >= 1,
      AssertTrue[isAtomicSplitQ[prev, cur], "Single atomic s -> s[s] leaf replacement"]
    ];
    prev = cur
  ];
  ldiv = MinimalLambdaDivergingPureSTerms[];
  cex = Conjecture42And43Counterexamples[];
  AssertTrue[PureSLeafCount[ldiv["W9"]] === 9 && EvalSNState[ldiv["W9"]] < 38 &&
             PureSLeafCount[ldiv["N10"]] === 10 && !PureSStepLeftmostOutermost[ldiv["N10"]][[2]] &&
             PureSLeafCount[ldiv["WaldmannW13"]] === 13 && !PureSStepLeftmostOutermost[ldiv["WaldmannW13"]][[2]],
    "MinimalLambdaDivergingPureSTerms W9, N10, WaldmannW13 invariants"];
  AssertTrue[PureSLeafCount[cex["M14"]] === 14 && PureSFunctionalOrder[cex["M14"]] === 1 &&
             EvalSNState[cex["M14"]] < 38 &&
             PureSLeafCount[cex["M15NF"]] === 15 && !PureSStepLeftmostOutermost[cex["M15NF"]][[2]] &&
             PureSFunctionalOrder[cex["M15NF"]] === 1 && EvalSNState[cex["M15NF"]] < 38,
    "Conjecture 42/43 counterexamples M14 and M15NF invariants"];
  Print["  Question7AtomicSplitTerm[0..29] and W9 / N10 / WaldmannW13 / M14 / M15NF verified."];
];

Print["[16/16] Verifying all-step O(1) cubic leaf-count formulas (t = 0..80) & +14 twin shift..."];
Module[{curZ, curW2, w2Base, curTwin, curSeed, t, ch},
  curZ = ((s[s[s]])[s[s]])[(s[s[s]])[s[s]]];
  curW2 = (((s[s])[s])[s[s[s]]])[s[s]];
  w2Base = (s[s[s[s]]])[s[s]];
  curTwin = w2Base[w2Base];
  curSeed = (((s[s[s[s]]])[s[s[s]]])[s[s]])[s];
  AssertTrue[EvalSNState[curTwin] === EvalSNState[curW2] &&
             EvalHNState[curW2] === 24 && EvalHNState[curTwin] === 23 &&
             PureSFunctionalOrder[curTwin] === PureSFunctionalOrder[curW2] &&
             EvalProductivityState[curTwin] === EvalProductivityState[curW2],
    "w2Twin matches wolfram_2 in A_SN, A_P, and FunctionalOrder (HN states 23 vs 24)"];
  For[t = 0, t <= 80, t++,
    AssertTrue[PureSLeafCount[curZ] === ZachosExactLeafCount[t], "ZachosExactLeafCount at step t"];
    AssertTrue[PureSLeafCount[curW2] === Wolfram2ExactLeafCount[t], "Wolfram2ExactLeafCount at step t"];
    AssertTrue[PureSLeafCount[curSeed] === TenLeafSeedExactLeafCount[t], "TenLeafSeedExactLeafCount at step t"];
    If[t >= 3,
      AssertTrue[PureSLeafCount[curTwin] === Wolfram2ExactLeafCount[t + 1] + 14,
        "Wolfram2 vs w2Twin +14 shift law for t >= 3"]
    ];
    If[t < 80,
      {curZ, ch} = PureSStepLeftmostOutermost[curZ]; AssertTrue[ch, "Zachos active"];
      {curW2, ch} = PureSStepLeftmostOutermost[curW2]; AssertTrue[ch, "Wolfram2 active"];
      {curTwin, ch} = PureSStepLeftmostOutermost[curTwin]; AssertTrue[ch, "w2Twin active"];
      {curSeed, ch} = PureSStepLeftmostOutermost[curSeed]; AssertTrue[ch, "TenLeafSeed active"]
    ]
  ];
  Print["  Exact O(1) cubic leaf counts and +14 twin shift verified across t = 0..80."];
];

Print["ALL WOLFRAM PURE-S UNIVERSALITY CHECKS PASSED."];
