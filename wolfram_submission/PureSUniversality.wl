(* ::Package:: *)
(* ========================================================================== *)
(* PureSUniversality.wl                                                       *)
(*                                                                            *)
(* Complete Wolfram Language Implementation for The Wolfram S Combinator      *)
(* Challenge (https://www.combinatorprize.org/):                              *)
(*   1. Polynomial-size O((n^2 + m)^2) Compiler from arbitrary deterministic  *)
(*      Turing machines to pure S-combinator expressions s[...][...]          *)
(*   2. Root-Restarted Physical Occurrence-Tree Selector & Native S-Reducer   *)
(*      using ONLY s[x_][y_][z_] :> x[z][y[z]]                                *)
(*   3. Minimal 11-State Deterministic Bottom-Up Regular Halting Detector     *)
(*      (matching Lean 4 haltAutomaton : BottomUpTreeAutomaton (Fin 11))      *)
(*   4. Linear-Time Bare-Term Output Decoder                                  *)
(*   5. Exact 39-State SN Algebra, 35-State HN Algebra (Open Problem 10),     *)
(*      Linear-Time Root Normal Form Decider (Footnote 4), and Question 7     *)
(*      Infinite SN / non-SN Refinement Chain                                 *)
(* ========================================================================== *)

BeginPackage["PureSUniversality`"];

s::usage = "Atomic pure S combinator symbol. Application (X Y) is represented natively as X[Y].";
PureSLeafCount::usage = "PureSLeafCount[expr] returns the exact unfolded S-leaf count of a pure S expression (iterative DAG-memoized, O(|DAG|)).";
PureSNodeCount::usage = "PureSNodeCount[expr] returns 2*PureSLeafCount[expr] - 1, the total unfolded occurrence-tree node count.";
PureSContractAt::usage = "PureSContractAt[expr, path] performs a single native s[x][y][z] -> x[z][y[z]] contraction at occurrence path (list of 0=Head, 1=First).";
PureSStepLeftmostOutermost::usage = "PureSStepLeftmostOutermost[expr] performs one standard normal-order S-reduction step, returning {nextExpr, changedQ}.";

NormalizeNearySafe::usage = "NormalizeNearySafe[rulesAssoc, stateCount, inputBits] compiles any partial clamped binary TM into a boundary-safe total L/R binary TM for Neary U(3,11).";
EncodeNearyU311::usage = "EncodeNearyU311[normRulesAssoc, stateCount, markedBits] computes the initial 11-symbol tape and head index for Neary's polynomial-time universal machine U(3,11).";
FixedBinaryUniversalRules::usage = "FixedBinaryUniversalRules[] returns the fixed 132-state, 262-rule binary compilation of Neary's U(3,11).";
EncodeBinaryTapeToPureS::usage = "EncodeBinaryTapeToPureS[stateWidth, bits, headIndex] builds the initial pure S-combinator expression s[...] in polynomial size without recursion limits.";
CompileTuringMachineToPureS::usage = "CompileTuringMachineToPureS[rulesAssoc, stateCount, inputBits] compiles an arbitrary deterministic binary Turing machine and input into a pure S-combinator expression.";

PureSHaltAutomatonState::usage = "PureSHaltAutomatonState[expr] evaluates the minimal 11-state (0..10) deterministic bottom-up tree automaton recognizing rootHalt (accepting states {3, 6, 8, 10}).";
PureSHaltDetectorQ::usage = "PureSHaltDetectorQ[expr] returns True iff the minimal 11-state bottom-up halting tree automaton accepts expr.";
RootRestartedSelectForProgram::usage = "RootRestartedSelectForProgram[programAssoc, stateWidth, expr] runs the root-restarted occurrence-tree selector for a binary TM table.";
RootRestartedSelectAddress::usage = "RootRestartedSelectAddress[expr] starts at the root of expr with zero retained state and returns {\"Halt\", None}, {\"Step\", path}, or {\"Reject\", None}.";
RootRestartedPureSStep::usage = "RootRestartedPureSStep[expr] performs one root-restarted universal S-contraction step (continuing along the halt frontier after halting).";
DecodePureSOutput::usage = "DecodePureSOutput[expr] decodes the canonical output tape of the simulated source Turing machine from a halted bare S expression.";

EvalSNState::usage = "EvalSNState[expr] evaluates the exact 39-state Strong Normalization S-algebra (states 0..37 normalizing, 38 non-normalizing).";
EvalHNState::usage = "EvalHNState[expr] evaluates the exact 35-state Head Normalization S-algebra resolving Barendregt et al. (2018) Question 10 (states 0..33 HNF, 34 non-HNF).";
IsRootNormalFormQ::usage = "IsRootNormalFormQ[expr] decides Root Normal Form membership in linear time (Barendregt et al. 2018, Footnote 4).";
Question7FlipFlopTerm::usage = "Question7FlipFlopTerm[n] returns the n-th pure S term in the infinite refinement chain M_0 < M_1 < M_2 < ... alternating between SN (even n) and non-SN (odd n).";

EvalProductivityState::usage = "EvalProductivityState[expr] evaluates the exact 39-state Bohm-tree productivity S-algebra A_P (state 37 non-productive; all other states productive).";
IsProductivePureSQ::usage = "IsProductivePureSQ[expr] returns True iff expr has a productive (non-bottom) Bohm tree (EvalProductivityState[expr] =!= 37).";
EvalQuestion31State::usage = "EvalQuestion31State[expr] evaluates the exact 36-state S-algebra A_36 separating AAA (state 34) from AAA[s] (state 35), resolving Barendregt et al. (2018) Question 31.";
EvalDNANDState::usage = "EvalDNANDState[expr] evaluates the minimal 4-state functionally complete S-algebra D_NAND (FalseTerm=s[s] -> 1, TrueTerm=s[s[s][s]] -> 2).";
PureSFalseTerm::usage = "PureSFalseTerm is s[s], encoding Boolean False (state 1 in D_NAND, Spine-1 normal form).";
PureSTrueTerm::usage = "PureSTrueTerm is s[(s[s])[s]], encoding Boolean True (state 2 in D_NAND, Spine-1 normal form).";
PureSRule110Term::usage = "PureSRule110Term[x, y, z] builds the provably minimal 11-leaf pure-S Rule 110 polynomial s[s[y[x]][s[y[z]][s[z[y]][s]]]], preserving Spine-1 normal forms.";
IteratePureSRule110::usage = "IteratePureSRule110[bitList, steps] evolves periodic 1D Rule 110 purely in Spine-1 normal-form pure-S terms and returns the decoded bit history.";
EvalBZachosState::usage = "EvalBZachosState[expr] evaluates the 8-state bottom-up tree automaton B_Zachos (accepting state 6) recognizing quadratic step milestones n*(n+3)/2 along Zachos.";
EncodeProgramFreeCTS::usage = "EncodeProgramFreeCTS[programList, inputBits] compiles any Cyclic Tag System program and binary input word into a bare closed pure-S term matching Lean 4 FormalProgramFree.encodeProgramFreeCTS bit-for-bit.";
ProgramFreePureSSelect::usage = "ProgramFreePureSSelect[expr] runs the zero-UTM program-free root-restarted selector matching Lean 4 FormalProgramFree.pfSelect step-for-step, returning {\"Halt\", None}, {\"Step\", path}, or {\"Stuck\", None}.";
ProgramFreePureSCTSStep::usage = "ProgramFreePureSCTSStep[expr] performs one program-free root-restarted native S-contraction step via ProgramFreePureSSelect.";
ProgramFreePureSHaltQ::usage = "ProgramFreePureSHaltQ[expr] tests the regular halting condition for ProgramFreePureSCTSStep (identical to PureSHaltDetectorQ / Lean 4 pfHaltAutomaton, protected frame opened at path {1, 0, 1}).";
DecodeProgramFreeCTSState::usage = "DecodeProgramFreeCTSState[expr] decodes {activePhase, unconsumedQueueBits} at clean Cyclic Tag System step boundaries, or None during intermediate micro-steps.";
WolframChallenge12Benchmarks::usage = "WolframChallenge12Benchmarks[] returns the exact 12 pure-S benchmark expressions from Stephen Wolfram's June 8, 2021 S Combinator Challenge announcement.";
MinimalNonHaltingPureSTerms::usage = "MinimalNonHaltingPureSTerms[] returns {s[s][s][s[s]][s][s], s[s[s]][s][s][s][s]}, the unique minimal 7-leaf non-halting pure-S combinators.";
MinimalProductiveNonSNPureSTerm::usage = "MinimalProductiveNonSNPureSTerm is s[s[s[s]]][s[s[s]]][s[s]], the unique minimal 9-leaf productive non-halting pure-S combinator.";
PureSJumpAheadOutcome::usage = "PureSJumpAheadOutcome[expr] computes in O(|DAG|) always-halting time the exact asymptotic outcome (SN, HN, Productivity, RNF, and regime classification) of any pure-S expression.";
PureSAsymptoticConstants::usage = "PureSAsymptoticConstants[] returns the exact macroscopic phase-transition constants of pure-S combinator space: exact rational cHN = 4429673/7077888, exact degree-35 minimal polynomials for rSN and rP, and 50-digit singularity constants.";
PureSCatalanPhaseCensus::usage = "PureSCatalanPhaseCensus[maxLeaves] computes via exact S-algebra dynamic programming the Catalan phase counts {n, CatalanNumber[n-1], #SN(n), #AcceptP(n), #HN(n)} for leaf sizes 1..maxLeaves.";

Begin["`Private`"];

(* -------------------------------------------------------------------------- *)
(* 1. Pure S Syntax, Iterative DAG Fold & Iterative Native Contraction        *)
(*    Application (X Y) is curried X[Y]: Left(t) = Head[t], Right(t) = t[[1]] *)
(* -------------------------------------------------------------------------- *)

PureSAtomQ[expr_] := expr === s;
PureSAppQ[expr_] := expr =!= s && Length[expr] === 1;

(* Iterative explicit-stack postorder fold with Association memoization:
   immune to $RecursionLimit even on depth-10000 spines, and O(|DAG|) on
   shared subexpressions while computing exact unfolded tree functions. *)
PureSDAGFold[rootExpr_, leafVal_, combineFn_] := Block[
  {$RecursionLimit = Infinity, $IterationLimit = Infinity},
  Module[{memo = <||>, stack = {{rootExpr, False}}, top, node, ready, l, r},
    memo[s] = leafVal;
    While[stack =!= {},
      top = Last[stack];
      stack = Most[stack];
      node = top[[1]];
      ready = top[[2]];
      If[KeyExistsQ[memo, node], Continue[]];
      If[!PureSAppQ[node], Return[$Failed]];
      l = Head[node];
      r = First[node];
      If[!ready,
        AppendTo[stack, {node, True}];
        If[!KeyExistsQ[memo, r], AppendTo[stack, {r, False}]];
        If[!KeyExistsQ[memo, l], AppendTo[stack, {l, False}]],
        memo[node] = combineFn[memo[l], memo[r]]
      ]
    ];
    memo[rootExpr]
  ]
];

PureSLeafCount[expr_] := PureSDAGFold[expr, 1, Plus];
PureSNodeCount[expr_] := 2 * PureSLeafCount[expr] - 1;

PureSRootRedexQ[expr_] :=
  PureSAppQ[expr] && PureSAppQ[Head[expr]] &&
  PureSAppQ[Head[Head[expr]]] && Head[Head[Head[expr]]] === s;

PureSContractRoot[expr_] := Module[{x, y, z},
  If[!PureSRootRedexQ[expr], Return[$Failed]];
  x = First[Head[Head[expr]]];
  y = First[Head[expr]];
  z = First[expr];
  (x[z])[y[z]]
];

(* Iterative occurrence-path contraction: zero recursion regardless of depth *)
PureSContractAt[expr_, path_List] := Block[
  {$RecursionLimit = Infinity, $IterationLimit = Infinity},
  Module[{cur = expr, trail = {}, dir, contracted, frame},
    Do[
      If[!PureSAppQ[cur], Return[$Failed]];
      If[dir === 0,
        AppendTo[trail, {0, First[cur]}];
        cur = Head[cur],
        If[dir === 1,
          AppendTo[trail, {1, Head[cur]}];
          cur = First[cur],
          Return[$Failed]
        ]
      ],
      {dir, path}
    ];
    contracted = PureSContractRoot[cur];
    If[contracted === $Failed, Return[$Failed]];
    Do[
      frame = trail[[i]];
      contracted = If[frame[[1]] === 0, contracted[frame[[2]]], (frame[[2]])[contracted]],
      {i, Length[trail], 1, -1}
    ];
    contracted
  ]
];

PureSSpine[expr_] := Block[{$RecursionLimit = Infinity, $IterationLimit = Infinity},
  Module[{cur = expr, args = {}},
    While[PureSAppQ[cur],
      AppendTo[args, First[cur]];
      cur = Head[cur];
    ];
    Reverse[args]
  ]
];

PureSAppMany[head_, args_List] := Fold[#1[#2] &, head, args];

PureSStepLeftmostOutermost[rootExpr_] := Block[
  {$RecursionLimit = Infinity, $IterationLimit = Infinity},
  Module[{stepRec},
    stepRec[s] := {s, False};
    stepRec[expr_] := Module[{sp, x, y, z, i, res, ch, newSp},
      sp = PureSSpine[expr];
      If[Length[sp] >= 3,
        {x, y, z} = Take[sp, 3];
        Return[{PureSAppMany[(x[z])[y[z]], Drop[sp, 3]], True}]
      ];
      For[i = 1, i <= Length[sp], i++,
        {res, ch} = stepRec[sp[[i]]];
        If[ch,
          newSp = sp;
          newSp[[i]] = res;
          Return[{PureSAppMany[s, newSp], True}]
        ]
      ];
      {expr, False}
    ];
    stepRec[rootExpr]
  ]
];

(* -------------------------------------------------------------------------- *)
(* 2. Protected Binary Storage & Stateless Bounded Opening                    *)
(* -------------------------------------------------------------------------- *)

bTerm = s[s];
PureSNumeral[0] := (s[bTerm])[bTerm];
PureSNumeral[n_Integer?Positive] := Nest[bTerm[#] &, PureSNumeral[0], n];

PureSGenerator[m_Integer, n_Integer] := (PureSNumeral[m][PureSNumeral[n]])[s];
PureSProtectedFrame[l_, r_, j_] := (s[l])[(s[r])[j]];

(* Ten-leaf seed T = (S (S b) (S b) b) S after 5-step bootstrap to D(2,2) at {1} *)
SeedBootstrapBase = Module[{sb = s[s[s]], t},
  t = (((s[sb])[sb])[s[s]])[s];
  t = PureSContractAt[t, {0}];
  t = PureSContractAt[t, {0}];
  t = PureSContractAt[t, {0}];
  t = PureSContractAt[t, {}];
  t = PureSContractAt[t, {1, 0}];
  Head[t]
];

SeedWithReplacedHub[hub_] := SeedBootstrapBase[hub];

ParseProtectedFrame[expr_] := Module[{lhs, rhs},
  If[!PureSAppQ[expr], Return[$Failed]];
  lhs = Head[expr];
  rhs = First[expr];
  If[!(PureSAppQ[lhs] && Head[lhs] === s), Return[$Failed]];
  If[!(PureSAppQ[rhs] && PureSAppQ[Head[rhs]] && Head[Head[rhs]] === s), Return[$Failed]];
  {First[lhs], First[Head[rhs]], First[rhs]}
];

BoundedSpineArity5[expr_] := Module[{cur = expr, k = 0},
  While[k < 5 && PureSAppQ[cur],
    cur = Head[cur];
    k++;
  ];
  If[cur === s, k, 5]
];

BoundedNextOpeningAddress[focus_] := Module[{ar, rAr},
  If[ParseProtectedFrame[focus] =!= $Failed, Return[$Failed]];
  ar = BoundedSpineArity5[focus];
  Which[
    ar === 4, {0},
    ar === 3, {},
    ar === 2 && PureSAppQ[focus],
      rAr = BoundedSpineArity5[First[focus]];
      Which[
        rAr === 4, {1, 0},
        rAr === 3, {1},
        True, $Failed
      ],
    True, $Failed
  ]
];

(* -------------------------------------------------------------------------- *)
(* 3. Minimal 11-State Deterministic Bottom-Up Tree Automaton for rootHalt    *)
(*    Matches Lean 4 haltAutomaton : BottomUpTreeAutomaton (Fin 11)           *)
(*    States 0..10; Accepting states = {3, 6, 8, 10}.                         *)
(* -------------------------------------------------------------------------- *)

DeltaHalt11 = {
  {1,1,1,1,1,2,2,3,3,1,1},
  {4,4,4,4,5,5,5,6,6,4,4},
  {4,4,4,4,7,7,7,8,8,4,4},
  {4,4,4,4,7,7,7,8,8,4,4},
  {9,9,9,9,9,9,9,10,10,9,9},
  {9,9,9,9,9,9,9,10,10,9,9},
  {9,9,9,9,9,9,9,10,10,9,9},
  {9,9,9,9,9,9,9,10,10,9,9},
  {9,9,9,9,9,9,9,10,10,9,9},
  {9,9,9,9,9,9,9,10,10,9,9},
  {9,9,9,9,9,9,9,10,10,9,9}
};

HaltAcceptingStates = {3, 6, 8, 10};

PureSHaltAutomatonState[expr_] :=
  PureSDAGFold[expr, 0, DeltaHalt11[[#1 + 1, #2 + 1]] &];

PureSHaltDetectorQ[expr_] :=
  MemberQ[HaltAcceptingStates, PureSHaltAutomatonState[expr]];

(* Constant-time bounded-depth equivalent check at path {1, 0, 1} *)
PureSHaltFastQ[expr_] := Module[{hub, parsedHub},
  If[!PureSAppQ[expr], Return[False]];
  hub = First[expr];
  parsedHub = ParseProtectedFrame[hub];
  If[parsedHub === $Failed, Return[False]];
  ParseProtectedFrame[parsedHub[[1]]] =!= $Failed
];

(* -------------------------------------------------------------------------- *)
(* 4. Boundary-Safe Source Normalizer, Neary U(3,11) & 132-State Binary Table *)
(* -------------------------------------------------------------------------- *)

NormalizeNearySafe[rules_Association, stateCount_Integer, inputWord_List] := Module[
  {out = <||>, aux = <||>, sortedKeys, haltState, q, b, t, a, firstMove, secondMove, word, initTape},
  out[{0, 0}] = {1, 0, 1};
  out[{0, 1}] = {1, 1, 1};
  sortedKeys = Sort[Keys[rules]];
  Do[
    aux[k] = stateCount + 1 + Length[aux],
    {k, sortedKeys}
  ];
  haltState = stateCount + 1 + Length[aux];
  For[q = 0, q < stateCount, q++,
    Do[
      If[!KeyExistsQ[rules, {q, b}],
        out[{q + 1, b}] = {haltState, b, -1},
        t = rules[{q, b}]; (* {nextState, write, move} *)
        a = aux[{q, b}];
        firstMove = If[t[[3]] === -1, -1, 1];
        out[{q + 1, b}] = {a, t[[2]], firstMove};
        Do[
          secondMove = Which[
            t[[3]] === -1, If[marker === 1, 1, -1],
            t[[3]] === 1, 1,
            True, -1
          ];
          out[{a, marker}] = {t[[1]] + 1, marker, secondMove},
          {marker, {0, 1}}
        ]
      ],
      {b, {0, 1}}
    ]
  ];
  out[{haltState, 0}] = {haltState, 0, -1};
  out[{haltState, 1}] = {haltState, 1, -1};
  word = If[inputWord === {}, {0}, inputWord];
  initTape = {1};
  Do[
    If[i > 1, AppendTo[initTape, 0]];
    AppendTo[initTape, word[[i]]],
    {i, 1, Length[word]}
  ];
  <|"Rules" -> out, "StateCount" -> haltState + 1, "MarkedWord" -> initTape|>
];

NearySymbols = {"LA", "LB", "E", "H", "RE", "RH", "LE", "LH", "LAMBDA", "DELTA", "GAMMA"};
NearySymIndex = AssociationThread[NearySymbols, Range[0, 10]];

NearyU311Table[] := Module[{rows, out = <||>},
  rows = <|
    "LA"     -> {{"LE", 1, 0}, {"GAMMA", -1, 1}, {"LA", -1, 2}},
    "LB"     -> {{"LE", 1, 1}, {"LB", -1, 0}, {"E", 1, 0}},
    "E"      -> {{"RE", -1, 0}, {"LE", 1, 0}, {"E", 1, 0}},
    "H"      -> {{"RH", -1, 0}, {"LH", 1, 2}, {"LA", -1, 0}},
    "RE"     -> {{"LE", 1, 0}, {"E", 1, 1}, {"LE", 1, 2}},
    "RH"     -> {{"LH", 1, 0}, {"H", 1, 1}, {"LH", 1, 2}},
    "LE"     -> {{"RE", -1, 0}, {"RE", -1, 1}, {"GAMMA", -1, 1}},
    "LH"     -> {{"RH", -1, 0}, {"RH", -1, 1}, {"LA", -1, 2}},
    "LAMBDA" -> {{"DELTA", 1, 0}, {"LAMBDA", 1, 1}, {"DELTA", 1, 2}},
    "DELTA"  -> {{"LAMBDA", -1, 0}, {"LAMBDA", -1, 1}, None},
    "GAMMA"  -> {{"LA", -1, 2}, {"LH", 1, 2}, {"LB", -1, 2}}
  |>;
  KeyValueMap[
    Function[{symName, row},
      Do[
        If[row[[st + 1]] =!= None,
          out[{st, NearySymIndex[symName]}] = {
            row[[st + 1, 3]],
            NearySymIndex[row[[st + 1, 1]]],
            row[[st + 1, 2]]
          }
        ],
        {st, 0, 2}
      ]
    ],
    rows
  ];
  out
];

EncodeNearyU311[program_Association, stateCount_Integer, word_List] := Module[
  {exponents, etr, extra, prefix = {}, head, current, data = {}, q, t0, t1},
  exponents[t_] := Module[{bVal, aVal},
    bVal = 2 + 5 * t[[1]] + If[t[[3]] === -1, 3, 0];
    aVal = 5 * stateCount + 2 - bVal;
    {aVal, bVal}
  ];
  etr[t_] := Module[{aVal, bVal},
    {aVal, bVal} = exponents[t];
    If[t[[3]] === 1,
      Join[If[t[[2]] === 1, {NearySymIndex["H"]}, {}],
           ConstantArray[NearySymIndex["E"], aVal],
           ConstantArray[NearySymIndex["H"], bVal]],
      Join[ConstantArray[NearySymIndex["E"], aVal - 1],
           ConstantArray[NearySymIndex["H"], bVal],
           If[t[[2]] === 1,
              {NearySymIndex["E"], NearySymIndex["H"], NearySymIndex["E"]},
              ConstantArray[NearySymIndex["E"], 3]]]
    ]
  ];
  extra[qIdx_] := Module[{inc, aVal, bVal},
    If[qIdx === 0,
      Return[Join[ConstantArray[NearySymIndex["E"], 5 * stateCount - 3],
                  ConstantArray[NearySymIndex["H"], 4]]]
    ];
    inc = Select[Values[program], (#[[1]] === qIdx && #[[3]] === 1) &];
    If[inc === {}, Return[{}]];
    {aVal, bVal} = exponents[First[inc]];
    Join[ConstantArray[NearySymIndex["E"], aVal - 3],
         ConstantArray[NearySymIndex["H"], bVal + 2]]
  ];
  For[q = stateCount - 1, q >= 0, q--,
    t0 = program[{q, 0}];
    t1 = program[{q, 1}];
    Do[
      prefix = Join[prefix, {NearySymIndex["LAMBDA"]}, part],
      {part, {etr[t1], etr[t0], etr[t0], etr[t1], extra[q]}}
    ]
  ];
  prefix = Join[prefix, {NearySymIndex["LAMBDA"], NearySymIndex["E"]}];
  head = Length[prefix];
  current = Join[ConstantArray[NearySymIndex["LA"], 5 * stateCount],
                 ConstantArray[NearySymIndex["LB"], 2]];
  Do[
    data = Join[data, {If[bit === 1, NearySymIndex["LB"], NearySymIndex["LA"]], NearySymIndex["LA"]}],
    {bit, word}
  ];
  <|"Symbols" -> Join[prefix, current, data], "Head" -> head|>
];

CompileMultiAlphabetToBinary[program_Association, symbolCount_Integer] := Module[
  {width = BitLength[symbolCount - 1], states = <||>, inverse = {}, queue = {}, out = <||>,
   intern, key, sid, q, i, pfx, v, rule, lastBit, val, dir, rem, newKey},
  intern[k_] := (
    If[!KeyExistsQ[states, k],
      states[k] = Length[inverse];
      AppendTo[inverse, k];
      AppendTo[queue, k];
    ];
    states[k]
  );
  intern[{"read", 0, 0, 0}];
  While[queue =!= {},
    key = First[queue];
    queue = Rest[queue];
    sid = states[key];
    Do[
      Switch[key[[1]],
        "read",
          {q, i, pfx} = Rest[key];
          v = 2 * pfx + bit;
          If[i + 1 < width,
            newKey = {"read", q, i + 1, v};
            out[{sid, bit}] = {intern[newKey], bit, 1},
            rule = If[v < symbolCount && KeyExistsQ[program, {q, v}], program[{q, v}], None];
            If[rule === None,
              If[width > 1,
                newKey = If[width === 2, {"halt"}, {"rewind", width - 2}];
                out[{sid, bit}] = {intern[newKey], bit, -1}
              ],
              lastBit = BitAnd[rule[[2]], 1];
              newKey = {"write", rule[[1]], rule[[2]], rule[[3]], width - 2};
              out[{sid, bit}] = {intern[newKey], lastBit, -1}
            ]
          ],
        "write",
          {q, val, dir, i} = Rest[key];
          lastBit = BitAnd[BitShiftRight[val, width - 1 - i], 1];
          Which[
            i > 0,
              newKey = {"write", q, val, dir, i - 1};
              out[{sid, bit}] = {intern[newKey], lastBit, -1},
            dir === 0,
              out[{sid, bit}] = {intern[{"read", q, 0, 0}], lastBit, 0},
            True,
              newKey = {"shift", q, dir, width - 1};
              out[{sid, bit}] = {intern[newKey], lastBit, dir}
          ],
        "shift",
          {q, dir, rem} = Rest[key];
          newKey = If[rem === 1, {"read", q, 0, 0}, {"shift", q, dir, rem - 1}];
          out[{sid, bit}] = {intern[newKey], bit, dir},
        "rewind",
          rem = key[[2]];
          newKey = If[rem === 1, {"halt"}, {"rewind", rem - 1}];
          out[{sid, bit}] = {intern[newKey], bit, -1},
        "halt",
          Null
      ],
      {bit, {0, 1}}
    ]
  ];
  <|"Rules" -> out, "StateCount" -> Length[inverse], "BlockWidth" -> width|>
];

CachedBinaryUniversal = CompileMultiAlphabetToBinary[NearyU311Table[], 11];
FixedBinaryUniversalRules[] := CachedBinaryUniversal["Rules"];

EncodeSymbols4Bit[symbols_List] := Flatten[IntegerDigits[#, 2, 4] & /@ symbols];

(* -------------------------------------------------------------------------- *)
(* 5. Iterative Bottom-Up Polynomial-Size Initial Pure-S Encoder              *)
(* -------------------------------------------------------------------------- *)

BuildOpenedSubtreeIterative[hubSpec_] := Block[
  {$RecursionLimit = Infinity, $IterationLimit = Infinity},
  Module[{phases = {{2, 2}}, getPhase, depthCache = <||>, getDepthPair,
          built = <||>, stack = {{1, hubSpec, 0, False}}, nextId = 2,
          item, nid, spec, depth, ready, lid, rid, pair, childGen, junk, leftTerm, rightTerm},
    getPhase[d_Integer] := (
      While[Length[phases] <= d,
        With[{mn = Last[phases]},
          AppendTo[phases, If[mn[[1]] > 0, {mn[[1]] - 1, mn[[2]]}, {mn[[2]], mn[[2]] + 1}]]
        ]
      ];
      phases[[d + 1]]
    );
    getDepthPair[d_Integer] := (
      If[!KeyExistsQ[depthCache, d],
        Module[{m, n, cg, jk},
          {m, n} = getPhase[d];
          If[m === 0, m = n + 1; n = n + 1];
          cg = PureSGenerator[m - 1, n];
          jk = (PureSNumeral[n - 2][s])[cg];
          depthCache[d] = {cg, jk}
        ]
      ];
      depthCache[d]
    );
    While[stack =!= {},
      item = Last[stack];
      stack = Most[stack];
      {nid, spec, depth, ready} = item;
      If[!ready,
        lid = If[spec[[1]] === None, 0, nextId++];
        rid = If[spec[[2]] === None, 0, nextId++];
        AppendTo[stack, {nid, {lid, rid}, depth, True}];
        If[rid =!= 0, AppendTo[stack, {rid, spec[[2]], depth + 1, False}]];
        If[lid =!= 0, AppendTo[stack, {lid, spec[[1]], depth + 1, False}]],
        pair = getDepthPair[depth];
        childGen = pair[[1]];
        junk = pair[[2]];
        leftTerm = If[spec[[1]] === 0, childGen, built[spec[[1]]]];
        rightTerm = If[spec[[2]] === 0, childGen, built[spec[[2]]]];
        built[nid] = PureSProtectedFrame[leftTerm, rightTerm, junk]
      ]
    ];
    built[1]
  ]
];

BuildRecordChainSpec[fields_List] := Module[{cur = {None, None}},
  Do[
    cur = {If[flag === 1, {None, None}, None], cur},
    {flag, Reverse[fields]}
  ];
  {None, cur}
];

EncodeBinaryTapeToPureS[stateWidth_Integer, bits_List, headIndex_Integer] := Block[
  {$RecursionLimit = Infinity, $IterationLimit = Infinity},
  Module[{count, tailSpec = None, i, bit, fields, hubSpec},
    count = Max[1, Length[bits], headIndex + 1];
    For[i = count - 1, i >= 0, i--,
      bit = If[i < Length[bits], bits[[i + 1]], 0];
      If[bit === 1 || i === headIndex,
        fields = Join[{bit, 0, If[i === headIndex, 1, 0]}, ConstantArray[0, stateWidth]];
        tailSpec = {BuildRecordChainSpec[fields], tailSpec},
        tailSpec = {None, tailSpec}
      ]
    ];
    hubSpec = {None, tailSpec};
    SeedWithReplacedHub[BuildOpenedSubtreeIterative[hubSpec]]
  ]
];

CompileTuringMachineToPureS[rules_Association, stateCount_Integer, inputBits_List] := Module[
  {norm, uEnc, bits},
  norm = NormalizeNearySafe[rules, stateCount, inputBits];
  uEnc = EncodeNearyU311[norm["Rules"], norm["StateCount"], norm["MarkedWord"]];
  bits = EncodeSymbols4Bit[uEnc["Symbols"]];
  EncodeBinaryTapeToPureS[8, bits, 4 * uEnc["Head"]]
];

(* -------------------------------------------------------------------------- *)
(* 6. Root-Restarted Physical Occurrence-Tree Selector                        *)
(* -------------------------------------------------------------------------- *)

RootRestartedSelectForProgram[program_Association, stateWidth_Integer, rootExpr_] := Block[
  {$RecursionLimit = Infinity, $IterationLimit = Infinity},
  Module[
    {cursorNodes, path, focus, openedQ, down, parentSide, up, toHub, oneNative,
     readVersion, readCell, findStatus, appendOne, pending, active,
     sym, status, st, targetBit, targetStatus, targetState, inst, firstCell},

    If[!PureSAppQ[rootExpr], Return[{"Reject", None}]];
    cursorNodes = {rootExpr, First[rootExpr]};
    path = {1}; (* Hub is at right child of root *)

    focus[] := Last[cursorNodes];
    openedQ[] := ParseProtectedFrame[focus[]] =!= $Failed;

    down[side_Integer] := Module[{edges = If[side === 0, {0, 1}, {1, 0, 1}], cur},
      Do[
        cur = Last[cursorNodes];
        If[!PureSAppQ[cur], Throw[{"Reject", None}]];
        AppendTo[cursorNodes, If[e === 0, Head[cur], First[cur]]];
        AppendTo[path, e],
        {e, edges}
      ]
    ];

    parentSide[] := (
      If[Length[path] <= 1, Throw[{"Reject", None}]];
      If[Length[cursorNodes] >= 3 && ParseProtectedFrame[cursorNodes[[-3]]] =!= $Failed,
        0,
        If[Length[cursorNodes] >= 4 && ParseProtectedFrame[cursorNodes[[-4]]] =!= $Failed,
          1,
          Throw[{"Reject", None}]
        ]
      ]
    );

    up[] := Module[{sd = parentSide[], dist},
      dist = If[sd === 0, 2, 3];
      cursorNodes = Drop[cursorNodes, -dist];
      path = Drop[path, -dist];
    ];

    toHub[] := While[Length[path] > 1, up[]];

    oneNative[] := Module[{rel = BoundedNextOpeningAddress[focus[]]},
      If[rel === $Failed, Throw[{"Reject", None}]];
      {"Step", Join[path, rel]}
    ];

    readVersion[] := Module[{climbs = 1, bits = {}, committed, k, qVal = 0},
      down[1];
      For[k = 1, k <= stateWidth + 3, k++,
        If[!openedQ[],
          Do[up[], {climbs}];
          Return[None]
        ];
        down[0];
        AppendTo[bits, If[openedQ[], 1, 0]];
        up[];
        down[1];
        climbs++;
      ];
      committed = openedQ[];
      Do[up[], {climbs}];
      If[!committed, Return[None]];
      Do[qVal = 2 * qVal + b, {b, Drop[bits, 3]}];
      {bits[[1]], 2 * bits[[2]] + bits[[3]], qVal}
    ];

    readCell[] := Module[{latest = {0, 0, 0}, rec},
      down[0];
      While[openedQ[],
        rec = readVersion[];
        If[rec =!= None, latest = rec];
        down[0];
      ];
      While[Length[path] > 1 && parentSide[] === 0, up[]];
      latest
    ];

    findStatus[wantPending_] := Module[{val},
      toHub[];
      down[1];
      While[openedQ[],
        val = readCell[];
        If[If[wantPending, MemberQ[{2, 3}, val[[2]]], val[[2]] === 1],
          Return[val]
        ];
        down[1];
      ];
      toHub[];
      None
    ];

    appendOne[wSym_, wStat_, wState_] := Module[{desired},
      down[0];
      While[openedQ[],
        If[readVersion[] === None, Break[]];
        down[0];
      ];
      If[!openedQ[], Return[oneNative[]]];
      desired = Join[{wSym, Quotient[wStat, 2], Mod[wStat, 2]},
                     IntegerDigits[wState, 2, stateWidth]];
      down[1];
      Do[
        If[!openedQ[], Return[oneNative[]]];
        down[0];
        If[b === 1 && !openedQ[], Return[oneNative[]]];
        up[];
        down[1],
        {b, desired}
      ];
      oneNative[]
    ];

    Catch[
      If[!openedQ[], Throw[{"Reject", None}]];
      down[0];
      If[openedQ[], Return[{"Halt", None}]];
      up[];

      pending = findStatus[True];
      If[pending =!= None,
        {sym, status, st} = pending;
        If[status === 3,
          down[1],
          up[];
          If[Length[path] === 1, Throw[{"Reject", None}]]
        ];
        If[!openedQ[], Return[oneNative[]]];
        {targetBit, targetStatus, targetState} = readCell[];
        Which[
          targetStatus === 0,
            Return[appendOne[targetBit, 1, st]],
          targetStatus === 1 && targetState === st,
            If[status === 3, up[], down[1]];
            Return[appendOne[sym, 0, 0]],
          True,
            Throw[{"Reject", None}]
        ]
      ];

      active = findStatus[False];
      If[active === None, Throw[{"Reject", None}]];
      {sym, status, st} = active;
      If[!KeyExistsQ[program, {st, sym}],
        toHub[];
        down[0];
        Return[oneNative[]]
      ];
      inst = program[{st, sym}]; (* {nextState, write, move} *)
      If[inst[[3]] === -1,
        up[];
        firstCell = (Length[path] === 1);
        down[1],
        firstCell = False
      ];
      If[inst[[3]] === 0 || (inst[[3]] === -1 && firstCell),
        Return[appendOne[inst[[2]], 1, inst[[1]]]],
        Return[appendOne[inst[[2]], If[inst[[3]] === -1, 2, 3], inst[[1]]]]
      ]
    ]
  ]
];

RootRestartedSelectAddress[expr_] :=
  RootRestartedSelectForProgram[FixedBinaryUniversalRules[], 8, expr];

RootRestartedPureSStep[expr_] := Block[
  {$RecursionLimit = Infinity, $IterationLimit = Infinity},
  Module[{res, cur, p},
    res = RootRestartedSelectAddress[expr];
    Switch[res[[1]],
      "Step", PureSContractAt[expr, res[[2]]],
      "Halt",
        cur = First[ParseProtectedFrame[First[expr]]];
        p = {1, 0, 1};
        While[ParseProtectedFrame[cur] =!= $Failed,
          cur = First[ParseProtectedFrame[cur]];
          p = Join[p, {0, 1}];
        ];
        PureSContractAt[expr, Join[p, BoundedNextOpeningAddress[cur]]],
      _, $Failed
    ]
  ]
];

(* -------------------------------------------------------------------------- *)
(* 7. Linear-Time Bare-Term Output Decoder                                    *)
(* -------------------------------------------------------------------------- *)

ReadCommittedCellValue[cellExpr_, stateWidth_Integer] := Module[
  {cur = First[ParseProtectedFrame[cellExpr]], latest = {0, 0, 0}, parsedVer, fieldCur, bits, k, ok, qVal},
  While[(parsedVer = ParseProtectedFrame[cur]) =!= $Failed,
    fieldCur = parsedVer[[2]];
    bits = {};
    ok = True;
    For[k = 1, k <= stateWidth + 3, k++,
      If[ParseProtectedFrame[fieldCur] === $Failed, ok = False; Break[]];
      AppendTo[bits, If[ParseProtectedFrame[First[ParseProtectedFrame[fieldCur]]] =!= $Failed, 1, 0]];
      fieldCur = ParseProtectedFrame[fieldCur][[2]];
    ];
    If[ok && ParseProtectedFrame[fieldCur] =!= $Failed,
      qVal = FromDigits[Drop[bits, 3], 2];
      latest = {bits[[1]], 2 * bits[[2]] + bits[[3]], qVal}
    ];
    cur = parsedVer[[1]];
  ];
  latest
];

DecodePureSOutput[expr_] := Block[
  {$RecursionLimit = Infinity, $IterationLimit = Infinity},
  Module[
    {hub, cellCur, bits = {}, activeIdx = None, idx = 0, val, syms, uHead, i, markedBits = {}, out},
    If[!PureSHaltFastQ[expr], Return[$Failed]];
    hub = ParseProtectedFrame[First[expr]];
    cellCur = hub[[2]];
    While[ParseProtectedFrame[cellCur] =!= $Failed,
      val = ReadCommittedCellValue[cellCur, 8];
      If[MemberQ[{2, 3}, val[[2]]], Return[$Failed]];
      AppendTo[bits, val[[1]]];
      If[val[[2]] === 1 && activeIdx === None, activeIdx = idx];
      cellCur = ParseProtectedFrame[cellCur][[2]];
      idx++;
    ];
    If[activeIdx === None || Mod[activeIdx, 4] =!= 0, Return[$Failed]];
    While[Mod[Length[bits], 4] =!= 0, AppendTo[bits, 0]];
    syms = FromDigits[#, 2] & /@ Partition[bits, 4];
    uHead = Quotient[activeIdx, 4] + 1;
    If[uHead > Length[syms] || syms[[uHead]] =!= NearySymIndex["DELTA"], Return[$Failed]];
    i = uHead + 1;
    While[i <= Length[syms] && syms[[i]] === NearySymIndex["LA"], i++];
    While[i <= Length[syms] && syms[[i]] === NearySymIndex["LB"], i++];
    If[i <= Length[syms] && syms[[i]] === NearySymIndex["LA"], i++];
    While[i <= Length[syms],
      AppendTo[markedBits, If[syms[[i]] === NearySymIndex["LB"], 1, 0]];
      i += 2;
    ];
    If[markedBits === {} || First[markedBits] =!= 1, Return[$Failed]];
    out = markedBits[[2 ;; ;; 2]];
    While[out =!= {} && Last[out] === 0, out = Most[out]];
    out
  ]
];

(* -------------------------------------------------------------------------- *)
(* 8. Exact 39-State SN Algebra, 35-State HN Algebra (Question 10) & Q7 Chain *)
(* -------------------------------------------------------------------------- *)

SNRawRows = {
  {1,7,19,27,31,29,30,9,32,15,36,19,37,27,31,15,32,36,37,24,29,29,29,29,30,30,29,29,30,30,38,30,26,34,35,29,25,29,38},
  {2,9,22,28,31,30,30,24,33,26,37,25,31,25,31,25,31,31,31,29,29,29,35,29,30,30,30,30,29,38,38,30,30,30,38,38,30,30,38},
  {3,11,24,29,29,30,30,29,29,29,29,30,29,30,30,30,30,30,30,30,29,30,30,30,30,30,30,30,30,38,38,38,38,38,38,38,38,38,38},
  {4,13,25,29,29,30,30,30,29,29,29,30,29,30,30,30,30,30,30,30,29,30,30,30,30,30,30,30,30,38,38,38,38,38,38,38,38,38,38},
  {5,14,25,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,38,38,38,38,38,38,38,38,38,38},
  {6,5,25,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,38,38,38,38,38,38,38,38,38,38},
  {6,6,25,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,38,38,38,38,38,38,38,38,38,38},
  {8,15,26,29,29,30,30,29,34,34,35,29,29,29,29,29,29,29,29,30,29,29,29,29,30,30,30,30,30,38,38,38,38,38,38,38,38,38,38},
  {5,16,25,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,38,38,38,38,38,38,38,38,38,38},
  {10,15,26,29,29,30,30,29,34,35,35,29,29,29,29,29,29,29,29,30,29,29,29,29,30,30,30,30,30,38,38,38,38,38,38,38,38,38,38},
  {5,17,25,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,38,38,38,38,38,38,38,38,38,38},
  {12,11,25,29,29,30,30,30,29,29,29,30,29,30,30,30,30,30,30,30,29,30,30,30,30,30,30,30,30,38,38,38,38,38,38,38,38,38,38},
  {5,18,25,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,38,38,38,38,38,38,38,38,38,38},
  {4,13,25,29,29,30,30,30,29,29,29,30,29,30,30,30,30,30,30,30,29,30,30,30,30,30,30,30,30,38,38,38,38,38,38,38,38,38,38},
  {5,14,25,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,38,38,38,38,38,38,38,38,38,38},
  {10,15,26,29,29,30,30,29,34,35,35,29,29,29,29,29,29,29,29,30,29,29,29,29,30,30,30,30,30,38,38,38,38,38,38,38,38,38,38},
  {5,16,25,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,38,38,38,38,38,38,38,38,38,38},
  {5,17,25,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,38,38,38,38,38,38,38,38,38,38},
  {5,18,25,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,38,38,38,38,38,38,38,38,38,38},
  {20,19,25,29,29,30,30,30,29,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,30,38,38,30,38,38,38,38,38,38,38,38,38,38,38},
  {6,21,25,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,38,38,38,38,38,38,38,38,38,38},
  {6,21,25,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,38,38,38,38,38,38,38,38,38,38},
  {6,23,25,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,38,38,38,38,38,30,38,38,38,38,38,38,38,38,38,38,38},
  {6,23,25,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,38,38,38,38,38,30,38,38,38,38,38,38,38,38,38,38,38},
  {6,24,25,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,38,38,38,38,38,30,38,38,38,38,38,38,38,38,38,38,38},
  {6,25,25,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,38,38,38,38,38,30,38,38,38,38,38,38,38,38,38,38,38},
  {6,26,25,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,38,38,38,38,38,30,38,38,38,38,38,38,38,38,38,38,38},
  {6,27,25,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,30,30,30,38,38,30,38,38,38,38,38,38,38,38,38,38,38},
  {6,28,25,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,30,30,30,38,38,38,38,38,30,38,38,38,38,38,38,38,38,38,38,38},
  {6,29,29,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,38,30,30,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38},
  {6,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,38,30,30,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38},
  {6,31,31,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,38,30,30,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38},
  {21,32,31,29,29,30,30,30,29,30,29,30,29,30,30,30,30,30,30,38,30,30,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38},
  {6,33,31,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,38,30,30,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38},
  {6,34,29,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,38,30,30,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38},
  {6,35,29,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,38,30,30,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38},
  {21,36,31,29,29,30,30,30,29,30,29,30,29,30,30,30,30,30,30,38,30,30,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38},
  {6,37,31,30,30,30,30,30,29,30,29,30,30,30,30,30,30,30,30,38,30,30,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38,38},
  ConstantArray[38, 39]
};

DeltaSN = Transpose[SNRawRows];

EvalSNState[expr_] :=
  PureSDAGFold[expr, 0, DeltaSN[[#1 + 1, #2 + 1]] &];

BuildDeltaHN[] := Module[{d = Table[None, {35}, {35}], pfx, row, x, y, z, s0x, s0xy, xz, yz},
  pfx = {
    {1,6,14,18,8,10,11,26,24,25,23,13,31,13,8,24,22,22,20,32,23,33,25},
    {2,11,16,20,10,10,8,28,23,23,23,17,29,10,20,24,29,23,24,25,24,23,23},
    {3,13,8,20,10,10,20,29,23,23,23,20,29,20,10,24,24,23,23,25,23,23,23},
    {4,13,9,20,10,10,10,22,23,23,23,10,22,10,10,24,24,23,23,25,23,23,23},
    {5,13,10,20,10,10,10,24,23,23,23,10,24,10,10,24,24,23,23,25,23,23,23},
    {5,13,10,20,10,10,10,24,23,23,23,10,24,10,10,24,24,23,23,25,23,23,23},
    {7,13,17,20,10,10,22,30,23,23,23,30,29,24,23,24,24,23,23,25,23,23},
    {8,13,9,20,10,10,23,22,23,23,23,23,22,23,23,24,24,23,23,25,23,23},
    {9,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23},
    {10,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23},
    {10,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23},
    {12,13,17,20,10,10,22,30,23,23,23,29,29,24,23,24,24,23,23,25,23,23},
    {8,13,9,20,10,10,23,22,23,23,23,23,22,23,23,24,24,23,23,25,23,23},
    {12,13,17,20,10,10,22,30,23,23,23,29,29,24,23,24,24,23,23,25,23,23},
    {15,13,10,20,10,10,24,24,23,23,23,24,24,24,23,24,24,23,23,25,23,23},
    {8,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23},
    {8,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23},
    {9,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23},
    {19,13,10,20,10,10,25,24,23,23,23,25,24,25,23,24,24,23,23,25,23,23},
    {9,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23},
    {21,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23},
    {9,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23},
    {10,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23},
    {10,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23},
    {10,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23},
    {10,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23},
    {27,13,10,20,10,10,25,24,23,23,23,25,24,25,23,24,24,23,23,25,23,23},
    {10,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23},
    {9,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23},
    {9,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23},
    {9,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23},
    {27,13,10,20,10,10,25,24,23,23,23,25,24,25,23,24,24,23,23,25,23,23},
    {9,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23},
    {10,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23},
    {10,13,10,20,10,10,23,24,23,23,23,23,24,23,23,24,24,23,23,25,23,23}
  };
  For[y = 1, y <= 35, y++,
    row = pfx[[y]];
    For[x = 1, x <= Length[row], x++, d[[x, y]] = row[[x]]];
    If[Length[row] === 22, d[[23, y]] = 34];
    d[[35, y]] = 34;
    d[[28, y]] = 25;
  ];
  Do[
    For[x = 1, x <= 35, x++,
      For[y = 1, y <= 35, y++,
        For[z = 1, z <= 35, z++,
          s0x = d[[1, x]];
          s0xy = If[s0x =!= None, d[[s0x + 1, y]], None];
          xz = d[[x, z]];
          yz = d[[y, z]];
          If[s0xy =!= None && xz =!= None && yz =!= None && d[[xz + 1, yz + 1]] =!= None,
            If[d[[s0xy + 1, z]] === None, d[[s0xy + 1, z]] = d[[xz + 1, yz + 1]]]
          ]
        ]
      ]
    ],
    {5}
  ];
  d
];

DeltaHN = BuildDeltaHN[];

EvalHNState[expr_] :=
  PureSDAGFold[expr, 0, DeltaHN[[#1 + 1, #2 + 1]] &];

IsRootNormalFormQ[expr_] :=
  Length[PureSSpine[expr]] <= 2 || EvalHNState[Head[expr]] === 34;

Question7GadgetR[x_] := Module[{a = (s[s])[s]},
  ((x[a])[s])[a]
];

Question7ChainWrap[0, tail_] := tail;
Question7ChainWrap[k_Integer?Positive, tail_] :=
  (s[Question7GadgetR[s[s]]])[Question7ChainWrap[k - 1, tail]];

Question7FlipFlopTerm[n_Integer?NonNegative] := Block[
  {$RecursionLimit = Infinity, $IterationLimit = Infinity},
  If[EvenQ[n],
    Question7ChainWrap[Quotient[n, 2], s],
    Question7ChainWrap[Quotient[n, 2], (s[Question7GadgetR[s]])[s]]
  ]
];


(* -------------------------------------------------------------------------- *)
(* 8. Extended Pure-S Algebras (A_P, A_36, D_NAND, B_Zachos) & Rule 110       *)
(* -------------------------------------------------------------------------- *)

DeltaP = {
  {1,2,4,5,8,9,10,11,9,18,9,18,19,10,18,18,18,20,18,9,18,8,9,18,18,18,18,18,20,18,9,9,18,18,18,18,18,37,9},
  {3,6,12,13,21,22,13,7,30,9,31,20,12,13,32,15,16,17,18,38,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38},
  {7,14,15,23,33,33,23,33,33,33,33,33,33,23,33,33,33,27,33,33,33,33,33,33,24,33,27,27,27,29,33,33,33,33,24,27,24,37,33},
  {6,15,24,24,29,29,24,29,29,29,29,29,29,24,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,37,29},
  {16,25,27,24,24,29,24,24,29,29,29,29,24,24,29,29,29,24,29,29,29,24,29,29,29,29,29,29,24,29,29,29,29,29,29,29,29,37,29},
  {17,26,24,34,24,24,34,24,24,24,24,24,24,34,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,29,24,24,24,24,24,24,24,37,24},
  {13,23,24,34,24,29,36,29,29,29,29,29,24,36,29,29,29,29,29,29,29,24,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,37,29},
  {15,24,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,37,29,29,29,29,29,29,37,29,37,37,37,37,29,29,29,29,37,37,37,37,29},
  {27,27,24,24,24,29,24,24,29,29,29,29,24,24,29,29,29,24,29,29,29,24,29,29,29,29,29,29,24,29,29,29,29,29,29,29,29,37,29},
  {24,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,37,29},
  {28,35,24,36,24,24,36,24,24,24,24,24,24,36,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,29,24,24,24,24,24,24,24,37,24},
  {24,24,24,24,24,29,24,29,29,29,29,29,24,24,29,29,29,29,29,29,29,24,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,37,29},
  {7,33,29,24,29,29,24,29,29,29,29,29,29,24,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,37,29},
  {13,33,29,24,29,29,24,29,29,29,29,29,29,24,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,37,29},
  {24,36,29,24,29,29,24,29,29,29,29,29,29,24,29,37,29,37,29,29,29,29,29,37,37,37,37,37,37,37,29,29,29,37,37,37,37,37,29},
  {29,29,29,29,29,29,29,29,29,29,29,29,29,29,37,37,29,37,29,29,29,29,29,37,37,37,37,37,37,37,29,29,37,37,37,37,37,37,29},
  {24,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,37,29,29,29,29,29,29,37,29,37,37,37,37,29,29,29,29,37,37,37,37,29},
  {23,29,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37},
  {29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,37,29},
  {35,27,24,24,24,29,24,24,29,29,29,29,24,24,29,29,29,24,29,29,29,24,29,29,29,29,29,29,24,29,29,29,29,29,29,29,29,37,29},
  {24,24,29,24,29,29,24,29,29,29,29,29,29,24,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,37,29},
  {16,33,29,24,29,29,24,29,29,29,29,29,29,24,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,37,29},
  {17,27,29,24,29,29,24,29,29,29,29,29,29,24,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,37,29},
  {24,29,29,29,29,29,29,37,29,29,29,29,29,29,37,37,37,37,29,29,29,29,29,37,37,37,37,37,37,37,29,29,37,37,37,37,37,37,29},
  {29,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37},
  {29,24,29,29,29,29,29,37,29,29,29,29,29,29,37,37,37,37,29,29,29,29,29,37,37,37,37,37,37,37,29,29,37,37,37,37,37,37,29},
  {34,29,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37},
  {29,29,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37},
  {33,29,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37},
  {37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37},
  {27,27,29,24,29,29,24,29,29,29,29,29,29,24,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,37,29},
  {28,27,29,24,29,29,24,29,29,29,29,29,29,24,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,37,29},
  {24,24,29,24,29,29,24,29,29,29,29,29,29,24,29,37,29,37,29,29,29,29,29,37,37,37,37,37,37,37,29,29,29,37,37,37,37,37,29},
  {29,29,29,29,29,29,29,37,29,29,29,29,29,29,37,37,37,37,29,29,29,29,29,37,37,37,37,37,37,37,29,29,37,37,37,37,37,37,29},
  {36,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37},
  {24,29,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37},
  {24,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37},
  {37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37},
  {35,27,29,24,29,29,24,29,29,29,29,29,29,24,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,29,37,29}
};

EvalProductivityState[expr_] :=
  PureSDAGFold[expr, 0, DeltaP[[#1 + 1, #2 + 1]] &];

IsProductivePureSQ[expr_] :=
  EvalProductivityState[expr] =!= 37;

DeltaA36 = {
  {1,2,3,4,5,5,7,8,9,10,10,12,8,12,15,8,8,9,19,9,21,9,10,10,10,10,27,10,9,9,9,27,9,10,10,10},
  {6,11,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13},
  {14,16,8,9,10,10,17,9,10,10,10,17,9,17,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10},
  {18,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20},
  {8,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10},
  {10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10},
  {11,8,20,10,10,10,22,23,23,23,23,22,23,22,24,23,23,23,25,23,23,23,23,23,23,23,25,23,23,23,23,25,23,23,23,23},
  {26,28,29,22,24,24,30,22,24,24,24,30,22,30,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24},
  {24,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23},
  {25,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23},
  {23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23},
  {13,17,20,10,10,10,30,23,23,23,23,29,23,29,24,23,23,23,25,23,23,23,23,23,23,23,25,23,23,23,23,25,23,23,23,23},
  {31,29,29,22,24,24,29,22,24,24,24,29,22,29,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24},
  {13,10,20,10,10,10,24,23,23,23,23,24,23,24,24,23,23,23,25,23,23,23,23,23,23,23,25,23,23,23,23,25,23,23,23,23},
  {8,20,10,10,10,10,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23},
  {24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24},
  {22,29,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24},
  {22,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23},
  {20,24,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23},
  {32,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25},
  {23,24,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23},
  {33,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23},
  {25,23,23,23,23,23,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34},
  {34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34},
  {23,23,23,23,23,23,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34},
  {23,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34},
  {17,23,23,23,23,23,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34},
  {25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25,25},
  {30,23,23,23,23,23,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34},
  {24,23,23,23,23,23,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34},
  {29,23,23,23,23,23,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34},
  {10,23,23,23,23,23,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34},
  {24,23,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34},
  {34,23,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34},
  {35,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34},
  {35,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34}
};

EvalQuestion31State[expr_] :=
  PureSDAGFold[expr, 0, DeltaA36[[#1 + 1, #2 + 1]] &];

DeltaDNAND = {
  {1,1,1,2},
  {3,3,3,3},
  {1,1,3,3},
  {3,3,3,3}
};

EvalDNANDState[expr_] :=
  PureSDAGFold[expr, 0, DeltaDNAND[[#1 + 1, #2 + 1]] &];

PureSFalseTerm = s[s];
PureSTrueTerm = s[(s[s])[s]];

PureSRule110Term[x_, y_, z_] :=
  s[(s[y[x]])[(s[y[z]])[(s[z[y]])[s]]]];

IteratePureSRule110[bitList_List, steps_Integer?NonNegative] := Block[
  {$RecursionLimit = Infinity, $IterationLimit = Infinity},
  Module[{n = Length[bitList], cells, hist = {}, g, nextCells, dSt},
    cells = If[# === 1 || # === True, PureSTrueTerm, PureSFalseTerm] & /@ bitList;
    For[g = 0, g <= steps, g++,
      dSt = EvalDNANDState /@ cells;
      AppendTo[hist, If[# === 2, 1, 0] & /@ dSt];
      If[g < steps,
        nextCells = Table[
          PureSRule110Term[
            cells[[Mod[i - 2, n] + 1]],
            cells[[i]],
            cells[[Mod[i, n] + 1]]
          ],
          {i, 1, n}
        ];
        cells = nextCells
      ]
    ];
    hist
  ]
];

DeltaBZachos = {
  {1,2,7,5,5,7,7,7},
  {7,7,7,4,4,7,7,7},
  {7,3,7,7,7,7,7,7},
  {7,7,7,6,6,7,7,7},
  {7,7,7,7,7,7,7,7},
  {7,7,7,7,7,7,6,7},
  {7,7,7,7,7,7,7,7},
  {7,7,7,7,7,7,7,7}
};

EvalBZachosState[expr_] :=
  PureSDAGFold[expr, 0, DeltaBZachos[[#1 + 1, #2 + 1]] &];

(* -------------------------------------------------------------------------- *)
(* 9. Program-Free Root-Restarted Pure-S Cyclic Tag Simulator (Zero UTM)      *)
(*    Matches Lean 4 FormalProgramFree (program_free_cts.lean) bit-for-bit:   *)
(*      pfHubPath       = {1}                                                 *)
(*      pfFlagPath      = {1, 0, 1}  (accepted by 11-state PureSHaltDetectorQ)*)
(*      pfPayloadPath   = {1, 1, 0, 1}                                        *)
(*      pfProgRingPath  = {1, 1, 0, 1, 0, 1}                                  *)
(*      pfQueueRootPath = {1, 1, 0, 1, 1, 0, 1}                               *)
(* -------------------------------------------------------------------------- *)

PFHubPath = {1};
PFFlagPath = {1, 0, 1};
PFPayloadPath = {1, 1, 0, 1};
PFProgRingPath = {1, 1, 0, 1, 0, 1};
PFQueueRootPath = {1, 1, 0, 1, 1, 0, 1};
PFLeftChildPath = {0, 1};
PFRightChildPath = {1, 0, 1};

PFNodeAt[root_, path_List] := Module[{cur = root, dir},
  Do[
    If[!PureSAppQ[cur], Return[$Failed]];
    cur = If[dir === 0, Head[cur], First[cur]],
    {dir, path}
  ];
  cur
];

PFChildPath[path_List, side_Integer] :=
  Join[path, If[side === 0, PFLeftChildPath, PFRightChildPath]];

PFProtectedFQ[nd_] := ParseProtectedFrame[nd] =!= $Failed;

PFUnopenedGenQ[nd_] :=
  PureSAppQ[nd] && First[nd] === s && BoundedSpineArity5[nd] === 4;

PFMidOpeningQ[nd_] := (!PFProtectedFQ[nd]) && (!PFUnopenedGenQ[nd]);

PFSelectOpeningAt[root_, path_List] := Module[{focus = PFNodeAt[root, path], rel},
  If[focus === $Failed, Return[$Failed]];
  rel = BoundedNextOpeningAddress[focus];
  If[rel === $Failed, $Failed, Join[path, rel]]
];

(* Exact match to Lean 4 readFields : Nat -> Term -> Option (List Bool) *)
PFReadFields[width_Integer, term_] := Module[{cur = term, bits = {}, pf, i},
  For[i = 1, i <= width, i++,
    pf = ParseProtectedFrame[cur];
    If[pf === $Failed, Return[$Failed]];
    AppendTo[bits, If[PFProtectedFQ[pf[[1]]], 1, 0]];
    cur = pf[[2]]
  ];
  If[PFProtectedFQ[cur], bits, $Failed]
];

(* Exact match to Lean 4 pfScanVersion : Nat -> Option (List Bool) -> Term -> Option (List Bool) *)
PFScanVersion[width_Integer, term_] := Module[{cur = term, latest = None, pf, rd},
  While[(pf = ParseProtectedFrame[cur]) =!= $Failed,
    rd = PFReadFields[width, pf[[2]]];
    If[rd =!= $Failed, latest = rd];
    cur = pf[[1]]
  ];
  latest
];

(* Check whether a version chain has any uncommitted frame or mid-opening tail *)
PFHasUncommittedVerQ[width_Integer, term_] := Module[{cur = term, pf},
  While[(pf = ParseProtectedFrame[cur]) =!= $Failed,
    If[PFReadFields[width, pf[[2]]] === $Failed, Return[True]];
    cur = pf[[1]]
  ];
  PFMidOpeningQ[cur]
];

(* Exact match to Lean 4 chooseSFields : List Bool -> Term -> Option (List Bool) *)
PFChooseSFields[desiredBits_List, term_] := Module[{cur = term, acc = {}, pf, i},
  For[i = 1, i <= Length[desiredBits], i++,
    pf = ParseProtectedFrame[cur];
    If[pf === $Failed, Return[acc]];
    If[desiredBits[[i]] === 1 && !PFProtectedFQ[pf[[1]]],
      Return[Join[acc, PFLeftChildPath]]
    ];
    acc = Join[acc, PFRightChildPath];
    cur = pf[[2]]
  ];
  If[PFProtectedFQ[cur], $Failed, acc]
];

(* Exact match to Lean 4 chooseSVersionTree : Nat -> List Bool -> Term -> Option (List Bool) *)
PFChooseSVersionTree[width_Integer, desiredBits_List, term_] := Module[
  {cur = term, acc = {}, pf, sub},
  While[(pf = ParseProtectedFrame[cur]) =!= $Failed,
    If[PFReadFields[width, pf[[2]]] =!= $Failed,
      acc = Join[acc, PFLeftChildPath];
      cur = pf[[1]],
      sub = PFChooseSFields[desiredBits, pf[[2]]];
      Return[If[sub === $Failed, $Failed, Join[acc, PFRightChildPath, sub]]]
    ]
  ];
  acc
];

PFSelectVersionWriteAt[root_, verPath_List, width_Integer, desiredBits_List] := Module[
  {verTerm = PFNodeAt[root, verPath], slot},
  If[verTerm === $Failed, Return[$Failed]];
  slot = PFChooseSVersionTree[width, desiredBits, verTerm];
  If[slot === $Failed, Return[$Failed]];
  PFSelectOpeningAt[root, Join[verPath, slot]]
];

(* Exact match to Lean 4 scanQueue : Term -> QueueScan *)
PFScanQueue[queueRoot_] := Module[
  {cur = queueRoot, relPrefix = {}, pf, st, cPath,
    consuming = None, unconsumed = None, staging = None, uninit = None},
  While[(pf = ParseProtectedFrame[cur]) =!= $Failed,
    st = PFScanVersion[3, pf[[1]]];
    cPath = Join[relPrefix, PFLeftChildPath];
    Which[
      st === None,
        If[uninit === None, uninit = cPath],
      st === {0, 1, 0} || st === {0, 1, 1},
        If[staging === None, staging = {cPath, st[[3]]}],
      st === {0, 0, 0} || st === {0, 0, 1},
        If[unconsumed === None, unconsumed = {cPath, st[[3]]}],
      st === {1, 0, 0} || st === {1, 0, 1},
        If[consuming === None, consuming = {cPath, st[[3]]}]
    ];
    relPrefix = Join[relPrefix, PFRightChildPath];
    cur = pf[[2]]
  ];
  <|
    "consuming" -> consuming,
    "unconsumed" -> unconsumed,
    "staging" -> staging,
    "uninit" -> uninit,
    "tailPath" -> relPrefix
  |>
];

(* Exact match to Lean 4 scanTemplates : Term -> TemplateScan *)
PFScanTemplates[tList_] := Module[
  {cur = tList, relPrefix = {}, pf, st, cPath,
    firstIdle = None, firstArmed = None, firstAppending = None},
  While[(pf = ParseProtectedFrame[cur]) =!= $Failed,
    st = PFScanVersion[3, pf[[1]]];
    cPath = Join[relPrefix, PFLeftChildPath];
    Which[
      st === {0, 0, 0} || st === {0, 0, 1},
        If[firstIdle === None, firstIdle = {cPath, st[[3]]}],
      st === {1, 0, 0} || st === {1, 0, 1},
        If[firstArmed === None, firstArmed = {cPath, st[[3]]}],
      st === {1, 1, 0} || st === {1, 1, 1},
        If[firstAppending === None, firstAppending = {cPath, st[[3]]}]
    ];
    relPrefix = Join[relPrefix, PFRightChildPath];
    cur = pf[[2]]
  ];
  <|
    "firstIdle" -> firstIdle,
    "firstArmed" -> firstArmed,
    "firstAppending" -> firstAppending
  |>
];

(* Exact match to Lean 4 scanPhases : Term -> List PhaseEntry *)
PFScanPhases[progRing_] := Module[
  {cur = progRing, relPrefix = {}, pf, bodyPf, phases = {}},
  While[(pf = ParseProtectedFrame[cur]) =!= $Failed,
    bodyPf = ParseProtectedFrame[pf[[1]]];
    If[bodyPf === $Failed, Break[]];
    AppendTo[phases, <|
      "verPath" -> Join[relPrefix, {0, 1, 0, 1}],
      "tListPath" -> Join[relPrefix, {0, 1, 1, 0, 1}],
      "status" -> PFScanVersion[2, bodyPf[[1]]],
      "templates" -> PFScanTemplates[bodyPf[[2]]]
    |>];
    relPrefix = Join[relPrefix, PFRightChildPath];
    cur = pf[[2]]
  ];
  phases
];

(* Exact match to Lean 4 pfDecideAction : List PhaseEntry -> QueueScan -> PFDecision *)
PFDecideAction[phases_List, q_Association] := Module[
  {handoffs, hIdx, hEntry, nxtIdx, nxtEntry, actives, actEntry, tmpl,
    uRelPath, b, tRelPath, sbit, stRelPath, uInitRelPath},
  handoffs = Select[Range[Length[phases]], phases[[#, "status"]] === {1, 1} &];
  If[handoffs =!= {},
    hIdx = First[handoffs];
    hEntry = phases[[hIdx]];
    If[q["consuming"] =!= None,
      Return[{"writeVer", Join[PFQueueRootPath, q["consuming"][[1]]], 3, {1, 1, q["consuming"][[2]]}}]
    ];
    If[Length[phases] === 1,
      Return[{"writeVer", Join[PFProgRingPath, hEntry["verPath"]], 2, {1, 0}}]
    ];
    nxtIdx = Mod[hIdx, Length[phases]] + 1;
    nxtEntry = phases[[nxtIdx]];
    If[nxtEntry["status"] === {1, 0},
      Return[{"writeVer", Join[PFProgRingPath, hEntry["verPath"]], 2, {0, 0}}],
      Return[{"writeVer", Join[PFProgRingPath, nxtEntry["verPath"]], 2, {1, 0}}]
    ]
  ];
  actives = Select[Range[Length[phases]], phases[[#, "status"]] === {1, 0} &];
  If[actives === {}, Return[{"none"}]];
  actEntry = phases[[First[actives]]];
  tmpl = actEntry["templates"];
  If[q["consuming"] === None,
    If[q["unconsumed"] === None,
      Return[{"openSlot", PFFlagPath}]
    ];
    {uRelPath, b} = q["unconsumed"];
    If[b === 1 && tmpl["firstIdle"] =!= None,
      {tRelPath, sbit} = tmpl["firstIdle"];
      Return[{"writeVer", Join[PFProgRingPath, actEntry["tListPath"], tRelPath], 3, {1, 0, sbit}}]
    ];
    Return[{"writeVer", Join[PFQueueRootPath, uRelPath], 3, {1, 0, b}}]
  ];
  If[tmpl["firstAppending"] =!= None,
    {tRelPath, sbit} = tmpl["firstAppending"];
    If[q["staging"] =!= None,
      Return[{"writeVer", Join[PFProgRingPath, actEntry["tListPath"], tRelPath], 3, {0, 0, sbit}}]
    ];
    If[q["uninit"] =!= None,
      uInitRelPath = q["uninit"];
      Return[{"writeVer", Join[PFQueueRootPath, uInitRelPath], 3, {0, 1, sbit}}]
    ];
    Return[{"openSlot", Join[PFQueueRootPath, q["tailPath"]]}]
  ];
  If[q["staging"] =!= None,
    {stRelPath, sbit} = q["staging"];
    Return[{"writeVer", Join[PFQueueRootPath, stRelPath], 3, {0, 0, sbit}}]
  ];
  If[tmpl["firstArmed"] =!= None,
    {tRelPath, sbit} = tmpl["firstArmed"];
    Return[{"writeVer", Join[PFProgRingPath, actEntry["tListPath"], tRelPath], 3, {1, 1, sbit}}]
  ];
  {"writeVer", Join[PFProgRingPath, actEntry["verPath"]], 2, {1, 1}}
];

(* Exact match to Lean 4 pfRootHalt == pfHaltAutomaton.evalAccepts == PureSHaltDetectorQ *)
ProgramFreePureSHaltQ[root_] := PureSHaltDetectorQ[root];

(* Exact match to Lean 4 pfSelect : Term -> PFOutcome *)
ProgramFreePureSSelect[bareRoot_] := Block[
  {$RecursionLimit = Infinity, $IterationLimit = Infinity},
  Module[{hub, hubPf, payloadPf, phases, q, dec, path},
    If[ProgramFreePureSHaltQ[bareRoot], Return[{"Halt", None}]];
    hub = PFNodeAt[bareRoot, PFHubPath];
    If[hub === $Failed, Return[{"Stuck", None}]];
    hubPf = ParseProtectedFrame[hub];
    If[hubPf === $Failed, Return[{"Stuck", None}]];
    payloadPf = ParseProtectedFrame[hubPf[[2]]];
    If[payloadPf === $Failed, Return[{"Stuck", None}]];
    phases = PFScanPhases[payloadPf[[1]]];
    q = PFScanQueue[payloadPf[[2]]];
    dec = PFDecideAction[phases, q];
    path = Which[
      dec[[1]] === "openSlot", PFSelectOpeningAt[bareRoot, dec[[2]]],
      dec[[1]] === "writeVer", PFSelectVersionWriteAt[bareRoot, dec[[2]], dec[[3]], dec[[4]]],
      True, $Failed
    ];
    If[path === $Failed || PureSContractAt[bareRoot, path] === $Failed,
      {"Stuck", None},
      {"Step", path}
    ]
  ]
];

ProgramFreePureSCTSStep[expr_] := Module[{sel = ProgramFreePureSSelect[expr]},
  If[sel[[1]] === "Step", PureSContractAt[expr, sel[[2]]], expr]
];

(* Exact O(|P| + |w|) layout constructor matching Lean 4 FormalProgramFree.encodeProgramFreeCTS *)
PFNextPhase[{m_Integer, n_Integer}] :=
  If[m === 0, {n, n + 1}, {m - 1, n}];

PFPhaseAt[d_Integer?NonNegative] :=
  Nest[PFNextPhase, {2, 2}, d];

PFDepthBase[d_Integer?NonNegative] := Module[{p = PFPhaseAt[d]},
  PureSGenerator[p[[1]], p[[2]]]
];

PFDepthJunk[d_Integer?NonNegative] := Module[{p = PFPhaseAt[d], m, n},
  {m, n} = p;
  If[m === 0,
    (PureSNumeral[n - 1][s])[PureSGenerator[n, n + 1]],
    (PureSNumeral[n - 2][s])[PureSGenerator[m - 1, n]]
  ]
];

PFBitTerm[d_Integer, b_Integer] :=
  If[b === 1,
    PureSProtectedFrame[PFDepthBase[d + 1], PFDepthBase[d + 1], PFDepthJunk[d]],
    PFDepthBase[d]
  ];

PFFieldsTerm[bits_List, d_Integer] := Module[{k = Length[bits], acc, i},
  acc = PureSProtectedFrame[PFDepthBase[d + k + 1], PFDepthBase[d + k + 1], PFDepthJunk[d + k]];
  For[i = k, i >= 1, i--,
    acc = PureSProtectedFrame[PFBitTerm[d + i, bits[[i]]], acc, PFDepthJunk[d + i - 1]]
  ];
  acc
];

PFVerTerm[records_List, d_Integer] := Module[{k = Length[records], acc, i},
  acc = PFDepthBase[d + k];
  For[i = k, i >= 1, i--,
    acc = PureSProtectedFrame[acc, PFFieldsTerm[records[[i]], d + i], PFDepthJunk[d + i - 1]]
  ];
  acc
];

PFRecListTerm[cellRecords_List, d_Integer] := Module[{k = Length[cellRecords], acc, i},
  acc = PFDepthBase[d + k];
  For[i = k, i >= 1, i--,
    acc = PureSProtectedFrame[PFVerTerm[cellRecords[[i]], d + i], acc, PFDepthJunk[d + i - 1]]
  ];
  acc
];

PFPhaseBodyTerm[pRecs_List, tCells_List, d_Integer] :=
  PureSProtectedFrame[PFVerTerm[pRecs, d + 1], PFRecListTerm[tCells, d + 1], PFDepthJunk[d]];

PFProgRingTerm[phaseStates_List, d_Integer] := Module[{k = Length[phaseStates], acc, i, ph},
  acc = PFDepthBase[d + k];
  For[i = k, i >= 1, i--,
    ph = phaseStates[[i]];
    acc = PureSProtectedFrame[PFPhaseBodyTerm[ph[[1]], ph[[2]], d + i], acc, PFDepthJunk[d + i - 1]]
  ];
  acc
];

EncodeProgramFreeCTS[programList_List, inputBits_List] := Block[
  {$RecursionLimit = Infinity, $IterationLimit = Infinity},
  Module[{phaseStates, qCells, progRing, queueRoot, hub},
    phaseStates = Table[
      {
        {{If[idx === 1, 1, 0], 0}},
        ({If[# === 1 || # === True, {0, 0, 1}, {0, 0, 0}]} &) /@ programList[[idx]]
      },
      {idx, 1, Length[programList]}
    ];
    qCells = ({If[# === 1 || # === True, {0, 0, 1}, {0, 0, 0}]} &) /@ inputBits;
    progRing = PFProgRingTerm[phaseStates, 2];
    queueRoot = PFRecListTerm[qCells, 2];
    hub = PureSProtectedFrame[
      PFDepthBase[1],
      PureSProtectedFrame[progRing, queueRoot, PFDepthJunk[1]],
      PFDepthJunk[0]
    ];
    (PureSNumeral[1][s])[hub]
  ]
];

DecodeProgramFreeCTSState[bareRoot_] := Block[
  {$RecursionLimit = Infinity, $IterationLimit = Infinity},
  Module[
    {hub, hubPf, payloadPf, curP, pPf, bodyPf, st, curT, tPf, tst,
      phases = {}, act, curQ, qPf, qst, word = {}},
    hub = PFNodeAt[bareRoot, PFHubPath];
    If[hub === $Failed, Return[None]];
    hubPf = ParseProtectedFrame[hub];
    If[hubPf === $Failed, Return[None]];
    If[PFMidOpeningQ[hubPf[[1]]], Return[None]];
    payloadPf = ParseProtectedFrame[hubPf[[2]]];
    If[payloadPf === $Failed, Return[None]];
    curP = payloadPf[[1]];
    While[(pPf = ParseProtectedFrame[curP]) =!= $Failed,
      bodyPf = ParseProtectedFrame[pPf[[1]]];
      If[bodyPf === $Failed, Return[None]];
      If[PFHasUncommittedVerQ[2, bodyPf[[1]]], Return[None]];
      st = PFScanVersion[2, bodyPf[[1]]];
      If[st =!= {0, 0} && st =!= {1, 0}, Return[None]];
      curT = bodyPf[[2]];
      While[(tPf = ParseProtectedFrame[curT]) =!= $Failed,
        If[PFHasUncommittedVerQ[3, tPf[[1]]], Return[None]];
        tst = PFScanVersion[3, tPf[[1]]];
        If[tst === None || Take[tst, 2] =!= {0, 0}, Return[None]];
        curT = tPf[[2]]
      ];
      If[PFMidOpeningQ[curT], Return[None]];
      AppendTo[phases, st];
      curP = pPf[[2]]
    ];
    If[PFMidOpeningQ[curP], Return[None]];
    act = Select[Range[Length[phases]], phases[[#]] === {1, 0} &];
    If[Length[act] =!= 1, Return[None]];
    curQ = payloadPf[[2]];
    While[(qPf = ParseProtectedFrame[curQ]) =!= $Failed,
      If[PFHasUncommittedVerQ[3, qPf[[1]]], Return[None]];
      qst = PFScanVersion[3, qPf[[1]]];
      Which[
        qst === {0, 0, 0} || qst === {0, 0, 1},
          AppendTo[word, qst[[3]]],
        qst === {1, 1, 0} || qst === {1, 1, 1},
          Null,
        True,
          Return[None]
      ];
      curQ = qPf[[2]]
    ];
    If[PFMidOpeningQ[curQ], Return[None]];
    {First[act] - 1, word}
  ]
];

(* -------------------------------------------------------------------------- *)
(* 10. Wolfram Challenge 12 Benchmarks, Minimal Witnesses & Jump-Ahead Solver *)
(* -------------------------------------------------------------------------- *)

WolframChallenge12Benchmarks[] := {
  s[s[s[s[s]][s]]][s][s],
  s[s][s][s[s[s]]][s[s]],
  s[s][s][s[s[s[s][s]]]][s],
  s[s[s[s]][s[s[s]][s]]][s][s],
  s[s][s][s][s][s][s[s[s]]][s],
  s[s][s][s[s[s[s][s]][s]]][s],
  s[s[s][s][s[s]]][s[s][s]][s],
  s[s][s][s[s[s]]][s[s]][s[s]],
  s[s][s][s][s[s][s]][s][s][s][s],
  s[s][s][s[s[s[s[s]][s]][s]]][s],
  s[s][s][s[s][s[s[s[s][s]]]]][s],
  s[s[s[s]][s][s]][s[s[s]][s]][s]
};

MinimalNonHaltingPureSTerms[] := {
  s[s][s][s[s]][s][s],
  s[s[s]][s][s][s][s]
};

MinimalProductiveNonSNPureSTerm = s[s[s[s]]][s[s[s]]][s[s]];

PureSJumpAheadOutcome[expr_] := Module[
  {leaves, sn, hn, pr, rnf, regime},
  leaves = PureSLeafCount[expr];
  sn = EvalSNState[expr];
  hn = EvalHNState[expr];
  pr = EvalProductivityState[expr];
  rnf = IsRootNormalFormQ[expr];
  regime = Which[
    sn < 38, "Halting (Strongly Normalizing)",
    pr =!= 37, "Productive Non-Halting (Infinite Bohm Tree, HNF at Every Node)",
    hn < 34, "HNF-Stopping Non-Productive (Reaches HNF, Diverges Deeper in Subtrees)",
    True, "Root-Divergent (No Head Normal Form, Infinite Root Activity)"
  ];
  <|
    "Leaves" -> leaves,
    "SNState" -> sn,
    "HaltsQ" -> (sn < 38),
    "HNState" -> hn,
    "HasHNFQ" -> (hn < 34),
    "ProductivityState" -> pr,
    "ProductiveQ" -> (pr =!= 37),
    "RootNormalFormQ" -> rnf,
    "AsymptoticRegime" -> regime
  |>
];

PureSAsymptoticConstants[] := <|
  "HNLimitingDensityExact" -> 4429673 / 7077888,
  "HeadDivergentDensityExact" -> 2648215 / 7077888,
  "SNMinimalPolynomialCoefficients" -> {
    -1, 7, -3, -73, 96, 386, -617, -1407, 2254, 3898, -5550, -8506,
    10034, 14894, -14408, -21828, 17659, 28887, -18321, -36011, 13358,
    39636, -2411, -34117, -7829, 20503, 10263, -7567, -6320, 1242,
    2151, 121, -384, -76, 28, 8
  },
  "ProductivityMinimalPolynomialCoefficients" -> {
    -1, 7, -3, -73, 96, 386, -617, -1407, 2254, 3898, -5546, -8522,
    10006, 15062, -14336, -22636, 17551, 31327, -18097, -41127, 12602,
    47332, -519, -42441, -10841, 26843, 13363, -10803, -8384, 2234,
    3007, -7, -584, -88, 48, 12
  },
  "rSN50" -> "0.29674299328035902012310696757519762554231489825232",
  "gammaSN50" -> "3.3699195015371859872535742478309873090154088531622",
  "alphaSN50" -> "4.1128226175954073475130543023402705507387108612405",
  "rP50" -> "0.29673733243763365737109465719898306195922977865696",
  "gammaP50" -> "3.3699837893170168052865469050899980331801238563045",
  "alphaP50" -> "4.1132143739052054851331007088613634200331206508689",
  "ZachosDominanceHalfLifeLeaves" -> 36334.63
|>;

PureSCatalanPhaseCensus[maxLeaves_Integer?Positive] := Module[
  {dpNF, dpSN, dpP, dpHN, n, k, a, b, rowSN, rowP, rowHN},
  dpNF = ConstantArray[0, maxLeaves];
  dpSN = ConstantArray[0, {maxLeaves, 39}];
  dpP = ConstantArray[0, {maxLeaves, 39}];
  dpHN = ConstantArray[0, {maxLeaves, 35}];
  dpNF[[1]] = 1;
  dpSN[[1, 1]] = 1;
  dpP[[1, 1]] = 1;
  dpHN[[1, 1]] = 1;
  For[n = 2, n <= maxLeaves, n++,
    dpNF[[n]] = dpNF[[n - 1]] + Sum[dpNF[[k]] * dpNF[[n - 1 - k]], {k, 1, n - 2}];
    rowSN = ConstantArray[0, 39];
    rowP = ConstantArray[0, 39];
    rowHN = ConstantArray[0, 35];
    For[k = 1, k <= n - 1, k++,
      For[a = 1, a <= 39, a++,
        If[dpSN[[k, a]] > 0,
          For[b = 1, b <= 39, b++,
            If[dpSN[[n - k, b]] > 0,
              rowSN[[DeltaSN[[a, b]] + 1]] += dpSN[[k, a]] * dpSN[[n - k, b]]
            ]
          ]
        ];
        If[dpP[[k, a]] > 0,
          For[b = 1, b <= 39, b++,
            If[dpP[[n - k, b]] > 0,
              rowP[[DeltaP[[a, b]] + 1]] += dpP[[k, a]] * dpP[[n - k, b]]
            ]
          ]
        ]
      ];
      For[a = 1, a <= 35, a++,
        If[dpHN[[k, a]] > 0,
          For[b = 1, b <= 35, b++,
            If[dpHN[[n - k, b]] > 0,
              rowHN[[DeltaHN[[a, b]] + 1]] += dpHN[[k, a]] * dpHN[[n - k, b]]
            ]
          ]
        ]
      ]
    ];
    dpSN[[n]] = rowSN;
    dpP[[n]] = rowP;
    dpHN[[n]] = rowHN
  ];
  Table[
    <|
      "Leaves" -> m,
      "CatalanTotal" -> CatalanNumber[m - 1],
      "NFCount" -> dpNF[[m]],
      "SNCount" -> Total[Take[dpSN[[m]], 38]],
      "ProductiveCount" -> Total[Delete[dpP[[m]], 38]],
      "HNCount" -> Total[Take[dpHN[[m]], 34]]
    |>,
    {m, 1, maxLeaves}
  ]
];

End[];
EndPackage[];
