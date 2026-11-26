# PureSUniversality: Wolfram Language Implementation and Verification Suite

This directory provides a self-contained Wolfram Language implementation and test runner accompanying the monograph *Computational Universality, Finite Tree Algebras, and Asymptotic Phase Transitions of the Pure $S$ Combinator* (`WOLFRAM_S_PRIZE_SUBMISSION.tex` and `WOLFRAM_S_PRIZE_SUBMISSION_CN.md`), together with a Python cross-validator verifying exact table and trajectory agreement with the Lean 4.33.1 formalization (`s_challenge_master_headline.lean`).

## Contents

- `PureSUniversality.wl` — Standalone Wolfram Language package (`PureSUniversality` context) implementing pure-$S$ syntax, iterative DAG-memoized folds, polynomial-size Turing machine compilation via Neary and Woods's $U_{3,11}$, stateless root-restarted occurrence-tree selection, program-free cyclic tag system simulation, the finite $S$-algebras $\mathcal{A}_{\mathrm{SN}}$, $\mathcal{A}_{\mathrm{HN}}$, $\mathcal{A}_P$, $\mathcal{A}_{36}$, $\mathcal{D}_4$, and $\mathcal{B}_Z$, benchmark classification, and Catalan asymptotic constants.
- `VerifyPureSUniversality.wls` — Standalone WolframScript verification suite executing twelve deterministic test blocks across the algebraic identities, simulation pipelines, benchmark terms, and Catalan phase counts.
- `cross_validate_wl.py` — Independent Python parser and cross-validator that checks delimiter balance in `.wl` and `.wls`, parses every transition matrix directly from `PureSUniversality.wl`, verifies entry-for-entry agreement with the Lean 4 and Python formal tables, and reproduces all simulation invariants without requiring a local Wolfram license.

## Term Representation and Evaluation Discipline

Closed pure-$S$ combinator expressions $\mathcal{T}_S$ are represented natively as curried expressions over the atomic symbol `s`:

- Atomic combinator $S \equiv \texttt{s}$.
- Left-associative binary application $(M\,N) \equiv \texttt{M[N]}$, with left child `Head[expr]` and right child `First[expr]`.
- Occurrence paths are lists over `{0, 1}`, where `0` descends into `Head[cur]` (left child) and `1` descends into `First[cur]` (right child).
- All tree folds (`PureSDAGFold`, `PureSLeafCount`, `EvalSNState`, `EvalHNState`, `EvalProductivityState`, `PureSHaltAutomatonState`) and occurrence-path contractions (`PureSContractAt`) use explicit iterative stacks with `Association` memoization rather than Wolfram call-stack recursion, avoiding `$RecursionLimit` bounds on deep spines while computing exact unfolded tree values.

## Exported Symbols and Mathematical Correspondence

### 1. Syntax, Tree Measures, and Contraction Primitives

| Wolfram Language Symbol | Mathematical Object | Description |
| :--- | :--- | :--- |
| `s` | $S \in \mathcal{T}_S$ | Atomic pure-$S$ combinator constant. |
| `PureSLeafCount[expr]` | $\lvert M \rvert$ | Exact unfolded $S$-leaf count computed in $O(\lvert\mathrm{DAG}\rvert)$ time. |
| `PureSNodeCount[expr]` | $\mathrm{nodes}(M) = 2\lvert M \rvert - 1$ | Exact unfolded binary-tree node count. |
| `PureSContractAt[expr, path]` | $M \to_S M'$ at $p \in \{0,1\}^*$ | Performs one contextual contraction `s[x][y][z] -> x[z][y[z]]` at `path`. |
| `PureSStepLeftmostOutermost[expr]` | $\to_{\mathrm{lo}}$ | Performs one leftmost-outermost (normal-order) reduction step, returning `{nextExpr, changedQ}`. |

### 2. Controlled Turing Machine Compilation, Halting Automaton, and Output Readback (Section 3)

| Wolfram Language Symbol | Mathematical Object | Description |
| :--- | :--- | :--- |
| `NormalizeNearySafe[rules, n, w]` | $\mathrm{normalizeSafe}(M, w)$ | Compiles a clamping-left binary Turing machine $M$ into a boundary-safe $(\lvert Q\rvert+2+\lvert\mathrm{dom}(\delta_M)\rvert)$-state (at most $(3\lvert Q\rvert+2)$-state) binary machine. |
| `EncodeNearyU311[rules, n, w]` | $u_0$ on $U_{3,11}$ | Encodes a normalized binary machine and word onto the 11-symbol tape of Neary and Woods's $U_{3,11}$. |
| `FixedBinaryUniversalRules[]` | $U_{\mathrm{bin}}$ | Returns the fixed 132-state, 262-rule binary compilation of $U_{3,11}$ under 4-bit big-endian symbol blocks. |
| `EncodeBinaryTapeToPureS[width, bits, head]` | Protected-frame tape layout | Encodes a binary tape and head position into spine-2 frames $F(a,b,j) \equiv S a (S b j)$ beneath the root hub. |
| `CompileTuringMachineToPureS[rules, n, w]` | $\mathcal{E}_{\mathrm{TM}}(M, w)$ | End-to-end $O((\lvert Q\rvert^2 + \lvert w\rvert)^2)$-leaf compiler from $(M, w)$ to $\mathcal{T}_S$. |
| `RootRestartedSelectForProgram[prog, width, expr]` | Parameterized tree-walker | Runs the stateless root-restarted selector parameterized by a binary transition table. |
| `RootRestartedSelectAddress[expr]` | $\sigma_{\mathrm{TM}}$ address phase | Starts at the root of `expr` without retained inter-step memory and returns `{"Halt", None}`, `{"Step", path}`, or `{"Reject", None}`. |
| `RootRestartedPureSStep[expr]` | $T \mapsto \sigma_{\mathrm{TM}}(T)$ | Applies one selected $S$-contraction step (continuing along the post-halt frontier after halting). |
| `PureSHaltAutomatonState[expr]` | $\llbracket M \rrbracket_{\mathcal{H}_{11}} \in \{0,\dots,10\}$ | Evaluates the minimal 11-state deterministic bottom-up halting tree automaton $\mathcal{H}_{11}$. |
| `PureSHaltDetectorQ[expr]` | $M \in L(\mathcal{H}_{11})$ | Returns `True` if and only if $\llbracket M \rrbracket_{\mathcal{H}_{11}} \in \{3, 6, 8, 10\}$. |
| `DecodePureSOutput[expr]` | $\mathcal{D}_{\mathrm{TM}}(T_k)$ | Linear-time bare-term output decoder recovering $\mathrm{out}_M(w)$ from any halted term $T_k \in L(\mathcal{H}_{11})$. |

### 3. Program-Free Cyclic Tag System Simulation (Section 4)

| Wolfram Language Symbol | Mathematical Object | Description |
| :--- | :--- | :--- |
| `EncodeProgramFreeCTS[prog, bits]` | $\mathcal{E}_{\mathrm{CTS}}(P, w)$ | Encodes a cyclic tag system $P$ and binary queue $w$ into a self-describing closed $S$-term reachable from $D_{\mathrm{seed}}$. |
| `ProgramFreePureSSelect[expr]` | $\sigma_{\mathrm{CTS}}$ address phase | Program-free root-restarted selector containing no embedded universal machine transition table. |
| `ProgramFreePureSCTSStep[expr]` | $T \mapsto \sigma_{\mathrm{CTS}}(T)$ | Executes one program-free pure-$S$ contraction step. |
| `ProgramFreePureSHaltQ[expr]` | $M \in L(\mathcal{H}_{11})$ | Tests halting via the identical 11-state bottom-up tree automaton $\mathcal{H}_{11}$ evaluated at the root of `expr`. |
| `DecodeProgramFreeCTSState[expr]` | $\mathcal{D}_{\mathrm{CTS}}(T_k)$ | Decodes `{activePhase, unconsumedQueueBits}` at clean cyclic tag macro-step boundaries, or `None` at intermediate micro-steps. |

### 4. Finite $S$-Algebras, Open Problems, and Cellular Polynomials (Sections 6 and 7)

| Wolfram Language Symbol | Mathematical Object | Description |
| :--- | :--- | :--- |
| `EvalSNState[expr]` | $\llbracket M \rrbracket_{\mathrm{SN}} \in Q_{\mathrm{SN}}$ | Evaluates the 39-state strong-normalization $S$-algebra $\mathcal{A}_{\mathrm{SN}}$ (`0..37` normalizing; `38` equals $\infty_{\mathrm{SN}}$). |
| `EvalHNState[expr]` | $\llbracket M \rrbracket_{\mathrm{HN}} \in Q_{\mathrm{HN}}$ | Evaluates the 35-state head-normalization $S$-algebra $\mathcal{A}_{\mathrm{HN}}$ (`0..33` solvable; `34` equals $\infty_{\mathrm{HN}}$; Question 10). |
| `IsRootNormalFormQ[expr]` | $M \in \mathrm{RNF}$ | Linear-time root normal form membership test ($\mathrm{ls}(M) \le 2$ or $\llbracket \mathrm{left}(M) \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$; Footnote 4). |
| `EvalProductivityState[expr]` | $\llbracket M \rrbracket_P \in Q_P$ | Evaluates the 39-state Böhm-tree productivity $S$-algebra $\mathcal{A}_P$ (`37` equals $\infty_P$; Question 5). |
| `IsProductivePureSQ[expr]` | $M \in \mathrm{Prod}$ | Returns `True` if and only if $\llbracket M \rrbracket_P \neq 37$. |
| `Question7FlipFlopTerm[n]` | $F_n$ | Constructs the $n$-th term in the one-leaf refinement chain $F_0 \sqsubset F_1 \sqsubset \dots$ alternating between $\mathrm{SN}$ and $\overline{\mathrm{SN}}$ (Question 7). |
| `EvalQuestion31State[expr]` | $\llbracket M \rrbracket_{36} \in Q_{36}$ | Evaluates the 36-state conversion-invariant $S$-algebra $\mathcal{A}_{36}$ separating $\llbracket A A A \rrbracket_{36} = 34$ from $\llbracket A A A S \rrbracket_{36} = 35$ ($A \equiv S S S$; Question 31). |
| `EvalBZachosState[expr]` | $\llbracket M \rrbracket_{\mathcal{B}_Z} \in \{0,\dots,7\}$ | Evaluates the 8-state tree automaton $\mathcal{B}_Z$ (accepting state `6`) recognizing quadratic milestones $n(n+3)/2$ along $Z_{\mathrm{Zac}} \equiv S T T(S T T)$ ($T \equiv S S$). |
| `EvalDNANDState[expr]` | $\llbracket M \rrbracket_{\mathcal{D}_4} \in \{0,1,2,3\}$ | Evaluates the 4-state functionally complete $S$-algebra $\mathcal{D}_4$. |
| `PureSFalseTerm`, `PureSTrueTerm` | $S S$, $S(SSS)$ | Spine-1 normal-form Boolean representatives evaluating to states `1` and `2` in $\mathcal{D}_4$. |
| `PureSRule110Term[x, y, z]` | $R_{110}(x,y,z)$ | Minimal 11-leaf pure-$S$ combinator `s[s[y[x]][s[y[z]][s[z[y]][s]]]]` realizing elementary cellular automaton Rule 110 in $\mathcal{D}_4$ while preserving Spine-1 normal forms. |
| `IteratePureSRule110[bits, steps]` | Rule 110 evolution | Iterates periodic 1D Rule 110 on Spine-1 normal-form $S$-terms and decodes the Boolean state history. |

### 5. Challenge Benchmarks, Jump-Ahead Classification, and Catalan Asymptotics (Section 8)

| Wolfram Language Symbol | Mathematical Object | Description |
| :--- | :--- | :--- |
| `MinimalNonHaltingPureSTerms[]` | $\{X_2, X_1\}$ | Returns `{s[s][s][s[s]][s][s], s[s[s]][s][s][s][s]}`, Duboué's two minimal 7-leaf non-normalizing $S$-terms. |
| `MinimalProductiveNonSNPureSTerm` | $Z_0$ | The unique minimal 9-leaf productive non-normalizing combinator $S(S(SS))(S(SS))(SS)$. |
| `WolframChallenge12Benchmarks[]` | $(W_1, \dots, W_{12})$ | Returns the twelve benchmark non-normalizing expressions from Wolfram's June 2021 Challenge announcement. |
| `PureSJumpAheadOutcome[expr]` | $(\llbracket M \rrbracket_{\mathrm{SN}}, \llbracket M \rrbracket_{\mathrm{HN}}, \llbracket M \rrbracket_P)$ | Computes leaf count, algebraic states, RNF membership, and dynamical regime classification in $O(\|\mathrm{DAG}\|)$ time. |
| `PureSAsymptoticConstants[]` | $(c_{\mathrm{HN}}, P_{\mathrm{SN}}, P_P, \rho_{\mathrm{SN}}, \rho_P)$ | Returns the exact rational HNF limiting density $4429673/7077888$, degree-35 minimal polynomial coefficients, and 50-digit singularity constants. |
| `PureSCatalanPhaseCensus[maxLeaves]` | Exact DP table | Computes exact Catalan counts $C_{n-1}$, $\#\mathrm{NF}(n)$, $\#\mathrm{SN}(n)$, $\#\mathrm{Prod}(n)$, and $\#\mathrm{HN}(n)$ for $1 \le n \le \texttt{maxLeaves}$. |

## Command-Line Verification

With Wolfram Engine or Mathematica (`wolframscript` on `PATH`), run from the repository root (`s_prize_research/`):

```powershell
wolframscript -file wolfram_submission/VerifyPureSUniversality.wls
```

The script exits with code `0` after verifying:
1. Native contraction on the 10-leaf seed $D_{\mathrm{seed}} \equiv S(S(SS))(S(SS))(SS)S$.
2. The $S$-algebra law $((q_S \odot x)\odot y)\odot z = (x\odot z)\odot(y\odot z)$ across all $39^3 = 59{,}319$ triples of $\mathcal{A}_{\mathrm{SN}}$ and $35^3 = 42{,}875$ triples of $\mathcal{A}_{\mathrm{HN}}$.
3. Alternation of $\mathrm{SN}$ and $\overline{\mathrm{SN}}$ along the Question 7 refinement sequence $F_0, \dots, F_8$.
4. Direct root-restarted pure-$S$ simulation of the 2-state Busy Beaver $\mathrm{BB}(2)$ to acceptance by $\mathcal{H}_{11}$.
5. Exact unfolded leaf counts for compiled Turing machines ($1{,}996{,}921$ leaves for the 1-state empty-input machine; $7{,}477{,}337$ leaves for the 2-state write-`1` machine).
6. End-to-end terminal $U_{3,11} \to \mathrm{CL}(S)$ cycle execution, $\mathcal{H}_{11}$ halting detection, and `DecodePureSOutput` readback.
7. All $59{,}319$ triples of $\mathcal{A}_P$, all $36^3 = 46{,}656$ triples of $\mathcal{A}_{36}$, productivity separation of $Z_{\mathrm{Zac}}$ vs. $W_2$, and $\llbracket A A A \rrbracket_{36} \neq \llbracket A A A S \rrbracket_{36}$.
8. All 8 truth-table rows and multi-generation periodic Spine-1 normal-form evolution of `PureSRule110Term` in $\mathcal{D}_4$.
9. Quadratic step milestones $\{0, 2, 5, 9, 14, 20, 27, 35, 44, 54\}$ of $\mathcal{B}_Z$ along $Z_{\mathrm{Zac}}$.
10. Program-free cyclic tag simulation on `{{1}, {}}` with input `{1, 0, 1}`, including explicit genesis of `EncodeProgramFreeCTS` from $D_{\mathrm{seed}}$ and macro-step queue readback.
11. Classification of all 12 Wolfram announcement benchmarks, the two 7-leaf minimal non-$\mathrm{SN}$ witnesses, and the 9-leaf productive witness $Z_0$.
12. Exact rational identity $c_{\mathrm{HN}} + (1 - c_{\mathrm{HN}}) = 1$ with $c_{\mathrm{HN}} = 4429673/7077888$, degree-35 minimal polynomials, and Catalan phase counts for $1 \le n \le 12$.

To run the standalone Python syntax, matrix-parity, and simulation cross-validator (no Wolfram license required):

```powershell
python -X utf8 wolfram_submission/cross_validate_wl.py
```
