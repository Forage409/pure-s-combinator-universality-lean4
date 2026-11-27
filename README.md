# Computational Universality, Finite Tree Algebras, and Asymptotic Phase Transitions of the Pure $S$ Combinator

This repository contains the manuscripts, constructive Lean 4.33.1 formalization, Wolfram Language implementation, and standalone Python verification suite prepared for the Wolfram $S$ Combinator Challenge (`DOI: 10.31855/7709b85c-8e6`) and the open problems and conjectures of Barendregt, Endrullis, Klop, and Waldmann, *Dance of the Starlings* (2017).

## Primary Deliverables

### 1. Archival Monographs & Standalone Short Note
- [`SHORT_NOTE_Q7_Q31.pdf`](SHORT_NOTE_Q7_Q31.pdf) / [`SHORT_NOTE_Q7_Q31.tex`](SHORT_NOTE_Q7_Q31.tex) — Standalone 6-page note giving **short, automaton-free book proofs** of Questions 7 and 31 in *Dance of the Starlings* (eliminating both the 36-state $\mathcal{A}_{36}$ table and the 35-state $\mathcal{A}_{\mathrm{HN}}$ table, strengthening Question 31 to the infinite family $A A A S^j \neq_S A A A S^k$ for all $j \neq k$, and proving the exact atomic leaf-splitting colour law $T_n \in \mathrm{SN} \iff n \not\equiv 9 \pmod{10}$).
- [`WOLFRAM_S_PRIZE_SUBMISSION.pdf`](WOLFRAM_S_PRIZE_SUBMISSION.pdf) — Full 82-page typeset English monograph (Computer Modern / KaTeX mathematical typography).
- [`WOLFRAM_S_PRIZE_SUBMISSION.tex`](WOLFRAM_S_PRIZE_SUBMISSION.tex) — Complete $\LaTeX$ source of the 10-section English monograph, including the 49-row theorem-to-Lean concordance in Appendix A.
- [`WOLFRAM_S_PRIZE_SUBMISSION.md`](WOLFRAM_S_PRIZE_SUBMISSION.md) — GitHub-flavored Markdown edition of the English monograph.

### 2. Constructive Lean 4.33.1 Formalization (`202` Transitive Modules + Standalone Book Proofs)
- [`SIMPLIFIED_Q31_Q7_BOOK_PROOFS.lean`](SIMPLIFIED_Q31_Q7_BOOK_PROOFS.lean) — Zero-import, automaton-free Lean 4.33.1 formalization of the simplified proofs of Questions 31 and 7 (including Takahashi's Church–Rosser theorem from scratch; `#print axioms`: `[propext, Quot.sound]` only).
- [`TRUST_ZERO_SPEC_CHECK.lean`](TRUST_ZERO_SPEC_CHECK.lean) — 60-second human-auditable specification & `#print axioms` check across all 10 unified grand theorems and all 11 open questions and conjectures of Barendregt et al. (2017).
- [`s_challenge_master_headline.lean`](s_challenge_master_headline.lean) — Unified entry point (`namespace SChallengeMaster`) importing all `202` transitive formal Lean modules, proving exact abstract-syntax and one-step reduction bijections across all subsystem term types, and re-exporting all 10 grand theorem suites.
- [`check_formal.ps1`](check_formal.ps1) / [`check_formal.sh`](check_formal.sh) — Standalone build and kernel-axiom verification scripts for Lean 4.33.1. Every exported theorem compiles with zero `sorry`, zero `admit`, zero user-declared `axiom`, zero `native_decide`, and zero `Classical.choice` (`#print axioms` reports at most `[propext, Quot.sound]`, `[propext]`, or `[]`).

Key formal subsystems imported by `s_challenge_master_headline.lean`:
- `formal_utm/` and `formal_controller/` — Unrestricted binary Turing machine compilation via Neary and Woods's $U_{3,11}$, explicit $4{,}376{,}490{,}905$-state memoryless root-restarted occurrence-tree walker (`invoke`), minimal 11-state bottom-up halting tree automaton (`haltAutomaton`), polynomial trajectory leaf bounds, and linear-time bare-term output decoder (`decodeBareSTermOutput`).
- `formal_program_free/` and `formal_wolfram_frontier/` — Program-free bare-term cyclic tag system simulation (`pfSelect : Term → PFOutcome`) reachable from the 10-leaf seed $D_{\mathrm{seed}} \equiv S(S(SS))(S(SS))(SS)S$, compressed into an explicit two-pass `(Fin 25, Fin 23, Fin 136)` contextual pocket tree transducer (`pocketPFTransducer`) halting in at most $2|M| - 1 + \mathrm{depth}(M)$ transitions per contraction (`+ 2 ≤ ...` strictly on `.step`); plus all-step $\to_{\mathrm{lo}}$ cubic closed forms (`zachos`, `wolfram_2`, $+14$ `w2Twin` shift, `tenLeafSeed`) and Garden-of-Eden normal-form characterization, decidability, and size-$1..7$ census.
- `formal_no_spiral/`, `formal_conjecture17_obstructions/`, `formal_conjecture17_deep/`, and `formal_order_and_isolated/` — Ranked leaf-preserving $\Delta L = -2$ conservation law (`leftSubtreeSum`) with sharp quarter-square bound $\lfloor(n-2)^2/4\rfloor$, constructive Bergstra/Waldmann/Klop non-spiralling and flat $\{S,K\}$ theorems, dependency-pair self-right-tail and universal $\mathrm{minRS}_x/\mathrm{minLS}_x$ monotonicity obstructions toward Conjecture 17, Visser–van Oostrom functional orders $\{0, 1, 2, 3\}$ with minimal $35$-, $12$-, and $3$-state $S$-algebras, and certified exact rational Catalan order densities $(c_0, c_1, c_2, c_3) = (2{,}648{,}215/7{,}077{,}888,\, 1{,}864{,}553/7{,}077{,}888,\, 835/2{,}304,\, 0)$.
- `formal_algebra/`, `formal_top_termination/`, `formal_q5_final/`, `q5_sn_stratified_game/`, `formal_q10_q5_simplified/`, and `formal_q30_q31_deep/` — Trivial-rule controller separation (`Leaf → Node Leaf Leaf`), Waldmann's 39-state $\mathcal{A}_{\mathrm{SN}}$ and global top-termination (`toRNF`), Question 10 & Footnote 4 (35-state $\mathcal{A}_{\mathrm{HN}}$, automaton-free head conservation, and pointwise minimal pure multiplier `hnA` with $B \equiv 0$), Question 5 (39-state $\mathcal{A}_P$, rank-10 reduction, 113-state `PH` Myhill–Nerode minimality, and size-8 Böhm-game asymmetry), and Questions 30 & 31 (productive Böhm faithfulness and decidability on $\mathrm{Prod} \times \mathcal{T}_S$, single-$\bot$ unfaithfulness, and clocked-Böhm fine structure).
- `formal_lambda_conjectures/` and `formal_q32_equational/` — Constructive weak-head standardization and Church's $\lambda\mathrm{I}$ conservation ($\mathrm{WN}_\beta \iff \mathrm{SN}_\beta$), affirmative resolution of Conjecture 40 across $\mathrm{CL}(\{S,K,I\})$ and $\mathrm{CL}(S)$, simultaneous refutation of Conjectures 42 and 43 at 14 leaves ($M_{14}$) and 15 leaves in normal form ($M_{15}$) with the bilateral `DeepNorm` saturation repair, single-constant `DeepNorm_1` reduction, unique absorbing sink $\infty_{34}$, and $q_6$ four-way splitting for Question 34, and the negative resolution of Question 32 (`no_finite_equational_axiomatization_of_lambda_beta`) via $S$-free backward-cone rigidity and deep $T$-core variable abstraction on $(M_m(y), N_m(y))$ of sizes $(2m + 10, 2m + 13)$.
- `intrinsic_research/`, `zero_navigator_fixed_order/`, `zero_navigator_multiway/`, `zero_navigator_cellular/`, `formal_wolfram12/`, `formal_census_and_minimality/`, and `formal_asymptotics/` — Pure-line six-strategy coincidence, Zachos quadratic trace automaton $\mathcal{B}_Z$, sharp 5-step innermost Case-3 ceiling, nonexistence of Church booleans under $\to_S^*$, Post-lattice monotonicity barriers, minimal 11-leaf Spine-1 Rule 110 polynomial in $\mathcal{D}_4$, Wolfram's 14 benchmark evolutions, small-term Catalan census ($1 \le n \le 11$), $c_{\mathrm{HN}} = 4{,}429{,}673/7{,}077{,}888$, and exponential decay of $\mathrm{SN}$ and $\mathrm{Prod}$.

### 3. Wolfram Language Package and Test Suite
- [`wolfram_submission/PureSUniversality.wl`](wolfram_submission/PureSUniversality.wl) — Self-contained Wolfram Language package (`PureSUniversality` context) implementing all encoders, selectors, finite $S$-algebras, functional-order classifiers, Garden-of-Eden detectors, cellular polynomials, closed-form cubic jump-ahead formulas, and Catalan phase censuses using iterative DAG-memoized folds.
- [`wolfram_submission/VerifyPureSUniversality.wls`](wolfram_submission/VerifyPureSUniversality.wls) — Standalone 16-block WolframScript test suite.
- [`wolfram_submission/cross_validate_wl.py`](wolfram_submission/cross_validate_wl.py) — Independent Python parser and bit-for-bit table/simulation cross-validator against the Lean 4 formalization.
- [`wolfram_submission/README.md`](wolfram_submission/README.md) — Exported symbol reference and usage documentation.

### 4. Standalone Python Verification and Audit Suites
- [`verify_all_theorems.py`](verify_all_theorems.py) and [`verification_report.json`](verification_report.json) — Self-contained 19-stage Python verification suite independently checking every finite algebra, Myhill–Nerode quotient, universal compiler, benchmark trajectory, Open Question 5 rank certificate, Open Question 32 tower family, and Catalan asymptotic identity.
- [`adversarial_referee_audit/run_adversarial_audit.py`](adversarial_referee_audit/run_adversarial_audit.py), [`adversarial_referee_audit/axiom_deep_audit.lean`](adversarial_referee_audit/axiom_deep_audit.lean), and [`adversarial_referee_audit/referee_audit_report.md`](adversarial_referee_audit/referee_audit_report.md) — Automated static scanner across all `286` `.lean` files, `202`-module transitive `.olean` freshness checker, `161`-declaration Lean kernel `#print axioms` auditor, and cross-language matrix parity checker.

---

## Reproducing All Verification Checks

Run the following commands from the repository root:

1. **Full 202-module Lean 4.33.1 build and constructive axiom check:**
   ```powershell
   powershell -ExecutionPolicy Bypass -File .\check_formal.ps1
   ```

2. **Direct kernel check of the master headline and trust-zero specification modules:**
   ```powershell
   $env:LEAN_PATH = (Get-Location).Path
   lean -o s_challenge_master_headline.olean s_challenge_master_headline.lean
   lean .\TRUST_ZERO_SPEC_CHECK.lean
   ```

3. **Standalone Python mathematical verification suite:**
   ```powershell
   python -X utf8 .\verify_all_theorems.py
   ```

4. **Wolfram Language package cross-validation (and optional `wolframscript` execution):**
   ```powershell
   python -X utf8 .\wolfram_submission\cross_validate_wl.py
   # If Wolfram Engine / Mathematica is installed:
   wolframscript -file .\wolfram_submission\VerifyPureSUniversality.wls
   ```

5. **Deep kernel `#print axioms` (`161` declarations) and cross-language audit:**
   ```powershell
   python -X utf8 .\adversarial_referee_audit\run_adversarial_audit.py
   ```

---

## 60-Second Human-Auditable Specification Check (`TRUST_ZERO_SPEC_CHECK.lean`)

To verify this formalization without reading all `202` proof modules, inspect [`TRUST_ZERO_SPEC_CHECK.lean`](TRUST_ZERO_SPEC_CHECK.lean) (~130 lines):
- **Part 1 (`rfl` Definitional Checks):** Verifies that `Term`, `Step` ($S x y z \to (x z)(y z)$), `StrongNormalizing`, `HasNormalForm`, `HasHNF`, `IsRootNormalForm`, and `Productive` ($\neg\exists d,\, \bot_d(M)$) are definitionally equal to the standard textbook notions, and checks the syntax/step isomorphisms across all AST namespaces in `SChallengeMaster`.
- **Part 2 & Part 3 (`#check` and `#print axioms`):** Prints the exact Lean kernel type signatures and axiom footprints of all 10 unified grand theorems and subsystem pillars (confirming zero `sorry`, zero custom `axiom`s, zero `native_decide`, and zero `Classical.choice`).

With [`elan`](https://github.com/leanprover/elan) installed (`lean-toolchain` pins `leanprover/lean4:v4.33.1`), run:
```bash
# Linux / macOS:
bash ./check_formal.sh

# Windows PowerShell:
powershell -ExecutionPolicy Bypass -File .\check_formal.ps1
```

## Transparency & Verification Note

Multi-agent AI tools were used under the author's direction to assist in proof exploration, reflection-table generation, and manuscript preparation. Every theorem reported in the monograph and concordance table is verified inside the **Lean 4.33.1 logical kernel** (core/`Std` only, with no external library dependencies and no appeal to `Classical.choice` or `native_decide`) and independently cross-checked by `PureSUniversality.wl` and `verify_all_theorems.py`.
