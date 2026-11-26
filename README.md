# Computational Universality, Finite Tree Algebras, and Asymptotic Phase Transitions of the Pure $S$ Combinator

This repository contains the manuscripts, constructive Lean 4.33.1 formalization, Wolfram Language implementation, and standalone Python verification suite prepared for the Wolfram $S$ Combinator Challenge (`DOI: 10.31855/7709b85c-8e6`).

## Primary Deliverables

### 1. Archival Monographs
- [`WOLFRAM_S_PRIZE_SUBMISSION.pdf`](WOLFRAM_S_PRIZE_SUBMISSION.pdf) — Typeset English monograph (Computer Modern / KaTeX mathematical typography).
- [`WOLFRAM_S_PRIZE_SUBMISSION.tex`](WOLFRAM_S_PRIZE_SUBMISSION.tex) — Complete $\LaTeX$ source of the English monograph, including the theorem-to-Lean concordance in Appendix A.
- [`WOLFRAM_S_PRIZE_SUBMISSION.md`](WOLFRAM_S_PRIZE_SUBMISSION.md) — GitHub-flavored Markdown edition of the English monograph.

### 2. Constructive Lean 4.33.1 Formalization (`153` Transitive Modules)
- [`s_challenge_master_headline.lean`](s_challenge_master_headline.lean) — Unified entry point (`namespace SChallengeMaster`) importing all `153` formal Lean modules, proving exact abstract-syntax and one-step reduction bijections across all subsystem term types, and re-exporting all seven headline theorem suites.
- [`check_formal.ps1`](check_formal.ps1) — Standalone PowerShell build and kernel-axiom verification script using the bundled Lean 4.33.1 toolchain (`tools/lean-4.33.1-windows/bin/lean.exe`). Every exported theorem compiles with zero `sorry`, zero `admit`, zero user-declared `axiom`, zero `native_decide`, and zero `Classical.choice` (`#print axioms` reports at most `[propext, Quot.sound]`, `[propext]`, or `[]`).

Key formal subsystems imported by `s_challenge_master_headline.lean`:
- `formal_utm/` and `formal_controller/` — Unrestricted binary Turing machine compilation via Neary and Woods's $U_{3,11}$, explicit $4{,}376{,}490{,}905$-state memoryless root-restarted occurrence-tree walker (`invoke`), minimal 11-state bottom-up halting tree automaton (`haltAutomaton`), polynomial trajectory leaf bounds, and linear-time bare-term output decoder (`decodeBareSTermOutput`).
- `formal_program_free/` — Program-free bare-term cyclic tag system simulation (`pfSelect : Term → PFOutcome`) containing no embedded universal transition table, together with constructive reachability from the 10-leaf seed $D_{\mathrm{seed}} \equiv S(S(SS))(S(SS))(SS)S$.
- `formal_algebra/` and `formal_top_termination/` — Trivial-rule controller separation (`Leaf → Node Leaf Leaf`), Waldmann's 39-state strong-normalization algebra $\mathcal{A}_{\mathrm{SN}}$, the 35-state head-normalization algebra $\mathcal{A}_{\mathrm{HN}}$ (Question 10 of Barendregt et al. 2017), Footnote 4 root-normal-form characterization, Question 7 flip-flop refinement chain, and constructive root normalization (`toRNF`).
- `formal_q5_final/` and `q5_sn_stratified_game/` — Constructive resolution of Question 5 of Barendregt, Endrullis, Klop, and Waldmann (2017): decidability and regularity of Böhm-tree productivity on closed pure-$S$ terms via the 39-state conversion-invariant $S$-algebra $\mathcal{A}_P$, canonical productive values $\mathcal{V}_P$, and rank-17 Patricia-tree stratification (`FormalQ5Final.barendregt_open_question_5` and `FormalQ5Final.productive_or_hasBot_closed`).
- `intrinsic_research/`, `zero_navigator_fixed_order/`, `zero_navigator_multiway/`, and `zero_navigator_cellular/` — The 36-state conversion-invariant algebra $\mathcal{A}_{36}$ separating $A A A$ from $A A A S$ (Question 31), Scott's $G_k$ cofinality (Question 30), the Case-3 ceiling ($\le 5$ consecutive leftmost-innermost Case-3 steps), pure-line six-strategy coincidence, Zachos quadratic trace automaton $\mathcal{B}_Z$, nonexistence of Church booleans under $\to_S^*$, Post-lattice monotonicity barriers, and the minimal 11-leaf Spine-1 Rule 110 polynomial in $\mathcal{D}_4$.
- `formal_wolfram12/`, `formal_census_and_minimality/`, and `formal_asymptotics/` — Exact dynamical classification of Wolfram's 12 challenge expressions plus Duboué's minimal 7-leaf witnesses $X_1, X_2$ (and separation from $Z_0$ and $Z_{\mathrm{Zac}}$), minimal leaf-size thresholds ($7$ for $\overline{\mathrm{SN}}$, $8$ for $\overline{\mathrm{HN}}$, $9$ for $\mathrm{Prod} \setminus \mathrm{SN}$), exact Catalan/Motzkin phase counts, the rational head-normalizing asymptotic density $c_{\mathrm{HN}} = 4429673/7077888$, and exponential rarity of $\mathrm{SN}$ and $\mathrm{Prod}$.

### 3. Wolfram Language Package and Test Suite
- [`wolfram_submission/PureSUniversality.wl`](wolfram_submission/PureSUniversality.wl) — Self-contained Wolfram Language package (`PureSUniversality` context) implementing all encoders, selectors, finite $S$-algebras, cellular polynomials, benchmark classifiers, and Catalan phase censuses using iterative DAG-memoized folds.
- [`wolfram_submission/VerifyPureSUniversality.wls`](wolfram_submission/VerifyPureSUniversality.wls) — Standalone 12-block WolframScript test suite.
- [`wolfram_submission/cross_validate_wl.py`](wolfram_submission/cross_validate_wl.py) — Independent Python parser and bit-for-bit table/simulation cross-validator against the Lean 4 formalization.
- [`wolfram_submission/README.md`](wolfram_submission/README.md) — Exported symbol reference and usage documentation.

### 4. Standalone Python Verification and Audit Suites
- [`verify_all_theorems.py`](verify_all_theorems.py) and [`verification_report.json`](verification_report.json) — Self-contained 18-stage Python verification suite independently checking every finite algebra, Myhill–Nerode quotient, universal compiler, benchmark trajectory, Open Question 5 rank certificate, and Catalan asymptotic identity.
- [`adversarial_referee_audit/run_adversarial_audit.py`](adversarial_referee_audit/run_adversarial_audit.py), [`adversarial_referee_audit/axiom_deep_audit.lean`](adversarial_referee_audit/axiom_deep_audit.lean), and [`adversarial_referee_audit/referee_audit_report.md`](adversarial_referee_audit/referee_audit_report.md) — Automated static scanner across all `.lean` files, transitive `.olean` freshness checker, 97-declaration Lean kernel `#print axioms` auditor, and cross-language matrix parity checker.

---

## Reproducing All Verification Checks

Run the following commands from this directory (`s_prize_research/`):

1. **Full 153-module Lean 4.33.1 build and constructive axiom check:**
   ```powershell
   powershell -ExecutionPolicy Bypass -File .\check_formal.ps1
   ```

2. **Direct kernel check of the master headline module:**
   ```powershell
   $env:LEAN_PATH = (Get-Location).Path
   .\tools\lean-4.33.1-windows\bin\lean.exe -o s_challenge_master_headline.olean s_challenge_master_headline.lean
   ```

3. **Standalone 18-stage Python mathematical verification suite:**
   ```powershell
   python -X utf8 .\verify_all_theorems.py
   ```

4. **Wolfram Language package cross-validation (and optional `wolframscript` execution):**
   ```powershell
   python -X utf8 .\wolfram_submission\cross_validate_wl.py
   # If Wolfram Engine / Mathematica is installed:
   wolframscript -file .\wolfram_submission\VerifyPureSUniversality.wls
   ```

5. **Deep kernel `#print axioms` and cross-language audit:**
   ```powershell
   python -X utf8 .\adversarial_referee_audit\run_adversarial_audit.py
   ```
---

## 60-Second Human-Auditable Specification Check (`TRUST_ZERO_SPEC_CHECK.lean`)

To verify this formalization without reading all 154 proof modules, inspect [`TRUST_ZERO_SPEC_CHECK.lean`](TRUST_ZERO_SPEC_CHECK.lean) (~110 lines):
- **Part 1 (`rfl` Definitional Checks):** Verifies that `Term`, `Step` ($S x y z \to (x z)(y z)$), `StrongNormalizing`, `HasNormalForm`, `HasHNF`, `IsRootNormalForm`, and `Productive` ($\neg\exists d,\, \bot_d(M)$) are definitionally equal to the standard textbook notions, and checks the syntax/step isomorphism with `SChallengeMaster`.
- **Part 2 & Part 3 (`#check` and `#print axioms`):** Prints the exact Lean kernel type signatures and axiom footprints of the main theorems (confirming zero `sorry`, zero custom `axiom`s, zero `native_decide`, and zero `Classical.choice`).

With [`elan`](https://github.com/leanprover/elan) installed (`lean-toolchain` pins `leanprover/lean4:v4.33.1`), run:
```bash
# Linux / macOS:
bash ./check_formal.sh

# Windows PowerShell:
powershell -ExecutionPolicy Bypass -File .\check_formal.ps1
```

## Transparency & Verification Note

Multi-agent AI tools were used under the author's direction to assist in proof exploration, reflection-table generation, and manuscript preparation. Every theorem reported in the monograph and concordance table is verified inside the **Lean 4.33.1 logical kernel** (core/`Std` only, with no external library dependencies and no appeal to `Classical.choice` or `native_decide`) and independently cross-checked by `PureSUniversality.wl` and `verify_all_theorems.py`.
