import formal_algebra.all_algebra_open_problems
import formal_top_termination.top_termination
import intrinsic_research.intrinsic_theorems
import formal_q5_final.q5_completeness
import s_challenge_master_headline

/-!
# 60-Second Human-Auditable Specification Check (`TRUST_ZERO_SPEC_CHECK.lean`)

To verify a large mechanized development without reading 150+ proof files, an auditor only needs to check two things:
1. **Specification Fidelity:** Do `Term`, `Step`, `StrongNormalizing`, `HasNormalForm`, `HasHNF`, `IsRootNormalForm`, and `Productive` match the standard textbook definitions of pure-`S` combinatory logic (`S x y z → (x z)(y z)`)?
2. **Kernel & Axiom Purity:** Does Lean 4's kernel accept the headline theorems with zero `sorry`, zero custom `axiom`s, zero `native_decide`, and zero `Classical.choice`?

Run from the repository root with Lean 4.33.1 (`LEAN_PATH=.`):
```bash
lean TRUST_ZERO_SPEC_CHECK.lean
```
-/

namespace TrustZeroAudit

/-! ## Part 1: Definitional Sanity Checks (`rfl`) on Pure-`S` Syntax & Rewriting -/

example :
    (FormalAlgebra.S = FormalAlgebra.Term.s) ∧
    (∀ x y z : FormalAlgebra.Term,
      FormalAlgebra.Step (FormalAlgebra.S ⋅ x ⋅ y ⋅ z) ((x ⋅ z) ⋅ (y ⋅ z))) ∧
    (∀ t : FormalAlgebra.Term,
      FormalAlgebra.StrongNormalizing t ↔ Acc (fun b a => FormalAlgebra.Step a b) t) ∧
    (∀ t : FormalAlgebra.Term,
      FormalAlgebra.HasNormalForm t ↔
        ∃ nf, FormalAlgebra.Reduces t nf ∧ (∀ t', ¬ FormalAlgebra.Step nf t')) ∧
    (∀ t : FormalAlgebra.Term,
      FormalAlgebra.HasHNF t ↔
        ∃ h, FormalAlgebra.Reduces t h ∧ FormalAlgebra.spineLen h ≤ 2) ∧
    (∀ t : FormalAlgebra.Term,
      FormalAlgebra.IsRootNormalForm t ↔
        ¬ ∃ x y z, FormalAlgebra.Reduces t (FormalAlgebra.S ⋅ x ⋅ y ⋅ z)) :=
  ⟨rfl, FormalAlgebra.Step.root, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

-- Verify `Q5SNStratifiedGame.Productive` is definitionally `¬ ∃ d, HasBotWithin d t`:
example (t : FormalAlgebra.Term) :
    Q5SNStratifiedGame.Productive t = (¬ ∃ d : Nat, Q5SNStratifiedGame.HasBotWithin d t) := rfl

-- Verify the root `Term` / `Step` AST in `s_challenge_master_headline.lean` is proved isomorphic to `FormalAlgebra.Term` / `FormalAlgebra.Step`:
#check @SChallengeMaster.ofAlgebra_toAlgebra
#check @SChallengeMaster.toAlgebra_ofAlgebra
#check @SChallengeMaster.step_iff_algebraStep

/-! ## Part 2: Exact Type Signatures of Resolved Open Problems (Barendregt et al. 2017) -/

-- 1. Waldmann's 39-state Strong Normalization Theorem (`SN ↔ WN ↔ evalSN ≠ .sn38`):
#check @FormalAlgebra.waldmann_theorem_9

-- 2. Open Question 10 & Footnote 4 (35-state `A_HN` for `HasHNF` & linear-time `RNF`):
#check @FormalAlgebra.barendregt_open_problem_10
#check @FormalAlgebra.footnote4_rnf_iff

-- 3. Global Top-Termination & Absence of Berarducci Mute Terms:
#check @FormalTopTermination.waldmann_theorem_29_top_termination
#check @FormalTopTermination.every_closed_sterm_has_rnf

-- 4. Open Question 5 (Regularity & Decidability of Böhm-Tree Productivity via 39-state `A_P`):
#check @FormalQ5Final.barendregt_open_question_5
#check @FormalQ5Final.productive_or_hasBot_closed

-- 5. Open Question 7 (Infinite `SN` / non-`SN` Refinement Chain & `{SS, S(SSS)}` Rescue Classification):
#check @FormalAlgebra.barendregt_question_7_solution
#check @FormalAlgebra.one_step_rescue_classification

-- 6. Open Question 31 (Unfaithfulness of Clocked Böhm Trees: `AAA ≠_S AAAS` via 36-state `A_36`):
#check @IntrinsicTheorems.aaa_not_conv_aaas

-- 7. Grand Master Universality, Controller Separation, Wolfram Benchmarks, and Catalan Phase Laws:
#check @SChallengeMaster.grand_pure_s_tm_universality_and_readback
#check @SChallengeMaster.grand_program_free_cts_universality
#check @SChallengeMaster.grand_controller_separation_and_spurious_halts
#check @SChallengeMaster.grand_zero_navigator_barriers_and_open_problems
#check @SChallengeMaster.grand_wolfram_benchmarks_and_minimality_census
#check @SChallengeMaster.grand_macroscopic_phase_transitions

/-! ## Part 3: Kernel Axiom Footprint Verification (Zero `Classical.choice`, Zero Custom Axioms) -/

#print axioms FormalAlgebra.waldmann_theorem_9
#print axioms FormalAlgebra.barendregt_open_problem_10
#print axioms FormalAlgebra.footnote4_rnf_iff
#print axioms FormalTopTermination.waldmann_theorem_29_top_termination
#print axioms FormalQ5Final.barendregt_open_question_5
#print axioms FormalQ5Final.productive_or_hasBot_closed
#print axioms FormalAlgebra.barendregt_question_7_solution
#print axioms FormalAlgebra.one_step_rescue_classification
#print axioms IntrinsicTheorems.aaa_not_conv_aaas
#print axioms SChallengeMaster.grand_pure_s_tm_universality_and_readback
#print axioms SChallengeMaster.grand_program_free_cts_universality
#print axioms SChallengeMaster.grand_controller_separation_and_spurious_halts
#print axioms SChallengeMaster.grand_zero_navigator_barriers_and_open_problems
#print axioms SChallengeMaster.grand_wolfram_benchmarks_and_minimality_census
#print axioms SChallengeMaster.grand_macroscopic_phase_transitions

end TrustZeroAudit
